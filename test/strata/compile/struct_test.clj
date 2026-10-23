(ns strata.compile.struct-test
  (:require [clojure.test :refer [deftest is testing]]
            [strata.test-util :refer [parse-src]])
  (:import (java.nio ByteBuffer ByteOrder)))

(defn- err [f]
  (try (f) nil (catch clojure.lang.ExceptionInfo e (ex-data e))))

(defn- p
  "Parses bytes with a one-struct program; field-vec is the field vector."
  [fields bs & [opts]]
  (parse-src [(list 'defstruct 's fields)] 's bs (or opts {})))

(defn- v-size [b] (strata.values/bsize b))

(defn- why [fields bs]
  (select-keys (p fields bs {:explain? true}) [:ok :reason :path :offset]))

(defn- encode
  "Test encoder: n-byte big/little-endian bytes of a long, or float bits."
  [prim x order]
  (let [n ({:u16 2 :u32 4 :i8 1 :f64 8} prim)
        bb (doto (ByteBuffer/allocate n) (.order order))]
    (case prim
      :u16 (.putShort bb (unchecked-short x))
      :u32 (.putInt bb (unchecked-int x))
      :i8 (.put bb (unchecked-byte x))
      :f64 (.putDouble bb (double x)))
    (mapv #(bit-and 0xff (long %)) (.array bb))))

(deftest prims-endian
  (doseq [[order e] [[ByteOrder/LITTLE_ENDIAN :le] [ByteOrder/BIG_ENDIAN :be]]]
    (let [bs (vec (concat (encode :u16 0xBEEF order) (encode :u32 0xDEADBEEF order)
                          (encode :i8 -5 order) (encode :f64 1.5 order)))
          r (parse-src [(list 'defstruct 's {:endian e}
                              '[a :u16 b :u32 c :i8 d :f64 e [:u16 :be]])]
                       's (into bs [0x12 0x34]))]
      (is (= {:a 0xBEEF :b 0xDEADBEEF :c -5 :d 1.5 :e 0x1234} (:value r)) (str e))
      (is (= 17 (:end r))))))

(deftest signed-prims
  (is (= {:a -2 :b -3 :c -4}
         (:value (p '[a :i16 b :i32 c :i64] (concat [0xFE 0xFF] [0xFD 0xFF 0xFF 0xFF]
                                                    [0xFC 0xFF 0xFF 0xFF 0xFF 0xFF 0xFF 0xFF]))))))

(deftest u64-full
  (is (= 18446744073709551615N (:a (:value (p '[a :u64] (repeat 8 0xff))))))
  (is (= 5 (:a (:value (p '[a :u64] [5 0 0 0 0 0 0 0]))))))

(deftest sized-exact
  (is (= {:a 1 :b 5} (:value (p '[a [:sized 4 [:u8]] b :u8] [1 2 3 4 5]))))
  (is (= {:a 1 :b 5} (:value (p '[a [:sized 4 :u8] b :u8] [1 2 3 4 5]))))
  (is (= 5 (:end (p '[a [:sized 4 :u8] b :u8] [1 2 3 4 5]))))
  (is (nil? (p '[a [:sized 4 [:bytes 5]]] [1 2 3 4 5 6])))
  (is (= :window (:reason (why '[a [:sized 4 [:bytes 5]]] [1 2 3 4 5 6]))))
  (is (= :window (:reason (why '[a [:sized 9 :u8]] [1 2 3]))))
  (testing "nested structs obey the enclosing window"
    (is (nil? (parse-src '[(defstruct inner [a :u8 b :u8])
                           (defstruct s [x [:sized 1 inner]])]
                         's [1 2 3])))))

(deftest at-zero-width
  (let [r (p '[o :u8 x [:at o :u8] y :u8] [2 9 7])]
    (is (= {:o 2 :x 7 :y 9} (:value r)))
    (is (= 2 (:end r))))
  (testing "window bounds do not apply to the target"
    (is (= 4 (:x (:value (p '[x [:sized 1 [:at 3 :u8]]] [0 0 0 4]))))))
  (is (nil? (p '[x [:at -1 :u8]] [1])))
  (is (nil? (p '[x [:at nil :u8]] [1])))
  (is (= :bad-size (:reason (why '[x [:at nil :u8]] [1])))))

(deftest repeat-modes
  (is (= [1 2 3] (:xs (:value (p '[xs [:repeat :u8 :eos]] [1 2 3])))))
  (is (= [] (:xs (:value (p '[xs [:repeat :u8 :eos]] [])))))
  (let [r (p '[xs [:repeat :u8 :until (fn [e] (= e 0))] z :u8] [1 2 0 9])]
    (is (= {:xs [1 2 0] :z 9} (:value r))))
  (let [r (p '[xs [:repeat :u8 :sentinel (fn [e] (= e 0))] z :u8] [1 2 0 9])]
    (is (= {:xs [1 2] :z 9} (:value r)))
    (is (= 4 (:end r))))
  (is (nil? (p '[xs [:repeat :u8 :until (fn [e] (= e 0))]] [1 2 3])))
  (is (= :zero-progress (:reason (why '[xs [:repeat [:calc 1] :eos]] [1 2]))))
  (is (= :zero-progress (:reason (why '[xs [:repeat [:calc 1] :until (fn [e] false)]] [1 2]))))
  (is (= :repeat-max (:reason (why '[xs [:repeat :u8 :eos :max 2]] [1 2 3]))))
  (is (= [1 2] (:xs (:value (p '[xs [:repeat :u8 :eos :max 2]] [1 2])))))
  (is (= :repeat-max (:reason (why '[xs [:repeat :u8 :sentinel (fn [e] (= e 0)) :max 2]] [1 2 3 0]))))
  (is (= [1 2] (:xs (:value (p '[xs [:repeat :u8 :sentinel (fn [e] (= e 0)) :max 2]] [1 2 0]))))))

(deftest cstring
  (let [bs (mapv int "abcdef\u0000")]
    (is (nil? (p '[s [:cstring :ascii :max 4]] bs)))
    (is (= :cstring (:reason (why '[s [:cstring :ascii :max 4]] bs)))))
  (let [r (p '[s [:cstring :ascii :max 4]] [97 98 0])]
    (is (= {:s "ab"} (:value r)))
    (is (= 3 (:end r))))
  (is (= :cstring (:reason (why '[s [:cstring :ascii]] [97 98]))))
  (testing "window limits the scan"
    (is (nil? (p '[a [:sized 2 [:cstring :ascii]]] [97 98 0]))))
  (is (= {:s "hi" } (:value (p '[s [:cstring :utf16le]] [104 0 105 0 0 0]))))
  (is (= :encoding (:reason (why '[s [:cstring :ascii]] [200 0])))))

(deftest string-trims-nul
  (is (= {:s ".text"} (:value (p '[s [:string 8 :ascii]] (concat (map int ".text") [0 0 0])))))
  (is (= 8 (:end (p '[s [:string 8 :ascii]] (concat (map int ".text") [0 0 0])))))
  (is (= :encoding (:reason (why '[s [:string 2 :ascii]] [200 65]))))
  (is (= {:s "é"} (:value (p '[s [:string 2 :utf8]] [0xc3 0xa9])))))

(deftest const
  (is (= {:m "MZ"} (:value (p '[m [:const "MZ"]] [77 90]))))
  (is (= {:m [1 2]} (:value (p '[m [:const [1 2]]] [1 2]))))
  (is (= {:ok false :reason :const :path [:magic] :offset 0}
         (why '[magic [:const "MZ"]] [77 91]))))

(deftest try-and-if-omit
  (is (= {:c 5} (:value (p '[a [:try [:const "X"]] b [:if false :u8] c :u8] [5]))))
  (is (= {:a "X" :b 1 :c 5} (:value (p '[a [:try [:const "X"]] b [:if true :u8] c :u8] [88 1 5]))))
  (is (= 1 (:end (p '[a [:try [:const "X"]] b [:if false :u8] c :u8] [5])))))

(deftest hidden-and-anon
  (is (= {:b 3} (:value (p '[_a :u8 _ :u8 b [:calc (+ _a 1)]] [2 9])))))

(deftest switch
  (is (= {:t 1 :v 7} (:value (p '[t :u8 v [:switch t {1 :u8 2 :u16}]] [1 7]))))
  (is (= :switch (:reason (why '[t :u8 v [:switch t {1 :u8}]] [3 7]))))
  (is (= {:t 3 :v 7} (:value (p '[t :u8 v [:switch t {1 [:calc 0]} :u8]] [3 7])))))

(deftest enum-unknown
  (is (= {:k :a} (:value (p '[k [:enum :u8 {1 :a}]] [1]))))
  (is (= {:k 9} (:value (p '[k [:enum :u8 {1 :a}]] [9])))))

(deftest assert-calc-skip-align
  (is (= {:a true} (:value (p '[a [:assert (= 1 1)]] []))))
  (is (= :assert (:reason (why '[a [:assert (= 1 2)]] []))))
  (is (= {:x 9} (:value (p '[_ [:skip 2] x :u8] [0 0 9]))))
  (is (nil? (p '[_ [:skip 4]] [0 0 9])))
  (let [r (p '[a :u8 _ [:align 4] b :u8] [1 0 0 0 7])]
    (is (= {:a 1 :b 7} (:value r)))
    (is (= 5 (:end r))))
  (is (= {:a 1} (:value (p '[a :u8 _ [:align 1]] [1]))))
  (is (= :eof (:reason (why '[a :u8 _ [:align 4]] [1 0])))))

(deftest positional
  (let [r (p '[a :u8 p [:calc $pos] s [:calc $start] r [:calc $remaining]] [1 2 3 4])]
    (is (= {:a 1 :p 1 :s 0 :r 3} (:value r))))
  (is (= {:r 1}
         (:value (p '[_ :u8 r [:sized 1 [:calc $remaining]]] [0 5])))
      "$remaining is measured at the start of the field")
  (is (= {:s 2} (:value (p '[s [:calc $start]] [0 0 0] {:off 2})))))

(deftest params
  (let [defs '[(defstruct p [n] [xs [:array :u8 n]])
               (defstruct s [a :u8 q [p 2]])]]
    (is (= {:a 1 :q {:xs [7 8]}} (:value (parse-src defs 's [1 7 8]))))
    (is (= {:xs [7 8]} (:value (parse-src defs 'p [7 8] {:args [2]})))))
  (testing "deftype aliases"
    (let [defs '[(deftype w :u16)
                 (deftype arr [n] [:array :u8 n])
                 (defstruct s [a w b [arr 2] c [arr a]])]]
      (is (= {:a 1 :b [5 6] :c [7]} (:value (parse-src defs 's [1 0 5 6 7])))))))

(deftest defn-in-expressions
  (is (= {:n 2 :xs [8 9]}
         (:value (parse-src '[(defn double [x] (* 2 x))
                              (defstruct s [n :u8 xs [:array :u8 (double (/ n 2))]])]
                            's [2 8 9] )))))

(deftest recursion
  (let [defs '[(defstruct node [more :u8 child [:if (= more 1) node]])]
        depth (fn [n] (vec (concat (repeat n 1) [0])))]
    (is (= {:more 1 :child {:more 1 :child {:more 1 :child {:more 0}}}}
           (:value (parse-src defs 'node (depth 3)))))
    (is (= :depth-exceeded (:strata/error (err #(parse-src defs 'node (depth 1000))))))))

(deftest eof-edges
  (is (nil? (p '[a :u8] [])))
  (is (= {:a 0} (-> (p '[a [:bytes 0]] []) :value (update :a v-size))))
  (is (= {:a 0} (-> (p '[_ :u8 a [:bytes :rest]] [1]) :value (update :a v-size))))
  (is (= {:a 0} (-> (p '[a [:bytes :rest]] []) :value (update :a v-size))))
  (is (nil? (p '[a [:at 1 :u8]] [1])))
  (is (= :eof (:reason (why '[a [:at 1 :u8]] [1]))))
  (is (= 0 (:end (p '[a [:bytes 0]] [])))))

(deftest explain
  (is (= {:ok false :reason :const :path [:magic] :offset 0}
         (why '[magic [:const "MZ"]] [1 2])))
  (is (= {:ok true :value {:a 1} :end 1}
         (p '[a :u8] [1] {:explain? true})))
  (is (= {:ok false :reason :eof :path [:xs 1] :offset 1}
         (why '[xs [:array :u8 2]] [1])))
  (is (= [:in :v]
         (:path (parse-src '[(defstruct inner [v :u8]) (defstruct s [in inner])]
                           's [] {:explain? true})))
      "nested struct fields extend the path")
  (testing "a swallowed :try failure is not reported for a later success"
    (is (:ok (p '[a [:try [:const "X"]]] [1] {:explain? true})))))

(deftest bad-size-type
  (is (= :type-error (:strata/error (err #(p '[a [:bytes "x"]] [1 2 3])))))
  (is (= :type-error (:strata/error (err #(p '[a [:array :u8 1.5]] [1 2 3])))))
  (is (nil? (p '[a [:bytes nil]] [1 2 3])))
  (is (nil? (p '[a [:bytes -1]] [1 2 3])))
  (is (= :bad-size (:reason (why '[a [:bytes nil]] [1])))))

(deftest fuel-charged-per-field
  (is (= :fuel-exhausted
         (:strata/error (err #(p '[a :u8 b :u8 c :u8] [1 2 3] {:limits {:fuel 2}}))))))

(deftest struct-relation
  (let [defs '[(defstruct p [n] [xs [:array :u8 n]])]
        rel (fn [src off & args]
              (parse-src defs 'p src {:relation? true :off off :args (vec args)}))]
    (is (= [[{:xs [1 2]} 2]] (rel [1 2 3] 0 2)))
    (is (= [[{:xs [2 3]} 3]] (rel [1 2 3] 1 2)))
    (is (= [] (rel [1 2 3] 2 2)))
    (is (= [] (rel [1 2 3] nil 2))))
  (let [r (requiring-resolve 'strata.compile.struct/struct-relation)
        rel (r {:qname 'user/p :arity 1 :parse (fn [& _] nil)})]
    (is (= 5 (:arity rel)))
    (is (= [[0 1 2] [3 4]] ((juxt :in :out) (first (:modes rel)))))
    (is (fn? (:impl (first (:modes rel)))))))

(deftest at-skip-align-past-eof
  (is (nil? (p '[x [:at 100 [:repeat :u8 :eos]]] [1 2 3])))
  (is (nil? (p '[x [:at 100 [:calc 1]]] [1 2 3])))
  (is (= :eof (:reason (why '[x [:at 100 [:calc 1]]] [1 2 3]))))
  (is (nil? (p ['x [:at Long/MAX_VALUE :u8]] [1])))
  (is (= {:x []} (:value (p '[x [:at 3 [:repeat :u8 :eos]]] [1 2 3]))))
  (is (nil? (p ['x [:skip Long/MAX_VALUE]] [1])))
  (is (nil? (p ['_ :u8 'x [:align Long/MAX_VALUE]] [1 2])))
  (is (nil? (p ['x [:sized Long/MAX_VALUE :u8]] [1]))))

(deftest const-high-bytes
  (is (= {:m [0x89 0x50]} (:value (p '[m [:const [0x89 0x50]]] [0x89 0x50]))))
  (is (nil? (p '[m [:const [0x89 0x50]]] [0x7f 0x50]))))

(deftest repeat-max-before-parse
  (is (= :repeat-max (:reason (why '[xs [:repeat :u8 :until (fn [e] false) :max 2]] [1 2 3])))))
