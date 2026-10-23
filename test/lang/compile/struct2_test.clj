(ns lang.compile.struct2-test
  (:require [clojure.test :refer [deftest is testing]]
            [lang.analyze.code :as ac]
            [lang.analyze.struct :as as]
            [lang.builtins :as b]
            [lang.compile.code :as cc]
            [lang.compile.struct :as cs]
            [lang.ns :as ns]
            [lang.resource :as res]
            [lang.runtime :as rt]
            [lang.test-util :refer [parse-src]]
            [lang.values :as v])
  (:import (java.util.zip Deflater)))

(defn- err [f]
  (try (f) nil (catch clojure.lang.ExceptionInfo e (ex-data e))))

(defn- bs [xs] (v/wrap-bytes (byte-array (map unchecked-byte xs))))

(defn- p [fields byte-vec & [opts]]
  (parse-src [(list 'defstruct 's fields)] 's byte-vec (or opts {})))

(defn- run
  "Loads forms (optional ns form, then defstruct/deftype/defn), compiles them
  with a parse environment, and evaluates expr with locals bound to values.
  opts: {:locals {sym value} :limits {…} :resources {…}}."
  [forms expr & [opts]]
  (let [[nsf forms] (if (and (seq? (first forms)) (= 'ns (ffirst forms)))
                      [(first forms) (rest forms)]
                      ['(ns user) forms])
        parsed (ns/parse-ns-form nsf)
        nm (:name parsed)
        entry (fn [f] (case (first f)
                        defstruct {:kinds #{:relation :type} :sub :struct}
                        deftype {:kinds #{:type} :sub :deftype}
                        defn {:kinds #{:fn} :sub :defn}))
        prog (reduce (fn [pr f]
                       (ns/add-def pr nm (second f)
                                   (assoc (entry f) :form f :qname (symbol (str nm) (str (second f))))))
                     (ns/add-namespace (ns/empty-program @b/registry {}) parsed)
                     forms)
        fn-table (atom {})
        st (atom {})
        locals (:locals opts)
        [scope ids] (reduce (fn [[sc ids] sym]
                              (let [[sc' id] (ac/bind-local sc sym)] [sc' (assoc ids sym id)]))
                            [(ac/new-scope) {}] (keys locals))]
    (binding [cc/*compile-env* (cs/parse-env prog st)]
      (doseq [f forms :when (= 'defn (first f))]
        (let [a (ac/analyze-defn prog nm f)]
          (swap! fn-table assoc (:qname a) (cc/compile-defn a fn-table))))
      (doseq [f forms :when (#{'defstruct 'deftype} (first f))]
        (let [c (if (= 'defstruct (first f))
                  (cs/compile-struct (as/analyze-struct prog nm f) st fn-table)
                  (cs/compile-deftype (as/analyze-deftype prog nm f) st fn-table))]
          (swap! st assoc (:qname c) c)))
      (let [compiled (cc/compile-node (ac/analyze prog nm expr scope) fn-table)
            ctx (rt/make-ctx (select-keys opts [:limits :resources]))
            env (into {} (map (fn [[sym x]] [(ids sym) x])) locals)]
        (rt/run-isolated #(cc/eval-code ctx compiled env))))))

(deftest bits-msb
  (is (= {:a 5 :b 3} (:value (p '[a [:bits 3] b [:bits 5]] [2r10100011])))))

(deftest bits-lsb
  (let [r (parse-src ['(defstruct s {:bit-order :lsb} [a [:bits 3] b [:bits 5]])] 's [2r10100011])]
    (is (= {:a 3 :b 20} (:value r)))
    (is (= 1 (:end r)))))

(deftest bits-spans-bytes
  (is (= {:a 0xABC :b 0xD} (:value (p '[a [:bits 12] b [:bits 4]] [0xAB 0xCD]))))
  (is (= 18446744073709551615N (:a (:value (p '[a [:bits 64]] (repeat 8 0xff))))))
  (is (nil? (p '[a [:bits 9]] [1]))))

(deftest bits-realign
  (let [r (p '[a [:bits 4] b :u8] [0xF0 0x07])]
    (is (= {:a 15 :b 7} (:value r)))
    (is (= 2 (:end r)))))

(defn- rev-fn []
  (v/->LangFn 'rev (fn [_ [b]]
                     (v/wrap-bytes (byte-array (reverse (seq (v/barray b))))))))

(deftest decode-frame
  (let [r (parse-src ['(defstruct s [f] [d [:decode 3 f [:at 0 :u8]] n :u8])]
                     's [1 2 3 9] {:args [(rev-fn)]})]
    (is (= {:d 3 :n 9} (:value r)))
    (is (= 4 (:end r))))
  (testing "a nil or non-bytes result fails the parse"
    (let [nil-fn (v/->LangFn 'f (fn [_ _] nil))
          explain (parse-src ['(defstruct s [f] [d [:decode 3 f :u8]])]
                             's [1 2 3] {:args [nil-fn] :explain? true})]
      (is (nil? (parse-src ['(defstruct s [f] [d [:decode 3 f :u8]])] 's [1 2 3] {:args [nil-fn]})))
      (is (= :decode (:reason explain)))))
  (testing "positional symbols are relative to the decoded frame"
    (let [r (parse-src ['(defstruct in [a :u8 b :u8 p [:calc $pos]])
                        '(defstruct s [f] [skip :u8 d [:decode :rest f in]])]
                       's [0 7 8 9] {:args [(rev-fn)]})]
      (is (= {:skip 0 :d {:a 9 :b 8 :p 2}} (:value r)))))
  (testing "the decoded size counts against the byte budget"
    (is (= :bytes-exhausted
           (:lang/error (err #(parse-src ['(defstruct s [f] [d [:decode 3 f :u8]])]
                                         's [1 2 3] {:args [(rev-fn)] :limits {:max-bytes 2}})))))))

(defn- deflate ^bytes [^bytes data]
  (let [d (doto (Deflater.) (.setInput data) (.finish))
        buf (byte-array 256)
        n (.deflate d buf)]
    (java.util.Arrays/copyOf buf n)))

(deftest decode-inflate
  (let [payload (deflate (byte-array (map unchecked-byte [7 65 66 67 99])))
        r (parse-src ['(ns user (:require [lang.bytes :as b]))
                      '(defstruct inner [a :u8 s [:string 3 :ascii]])
                      '(defstruct s [len :u8 d [:decode len (fn [x] (b/inflate x 100)) inner]])]
                     's (cons (alength payload) (map #(bit-and 0xff (long %)) payload)))]
    (is (= {:len (alength payload) :d {:a 7 :s "ABC"}} (:value r)))))

(deftest defer-lazy
  (let [forms ['(defstruct bad [m [:const "ZZ"]])
               '(defstruct s [pad :u8 d [:defer 4 bad] t :u8])]
        r (parse-src forms 's [0 1 2 3 4 9])
        {:keys [pad d t]} (:value r)
        ctx (rt/make-ctx {})]
    (is (some? r))
    (is (= 6 (:end r)))
    (is (= {:pad 0 :t 9} (select-keys (:value r) [:pad :t])))
    (is (v/deferred? d))
    (is (= 1 (v/deferred-offset d)))
    (is (= 4 (v/deferred-length d)))
    (is (nil? (res/force-value ctx d)))
    (is (nil? (res/force-value ctx nil)))))

(deftest defer-force-memo-and-trace
  (let [events (atom [])
        ctx (rt/make-ctx {:trace #(swap! events conj %)})
        r (parse-src ['(defstruct in [a :u8 b :u8])
                      '(defstruct s [x [:defer 2 in] y [:defer :rest [:array :u8 2]]])]
                     's [5 6 7 8])
        {:keys [x y]} (:value r)]
    (is (= {:a 5 :b 6} (res/force-value ctx x)))
    (is (= {:a 5 :b 6} (res/force-value ctx x)))
    (is (= 1 (count @events)))
    (is (= {:event :parse :type 'user/in :off 0} (first @events)))
    (is (= [7 8] (res/force-value ctx y)))))

(deftest defer-equality
  (let [forms ['(defstruct in [a :u8])
               '(defstruct s [x [:defer 1 in]])]
        d1 (:x (:value (parse-src forms 's [5])))
        d2 (:x (:value (parse-src forms 's [5])))
        d3 (:x (:value (parse-src forms 's [6])))]
    (is (= d1 d2))
    (is (= (hash d1) (hash d2)))
    (is (not= d1 d3)))
  (testing "deferred values carry evaluated type args"
    (let [forms ['(defstruct in [n] [xs [:array :u8 n]])
                 '(defstruct s [x [:defer 2 [in 2]] y [:defer 2 [in 1]]])]
          {:keys [x y]} (:value (parse-src forms 's [1 2 3 4]))]
      (is (not= x y))
      (is (= {:xs [1 2]} (res/force-value (rt/make-ctx {}) x))))))

(deftest trace-parse
  (let [events (atom [])]
    (parse-src ['(defstruct s [a :u8])] 's [1] {:trace #(swap! events conj %)})
    (is (= [{:event :parse :type 'user/s :off 0}] @events))))

(deftest handle-source
  (let [data [1 2 3 4 5 6 7 8 9 0 11]
        arr (byte-array data)
        h (v/->Handle "f" (res/bytes-resource arr))
        forms ['(defstruct s [a :u16 n :u8 xs [:array :u8 n] c [:cstring :ascii]])]
        args {:locals {'h h 'b (v/copy-bytes arr)}}]
    (doseq [limits [{} {:page-size 3}]]
      (let [[rh rb] (run forms '[(parse s h 0) (parse s b 0)] (assoc args :limits limits))]
        (is (some? rb))
        (is (= rb rh) (str limits))))
    (testing "the relation works over a handle"
      (let [rel (cs/struct-relation (let [st (atom {})
                                          prog (ns/add-namespace (ns/empty-program @b/registry {})
                                                                 (ns/parse-ns-form '(ns user)))
                                          f '(defstruct s [a :u8])
                                          prog (ns/add-def prog 'user 's {:kinds #{:relation :type} :sub :struct
                                                                          :form f :qname 'user/s})]
                                      (cs/compile-struct (as/analyze-struct prog 'user f) st (atom {}))))
            ctx (rt/make-ctx {})]
        (is (= [[{:a 1} 1]] ((:impl (first (:modes rel))) ctx [h 0])))))))

(deftest parse-in-code
  (let [forms '[(defstruct p [n] [xs [:array :u8 n]])
                (defstruct q [a :u8])]
        locals {:locals {'bs (bs [104 105 0 7])}}]
    (is (= {:value "hi" :end 3} (run forms '(parse [:cstring :ascii] bs) locals)))
    (is (= {:value {:xs [104 105]} :end 2} (run forms '(parse [p 2] bs 0) locals)))
    (is (= {:value {:xs [105 0]} :end 3} (run forms '(parse [p 2] bs 1) locals)))
    (is (= {:value {:a 105} :end 2} (run forms '(parse q bs 1) locals)))
    (testing "type arguments are evaluated in the enclosing scope"
      (is (= {:value {:xs [104 105 0]} :end 3} (run forms '(let [k 3] (parse [p k] bs)) locals))))
    (testing "nil on failure or nil source"
      (is (nil? (run forms '(parse [p 9] bs) locals)))
      (is (nil? (run forms '(parse q nil) locals))))
    (testing "explain"
      (is (= :eof (:reason (run forms '(parse-explain [p 9] bs) locals))))
      (is (= :cstring (:reason (run forms '(parse-explain [:cstring :ascii] bs 3) locals))))
      (is (= {:ok true :value {:a 104} :end 1} (run forms '(parse-explain q bs) locals))))
    (testing "namespace defaults reach inline types"
      (is (= {:value 0x0102 :end 2}
             (run ['(ns user {:endian :be})] '(parse :u16 bs) {:locals {'bs (bs [1 2])}}))))
    (testing "bad source type is a type error"
      (is (= :type-error (:lang/error (err #(run forms '(parse q 5) locals))))))
    (testing "defn bodies compile with the environment too"
      (is (= {:value {:a 104} :end 1}
             (run (conj forms '(defn f [x] (parse q x))) '(f bs) locals))))))

(deftest force-in-code
  (let [forms '[(defstruct in [a :u8])
                (defstruct s [x [:defer 1 in]])]
        locals {:locals {'bs (bs [5])}}]
    (is (= {:a 5} (run forms '(force (get (get (parse s bs) :value) :x)) locals)))
    (is (nil? (run forms '(force nil) locals)))
    (is (= 0 (run forms '(deferred-offset (get (get (parse s bs) :value) :x)) locals)))
    (is (= :type-error (:lang/error (err #(run forms '(force 5) locals)))))))

(defn- rel [sym] (get-in @b/registry ['lang.core :relation sym]))
(defn- call-rel [sym & in]
  (let [{:keys [modes]} (rel sym)] ((:impl (first modes)) (rt/make-ctx {}) (vec in))))

(deftest core-relations
  (is (= [[0] [1] [2]] (call-rel 'between 0 3)))
  (is (= [] (call-rel 'between 3 3)))
  (is (= [] (call-rel 'between nil 3)))
  (is (= [] (call-rel 'elem nil)))
  (is (= [[1] [2]] (call-rel 'elem [1 2])))
  (is (= [[[:a 1]]] (call-rel 'elem {:a 1})))
  (is (= [[0 :x] [1 :y]] (call-rel 'indexed [:x :y])))
  (is (= [] (call-rel 'indexed nil)))
  (is (= [[:a 1]] (call-rel 'entry {:a 1})))
  (is (= [] (call-rel 'entry nil)))
  (is (= [] (call-rel 'force nil)))
  (is (= {:qname 'lang.core/between :arity 3}
         (select-keys (rel 'between) [:qname :arity])))
  (is (= [0 1] (:in (first (:modes (rel 'between))))))
  (testing "between charges fuel per integer"
    (let [ctx (rt/make-ctx {:limits {:fuel 10}})]
      (is (= :fuel-exhausted
             (:lang/error (err #((:impl (first (:modes (rel 'between)))) ctx [0 100])))))))
  (testing "force relation"
    (let [d (:x (:value (parse-src ['(defstruct in [a :u8]) '(defstruct s [x [:defer 1 in]])] 's [5])))]
      (is (= [[{:a 5}]] (call-rel 'force d))))))

(deftest io
  (let [fns (fn [sym] (:impl (get-in @b/registry ['lang.io :fn sym])))
        resource (res/bytes-resource (byte-array [1 2 3 4 5]))
        ctx (rt/make-ctx {:resources {"f" resource}})
        h ((fns 'open) ctx "f")]
    (is (v/handle? h))
    (is (nil? ((fns 'open) ctx "missing")))
    (is (= 5 ((fns 'size) ctx h)))
    (is (= (bs [2 3]) ((fns 'read-bytes) ctx h 1 2)))
    (is (nil? ((fns 'read-bytes) ctx h 0 10)))
    (is (nil? ((fns 'read-bytes) ctx h -1 2)))
    (is (nil? ((fns 'read-bytes) ctx h 0 -2)))
    (is (= (bs [1 2 3 4 5]) ((fns 'read-all) ctx h)))
    (testing ":max-read"
      (let [ctx (rt/make-ctx {:resources {"f" resource} :limits {:max-read 4}})
            h ((fns 'open) ctx "f")]
        (is (= :read-too-large (:lang/error (err #((fns 'read-bytes) ctx h 0 5)))))
        (is (= :read-too-large (:lang/error (err #((fns 'read-all) ctx h)))))
        (is (= (bs [1 2 3 4]) ((fns 'read-bytes) ctx h 0 4)))))
    (is (= :type-error (:lang/error (err #((fns 'size) ctx 5)))))))

(deftest inline-defer-identity
  (let [forms ['(defstruct s [n] [d [:defer 4 [:array :u8 n]]])]
        d (fn [n] (:d (:value (parse-src forms 's [1 2 3 4] {:args [n]}))))
        d2 (d 2) d3 (d 3)
        ctx (rt/make-ctx {})]
    (is (not= d2 d3))
    (is (= d2 (d 2)))
    (is (= [1 2] (res/force-value ctx d2)))
    (is (= [1 2 3] (res/force-value ctx d3)))))

(deftest bits-through-containers
  (is (= {:a [2 3 0 1]} (:value (p '[a [:array [:bits 2] 4]] [2r10110001]))))
  (let [r (p '[a [:bits 3] b [:if true [:bits 5]]] [2r10100011])]
    (is (= {:a 5 :b 3} (:value r)))
    (is (= 1 (:end r)))))

(deftest bits-lsb-boundary
  (let [r (parse-src ['(defstruct s {:bit-order :lsb} [a [:bits 4] b [:bits 8] c [:bits 4]])]
                     's [0xAB 0xCD])]
    ;; a = low nibble of 0xAB, b = high nibble of 0xAB (low) + low nibble of 0xCD (high), c = high nibble of 0xCD
    (is (= {:a 0xB :b 0xDA :c 0xC} (:value r)))))

(deftest bits-width-rejected
  (doseq [n [0 65]]
    (is (= :bad-type-form (:lang/error (err #(p [(symbol "a") [:bits n]] [1])))))))
