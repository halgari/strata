(ns lang.analyze.struct-test
  (:require [clojure.test :refer [deftest is testing]]
            [lang.analyze.code :as ac]
            [lang.analyze.struct :as s]
            [lang.builtins :as b]
            [lang.ns :as ns]))

(defn- err [f]
  (try (f) nil (catch clojure.lang.ExceptionInfo e (ex-data e))))

(defn- prog [attrs & forms]
  (reduce (fn [p f]
            (let [n (second f)]
              (ns/add-def p 'a n
                          {:kinds (if (= 'defstruct (first f)) #{:relation :type} #{:type})
                           :sub (if (= 'defstruct (first f)) :struct :deftype)
                           :qname (symbol "a" (str n)) :form f})))
          (ns/add-namespace (ns/empty-program @b/registry {})
                            {:name 'a :attrs attrs :requires []})
          forms))

(defn- st [form & {:keys [attrs defs] :or {attrs {}}}]
  (s/analyze-struct (apply prog attrs form defs) 'a form))

(defn- kind [f] (:lang/error (err f)))

(deftest endian-lexical
  (let [r (st '(defstruct s [x :u32 y [:u32 :le]]) :attrs {:endian :be})
        [x y] (:fields r)]
    (is (= :be (:endian r)))
    (is (= :be (get-in x [:type :endian])))
    (is (= :le (get-in y [:type :endian]))))
  (is (= :le (:endian (st '(defstruct s [x :u8])))))
  (is (= :be (:endian (st '(defstruct s {:endian :be} [x :u8])))))
  (is (= :lsb (:bit-order (st '(defstruct s {:bit-order :lsb} [x [:bits 3]])))))
  (is (= :lsb (get-in (st '(defstruct s [x [:bits 3]]) :attrs {:bit-order :lsb})
                      [:fields 0 :type :order]))))

(deftest hidden-fields
  (let [r (st '(defstruct s [_a :u8 _ :u8 b [:calc _a]]))
        [a u b] (:fields r)]
    (is (:hidden? a))
    (is (= :_a (:key a)))
    (is (nil? (:key u)))
    (is (= :b (:key b)))
    (is (= (:id a) (get-in b [:type :expr :id])))))

(deftest anon-not-referenceable
  (is (= :unresolved-symbol (kind #(st '(defstruct s [_ :u8 b [:calc _]])))))
  (is (some? (st '(defstruct s [_ :u8 _ :u8])))))

(deftest forward-field-ref-rejected
  (is (= :unresolved-symbol (kind #(st '(defstruct s [a [:bytes b] b :u8])))))
  (is (= :unresolved-symbol (kind #(st '(defstruct s [a [:bytes a]]))))))

(deftest params
  (let [p '(defstruct p [n] [xs [:array :u8 n]])
        r (st p)]
    (is (= 1 (count (:params r))))
    (is (= (:id (first (:params r))) (get-in r [:fields 0 :type :n :id])))
    (is (= :type-arity (kind #(st '(defstruct t [x [:sized 4 p]]) :defs [p]))))
    (is (= :type-arity (kind #(st '(defstruct t [x [p 1 2]]) :defs [p]))))
    (is (= :type-arity (kind #(st '(defstruct t [x [q 1]]) :defs ['(defstruct q [y :u8])]))))
    (let [ok (st '(defstruct t [x [p 4]]) :defs [p])]
      (is (= {:t :ref :qname 'a/p} (select-keys (get-in ok [:fields 0 :type]) [:t :qname])))
      (is (= 1 (count (get-in ok [:fields 0 :type :args])))))))

(deftest unknown-and-bad-forms
  (is (= :unknown-type (kind #(st '(defstruct s [x :u33])))))
  (is (= :unknown-type (kind #(st '(defstruct s [x nope])))))
  (is (= :bad-type-form (kind #(st '(defstruct s [x :u8 x :u8])))))
  (is (= :bad-type-form (kind #(st '(defstruct s [x [:string 1 :nope]])))))
  (is (= :bad-type-form (kind #(st '(defstruct s [1 :u8])))))
  (is (= :bad-type-form (kind #(st '(defstruct s [x [:bits 65]])))))
  (is (= :bad-type-form (kind #(st '(defstruct s {:endian :mid} [x :u8]))))))

(deftest switch-default
  (let [t (get-in (st '(defstruct s [t :u8 v [:switch t {1 :u8 "x" :u32} :u16]])) [:fields 1 :type])]
    (is (= :switch (:t t)))
    (is (= [[1 :u8] ["x" :u32]] (mapv (fn [[k ty]] [k (:prim ty)]) (:cases t))))
    (is (= :u16 (get-in t [:default :prim]))))
  (is (nil? (get-in (st '(defstruct s [t :u8 v [:switch t {1 :u8}]])) [:fields 1 :type :default])))
  (is (= :bad-type-form (kind #(st '(defstruct s [t :u8 v [:switch t {t :u8}]]))))))

(deftest positional
  (let [r (st '(defstruct s [a [:calc $start] b [:calc $pos] c [:calc $remaining]]))
        ids (:pos-ids r)]
    (is (= (:start ids) (get-in r [:fields 0 :type :expr :id])))
    (is (= (:pos ids) (get-in r [:fields 1 :type :expr :id])))
    (is (= (:remaining ids) (get-in r [:fields 2 :type :expr :id])))))

(deftest const-string
  (is (= [77 90] (get-in (st '(defstruct s [m [:const "MZ"]])) [:fields 0 :type :bytes])))
  (is (= [1 2] (get-in (st '(defstruct s [m [:const [1 2]]])) [:fields 0 :type :bytes])))
  (is (= :bad-type-form (kind #(st '(defstruct s [m [:const [256]]]))))))

(deftest constructors
  (let [t (fn [ty] (get-in (st (list 'defstruct 's ['n :u8 'x ty])) [:fields 1 :type]))]
    (is (= {:t :repeat :mode :eos :pred nil :max 1000000} (select-keys (t '[:repeat :u8 :eos]) [:t :mode :pred :max])))
    (is (= 5 (:max (t '[:repeat :u8 :until (fn [e] (= e 0)) :max 5]))))
    (is (= :sentinel (:mode (t '[:repeat :u8 :sentinel (fn [e] (= e 0))]))))
    (is (= 65536 (:max (t '[:cstring :utf8]))))
    (is (= 10 (:max (t '[:cstring :ascii :max 10]))))
    (is (= :rest (:n (t '[:bytes :rest]))))
    (is (= :rest (:n (t '[:decode :rest (fn [b] b) :u8]))))
    (is (= :msb (:order (t '[:bits 4]))))
    (is (= {1 :a} (:map (t '[:enum :u8 {1 :a}]))))
    (is (= :alias (:t (get-in (st '(defstruct s [x t]) :defs ['(deftype t :u8)]) [:fields 0 :type]))))
    (doseq [[form k] '[[[:if (= n 1) :u8] :if] [[:at n :u8] :at] [[:sized n :u8] :sized]
                       [[:try :u8] :try] [[:defer n :u8] :defer] [[:skip n] :skip]
                       [[:align n] :align] [[:assert (= n 1)] :assert] [[:array :u8 n] :array]
                       [[:string n :utf8] :string]]]
      (is (= k (:t (t form)))))))

(deftest deftype-analysis
  (let [p (prog {:endian :be})
        r (s/analyze-deftype p 'a '(deftype w [n] [:array :u16 n]))]
    (is (= 'a/w (:qname r)))
    (is (= :be (get-in r [:type :elem :endian])))
    (is (= (:id (first (:params r))) (get-in r [:type :n :id]))))
  (is (= :u32 (:prim (:type (s/analyze-deftype (prog {}) 'a '(deftype w :u32))))))
  (is (= :be (get-in (s/analyze-deftype (prog {}) 'a '(deftype w [:u32 :be])) [:type :endian]))))

(deftest inline-type
  (let [sc (ac/new-scope)
        [sc id] (ac/bind-local sc 'k)
        t (s/analyze-type (prog {}) 'a '[:array :u16 k] sc :be :msb)]
    (is (= id (get-in t [:n :id])))
    (is (= :be (get-in t [:elem :endian])))))
