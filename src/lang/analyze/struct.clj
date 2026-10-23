(ns lang.analyze.struct
  "Analyzer for defstruct / deftype binary struct definitions into type ASTs
  (spec 5.1-5.4)."
  (:require [lang.analyze.code :as ac]
            [lang.errors :refer [error! loc-of]]
            [lang.ns :as ns]
            [lang.values :as v]))

(def ^:private prims #{:u8 :i8 :u16 :i16 :u32 :i32 :i64 :u64 :f32 :f64})
(def ^:private encodings #{:ascii :utf8 :latin1 :cp1252 :utf16le :utf16be})
(def ^:private default-max-repeat 1000000)
(def ^:private default-max-cstring 65536)

(defn- fail [cx form kind msg & [data]]
  (error! kind :analyze msg
          (merge (loc-of form) {:form form :ns (:ns cx)} data)))

(defn- bad [cx form msg] (fail cx form :bad-type-form msg))

;; ---------------------------------------------------------------- definition shapes

(defn- struct-parts
  "Splits (defstruct name [params]? {opts}? [fields]) into
  {:params :opts :fields}, or nil when malformed."
  [form]
  (when (and (seq? form) (>= (count form) 3) (simple-symbol? (second form)))
    (let [more (drop 2 form)
          [params more] (if (and (vector? (first more)) (seq (rest more)))
                          [(first more) (rest more)]
                          [nil more])
          [opts more] (if (map? (first more)) [(first more) (rest more)] [{} more])]
      (when (and (= 1 (count more)) (vector? (first more)))
        {:params params :opts opts :fields (first more)}))))

(defn- deftype-parts [form]
  (when (and (seq? form) (simple-symbol? (second form)))
    (case (count form)
      3 {:params nil :type (nth form 2)}
      4 {:params (nth form 2) :type (nth form 3)}
      nil)))

(defn- param-count
  "Number of parameters of a referenced struct/deftype def, or nil when it is
  not parameterized."
  [{:keys [sub form]}]
  (let [params (case sub
                 :struct (:params (struct-parts form))
                 :deftype (:params (deftype-parts form))
                 nil)]
    (when params (count params))))

;; ---------------------------------------------------------------- helpers

(defn- expr [cx scope form]
  (ac/analyze (:prog cx) (:ns cx) form scope))

(defn- exprs [cx scope forms] (mapv #(expr cx scope %) forms))

(defn- size-or-rest [cx scope form]
  (if (= :rest form) :rest (expr cx scope form)))

(defn- lit-int [cx form x lo hi what]
  (when-not (and (integer? x) (<= lo x hi))
    (bad cx form (str what " must be an integer literal in " lo ".." hi)))
  (long x))

(defn- check-enc [cx form enc]
  (when-not (contains? encodings enc)
    (bad cx form (str "Unknown encoding " (pr-str enc))))
  enc)

(defn- ground? [x]
  (or (nil? x) (boolean? x) (string? x) (char? x) (keyword? x) (number? x)
      (and (vector? x) (every? ground? x))))

(defn- ground-key [cx form k]
  (when-not (ground? k)
    (bad cx form (str "Case key must be a constant: " (pr-str k))))
  (v/canon k))

(defn- const-bytes [cx form x]
  (cond
    (string? x)
    (do (when-not (every? #(< (int %) 128) x)
          (bad cx form ":const strings must be ASCII"))
        (mapv #(long (int %)) x))
    (and (vector? x) (every? #(and (integer? %) (<= 0 % 255)) x)) (mapv long x)
    :else (bad cx form ":const expects a string or a vector of byte values")))

;; ---------------------------------------------------------------- types

(declare analyze-type*)

(defn- arity! [cx form n]
  (when-not (= n (dec (count form)))
    (bad cx form (str (first form) " expects " n " argument(s)"))))

(defn- resolve-type-ref [cx scope form sym args]
  (let [{:keys [qname def]} (ns/resolve-name (:prog cx) (:ns cx) sym :type)
        sub (:sub def)]
    (when-not (and def (#{:struct :deftype} sub))
      (fail cx form :unknown-type (str "Unknown type " sym)))
    (let [expected (param-count def)]
      (when-not (= (or expected 0) (count args))
        (fail cx form :type-arity
              (if (and expected (zero? (count args)))
                (str sym " is parameterized and must be used as [" sym " args…]")
                (str sym " expects " (or expected 0) " argument(s), got " (count args)))
              {:expected (or expected 0) :got (count args)}))
      {:t (if (= :struct sub) :ref :alias)
       :qname qname
       :args (exprs cx scope args)})))

(defn- analyze-repeat [cx scope endian order [_ t mode & more :as form]]
  (let [[pred more] (case mode
                      :eos [nil more]
                      (:until :sentinel) (if (seq more)
                                           [(expr cx scope (first more)) (rest more)]
                                           (bad cx form (str ":repeat " mode " needs a predicate")))
                      (bad cx form ":repeat mode must be :eos, :until or :sentinel"))
        mx (cond
             (empty? more) default-max-repeat
             (and (= 2 (count more)) (= :max (first more)))
             (lit-int cx form (second more) 0 Long/MAX_VALUE ":max")
             :else (bad cx form "Malformed :repeat options"))]
    {:t :repeat :elem (analyze-type* cx scope t endian order) :mode mode :pred pred :max mx}))

(defn- analyze-switch [cx scope endian order [_ test cases default :as form]]
  (when-not (and (<= 3 (count form) 4) (map? cases))
    (bad cx form "[:switch expr {case type …} default?]"))
  {:t :switch
   :test (expr cx scope test)
   :cases (mapv (fn [[k t]]
                  [(ground-key cx form k) (analyze-type* cx scope t endian order)])
                cases)
   :default (when (= 4 (count form)) (analyze-type* cx scope default endian order))})

(defn- analyze-constructor [cx scope endian order [head & args :as form]]
  (let [ty #(analyze-type* cx scope % endian order)
        ex #(expr cx scope %)]
    (case head
      :bytes (do (arity! cx form 1) {:t :bytes :n (size-or-rest cx scope (first args))})
      :string (do (arity! cx form 2)
                  {:t :string :n (ex (first args)) :enc (check-enc cx form (second args))})
      :cstring (let [[enc & opts] args]
                 (when (empty? args) (bad cx form "[:cstring enc :max n]"))
                 {:t :cstring :enc (check-enc cx form enc)
                  :max (cond
                         (empty? opts) default-max-cstring
                         (and (= 2 (count opts)) (= :max (first opts)))
                         (lit-int cx form (second opts) 1 Long/MAX_VALUE ":max")
                         :else (bad cx form "[:cstring enc :max n]"))})
      :const (do (arity! cx form 1)
                 {:t :const :bytes (const-bytes cx form (first args)) :val (v/canon (first args))})
      :array (do (arity! cx form 2) {:t :array :elem (ty (first args)) :n (ex (second args))})
      :repeat (analyze-repeat cx scope endian order form)
      :if (do (arity! cx form 2) {:t :if :test (ex (first args)) :then (ty (second args))})
      :switch (analyze-switch cx scope endian order form)
      :enum (let [[t m] args]
              (arity! cx form 2)
              (when-not (and (map? m) (every? keyword? (vals m)))
                (bad cx form "[:enum type {raw keyword …}]"))
              {:t :enum :elem (ty t)
               :map (into {} (map (fn [[k kw]] [(ground-key cx form k) kw])) m)})
      :bits (do (arity! cx form 1)
                {:t :bits :n (lit-int cx form (first args) 1 64 "Bit width") :order order})
      :calc (do (arity! cx form 1) {:t :calc :expr (ex (first args))})
      :assert (do (arity! cx form 1) {:t :assert :expr (ex (first args))})
      :skip (do (arity! cx form 1) {:t :skip :n (ex (first args))})
      :align (do (arity! cx form 1) {:t :align :n (ex (first args))})
      :at (do (arity! cx form 2) {:t :at :off (ex (first args)) :elem (ty (second args))})
      :sized (do (arity! cx form 2) {:t :sized :n (ex (first args)) :elem (ty (second args))})
      :decode (do (arity! cx form 3)
                  {:t :decode :n (size-or-rest cx scope (first args))
                   :f (ex (second args)) :elem (ty (nth args 2))})
      :try (do (arity! cx form 1) {:t :try :elem (ty (first args))})
      :defer (do (arity! cx form 2)
                 {:t :defer :n (size-or-rest cx scope (first args)) :elem (ty (second args))})
      (if (prims head)
        (let [[e & more] args]
          (when-not (and (= 1 (count args)) (empty? more) (#{:le :be} e))
            (bad cx form "A primitive takes one optional endianness, :le or :be"))
          {:t :prim :prim head :endian e})
        (fail cx form :unknown-type (str "Unknown type constructor " head))))))

(defn- analyze-type* [cx scope form endian order]
  (cond
    (keyword? form)
    (if (prims form)
      {:t :prim :prim form :endian endian}
      (fail cx form :unknown-type (str "Unknown type " form)))

    (symbol? form) (resolve-type-ref cx scope form form [])

    (and (vector? form) (symbol? (first form)))
    (resolve-type-ref cx scope form (first form) (rest form))

    (and (vector? form) (keyword? (first form)))
    (analyze-constructor cx scope endian order form)

    :else (bad cx form "Malformed type")))

(defn analyze-type
  "Analyzes one inline type form in the given scope into a type AST."
  [prog ns form scope endian bit-order]
  (analyze-type* {:prog prog :ns ns} scope form endian bit-order))

;; ---------------------------------------------------------------- definitions

(defn- ns-defaults [prog ns opts cx form]
  (doseq [[k val] opts]
    (when-not (and (#{:endian :bit-order} k)
                   (contains? (if (= k :endian) #{:le :be} #{:msb :lsb}) val))
      (bad cx form (str "Bad struct option " (pr-str k) " " (pr-str val)))))
  (let [attrs (get-in prog [:namespaces ns :attrs])]
    {:endian (or (:endian opts) (:endian attrs) :le)
     :bit-order (or (:bit-order opts) (:bit-order attrs) :msb)}))

(defn- bind-params [cx scope params form]
  (when-not (and (vector? params) (every? simple-symbol? params)
                 (apply distinct? (conj params ::none)))
    (bad cx form "Parameters must be a vector of distinct symbols"))
  (reduce (fn [[sc ps] sym]
            (let [[sc' id] (ac/bind-local sc sym)]
              [sc' (conj ps {:sym sym :id id})]))
          [scope []] params))

(defn- qname-of [ns form] (symbol (str ns) (name (second form))))

(defn analyze-struct
  "Analyzes a defstruct form of namespace ns."
  [prog ns form]
  (let [cx {:prog prog :ns ns}
        {:keys [params opts fields]} (or (struct-parts form) (bad cx form "Malformed defstruct"))
        {:keys [endian bit-order]} (ns-defaults prog ns opts cx form)
        [scope ps] (bind-params cx (ac/new-scope) (or params []) form)
        [scope pos] (ac/bind-local scope '$pos)
        [scope start] (ac/bind-local scope '$start)
        [scope remaining] (ac/bind-local scope '$remaining)]
    (when-not (even? (count fields)) (bad cx form "Fields must be name/type pairs"))
    (loop [[[sym tform] & more] (partition 2 fields)
           scope scope, seen #{}, out []]
      (if (nil? sym)
        {:qname (qname-of ns form) :params ps :endian endian :bit-order bit-order
         :pos-ids {:pos pos :start start :remaining remaining}
         :fields out}
        (do
          (when-not (simple-symbol? sym) (bad cx form (str "Field name must be a symbol: " (pr-str sym))))
          (when (and (not= '_ sym) (seen sym))
            (bad cx form (str "Duplicate field " sym)))
          (let [t (analyze-type* cx scope tform endian bit-order)
                anon? (= '_ sym)
                [scope' id] (if anon?
                              [scope (ac/fresh-id scope)]
                              (ac/bind-local scope sym))]
            (recur more scope' (conj seen sym)
                   (conj out {:sym sym
                              :key (when-not anon? (keyword (name sym)))
                              :hidden? (.startsWith (name sym) "_")
                              :id id
                              :type t}))))))))

(defn analyze-deftype
  "Analyzes a deftype form of namespace ns."
  [prog ns form]
  (let [cx {:prog prog :ns ns}
        {:keys [params type]} (or (deftype-parts form) (bad cx form "Malformed deftype"))
        {:keys [endian bit-order]} (ns-defaults prog ns {} cx form)
        [scope ps] (bind-params cx (ac/new-scope) (or params []) form)]
    {:qname (qname-of ns form)
     :params ps
     :type (analyze-type* cx scope type endian bit-order)}))
