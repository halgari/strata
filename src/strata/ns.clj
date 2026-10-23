(ns strata.ns
  "Namespace forms, load ordering, the program symbol table and positional
  name resolution (spec 2)."
  (:require [strata.builtins :as builtins]
            [strata.errors :refer [error! loc-of]]))

(def ^:private reserved-prefix "strata.")

(defn- reserved? [ns-sym]
  (.startsWith (str ns-sym) ^String reserved-prefix))

(defn- bad-ns! [form msg]
  (error! :bad-ns-form :resolve msg (assoc (loc-of form) :form form)))

(def ^:private attr-values {:endian #{:le :be} :bit-order #{:msb :lsb}})

(defn- parse-require [form spec]
  (cond
    (simple-symbol? spec) {:ns spec :as nil :refer []}
    (and (vector? spec) (simple-symbol? (first spec)))
    (let [opts (rest spec)]
      (when-not (even? (count opts)) (bad-ns! form "Malformed :require spec"))
      (reduce (fn [acc [k v]]
                (case k
                  :as (if (simple-symbol? v)
                        (assoc acc :as v)
                        (bad-ns! form ":as expects a symbol"))
                  :refer (if (and (vector? v) (every? simple-symbol? v))
                           (assoc acc :refer v)
                           (bad-ns! form ":refer expects a vector of symbols"))
                  (bad-ns! form (str "Unknown :require option " (pr-str k)))))
              {:ns (first spec) :as nil :refer []}
              (partition 2 opts)))
    :else (bad-ns! form "Malformed :require spec")))

(defn parse-ns-form
  "Parses (ns name attr-map? (:require spec…)*) into
  {:name :attrs :requires}."
  [form]
  (when-not (and (seq? form) (= 'ns (first form)) (simple-symbol? (second form)))
    (bad-ns! form "Expected (ns name …)"))
  (let [[_ nm & more] form
        [attrs more] (if (map? (first more)) [(first more) (rest more)] [{} more])]
    (doseq [[k v] attrs]
      (when-not (contains? (get attr-values k #{}) v)
        (bad-ns! form (str "Bad namespace attribute " (pr-str k) " " (pr-str v)))))
    {:name nm
     :attrs attrs
     :requires (vec (mapcat (fn [clause]
                              (when-not (and (seq? clause) (= :require (first clause)))
                                (bad-ns! form "Only (:require …) clauses are allowed"))
                              (map #(parse-require form %) (rest clause)))
                            more))}))

(defn order-namespaces
  "Returns source namespace symbols in dependency order."
  [units {:keys [builtins externs]}]
  (let [fail! (fn [kind msg data] (error! kind :resolve msg data))
        names (vec (sort-by str (keys units)))
        parsed (into {}
                     (map (fn [n]
                            (when (reserved? n)
                              (fail! :reserved-namespace "Namespace name is reserved" {:ns n}))
                            (when (contains? externs n)
                              (fail! :name-collision "Namespace is both a source and an extern" {:ns n}))
                            (let [p (parse-ns-form (first (get units n)))]
                              (when (not= n (:name p))
                                (fail! :ns-name-mismatch "ns name differs from its source key"
                                       {:ns n :name (:name p)}))
                              [n p])))
                     names)]
    (doseq [e (keys externs)]
      (when (contains? builtins/builtin-namespaces e)
        (fail! :name-collision "Namespace is both an extern and a built-in" {:ns e})))
    (let [done (volatile! [])
          visited (volatile! #{})
          visit (fn visit [n path]
                  (cond
                    (some #{n} path)
                    (fail! :require-cycle "Require cycle"
                           {:ns n :chain (conj (vec (drop-while #(not= % n) path)) n)})
                    (@visited n) nil
                    :else
                    (let [path (conj path n)]
                      (doseq [{r :ns} (:requires (parsed n))]
                        (cond
                          (contains? parsed r) (visit r path)
                          (contains? externs r) nil
                          (= r 'strata.core) nil
                          (contains? builtins/builtin-namespaces r)
                          (when-not (contains? builtins r)
                            (fail! :withheld-namespace "Built-in namespace is not available"
                                   {:ns n :required r :chain (conj path r)}))
                          :else (fail! :unknown-namespace "Unknown namespace"
                                       {:ns n :required r :chain (conj path r)})))
                      (vswap! visited conj n)
                      (vswap! done conj n))))]
      (run! #(visit % []) names)
      @done)))

(defn empty-program [registry externs]
  {:registry registry :namespaces {} :externs externs})

(defn add-namespace
  "Registers a parsed ns form (see parse-ns-form): attrs, aliases and refers."
  [prog {:keys [name attrs requires]}]
  (update-in prog [:namespaces name] merge
             {:attrs attrs
              :requires (mapv :ns requires)
              :aliases (into {} (keep (fn [{:keys [as] n :ns}] (when as [as n]))) requires)
              :refers (into {} (mapcat (fn [{:keys [refer] n :ns}] (map (fn [s] [s n]) refer))) requires)}))

(defn add-def
  "Adds a definition to a namespace. Repeated defrules merge their clauses."
  [prog ns-sym sym def]
  (let [existing (get-in prog [:namespaces ns-sym :defs sym])
        data {:ns ns-sym :sym sym :form (:form def)}
        def' (if (= :rule (:sub def))
               (assoc def :clauses (or (:clauses def) [(:form def)]))
               def)]
    (cond
      (nil? existing) (assoc-in prog [:namespaces ns-sym :defs sym] def')
      (not= (:kinds existing) (:kinds def))
      (error! :kind-conflict :resolve (str "Conflicting kinds for " sym) data)
      (and (= :rule (:sub existing)) (= :rule (:sub def)))
      (update-in prog [:namespaces ns-sym :defs sym :clauses] into (:clauses def'))
      :else (error! :duplicate-definition :resolve (str "Duplicate definition of " sym) data))))

(def ^:private kind-of-position {:relation :relation :fn :fn :type :type})

(defn- lookup-in
  "Looks sym up inside namespace nsym (user, extern or built-in)."
  [prog nsym sym position]
  (let [qname (symbol (str nsym) (name sym))]
    (if-let [user (get-in prog [:namespaces nsym])]
      (when-let [d (get-in user [:defs sym])]
        (when (contains? (:kinds d) (kind-of-position position))
          {:qname (or (:qname d) qname) :def d :builtin? false}))
      (if-let [rels (get-in prog [:externs nsym])]
        (when (and (= position :relation) (contains? rels sym))
          {:qname qname
           :def {:kinds #{:relation} :sub :extern :arity (get rels sym)}
           :builtin? false})
        (when-let [reg (get-in prog [:registry nsym])]
          (if (= position :aggregate)
            (when (contains? (:aggregate reg) sym)
              {:qname qname :def {:kind :aggregate} :builtin? true})
            (when-let [e (get-in reg [position sym])]
              {:qname qname :def e :builtin? true})))))))

(defn resolve-name
  "Resolves sym by position (:relation :fn :type :aggregate). Returns
  {:qname :def :builtin?} or nil."
  [prog cur-ns sym position]
  (let [cur (get-in prog [:namespaces cur-ns])]
    (if-let [q (namespace sym)]
      (let [q (symbol q)
            target (or (get-in cur [:aliases q])
                       (when (= q 'core) 'strata.core)
                       (when (or (= q cur-ns) (= q 'strata.core) (some #{q} (:requires cur)))
                         q))]
        (when target (lookup-in prog target (symbol (name sym)) position)))
      (or (lookup-in prog cur-ns sym position)
          (when-let [r (get-in cur [:refers sym])]
            (lookup-in prog r sym position))
          (lookup-in prog 'strata.core sym position)))))

(defn shadow-warnings
  "User definitions that shadow strata.core names of the same kind."
  [prog]
  (let [core (get-in prog [:registry 'strata.core])]
    (sort-by (juxt (comp str :ns) (comp str :sym) :position)
             (for [[ns-sym {:keys [defs]}] (:namespaces prog)
                   [sym d] defs
                   kind (:kinds d)
                   :when (contains? (get core kind) sym)]
               {:ns ns-sym :sym sym :position kind}))))
