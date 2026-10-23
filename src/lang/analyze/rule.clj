(ns lang.analyze.rule
  "Analysis of defrule clauses and defrel code relations, plus whole-program
  rule checks (spec 3, 4.2, 6.1). Literals are not ordered here; planning is
  a later stage."
  (:require [lang.analyze.code :as ac]
            [lang.compile.code :as cc]
            [lang.errors :refer [error! loc-of]]
            [lang.ns :as ns]
            [lang.values :as v]))

;; ---------------------------------------------------------------- forms

(defn- var-sym? [x]
  (and (symbol? x) (nil? (namespace x)) (.startsWith (name x) "?")))

(defn- wild? [x] (= '_ x))

(defn- ground?
  "True for a constant: no symbols and no lists anywhere inside."
  [x]
  (cond
    (symbol? x) false
    (seq? x) false
    (map? x) (every? ground? (concat (keys x) (vals x)))
    (coll? x) (every? ground? x)
    :else true))

(defn- form-var-seq
  "?vars in first-occurrence order; quoted forms are skipped."
  [form]
  (cond
    (var-sym? form) [form]
    (and (seq? form) (= 'quote (first form))) []
    (map? form) (mapcat form-var-seq (apply concat form))
    (coll? form) (mapcat form-var-seq form)
    :else []))

(defn- bad-form! [form msg]
  (error! :bad-form :analyze msg (assoc (loc-of form) :form form)))

;; ---------------------------------------------------------------- context

(defn- new-wild! [cx]
  (let [i (first (swap-vals! (:next cx) inc))]
    (swap! (:wild cx) conj i)
    i))

(defn- var-idx [cx sym] (get (:names cx) sym))

(defn- vars-of [cx form]
  (into #{} (map #(var-idx cx %)) (form-var-seq form)))

(defn- problem!
  "Records a check-phase problem; check-program throws the first."
  [cx kind msg form data]
  (swap! (:problems cx) conj {:kind kind :msg msg :form form :loc (or (not-empty (loc-of form)) (:loc cx)) :data data}))

(defn- analyze-expr [cx form]
  (ac/analyze (:prog cx) (:ns cx) form (:scope cx)))

;; ---------------------------------------------------------------- relation info

(defn- skip-opts [forms]
  (if (map? (first forms)) (rest forms) forms))

(defn- rule-head-arity [clause-form]
  (count (first (skip-opts (drop 2 clause-form)))))

(defn- defrel-sig
  "Modes [{:in [idx…] :out [idx…]}] read leniently from a defrel form."
  [form]
  (let [params (vec (nth form 2 []))
        idx (zipmap params (range))]
    (vec (for [clause (drop 3 form)
               :when (and (seq? clause) (vector? (first clause)))
               :let [[in out] (split-with #(not= '-> %) (first clause))]
               :when (and (every? idx in) (every? idx (rest out)))]
           {:in (mapv idx in) :out (mapv idx (rest out))}))))

(defn- struct-param-count [form]
  (let [[_ _ a b] form]
    (if (and (vector? a) (or (vector? b) (map? b))) (count a) 0)))

(defn- relation-info
  "{:qname :computed? :arity :modes [{:in :out}]} for a resolved relation."
  [{:keys [qname def builtin?]}]
  (cond
    builtin? {:qname qname :computed? true :arity (:arity def)
              :modes (mapv #(select-keys % [:in :out]) (:modes def))}
    (= :defrel (:sub def)) {:qname qname :computed? true
                            :arity (count (nth (:form def) 2))
                            :modes (defrel-sig (:form def))}
    (= :struct (:sub def)) (let [n (+ 4 (struct-param-count (:form def)))]
                             {:qname qname :computed? true :arity n
                              :modes [{:in (vec (range (- n 2))) :out [(- n 2) (dec n)]}]})
    (= :extern (:sub def)) {:qname qname :computed? false :arity (:arity def)}
    :else {:qname qname :computed? false
           :arity (rule-head-arity (first (or (:clauses def) [(:form def)])))}))

(defn- lookup-relation [cx sym]
  (when-let [r (ns/resolve-name (:prog cx) (:ns cx) sym :relation)]
    (relation-info r)))

;; ---------------------------------------------------------------- terms and patterns

(defn- term-of [cx form]
  (cond
    (wild? form) {:var (new-wild! cx)}
    (var-sym? form) {:var (var-idx cx form)}
    (ground? form) {:const (v/canon form)}
    :else {:expr (analyze-expr cx form) :vars (vars-of cx form)}))

(defn- pattern-of [cx form]
  (cond
    (wild? form) {:pvar (new-wild! cx)}
    (var-sym? form) {:pvar (var-idx cx form)}
    (vector? form)
    (let [[items rst] (split-with #(not= '& %) form)]
      (when (and (seq rst) (not= 2 (count rst)))
        (bad-form! form "& must be followed by exactly one pattern"))
      {:pvec (mapv #(pattern-of cx %) items)
       :rest (when (seq rst) (pattern-of cx (second rst)))})
    (map? form)
    {:pmap (mapv (fn [[k p]]
                   (when-not (ground? k) (bad-form! form "Map pattern keys must be constants"))
                   [(v/canon k) (pattern-of cx p)])
                 form)}
    (and (ground? form) (not (coll? form))) {:pconst (v/canon form)}
    :else (bad-form! form "Unsupported bind pattern")))

;; ---------------------------------------------------------------- literals

(defn- rel-literal
  "Analyzes (rel t…). negated? marks a literal inside (not …)."
  [cx [head & args :as form] negated?]
  (when-not (symbol? head) (bad-form! form "A literal must name a relation"))
  (let [info (lookup-relation cx head)
        terms (mapv #(term-of cx %) args)
        computed? (boolean (:computed? info))]
    (cond
      (nil? info)
      (if (and (ns/resolve-name (:prog cx) (:ns cx) head :fn))
        (problem! cx :fn-as-relation
                  (str head " is a function, not a relation; use defrel, or bind in a rule body")
                  form {:sym head})
        (problem! cx :undefined-relation (str "Undefined relation " head) form {:sym head}))

      :else
      (do
        (when (not= (count terms) (:arity info))
          (problem! cx :arity-mismatch
                    (str "Relation " (:qname info) " expects " (:arity info) " arguments, got "
                         (count terms))
                    form {:rel (:qname info) :expected (:arity info) :actual (count terms)}))
        (let [inputs (into #{} (mapcat :in) (:modes info))]
          (doseq [[i t] (map-indexed vector terms)
                  :when (and (:expr t) (not (and computed? (contains? inputs i))))]
            (problem! cx :expression-in-stored-literal
                      "Expressions are only allowed in input positions of computed relations; use bind"
                      form {:rel (:qname info) :position i})))))
    (cond-> {:lit (if negated? :not :rel) :rel (or (:qname info) head) :args terms}
      (not negated?) (assoc :computed? computed?)
      computed? (assoc :modes (:modes info)))))

(defn- literal [cx form]
  (when-not (and (seq? form) (seq form))
    (bad-form! form "Body literals must be lists"))
  (let [h (first form)]
    (case (when (symbol? h) (name h))
      "not" (do (when-not (and (= 2 (count form)) (seq? (second form)) (seq (second form)))
                  (bad-form! form "not expects one relation literal"))
                (rel-literal cx (second form) true))
      "when" (do (when-not (= 2 (count form)) (bad-form! form "when expects one expression"))
                 {:lit :when :expr (analyze-expr cx (second form)) :vars (vars-of cx (second form))})
      ("bind" "bind-nil")
      (do (when-not (= 3 (count form)) (bad-form! form (str h " expects a pattern and an expression")))
          (let [[_ pat expr] form]
            {:lit :bind :pat (pattern-of cx pat) :expr (analyze-expr cx expr)
             :vars (vars-of cx expr) :nil-ok? (= "bind-nil" (name h))}))
      (rel-literal cx form false))))

;; ---------------------------------------------------------------- heads

(defn- head-term [cx aggs pos form]
  (cond
    (and (seq? form) (symbol? (first form))
         (ns/resolve-name (:prog cx) (:ns cx) (first form) :aggregate))
    (do (when-not (and (seq (rest form)) (every? var-sym? (rest form)))
          (bad-form! form "Aggregate arguments must be variables"))
        (swap! aggs conj {:pos pos :agg (symbol (name (first form)))
                          :args (mapv #(var-idx cx %) (rest form))})
        {:agg (dec (count @aggs))})

    (wild? form)
    (do (problem! cx :wildcard-in-head "_ is not allowed in a head" form {})
        {:var (new-wild! cx)})

    (or (var-sym? form) (ground? form)) (term-of cx form)

    :else
    (do (problem! cx :expression-in-stored-literal "Expressions are not allowed in a head" form {})
        {:expr nil :vars (vars-of cx form)})))

;; ---------------------------------------------------------------- analyze-rule

(defn- target-ns [prog cur q]
  (let [q (symbol q)]
    (or (get-in prog [:namespaces cur :aliases q]) q)))

(defn analyze-rule
  "Analyzes (defrule name {opts}? [head] body…) of namespace cur-ns. Problems
  found by the checks of spec 3 are recorded under :problems; check-program
  reports them."
  [prog cur-ns form]
  (when-not (and (seq? form) (>= (count form) 3) (symbol? (second form)))
    (bad-form! form "Expected (defrule name {opts}? [head] body…)"))
  (let [[_ nm & more] form
        opts (when (map? (first more)) (first more))
        more (skip-opts more)
        head (first more)
        body (rest more)]
    (when-not (vector? head) (bad-form! form "Expected a head vector"))
    (when-not (every? (fn [[k val]] (and (= :ordered k) (boolean? val))) opts)
      (bad-form! form "The only rule option is {:ordered true}"))
    (let [names (vec (distinct (mapcat form-var-seq (cons head body))))
          name->idx (zipmap names (range))
          scope0 (ac/new-scope)
          [scope var-locals]
          (reduce (fn [[s m] sym]
                    (let [[s' id] (ac/bind-local s sym)]
                      [s' (assoc m (name->idx sym) id)]))
                  [scope0 {}] names)
          cx {:prog prog :ns cur-ns :scope scope
              :names name->idx
              :loc (loc-of form)
              :next (atom (count names)) :wild (atom #{}) :problems (atom [])}
          q-ns (if-let [q (namespace nm)] (target-ns prog cur-ns q) cur-ns)
          _ (when (not= q-ns cur-ns)
              (problem! cx :foreign-rule
                        (str "Namespace " cur-ns " cannot define rule clauses for " nm) form
                        {:rel nm}))
          aggs (atom [])
          head-terms (vec (map-indexed #(head-term cx aggs %1 %2) head))
          body-lits (mapv #(literal cx %) body)]
      {:rel (symbol (str q-ns) (name nm))
       :ns cur-ns
       :ordered? (true? (:ordered opts))
       :loc (loc-of form)
       :form form
       :nvars @(:next cx)
       :var-names (:names cx)
       :var-locals var-locals
       :wild @(:wild cx)
       :head head-terms
       :aggs @aggs
       :body body-lits
       :problems @(:problems cx)})))

;; ---------------------------------------------------------------- defrel

(defn analyze-defrel
  "Analyzes (defrel name [params…] ([in… -> out…] body…)…) into
  {:qname :params :modes [{:in :out :body :param-ids}]}."
  [prog cur-ns form]
  (when-not (and (seq? form) (>= (count form) 3) (symbol? (second form))
                 (vector? (nth form 2)) (every? simple-symbol? (nth form 2))
                 (apply distinct? (nth form 2)))
    (bad-form! form "Expected (defrel name [params…] clauses…) with distinct parameters"))
  (let [params (vec (nth form 2))
        idx (zipmap params (range))]
    {:qname (symbol (str cur-ns) (name (second form)))
     :loc (loc-of form)
     :params params
     :modes (vec (for [clause (drop 3 form)]
                   (do
                     (when-not (and (seq? clause) (vector? (first clause)))
                       (bad-form! clause "Expected ([in… -> out…] body…)"))
                     (let [[in arrow+out] (split-with #(not= '-> %) (first clause))
                           out (rest arrow+out)]
                       (when (or (empty? arrow+out) (some #{'->} out))
                         (bad-form! clause "A mode needs exactly one ->"))
                       (when-not (every? idx (concat in out))
                         (bad-form! clause "Mode names must be parameters"))
                       (let [[scope ids] (reduce (fn [[s ids] sym]
                                                   (let [[s' id] (ac/bind-local s sym)]
                                                     [s' (conj ids id)]))
                                                 [(ac/new-scope) []] in)
                             body (with-meta (cons 'do (rest clause)) (meta clause))]
                         {:in (mapv idx in) :out (mapv idx out)
                          :param-ids ids
                          :body (ac/analyze prog cur-ns body scope)})))))}))

(defn- check-result [qname n-out result]
  (let [bad! #(error! :bad-relation-result :run
                      (str "Relation " qname " returned an invalid result") {:rel qname})]
    (cond
      (zero? n-out) result
      (nil? result) []
      (or (sequential? result) (set? result))
      (mapv (fn [t] (if (and (vector? t) (= n-out (count t))) t (bad!))) result)
      :else (bad!))))

(defn compile-defrel
  "Compiles an analyzed defrel into a computed relation entry."
  [{:keys [qname params modes]} fn-table]
  {:qname qname
   :arity (count params)
   :modes (mapv (fn [{:keys [in out body param-ids]}]
                  (let [compiled (cc/compile-node body fn-table)
                        n-out (count out)]
                    {:in in :out out
                     :impl (fn [ctx in-vals]
                             (check-result qname n-out
                                           (cc/eval-code ctx compiled
                                                         (zipmap param-ids in-vals))))}))
                modes)})

;; ---------------------------------------------------------------- check-program

(defn- fail! [kind msg {:keys [loc ns form]} data]
  (error! kind :check msg (merge loc {:ns ns :form form} data)))

(defn- pat-vars [{:keys [pvar pvec pmap] :as p}]
  (cond
    (contains? p :pvar) #{pvar}
    (contains? p :pvec) (into (if (:rest p) (pat-vars (:rest p)) #{}) (mapcat pat-vars) pvec)
    (contains? p :pmap) (into #{} (mapcat (comp pat-vars second)) pmap)
    :else #{}))

(defn- lit-bound
  "Variables a positive literal can bind. Optimistic for computed literals (any
  mode's outputs count); the planner is the real gate."
  [lit]
  (case (:lit lit)
    :rel (let [outs (when (:computed? lit) (into #{} (mapcat :out) (:modes lit)))]
           (into #{} (comp (keep-indexed (fn [i t]
                                           (when (and (:var t) (or (not (:computed? lit))
                                                                   (contains? outs i)))
                                             (:var t)))))
                 (:args lit)))
    :bind (pat-vars (:pat lit))
    #{}))

(defn- var-name [rule i]
  (some (fn [[s j]] (when (= i j) s)) (:var-names rule)))

(defn- check-rule [prog {:keys [rel ns head aggs body wild] :as rule}]
  (when-let [{:keys [kind msg form loc data]} (first (:problems rule))]
    (fail! kind msg {:loc loc :ns ns :form form} data))
  (let [ctxd {:loc (:loc rule) :ns ns :form (:form rule)}
        def (get-in prog [:namespaces (symbol (namespace rel)) :defs (symbol (name rel))])
        clauses (or (:clauses def) [(:form def)])
        visible #(remove wild %)]
    (when (and def (not= (count head) (rule-head-arity (first clauses))))
      (fail! :arity-mismatch (str "Clauses of " rel " have different arities") ctxd {:rel rel}))
    (when (and (seq aggs) (> (count clauses) 1))
      (fail! :aggregate-multiple-clauses
             (str "Aggregate relation " rel " must have exactly one clause") ctxd {:rel rel}))
    (when (and (empty? body) (not (every? #(contains? % :const) head)))
      (fail! :fact-not-ground "A fact must be ground" ctxd {:rel rel}))
    (let [all-bound (into #{} (mapcat lit-bound) body)
          step (fn [bound lit]
                 (when (= :not (:lit lit))
                   (doseq [t (:args lit)
                           :let [i (:var t)]
                           :when (and i (not (wild i))
                                      (not ((if (:ordered? rule) bound all-bound) i)))]
                     (fail! :unbound-in-negation
                            (str "Variable " (var-name rule i) " in not is not bound by a positive literal")
                            ctxd {:var (var-name rule i)})))
                 (into bound (lit-bound lit)))
          bound (reduce step #{} body)
          needed (concat (keep :var head) (mapcat :args aggs))]
      (doseq [i (visible needed)
              :when (not (bound i))]
        (fail! :unsafe-head-var (str "Head variable " (var-name rule i) " is not bound by the body")
               ctxd {:var (var-name rule i)})))))

(defn- check-defrel [{:keys [qname params modes loc]}]
  (let [n (count params)]
    (doseq [[k {:keys [in out]}] (map-indexed vector modes)]
      (when-not (and (= n (count (concat in out)))
                     (= (set (concat in out)) (set (range n))))
        (fail! :mode-coverage "Mode inputs and outputs must be exactly the parameters"
               {:loc loc :ns (symbol (namespace qname))}
               {:rel qname :mode k})))))

(defn check-program
  "Checks analyzed rules and defrels (spec 3, 4.2). Throws the first error
  found as a :check-phase language error."
  [prog analyzed]
  (doseq [a analyzed]
    (if (contains? a :rel)
      (check-rule prog a)
      (check-defrel a))))
