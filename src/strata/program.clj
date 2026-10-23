(ns strata.program
  "Whole-program pipeline (spec 6.1, 8.3): host sources -> compiled immutable
  program -> isolated runs.

  (load-program {:sources {ns src} :builtins #{ns} :externs {ns {rel arity}}
                 :limits m :registry r})
  reads, orders, collects definitions, analyzes, checks, plans, stratifies and
  compiles. :registry (default: the full built-in registry) and :unchecked?
  (skip the rule checks) are test hooks. The result is a plain immutable map.

  (run-program prog {:facts {q tuples} :resources :limits :trace :on-code-error})
  evaluates in a fresh ctx on an isolated thread and returns
  {:relations {q #{tuple}} :diagnostics … :stats … :tainted #{q}}."
  (:require [strata.analyze.code :as ac]
            [strata.analyze.rule :as ar]
            [strata.analyze.struct :as as]
            [strata.builtins :as b]
            [strata.compile.code :as cc]
            [strata.compile.struct :as cs]
            [strata.engine :as e]
            [strata.errors :as err :refer [error! loc-of]]
            [strata.ns :as ns]
            [strata.reader :as reader]
            [strata.runtime :as rt]
            [strata.values :as v]))

;; ---------------------------------------------------------------- definitions

(def ^:private def-kinds
  {'defn {:kinds #{:fn} :sub :defn}
   'defrel {:kinds #{:relation} :sub :defrel}
   'defrule {:kinds #{:relation} :sub :rule}
   'defstruct {:kinds #{:relation :type} :sub :struct}
   'deftype {:kinds #{:type} :sub :deftype}})

(defn- bad-form! [ns-sym form msg]
  (error! :bad-form :analyze msg (assoc (loc-of form) :ns ns-sym :form form)))

(defn- check-form! [ns-sym form]
  (when-not (and (seq? form) (contains? def-kinds (first form)))
    (bad-form! ns-sym form "Expected one of defn, defrel, defrule, defstruct, deftype"))
  (when-not (symbol? (second form))
    (bad-form! ns-sym form "A definition needs a symbol name")))

(defn- register-defs
  "Adds every namespace and its definitions to the symbol table."
  [prog order units]
  (reduce
   (fn [prog n]
     (let [[nsf & forms] (get units n)
           prog (ns/add-namespace prog (ns/parse-ns-form nsf))]
       (reduce (fn [p f]
                 (check-form! n f)
                 (let [sym (symbol (name (second f)))]
                   (ns/add-def p n sym
                               (assoc (def-kinds (first f))
                                      :form f
                                      :qname (symbol (str n) (str sym))))))
               prog forms)))
   prog order))

(defn- forms-of [units order head]
  (for [n order, f (rest (get units n)) :when (= head (first f))]
    [n f]))

;; ---------------------------------------------------------------- load

(defn- load* [{:keys [sources builtins externs limits registry unchecked?]}]
  (let [limits (merge rt/default-limits limits)
        units (into {} (map (fn [[n src]]
                              [n (reader/read-forms src {:ns-name n
                                                         :max-source-bytes (:max-source-bytes limits)
                                                         :max-form-depth (:max-form-depth limits)})]))
                    sources)
        order (ns/order-namespaces units {:builtins (set builtins) :externs externs})
        registry (or registry @b/registry)
        prog (register-defs (ns/empty-program registry externs) order units)
        fn-table (atom {})
        struct-table (atom {})
        analyzed-fns (vec (for [[n f] (forms-of units order 'defn)] (ac/analyze-defn prog n f)))
        analyzed-types (vec (for [n order, f (rest (get units n))
                                  :when (#{'defstruct 'deftype} (first f))]
                              [(first f)
                               (if (= 'defstruct (first f))
                                 (as/analyze-struct prog n f)
                                 (as/analyze-deftype prog n f))]))
        analyzed-rels (vec (for [[n f] (forms-of units order 'defrel)] (ar/analyze-defrel prog n f)))
        rules (vec (for [[n f] (forms-of units order 'defrule)] (ar/analyze-rule prog n f)))]
    (when-not unchecked? (ar/check-program prog (concat analyzed-rels rules)))
    (binding [cc/*compile-env* (cs/parse-env prog struct-table)]
      (doseq [a analyzed-fns]
        (swap! fn-table assoc (:qname a) (cc/compile-defn a fn-table)))
      (doseq [[kind a] analyzed-types]
        (let [c (if (= 'defstruct kind)
                  (cs/compile-struct a struct-table fn-table)
                  (cs/compile-deftype a struct-table fn-table))]
          (swap! struct-table assoc (:qname c) c)))
      (let [computed (merge (into {} (comp (mapcat (fn [[_ r]] (vals (:relation r)))) (map (juxt :qname identity)))
                                  registry)
                            (into {} (map (fn [a] (let [en (ar/compile-defrel a fn-table)] [(:qname en) en])))
                                  analyzed-rels)
                            (into {} (keep (fn [[q c]] (when (= :struct (:kind c)) [q (cs/struct-relation c)])))
                                  @struct-table))
            stored (into #{} (concat (for [[n rels] externs, r (keys rels)] (symbol (str n) (str r)))
                                     (map :rel rules)))
            prepared (e/prepare {:rules rules :computed computed :fn-table fn-table :stored? stored})]
        {:strata (:strata prepared)
         :plans (reduce (fn [m r] (update m (:rel r) (fnil conj []) (:plans r)))
                       {} (for [s (:strata prepared), r (:rules s)] r))
         :computed computed
         :facts (:facts prepared)
         :prepared prepared
         :fn-table @fn-table
         :struct-table @struct-table
         :externs externs
         :warnings (vec (ns/shadow-warnings prog))
         :limits limits}))))

(defn load-program*
  "load-program plus the test hooks :registry and :unchecked?."
  {:no-doc true}
  [opts]
  (rt/run-isolated #(load* opts) :load))

(defn load-program
  "Builds a compiled, immutable program from host sources; see the ns
  docstring. Accepts :sources :builtins :externs :limits only."
  [opts]
  (load-program* (select-keys opts [:sources :builtins :externs :limits])))

;; ---------------------------------------------------------------- run

(defn- bad-fact! [msg q]
  (error! :bad-fact :run msg {:rel q}))

(defn- check-facts
  "Validates host facts against the externs and canonicalizes their values.
  Returns {q #{tuple}}."
  [externs facts]
  (let [arities (into {} (for [[n rels] externs, [r a] rels] [(symbol (str n) (str r)) a]))]
    (into {}
          (map (fn [[q tuples]]
                 (let [arity (get arities q ::none)]
                   (when (= ::none arity) (bad-fact! "Unknown relation" q))
                   (when-not (or (set? tuples) (sequential? tuples)) (bad-fact! "Facts must be a set or sequence of tuples" q))
                   [q (into #{}
                            (map (fn [t]
                                   (when-not (sequential? t) (bad-fact! "A tuple must be sequential" q))
                                   (when-not (= arity (count t)) (bad-fact! "Wrong tuple arity" q))
                                   (try (v/canon (vec t))
                                        (catch clojure.lang.ExceptionInfo ex
                                          (if (= :unsupported-value (:strata/error (ex-data ex)))
                                            (bad-fact! "Unsupported value in a tuple" q)
                                            (throw ex))))))
                            tuples)])))
          facts)))

(defn run-program
  "Evaluates a loaded program over host facts; see the ns docstring.
  Diagnostic counts are per evaluation of a failing step, not per distinct
  input: failures are not memoized, so the same bad input can count twice."
  [prog {:keys [facts resources limits trace on-code-error]}]
  (rt/run-isolated
   (fn []
     (let [edb (check-facts (:externs prog) facts)]
       (let [ctx (rt/make-ctx {:limits (merge (:limits prog) limits)
                               :resources resources
                               :trace trace
                               :on-code-error on-code-error})]
         (try
           (let [rels (e/evaluate ctx (:prepared prog) edb)
                 diags (rt/diagnostics ctx)]
             {:relations rels
              :diagnostics diags
              :stats @(:stats ctx)
              :tainted @(:taint ctx)})
           (finally (reset! (:page-cache ctx) {}))))))))
