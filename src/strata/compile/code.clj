(ns strata.compile.code
  "Compiles code-language AST nodes into Clojure closures (spec 4.1, 4.3, 4.4).
  A compiled node is (fn [ctx env] value); env maps local ids to values."
  (:require [strata.errors :refer [error!]]
            [strata.runtime :as rt]
            [strata.values :as v]))

;; Returned by `recur`; consumed by the nearest enclosing loop or fn body.
(defrecord Recur [args])

(defn- recur? [x] (instance? Recur x))

(def ^:dynamic *compile-env*
  "Bound while a program's code is compiled: {:prog :struct-table
  :compile-parse f}, as built by strata.compile.struct/parse-env. `parse` forms
  need the program to analyze their type at compile time, and
  strata.compile.struct depends on this namespace, so it is injected here."
  nil)

(declare compile-node)

(defn- compile-all [nodes fn-table]
  (mapv #(compile-node % fn-table) nodes))

(defn- eval-all [cs ctx env]
  (mapv #(% ctx env) cs))

(defn- lookup-defn [fn-table qname]
  (or (get @fn-table qname)
      (error! :internal-error :run "Undefined function" {:fn qname})))

(defn- call-user
  "Applies f; user LangFns charge fuel and count depth themselves."
  [ctx f args]
  (v/apply-fn ctx f args))

(defn- arity-matcher [{:keys [params rest]}]
  (let [n (count params)]
    (if rest #(>= % n) #(== % n))))

(defn- bind-args
  "Bind values of one arity's params (and rest) from the call args."
  [{:keys [params rest]} args]
  (let [n (count params)]
    (if rest
      (conj (subvec args 0 n) (when (> (count args) n) (subvec args n)))
      args)))

(defn- run-body
  "Runs a body with ids bound to vals, re-entering on Recur."
  [ctx env ids body vals]
  (loop [vals vals]
    (let [r (body ctx (into env (map vector ids vals)))]
      (if (recur? r)
        (do (rt/charge! ctx 1) (recur (:args r)))
        r))))

(defn- make-fn
  "A LangFn over compiled arities, closing over env. self-id, when given, is
  bound to the function itself in its body."
  [nm arities env self-id]
  (let [self (volatile! nil)
        impl (fn [ctx args]
               (let [args (vec args)
                     argc (count args)
                     a (some (fn [a] (when ((:match a) argc) a)) arities)]
                 (when-not a
                   (error! :arity-error :run "Wrong number of arguments"
                           {:fn nm :actual argc}))
                 (rt/charge! ctx 1)
                 (rt/with-depth ctx
                   #(run-body ctx (if self-id (assoc env self-id @self) env)
                              (:ids a) (:body a) (bind-args a args)))))]
    (vreset! self (v/->LangFn nm impl))))

(defn- compile-arities [arities fn-table]
  (mapv (fn [{:keys [params rest body] :as a}]
          {:match (arity-matcher a)
           :params params
           :rest rest
           :ids (cond-> (vec params) rest (conj rest))
           :body (compile-node body fn-table)})
        arities))

(defn compile-defn
  "Compiles an analyzed defn into a LangFn."
  [{:keys [qname arities]} fn-table]
  (make-fn qname (compile-arities arities fn-table) {} nil))

(defn- compile-fn-ref [{:keys [qname builtin? impl]} fn-table]
  (if builtin?
    (let [f (v/->LangFn qname (fn [ctx args] (apply impl ctx args)))]
      (fn [_ _] f))
    (let [f (v/->LangFn qname
                        (fn [ctx args]
                          (v/apply-fn ctx (lookup-defn fn-table qname) args)))]
      (fn [_ _] f))))

(defn- compile-case [{:keys [test clauses default]} fn-table]
  (let [t (compile-node test fn-table)
        cs (compile-all (map second clauses) fn-table)
        table (into {} (mapcat (fn [[consts _] c] (map (fn [k] [k c]) consts)) clauses cs))
        d (when default (compile-node default fn-table))]
    (fn [ctx env]
      (let [x (t ctx env)
            c (get table x ::miss)]
        (cond
          (not= ::miss c) (c ctx env)
          d (d ctx env)
          :else (error! :no-matching-clause :run "No matching case clause" {:value x}))))))

(defn- compile-loop [{:keys [bindings body]} fn-table]
  (let [ids (mapv first bindings)
        inits (compile-all (map second bindings) fn-table)
        b (compile-node body fn-table)]
    (fn [ctx env]
      (let [vals (loop [e env vs [] [i & more] (seq (map vector ids inits))]
                   (if i
                     (let [x ((second i) ctx e)]
                       (recur (assoc e (first i) x) (conj vs x) more))
                     vs))]
        (run-body ctx env ids b vals)))))

(defn compile-node
  "Compiles an AST node into (fn [ctx env] value). fn-table is an atom of
  {qname LangFn}, resolved at call time."
  [{:keys [op] :as node} fn-table]
  (case op
    :const (let [x (:val node)] (fn [_ _] x))
    :local (let [id (:id node)] (fn [_ env] (get env id)))
    :fn-ref (compile-fn-ref node fn-table)
    :if (let [t (compile-node (:test node) fn-table)
              th (compile-node (:then node) fn-table)
              el (compile-node (:else node) fn-table)]
          (fn [ctx env] (if (t ctx env) (th ctx env) (el ctx env))))
    :do (let [cs (compile-all (:exprs node) fn-table)]
          (fn [ctx env] (reduce (fn [_ c] (c ctx env)) nil cs)))
    :let (let [bs (mapv (fn [[id n]] [id (compile-node n fn-table)]) (:bindings node))
               body (compile-node (:body node) fn-table)]
           (fn [ctx env]
             (body ctx (reduce (fn [e [id c]] (assoc e id (c ctx e))) env bs))))
    :and (let [cs (compile-all (:exprs node) fn-table)]
           (fn [ctx env]
             (if (empty? cs) true (loop [[c & more] cs]
               (let [x (c ctx env)]
                 (if (and x more) (recur more) x))))))
    :or (let [cs (compile-all (:exprs node) fn-table)]
          (fn [ctx env]
            (if (empty? cs) nil (loop [[c & more] cs]
              (let [x (c ctx env)]
                (if (and (not x) more) (recur more) x))))))
    :case (compile-case node fn-table)
    :loop (compile-loop node fn-table)
    :recur (let [cs (compile-all (:args node) fn-table)]
             (fn [ctx env] (->Recur (eval-all cs ctx env))))
    :fn (let [arities (compile-arities (:arities node) fn-table)
              self-id (:self node)]
          (fn [_ env] (make-fn 'fn arities env self-id)))
    :vector (let [cs (compile-all (:items node) fn-table)]
              (fn [ctx env] (eval-all cs ctx env)))
    :set (let [cs (compile-all (:items node) fn-table)]
           (fn [ctx env] (set (map #(rt/check-deep! ctx %) (eval-all cs ctx env)))))
    :map (let [ps (mapv (fn [[k x]] [(compile-node k fn-table) (compile-node x fn-table)])
                        (:pairs node))]
           (fn [ctx env]
             (reduce (fn [m [k x]] (assoc m (rt/check-deep! ctx (k ctx env)) (x ctx env))) {} ps)))
    :call-builtin (let [impl (:impl node)
                        cs (compile-all (:args node) fn-table)]
                    (fn [ctx env]
                      (rt/charge! ctx 1)
                      (apply impl ctx (eval-all cs ctx env))))
    :call-defn (let [qname (:qname node)
                     cs (compile-all (:args node) fn-table)]
                 (fn [ctx env]
                   (let [args (eval-all cs ctx env)]
                     (call-user ctx (lookup-defn fn-table qname) args))))
    :invoke (let [f (compile-node (:f node) fn-table)
                  cs (compile-all (:args node) fn-table)]
              (fn [ctx env]
                (let [fv (f ctx env)]
                  (call-user ctx fv (eval-all cs ctx env)))))
    :kw-invoke (let [kw (:kw node)
                     cs (compile-all (:args node) fn-table)]
                 (fn [ctx env]
                   (rt/charge! ctx 1)
                   (v/apply-fn ctx kw (eval-all cs ctx env))))
    :parse (if-let [f (:compile-parse *compile-env*)]
             (f node *compile-env* fn-table)
             (error! :internal-error :run "parse needs a program compile environment" {}))))

(defn eval-code
  "Runs a compiled closure under a fresh per-call fuel budget."
  [ctx compiled env]
  (rt/with-call-budget ctx #(compiled ctx env)))
