(ns lang.analyze.code
  "Analyzer for the code sublanguage: turns forms into AST maps (spec 4.1, 4.3)."
  (:require [lang.errors :refer [error! loc-of]]
            [lang.ns :as ns]
            [lang.values :as v]))

;; ---------------------------------------------------------------- scope

(defn new-scope
  "An empty analysis scope."
  []
  {:locals {} :tail? false :loop nil :next-id (atom 0)})

(defn fresh-id [scope] (swap! (:next-id scope) inc))

(defn bind-local
  "Binds sym to a fresh id. Returns [scope' id]."
  [scope sym]
  (let [id (fresh-id scope)]
    [(assoc-in scope [:locals sym] id) id]))

(defn defn-arities
  "Arities [[min max-or-nil] …] of a (defn name doc? attrs? [params] …) or
  multi-arity defn form."
  [form]
  (let [more (drop 2 form)
        more (if (string? (first more)) (rest more) more)
        more (if (map? (first more)) (rest more) more)
        sig (fn [params]
              (let [[fixed rst] (split-with #(not= '& %) params)]
                [(count fixed) (when-not (seq rst) (count fixed))]))]
    (if (vector? (first more))
      [(sig (first more))]
      (mapv (comp sig first) (filter seq? more)))))

;; ---------------------------------------------------------------- helpers

(def ^:private illegal-heads '#{new set! def var throw})

(defn- fail [{:keys [ns]} scope form kind msg data]
  (error! kind :analyze msg
          (merge (or (not-empty (loc-of form)) (:loc scope))
                 {:form form :ns ns}
                 data)))

(defn- node [loc op & kvs]
  (apply assoc {:op op :loc loc} kvs))

(defn- const [loc val] (node loc :const :val val))

(defn- nil-node [loc] (const loc nil))

(defn- const? [n] (= :const (:op n)))

(defn- non-tail [scope] (assoc scope :tail? false))

(defn- core-call [cx scope form loc sym args]
  (let [e (get-in (:prog cx) [:registry 'lang.core :fn sym])]
    (when-not e
      (fail cx scope form :internal-error "Missing core built-in for destructuring" {:sym sym}))
    (node loc :call-builtin :name (symbol "lang.core" (name sym)) :impl (:impl e) :args args)))

(declare analyze*)

(defn- analyze-body
  "Analyzes forms as an implicit do; the last inherits the scope's tail?."
  [cx scope forms loc]
  (case (count forms)
    0 (nil-node loc)
    1 (analyze* cx scope (first forms))
    (let [exprs (into (mapv #(analyze* cx (non-tail scope) %) (butlast forms))
                      [(analyze* cx scope (last forms))])]
      (node loc :do :exprs exprs))))

(defn- wrap-let [loc bindings body]
  (if (seq bindings) (node loc :let :bindings bindings :body body) body))

;; ---------------------------------------------------------------- destructuring

(declare bind-pattern)

(defn- key-sym-local [s]
  (symbol (name s)))

(defn- bind-vector [cx scope pattern init loc]
  (let [tmp (fresh-id scope)
        tl (node loc :local :id tmp)
        scope (non-tail scope)]
    (loop [items (seq pattern) i 0 scope scope bs [[tmp init]]]
      (if-not items
        [scope bs]
        (let [[p & more] items]
          (cond
            (= '& p)
            (let [[rp & more2] more
                  cnt (core-call cx scope pattern loc 'count [tl])
                  test (core-call cx scope pattern loc '> [cnt (const loc i)])
                  rest-init (node loc :if :test test
                                  :then (core-call cx scope pattern loc 'subvec [tl (const loc i)])
                                  :else (nil-node loc))
                  [scope' bs'] (bind-pattern cx scope rp rest-init loc)]
              (recur more2 i scope' (into bs bs')))

            (= :as p)
            (let [[s' bs'] (bind-pattern cx scope (first more) tl loc)]
              (recur (next more) i s' (into bs bs')))

            :else
            (let [init' (core-call cx scope pattern loc 'nth [tl (const loc i) (nil-node loc)])
                  [scope' bs'] (bind-pattern cx scope p init' loc)]
              (recur more (inc i) scope' (into bs bs')))))))))

(defn- bind-map [cx scope pattern init loc]
  (let [tmp (fresh-id scope)
        tl (node loc :local :id tmp)
        defaults (get pattern :or {})
        scope (non-tail scope)
        get-node (fn [scope key-node default-form sym]
                   (let [d (if (contains? defaults sym) default-form ::none)]
                     (core-call cx scope pattern loc 'get
                                (cond-> [tl key-node]
                                  (not= d ::none) (conj (analyze* cx scope d))))))
        bind-one (fn [[scope bs] p key-node]
                   (let [sym (when (symbol? p) (key-sym-local p))
                         dflt (when sym (get defaults sym))
                         init' (get-node scope key-node dflt sym)
                         [scope' bs'] (bind-pattern cx scope p init' loc)]
                     [scope' (into bs bs')]))
        bind-keys (fn [acc syms mk-key]
                    (reduce (fn [acc s]
                              (bind-one acc (key-sym-local s) (const loc (mk-key s))))
                            acc syms))]
    (reduce
     (fn [[scope bs :as acc] [k vv]]
       (case k
         :or acc
         :as (let [[s' bs'] (bind-pattern cx scope vv tl loc)] [s' (into bs bs')])
         :keys (bind-keys acc vv #(keyword (namespace %) (name %)))
         :strs (bind-keys acc vv #(name %))
         :syms (bind-keys acc vv #(symbol (namespace %) (name %)))
         (bind-one acc k (analyze* cx scope vv))))
     [scope [[tmp init]]]
     pattern)))

(defn- bind-pattern
  "Binds pattern to the init node. Returns [scope' [[id node]…]]."
  [cx scope pattern init loc]
  (cond
    (and (symbol? pattern) (nil? (namespace pattern)) (not= '& pattern))
    (let [[s id] (bind-local scope pattern)] [s [[id init]]])
    (vector? pattern) (bind-vector cx scope pattern init loc)
    (map? pattern) (bind-map cx scope pattern init loc)
    :else (fail cx scope pattern :bad-form "Unsupported binding pattern" {})))

(defn- bind-pairs
  "Sequential let-style binding of a [pattern init …] vector. Returns
  [scope' bindings] with tail? restored on scope'."
  [cx scope bvec form loc]
  (when-not (and (vector? bvec) (even? (count bvec)))
    (fail cx scope form :bad-form "Expected a binding vector with an even number of forms" {}))
  (let [tail? (:tail? scope)
        [s bs] (reduce (fn [[s bs] [p init]]
                         (let [init-node (analyze* cx (non-tail s) init)
                               [s' bs'] (bind-pattern cx s p init-node loc)]
                           [s' (into bs bs')]))
                       [(non-tail scope) []]
                       (partition 2 bvec))]
    [(assoc s :tail? tail?) bs]))

;; ---------------------------------------------------------------- special forms

(defn- sf-let [cx scope [_ bvec & body :as form] loc]
  (let [[s bs] (bind-pairs cx scope bvec form loc)]
    (wrap-let loc bs (analyze-body cx s body loc))))

(defn- sf-if [cx scope [_ t th & el :as form] loc]
  (when-not (and (<= 2 (dec (count form)) 3))
    (fail cx scope form :bad-form "if expects 2 or 3 forms" {}))
  (node loc :if
        :test (analyze* cx (non-tail scope) t)
        :then (analyze* cx scope th)
        :else (if (seq el) (analyze* cx scope (first el)) (nil-node loc))))

(defn- sf-when [cx scope [_ t & body] loc]
  (node loc :if :test (analyze* cx (non-tail scope) t)
        :then (analyze-body cx scope body loc) :else (nil-node loc)))

(defn- sf-when-not [cx scope [_ t & body] loc]
  (node loc :if :test (analyze* cx (non-tail scope) t)
        :then (nil-node loc) :else (analyze-body cx scope body loc)))

(defn- sf-if-let* [cx scope form loc bvec then-forms else-form]
  (when-not (and (vector? bvec) (= 2 (count bvec)))
    (fail cx scope form :bad-form "Expected a binding vector with one binding" {}))
  (let [[pattern test] bvec
        tmp (fresh-id scope)
        tl (node loc :local :id tmp)
        test-node (analyze* cx (non-tail scope) test)
        [s bs] (bind-pattern cx (non-tail scope) pattern tl loc)
        s (assoc s :tail? (:tail? scope))]
    (node loc :let :bindings [[tmp test-node]]
          :body (node loc :if :test tl
                      :then (wrap-let loc bs (analyze-body cx s then-forms loc))
                      :else (if else-form
                              (analyze* cx scope (first else-form))
                              (nil-node loc))))))

(defn- sf-when-let [cx scope [_ bvec & body :as form] loc]
  (sf-if-let* cx scope form loc bvec body nil))

(defn- sf-if-let [cx scope [_ bvec th & el :as form] loc]
  (sf-if-let* cx scope form loc bvec [th] (when (seq el) el)))

(defn- sf-cond [cx scope [_ & clauses :as form] loc]
  (when (odd? (count clauses))
    (fail cx scope form :bad-form "cond expects an even number of forms" {}))
  (reduce (fn [else [t e]]
            (if (or (= :else t) (= true t))
              (analyze* cx scope e)
              (node loc :if :test (analyze* cx (non-tail scope) t)
                    :then (analyze* cx scope e) :else else)))
          (nil-node loc)
          (reverse (partition 2 clauses))))

(defn- sf-do [cx scope [_ & body] loc]
  (analyze-body cx scope body loc))

(defn- sf-quote [cx scope [_ x :as form] loc]
  (when-not (= 2 (count form))
    (fail cx scope form :bad-form "quote expects one form" {}))
  (const loc (v/canon x)))

(defn- sf-and-or [op cx scope [_ & forms] loc]
  (case (count forms)
    0 (const loc (= op :and))
    1 (analyze* cx scope (first forms))
    (node loc op :exprs (into (mapv #(analyze* cx (non-tail scope) %) (butlast forms))
                              [(analyze* cx scope (last forms))]))))

(defn- thread [form-fn [_ x & steps]]
  (reduce (fn [acc step]
            (let [l (cond
                      (seq? step) (form-fn acc step)
                      (keyword? step) (list step acc)
                      :else (list step acc))]
              (with-meta l (meta step))))
          x steps))

(defn- sf-thread-first [cx scope form loc]
  (analyze* cx scope (thread (fn [acc [f & args]] (list* f acc args)) form)))

(defn- sf-thread-last [cx scope form loc]
  (analyze* cx scope (thread (fn [acc [f & args]] (concat (list f) args (list acc))) form)))

(defn- parse-params
  "Analyzes a param vector. Returns [scope' params rest-id wrap-bindings]."
  [cx scope params form loc]
  (when-not (vector? params)
    (fail cx scope form :bad-form "Expected a parameter vector" {}))
  (let [[fixed rst] (split-with #(not= '& %) params)
        rest-pat (second rst)]
    (when (and (seq rst) (not= 2 (count rst)))
      (fail cx scope form :bad-form "& must be followed by exactly one parameter" {}))
    (let [step (fn [[s ids bs] p]
                 (if (and (symbol? p) (nil? (namespace p)))
                   (let [[s' id] (bind-local s p)] [s' (conj ids id) bs])
                   (let [id (fresh-id s)
                         [s' bs'] (bind-pattern cx s p (node loc :local :id id) loc)]
                     [s' (conj ids id) (into bs bs')])))
          [s ids bs] (reduce step [(non-tail scope) [] []] fixed)
          [s rest-id bs] (if (seq rst)
                           (let [[s' ids' bs'] (step [s [] bs] rest-pat)]
                             [s' (first ids') bs'])
                           [s nil bs])]
      [s ids rest-id bs])))

(defn- analyze-arity [cx scope [params & body :as sig] form loc]
  (let [[s ids rest-id bs] (parse-params cx scope params form loc)
        s (assoc s :tail? true :loop {:arity (+ (count ids) (if rest-id 1 0))})]
    {:params ids :rest rest-id
     :body (wrap-let loc bs (analyze-body cx s body loc))}))

(defn- sf-fn [cx scope [_ & more :as form] loc]
  (let [[self more] (if (symbol? (first more)) [(first more) (rest more)] [nil (seq more)])
        [scope self-id] (if self (bind-local scope self) [scope nil])
        sigs (cond
               (vector? (first more)) [more]
               (and (seq more) (every? seq? more)) more
               :else (fail cx scope form :bad-form "Malformed fn" {}))]
    (node loc :fn :self self-id
          :arities (mapv #(analyze-arity cx scope % form loc) sigs))))

(defn- sf-loop [cx scope [_ bvec & body :as form] loc]
  (when-not (and (vector? bvec) (even? (count bvec)))
    (fail cx scope form :bad-form "Expected a binding vector with an even number of forms" {}))
  (let [step (fn [[s lbs dbs] [p init]]
               (let [init-node (analyze* cx (non-tail s) init)]
                 (if (and (symbol? p) (nil? (namespace p)))
                   (let [[s' id] (bind-local s p)] [s' (conj lbs [id init-node]) dbs])
                   (let [id (fresh-id s)
                         [s' bs'] (bind-pattern cx s p (node loc :local :id id) loc)]
                     [s' (conj lbs [id init-node]) (into dbs bs')]))))
        [s lbs dbs] (reduce step [(non-tail scope) [] []] (partition 2 bvec))
        s (assoc s :tail? true :loop {:arity (count lbs)})]
    (node loc :loop :bindings lbs :body (wrap-let loc dbs (analyze-body cx s body loc)))))

(defn- sf-recur [cx scope [_ & args :as form] loc]
  (when-not (and (:tail? scope) (:loop scope))
    (fail cx scope form :recur-not-tail "recur must be in tail position of a loop or fn" {}))
  (let [n (get-in scope [:loop :arity])]
    (when-not (= n (count args))
      (fail cx scope form :recur-arity
            (str "recur expects " n " arguments, got " (count args))
            {:expected n :actual (count args)}))
    (node loc :recur :args (mapv #(analyze* cx (non-tail scope) %) args))))

(defn- sf-case [cx scope [_ e & clauses :as form] loc]
  (let [default? (odd? (count clauses))
        pairs (partition 2 clauses)
        group (fn [t] (if (seq? t) (set (map v/canon t)) #{(v/canon t)}))
        cs (mapv (fn [[t r]] [(group t) (analyze* cx scope r)]) pairs)
        all (mapcat first cs)]
    (when (not= (count all) (count (set all)))
      (fail cx scope form :bad-form "Duplicate case constant" {}))
    (node loc :case
          :test (analyze* cx (non-tail scope) e)
          :clauses cs
          :default (when default? (analyze* cx scope (last clauses))))))

(defn- sf-parse [explain? cx scope [_ t & args :as form] loc]
  (when-not (<= 1 (count args) 2)
    (fail cx scope form :arity-error
          (str (first form) " expects a type and a source, with an optional offset") {}))
  (node loc :parse :explain? explain? :type t :ns (:ns cx) :scope (non-tail scope)
        :args (mapv #(analyze* cx (non-tail scope) %) args)))

(def ^:private special-handlers
  {'let sf-let 'if sf-if 'when sf-when 'when-not sf-when-not
   'when-let sf-when-let 'if-let sf-if-let 'cond sf-cond 'do sf-do
   'quote sf-quote 'and (partial sf-and-or :and) 'or (partial sf-and-or :or)
   '-> sf-thread-first '->> sf-thread-last 'fn sf-fn 'loop sf-loop
   'recur sf-recur 'case sf-case
   'parse (partial sf-parse false) 'parse-explain (partial sf-parse true)})

;; ---------------------------------------------------------------- symbols and calls

(defn- unresolved [cx scope sym]
  (let [prog (:prog cx) cur (:ns cx)
        msg (cond
              (or (contains? illegal-heads sym) (.startsWith (str sym) "."))
              (str "Illegal symbol " sym)
              (contains? (set (keys special-handlers)) sym)
              (str sym " is a special form and cannot be used as a value")
              (ns/resolve-name prog cur sym :relation)
              nil
              (ns/resolve-name prog cur sym :type)
              (str sym " names a type, not a function or value")
              :else (str "Unable to resolve symbol " sym))]
    (when-not msg
      (fail cx scope sym :relation-in-code
            (str sym " is a relation and cannot be called from code; use bind in a rule body")
            {}))
    (fail cx scope sym :unresolved-symbol msg {})))

(defn- resolve-fn [cx scope sym]
  (or (when-not (contains? illegal-heads sym)
        (ns/resolve-name (:prog cx) (:ns cx) sym :fn))
      (unresolved cx scope sym)))

(defn- analyze-symbol [cx scope sym loc]
  (if-let [id (get-in scope [:locals sym])]
    (node loc :local :id id)
    (let [{:keys [qname def builtin?]} (resolve-fn cx scope sym)]
      (node loc :fn-ref :qname qname :builtin? builtin? :impl (when builtin? (:impl def))))))

(defn- arity-ok? [argc arities]
  (some (fn [[mn mx]] (and (>= argc mn) (or (nil? mx) (<= argc mx)))) arities))

(defn- check-arity! [cx scope form qname argc arities]
  (when-not (arity-ok? argc arities)
    (fail cx scope form :arity-error
          (str "Wrong number of arguments (" argc ") passed to " qname)
          {:fn qname :actual argc :expected arities})))

(defn- analyze-call [cx scope [head & args :as form] loc]
  (let [argv #(mapv (fn [a] (analyze* cx (non-tail scope) a)) args)]
    (cond
      (keyword? head)
      (do (when-not (<= 1 (count args) 2)
            (fail cx scope form :arity-error "Keyword call expects 1 or 2 arguments"
                  {:actual (count args)}))
          (node loc :kw-invoke :kw head :args (argv)))

      (and (symbol? head) (not (get-in scope [:locals head])))
      (if-let [h (and (not (contains? illegal-heads head)) (get special-handlers head))]
        (h cx scope form loc)
        (let [{:keys [qname def builtin?]} (resolve-fn cx scope head)]
          (if builtin?
            (do (check-arity! cx scope form qname (count args) [(:arity def)])
                (node loc :call-builtin :name qname :impl (:impl def) :args (argv)))
            (do (when (:form def)
                  (check-arity! cx scope form qname (count args) (defn-arities (:form def))))
                (node loc :call-defn :qname qname :args (argv))))))

      :else
      (node loc :invoke :f (analyze* cx (non-tail scope) head) :args (argv)))))

;; ---------------------------------------------------------------- entry

(defn- analyze-coll [cx scope form loc]
  (let [sc (non-tail scope)
        an #(analyze* cx sc %)]
    (cond
      (vector? form)
      (let [items (mapv an form)]
        (if (every? const? items) (const loc (mapv :val items)) (node loc :vector :items items)))
      (set? form)
      (let [items (mapv an form)]
        (if (every? const? items) (const loc (set (map :val items))) (node loc :set :items items)))
      :else
      (let [pairs (mapv (fn [[k val]] [(an k) (an val)]) form)]
        (if (every? (fn [[k val]] (and (const? k) (const? val))) pairs)
          (const loc (into {} (map (fn [[k val]] [(:val k) (:val val)])) pairs))
          (node loc :map :pairs pairs))))))

(defn- analyze* [cx scope form]
  (let [loc (or (not-empty (loc-of form)) (:loc scope) {})
        scope (assoc scope :loc loc)]
    (cond
      (symbol? form) (analyze-symbol cx scope form loc)
      (seq? form) (if (empty? form) (const loc ()) (analyze-call cx scope form loc))
      (or (vector? form) (map? form) (set? form)) (analyze-coll cx scope form loc)
      (or (nil? form) (boolean? form) (string? form) (char? form) (keyword? form) (number? form))
      (const loc (v/canon form))
      :else (fail cx scope form :bad-form "Unsupported form" {}))))

(defn analyze
  "Analyzes a code form in namespace cur-ns into an AST node."
  [prog cur-ns form scope]
  (analyze* {:prog prog :ns cur-ns} scope form))

(defn analyze-defn
  "Analyzes a (defn name doc? attrs? [params] body…) or multi-arity form of
  namespace cur-ns into {:qname :arities [{:params [id…] :rest id-or-nil :body node}]}."
  [prog cur-ns form]
  (let [cx {:prog prog :ns cur-ns}
        scope (new-scope)
        loc (or (not-empty (loc-of form)) {})
        more (drop 2 form)
        more (if (string? (first more)) (rest more) more)
        more (if (map? (first more)) (rest more) more)
        sigs (cond
               (vector? (first more)) [more]
               (and (seq more) (every? seq? more)) more
               :else (fail cx scope form :bad-form "Malformed defn" {}))]
    {:qname (symbol (str cur-ns) (name (second form)))
     :arities (mapv #(analyze-arity cx scope % form loc) sigs)}))
