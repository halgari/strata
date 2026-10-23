(ns lang.engine
  "Metered semi-naive bottom-up evaluation with stratified negation,
  aggregates and computed relations (spec 6.4, 3.3-3.5, 4.2).

  (prepare {:rules [rule…]        ; analyzed rules (lang.analyze.rule)
            :computed {qname entry} ; computed relation entries
            :fn-table atom          ; defn table, for compiling expressions
            :stored? #{qname}})     ; stored relations (externs, rule heads)
  returns a prepared map
    {:strata [{:rels :recursive? :rules [compiled-rule…]}]
     :facts {qname #{tuple}}        ; ground defrule facts
     :computed … :index-requirements {qname #{mask}}}
  Plans, delta variants and expression closures are built once here.

  (evaluate ctx prepared) / (evaluate ctx prepared edb) returns
  {qname #{tuple…}} for every stored relation; edb is {qname coll-of-tuples}
  (or already under (:edb prepared)). evaluate-naive takes the same arguments
  and re-runs every rule of a stratum until nothing changes; it exists to test
  the semi-naive evaluator."
  (:require [lang.compile.code :as cc]
            [lang.errors :as err :refer [error!]]
            [lang.order :as order]
            [lang.plan :as plan]
            [lang.runtime :as rt]
            [lang.stratify :as strat]
            [lang.values :as v])
  (:import (clojure.lang IPersistentVector)
           (java.util ArrayList HashMap HashSet LinkedHashMap LinkedHashSet)))

(set! *warn-on-reflection* true)

;; ---------------------------------------------------------------- storage

(deftype Idx [positions ^HashMap m])
(deftype Rel [^HashSet tuples ^ArrayList order ^HashMap indexes])
(defrecord Db [^HashMap rels delta ^longs total])

(defn- new-rel ^Rel [] (Rel. (HashSet.) (ArrayList.) (HashMap.)))

(defn- rel-of ^Rel [^Db db q]
  (let [^HashMap rels (.-rels db)]
    (or (.get rels q)
        (let [r (new-rel)] (.put rels q r) r))))

(defn- positions [mask] (vec (keep-indexed (fn [i m] (when m i)) mask)))

(defn- key-of [ps ^IPersistentVector t] (mapv #(.nth t (int %)) ps))

(defn- idx-add! [^Idx ix t]
  (let [k (key-of (.-positions ix) t)
        ^HashMap m (.-m ix)
        ^ArrayList l (or (.get m k) (let [l (ArrayList.)] (.put m k l) l))]
    (.add l t)))

(defn- add-tuple! [^Rel r t]
  (.add ^HashSet (.-tuples r) t)
  (.add ^ArrayList (.-order r) t)
  (doseq [^Idx ix (vals (.-indexes r))] (idx-add! ix t)))

(defn- index-for ^Idx [^Rel r mask]
  (let [^HashMap ixs (.-indexes r)]
    (or (.get ixs mask)
        (let [ix (Idx. (positions mask) (HashMap.))]
          (doseq [t (.-order r)] (idx-add! ix t))
          (.put ixs mask ix)
          ix))))

(defn- note-insert!
  "Counts one new stored tuple of q against :max-tuples (total and per relation)."
  [ctx ^Db db q rel-count]
  (let [mx (long (rt/limit ctx :max-tuples))
        ^longs tot (.-total db)
        n (inc (aget tot 0))]
    (when (or (> n mx) (> (inc (long rel-count)) mx))
      (error! :tuple-limit :run "Tuple limit exceeded" {:rel q}))
    (aset tot 0 n)))

(defn- derive!
  "Charges, checks and stages a derived tuple (not yet visible to readers)."
  [ctx ^Db db ^LinkedHashMap stage q tuple]
  (rt/check-deep-total! ctx tuple)
  (when-not (v/storable? tuple)
    (error! :unstorable-value :run "A function cannot be stored in a relation" {:rel q}))
  (let [^Rel rel (rel-of db q)]
    (when-not (.contains ^HashSet (.-tuples rel) tuple)
      (let [^LinkedHashSet s (or (.get stage q)
                                 (let [s (LinkedHashSet.)] (.put stage q s) s))]
        (when-not (.contains s tuple)
          (note-insert! ctx db q (+ (.size ^ArrayList (.-order rel)) (.size s)))
          (.add s tuple))))))

(defn- commit!
  "Moves staged tuples into the store; they become the new delta."
  [^Db db ^LinkedHashMap stage]
  (let [delta (reduce (fn [m [q ^LinkedHashSet s]]
                        (let [rel (rel-of db q)
                              l (ArrayList. s)]
                          (doseq [t l] (add-tuple! rel t))
                          (assoc m q l)))
                      {} (seq stage))]
    (.clear stage)
    (vreset! (:delta db) delta)
    (boolean (seq delta))))

(defn- insert-direct! [ctx ^Db db q t]
  (rt/check-deep-total! ctx t)
  (when-not (v/storable? t)
    (error! :unstorable-value :run "A function cannot be stored in a relation" {:rel q}))
  (let [^Rel rel (rel-of db q)]
    (when-not (.contains ^HashSet (.-tuples rel) t)
      (note-insert! ctx db q (.size ^ArrayList (.-order rel)))
      (add-tuple! rel t))))

;; ---------------------------------------------------------------- expressions

(defn- var-env-fn [var-locals vars]
  (let [pairs (vec (for [vi vars :let [l (get var-locals vi)] :when l] [l vi]))]
    (fn [b] (reduce (fn [m [l vi]] (assoc m l (nth b vi))) {} pairs))))

(defn- expr-fn
  "(fn [ctx b]) evaluating a code node whose locals come from bindings."
  [rule fn-table node vars]
  (let [compiled (cc/compile-node node fn-table)
        env (var-env-fn (:var-locals rule) vars)]
    (fn [ctx b] (rt/check-deep-total! ctx (cc/eval-code ctx compiled (env b))))))

(defn- term-fn [rule fn-table t]
  (cond
    (contains? t :const) (let [c (:const t)] (fn [_ _] c))
    (contains? t :var) (let [vi (:var t)] (fn [_ b] (nth b vi)))
    :else (expr-fn rule fn-table (:expr t) (:vars t))))

;; ---------------------------------------------------------------- matching

(defn- arg-ops
  "Compiles argument matching against positions: [[kind pos x]…] and the bound
  set afterwards. Kinds: :const, :check (bound var), :bind. In negation (neg?)
  wildcards are :skip."
  [rule bound args neg?]
  (reduce (fn [[ops bound] [pos t]]
            (cond
              (contains? t :const) [(conj ops [:const pos (:const t)]) bound]
              (and neg? ((:wild rule) (:var t))) [(conj ops [:skip pos nil]) bound]
              (bound (:var t)) [(conj ops [:check pos (:var t)]) bound]
              :else [(conj ops [:bind pos (:var t)]) (conj bound (:var t))]))
          [[] bound]
          (map-indexed vector args)))

(defn- match-ops [ops b ^IPersistentVector t]
  (loop [ops (seq ops) b b]
    (if ops
      (let [[kind pos x] (first ops)
            tv (.nth t (int pos))]
        (case kind
          :const (when (= x tv) (recur (next ops) b))
          :check (when (= (nth b x) tv) (recur (next ops) b))
          :bind (recur (next ops) (assoc b x tv))
          :skip (recur (next ops) b)))
      b)))

(defn- out-ops
  "Like arg-ops for computed outputs, where an :expr term filters by equality."
  [rule fn-table bound out-terms neg?]
  (reduce (fn [[ops bound] [k [_ t]]]
            (cond
              (contains? t :expr) [(conj ops [:expr k (expr-fn rule fn-table (:expr t) (:vars t))]) bound]
              (contains? t :const) [(conj ops [:const k (:const t)]) bound]
              (and neg? ((:wild rule) (:var t))) [(conj ops [:skip k nil]) bound]
              (bound (:var t)) [(conj ops [:check k (:var t)]) bound]
              :else [(conj ops [:bind k (:var t)]) (conj bound (:var t))]))
          [[] bound]
          (map-indexed vector out-terms)))

(defn- match-out [ctx ops b ^IPersistentVector t]
  (loop [ops (seq ops) b b]
    (if ops
      (let [[kind k x] (first ops)
            tv (.nth t (int k))]
        (case kind
          :const (when (= x tv) (recur (next ops) b))
          :check (when (= (nth b x) tv) (recur (next ops) b))
          :expr (when (= (x ctx b) tv) (recur (next ops) b))
          :bind (recur (next ops) (assoc b x tv))
          :skip (recur (next ops) b)))
      b)))

;; ---------------------------------------------------------------- steps
;; A compiled step is (fn [ctx db b sink]); it calls its successor per solution.

(defn- key-fn [t]
  (if (contains? t :const)
    (let [c (:const t)] (fn [_] c))
    (let [vi (:var t)] (fn [b] (nth b vi)))))

(defn- compile-stored [rule {:keys [rel mask args delta? bound-before]} nxt]
  (let [[ops _] (arg-ops rule bound-before args false)
        n (count args)
        key-fns (vec (for [[i m] (map-indexed vector mask) :when m] (key-fn (nth args i))))
        keyed? (boolean (seq key-fns))
        mask (vec mask)]
    (fn [ctx ^Db db b sink]
      (let [^ArrayList cands (cond
                               delta? (get @(:delta db) rel)
                               keyed? (let [ix (index-for (rel-of db rel) mask)
                                            k (mapv #(% b) key-fns)]
                                        (.get ^HashMap (.-m ix) k))
                               :else (.-order (rel-of db rel)))]
        (when cands
          (let [sz (.size cands)]
            (loop [i 0]
              (when (< i sz)
                (let [^IPersistentVector t (.get cands i)]
                  (rt/charge-total! ctx 1)
                  (when (== (count t) n)
                    (when-let [b' (match-ops ops b t)]
                      (nxt ctx db b' sink))))
                (recur (inc i))))))))))

(defn- compile-not-stored [rule {:keys [rel mask args bound-before]} nxt]
  (let [[ops _] (arg-ops rule bound-before args true)
        n (count args)
        mask (vec mask)
        key-fns (vec (for [[i m] (map-indexed vector mask) :when m] (key-fn (nth args i))))
        keyed? (boolean (seq key-fns))
        full? (every? #(not= :skip (first %)) ops)
        build (when full?
                (let [fs (mapv (fn [t] (if (contains? t :const)
                                         (let [c (:const t)] (fn [_] c))
                                         (key-fn t)))
                               args)]
                  (fn [b] (mapv #(% b) fs))))]
    (fn [ctx ^Db db b sink]
      (let [^Rel r (rel-of db rel)
            exists? (if full?
                      (.contains ^HashSet (.-tuples r) (build b))
                      (let [^ArrayList cands (if keyed?
                                               (.get ^HashMap (.-m (index-for r mask)) (mapv #(% b) key-fns))
                                               (.-order r))]
                        (and cands
                             (let [sz (.size cands)]
                               (loop [i 0]
                                 (when (< i sz)
                                   (rt/charge-total! ctx 1)
                                   (let [t (.get cands i)]
                                     (if (and (== (count t) n) (match-ops ops b t))
                                       true
                                       (recur (inc i))))))))))]
        (rt/charge-total! ctx 1)
        (when-not exists?
          (nxt ctx db b sink))))))

;; ------------------------------------------------ :on-code-error :skip
;; Program-bug errors raised by user code are caught at the computed-literal
;; call and at when/bind expressions: the step yields no solutions, a diag is
;; recorded and the rule's head relation is tainted (see run-eval).

(def skippable-kinds
  #{:type-error :arity-error :bad-relation-result :arithmetic-error :collect-map-conflict})

(defn- guarded
  "Runs thunk; under :on-code-error :skip a program-bug error is recorded
  against the head relation rel and `fallback` is returned instead."
  [ctx rel fallback thunk]
  (if (= :skip (:on-code-error ctx))
    (try (thunk)
         (catch StackOverflowError e (throw e))
         (catch Throwable e
           (let [le (err/map-throwable e :run)
                 kind (:lang/error (ex-data le))]
             (if (skippable-kinds kind)
               (do (rt/diag! ctx kind {:rel rel :message (:message (ex-data le))})
                   (vswap! (:taint ctx) conj rel)
                   fallback)
               (throw e)))))
    (thunk)))

(defn- call-computed
  "Out tuples (a seqable of vectors) of one mode call, memoized per run."
  [ctx rel mode-idx impl n-out memo? in-vals]
  (let [run (fn []
              (let [r (rt/with-call-budget ctx #(impl ctx in-vals))]
                (if (zero? n-out)
                  (if r [[]] [])
                  (or r []))))]
    (if memo?
      (let [k [rel mode-idx (rt/check-deep! ctx in-vals)]
            hit (rt/memo-get ctx k)]
        (if (identical? hit :lang.runtime/miss)
          (rt/memo-put! ctx k (vec (run)))
          hit))
      (run))))

(defn- compile-computed [rule fn-table computed {:keys [rel mode in-terms out-terms bound-before lit]} nxt]
  (let [head-rel (:rel rule)
        neg? (= :not lit)
        entry (or (get computed rel)
                  (error! :internal-error :run "Missing computed relation" {:rel rel}))
        {:keys [impl out]} (nth (:modes entry) mode)
        n-out (count out)
        memo? (and (not= "lang.core" (namespace rel)) (not (false? (:memo? entry))))
        in-fns (mapv #(term-fn rule fn-table (second %)) in-terms)
        [ops _] (out-ops rule fn-table bound-before out-terms neg?)]
    (fn [ctx db b sink]
      (let [tuples (guarded ctx head-rel ::skipped
                            #(call-computed ctx rel mode impl n-out memo?
                                            (mapv (fn [f] (f ctx b)) in-fns)))]
        (when (and neg? (identical? tuples ::skipped))
          (error! :tainted-negation :run "A skipped call is the target of a negation" {:rel rel}))
        (if (identical? tuples ::skipped)
          nil
         (if neg?
          (do (rt/charge-total! ctx 1)
              (run! #(rt/check-deep-total! ctx %) tuples)
              (when-not (some (fn [t] (match-out ctx ops b t)) tuples)
                (nxt ctx db b sink)))
          (run! (fn [t]
                  (rt/charge-total! ctx 1)
                  (rt/check-deep-total! ctx t)
                  (when-let [b' (match-out ctx ops b t)]
                    (nxt ctx db b' sink)))
                tuples)))))))

(defn- compile-when [rule fn-table {:keys [expr vars]} nxt]
  (let [f (expr-fn rule fn-table expr vars)]
    (fn [ctx db b sink]
      (rt/charge-total! ctx 1)
      (when (guarded ctx (:rel rule) false #(f ctx b)) (nxt ctx db b sink)))))

;; Pattern matchers are (fn [b val]) -> b' or nil.
(defn- compile-pat [bound pat nil-ok?]
  (let [ok? (fn [val] (or nil-ok? (some? val)))]
    (cond
      (contains? pat :pvar)
      (let [vi (:pvar pat)]
        (if (bound vi)
          [(fn [b val] (when (and (ok? val) (= (nth b vi) val)) b)) bound]
          [(fn [b val] (when (ok? val) (assoc b vi val))) (conj bound vi)]))

      (contains? pat :pconst)
      (let [c (:pconst pat)] [(fn [b val] (when (and (ok? val) (= c val)) b)) bound])

      (contains? pat :pvec)
      (let [[ms bound] (reduce (fn [[ms bound] p]
                                 (let [[m bound] (compile-pat bound p nil-ok?)] [(conj ms m) bound]))
                               [[] bound] (:pvec pat))
            [rm bound] (if (:rest pat)
                         (let [[m bound] (compile-pat bound (:rest pat) nil-ok?)] [m bound])
                         [nil bound])
            n (count ms)]
        [(fn [b val]
           (when (ok? val)
             (let [s (cond (vector? val) val
                           (sequential? val) (vec val)
                           (nil? val) []
                           :else ::no)]
               (when-not (identical? s ::no)
                 (let [b' (loop [i 0 b b]
                            (if (< i n)
                              (when-let [b (and b ((nth ms i) b (nth s i nil)))] (recur (inc i) b))
                              b))]
                   (if (and b' rm) (rm b' (vec (drop n s))) b'))))))
         bound])

      :else
      (let [[ms bound] (reduce (fn [[ms bound] [k p]]
                                 (let [[m bound] (compile-pat bound p nil-ok?)] [(conj ms [k m]) bound]))
                               [[] bound] (:pmap pat))]
        [(fn [b val]
           (when (ok? val)
             (let [m (cond (map? val) val (nil? val) {} :else ::no)]
               (when-not (identical? m ::no)
                 (reduce (fn [b [k mt]] (if-let [b (mt b (get m k))] b (reduced nil))) b ms)))))
         bound]))))

(defn- compile-bind [rule fn-table {:keys [pat expr vars nil-ok? bound-before]} nxt]
  (let [f (expr-fn rule fn-table expr vars)
        [m _] (compile-pat bound-before pat nil-ok?)]
    (fn [ctx db b sink]
      (rt/charge-total! ctx 1)
      (let [val (guarded ctx (:rel rule) ::skipped #(f ctx b))]
        (when-not (identical? val ::skipped)
          (when-let [b' (m b val)]
            (nxt ctx db b' sink)))))))

(defn- compile-step [rule fn-table computed step nxt]
  (case (:lit step)
    :when (compile-when rule fn-table step nxt)
    :bind (compile-bind rule fn-table step nxt)
    (if (contains? step :mode)
      (compile-computed rule fn-table computed step nxt)
      (if (= :not (:lit step))
        (compile-not-stored rule step nxt)
        (compile-stored rule step nxt)))))

(defn- compile-plan
  "(fn [ctx db sink]) running a plan's steps; sink receives full bindings."
  [rule fn-table computed {:keys [steps]}]
  (let [chain (reduce (fn [nxt step] (compile-step rule fn-table computed step nxt))
                      (fn [_ _ b sink] (sink b))
                      (reverse steps))
        init (vec (repeat (:nvars rule) nil))]
    (fn [ctx db sink] (chain ctx db init sink))))

;; ---------------------------------------------------------------- aggregates

(defn- type-error! [x msg] (error! :type-error :run msg {:value x}))

(defn- aggregate [ctx kind vals]
  (case kind
    count (count vals)
    count-distinct (count (set vals))
    sum (let [vs (order/sort-values ctx vals)]
          (doseq [x vs] (when-not (or (number? x) (v/nan? x)) (type-error! x "sum expects numbers")))
          (if (some v/nan? vs)
            v/nan
            (reduce (fn [acc x] (rt/check-int! ctx (v/canon-num (+' acc x)))) vs)))
    min (reduce (fn [a x] (if (neg? (order/compare-values ctx x a)) x a)) vals)
    max (reduce (fn [a x] (if (pos? (order/compare-values ctx x a)) x a)) vals)
    collect (let [r (set vals)] (rt/check-size! ctx (count r)) r)))

(defn- aggregate2 [ctx kind pairs]
  (case kind
    collect-by (do (rt/check-size! ctx (count pairs))
                   (mapv second (order/sort-values ctx pairs)))
    collect-map (let [r (reduce (fn [m [k x]]
                                  (if (and (contains? m k) (not= (get m k) x))
                                    (error! :collect-map-conflict :run "collect-map: duplicate key with different values"
                                            {:key k})
                                    (assoc m k x)))
                                {} pairs)]
                  (rt/check-size! ctx (count r))
                  r)))

(defn- compile-head [{:keys [head]}]
  (let [ts (mapv (fn [t] (if (contains? t :const) [:const (:const t)] [:var (:var t)])) head)]
    (fn [b] (mapv (fn [[k x]] (if (identical? k :const) x (nth b x))) ts))))

(defn- compile-agg-head
  "(fn [ctx assignments]) -> head tuples, one per group."
  [{:keys [head aggs]}]
  (let [cols (mapv (fn [t]
                     (cond (contains? t :agg) [:agg (nth aggs (:agg t))]
                           (contains? t :const) [:const (:const t)]
                           :else [:var (:var t)]))
                   head)
        key-cols (vec (remove #(= :agg (first %)) cols))
        keyf (fn [b] (mapv (fn [[k x]] (if (identical? k :const) x (nth b x))) key-cols))]
    (fn [ctx assignments]
      (let [^LinkedHashMap groups (LinkedHashMap.)]
        (doseq [b assignments]
          (let [k (keyf b)
                ^ArrayList l (or (.get groups k) (let [l (ArrayList.)] (.put groups k l) l))]
            (.add l b)))
        (vec (for [[k bs] (seq groups)]
               (let [kvals (volatile! (seq k))]
                 (mapv (fn [[kind x]]
                         (case kind
                           :agg (let [{:keys [agg args]} x
                                      col (fn [i] (mapv #(nth % i) bs))]
                                  (case agg
                                    (collect-by collect-map)
                                    (aggregate2 ctx agg (mapv (fn [b] [(nth b (first args)) (nth b (second args))]) bs))
                                    (aggregate ctx agg (col (first args)))))
                           (let [x (first @kvals)] (vswap! kvals next) x)))
                       cols))))))))

;; ---------------------------------------------------------------- prepare

(defn- fact? [{:keys [body aggs head]}]
  (and (empty? body) (empty? aggs) (every? #(contains? % :const) head)))

(defn- compile-rule [fn-table computed recursive-rels {:keys [rel aggs] :as rule}]
  (let [full (plan/plan-body rule computed {})
        variants (if (seq recursive-rels) (plan/delta-variants rule recursive-rels) [])]
    (cond-> {:rel rel
             :plan full
             :run (compile-plan rule fn-table computed full)
             :variants (mapv (fn [p]
                               {:delta-rel (:rel (nth (:body rule) (:delta-lit p)))
                                :run (compile-plan rule fn-table computed p)})
                             variants)
             :plans (into [full] variants)}
      (seq aggs) (assoc :agg (compile-agg-head rule))
      (empty? aggs) (assoc :head (compile-head rule)))))

;; Dependency edges [head body-rel negative?] over stored body literals, used
;; to propagate taint (a relation depends on everything its rules read).
(defn- rule-edges [{:keys [rel body aggs]}]
  (for [{:keys [lit] r :rel :as l} body
        :when (and (#{:rel :not} lit) (not (:modes l)))]
    [rel r (boolean (or (= :not lit) (seq aggs)))]))

(defn- taint-closure [edges tainted]
  (let [users (reduce (fn [m [h b _]] (update m b (fnil conj #{}) h)) {} edges)]
    (loop [seen (set tainted) todo (vec tainted)]
      (if-let [q (peek todo)]
        (let [new (remove seen (get users q))]
          (recur (into seen new) (into (pop todo) new)))
        seen))))

(defn prepare
  "Plans and compiles rules (see ns docstring)."
  [{:keys [rules computed fn-table stored?]}]
  (let [facts (reduce (fn [m r] (update m (:rel r) (fnil conj #{}) (mapv :const (:head r))))
                      {} (filter fact? rules))
        others (remove fact? rules)
        strata (strat/stratify others (into (set stored?) (map :rel) rules))
        compiled (mapv (fn [{:keys [rels rules recursive?]}]
                         {:rels rels
                          :recursive? recursive?
                          :neg-targets (into #{} (comp (mapcat rule-edges)
                                                       (filter #(nth % 2))
                                                       (map second))
                                             rules)
                          :rules (mapv #(compile-rule fn-table computed (when recursive? rels) %) rules)})
                       strata)]
    {:strata compiled
     :facts facts
     :computed computed
     :edges (vec (mapcat rule-edges others))
     :index-requirements (plan/index-requirements
                          (for [s compiled, r (:rules s), p (:plans r)] p))}))

;; ---------------------------------------------------------------- evaluation

(defn- exec-rule! [ctx db stage {:keys [rel run head agg]}]
  (rt/trace! ctx {:event :rule-fired :rel rel})
  (if agg
    (let [seen (LinkedHashSet.)]
      (run ctx db (fn [b]
                    (rt/charge-total! ctx 1)
                    (when (.add seen b)
                      (when (> (.size seen) (long (rt/limit ctx :max-tuples)))
                        (error! :tuple-limit :run "Tuple limit exceeded" {:rel rel})))))
      (doseq [t (rt/with-call-budget ctx #(agg ctx (vec seen)))]
        (derive! ctx db stage rel t)))
    (run ctx db (fn [b] (derive! ctx db stage rel (head b))))))

(defn- grown-rel [^Db db]
  (->> @(:delta db)
       (sort-by (fn [[q ^ArrayList l]] [(- (.size l)) (str q)]))
       ffirst))

(defn- eval-stratum!
  "Evaluates one stratum; returns its iteration count."
  [ctx ^Db db {:keys [rules recursive?]} naive?]
  (let [stage (LinkedHashMap.)
        max-it (long (rt/limit ctx :max-iterations))
        run-full! (fn [] (doseq [r rules] (exec-rule! ctx db stage r)))
        run-deltas! (fn []
                      (let [delta @(:delta db)]
                        (doseq [r rules, {:keys [delta-rel run]} (:variants r)
                                :when (seq (get delta delta-rel))]
                          (run ctx db (fn [b] (derive! ctx db stage (:rel r) ((:head r) b)))))))]
    (run-full!)
    (commit! db stage)
    (if-not recursive?
      1
      (loop [iter 1]
        (if (empty? @(:delta db))
          iter
          (do (when (>= iter max-it)
                (error! :iteration-limit :run "Iteration limit exceeded" {:rel (grown-rel db)}))
              (if naive? (run-full!) (run-deltas!))
              (commit! db stage)
              (recur (inc iter))))))))

(defn- check-tainted-negation! [ctx edges {:keys [neg-targets]}]
  (let [tainted @(:taint ctx)]
    (when (and (seq tainted) (seq neg-targets))
      (when-let [q (first (sort-by str (filter (taint-closure edges tainted) neg-targets)))]
        (error! :tainted-negation :run
                "A relation affected by a skipped error is the target of a negation or aggregate"
                {:rel q})))))

(defn- run-eval [ctx {:keys [strata facts index-requirements edges] :as prepared} edb naive?]
  (let [^Db db (->Db (HashMap.) (volatile! {}) (long-array 1))]
    (doseq [[q ts] (merge-with into {} (:edb prepared) edb facts)
            t ts]
      (insert-direct! ctx db q (v/canon (vec t))))
    (doseq [[q masks] index-requirements, m masks]
      (index-for (rel-of db q) m))
    (let [iters (reduce (fn [acc s]
                          (doseq [q (:rels s)] (rel-of db q))
                          (let [n (eval-stratum! ctx db s naive?)]
                            (check-tainted-negation! ctx edges s)
                            (into acc (map (fn [q] [q n])) (:rels s))))
                        {} strata)
          rels (into {} (map (fn [[q ^Rel r]] [q (set (.-order r))])) (.-rels db))]
      (vswap! (:taint ctx) #(taint-closure edges %))
      (rt/diag! ctx :stats {:tuples (into {} (map (fn [[q s]] [q (count s)])) rels)
                            :iterations iters})
      rels)))

(defn evaluate
  "Semi-naive evaluation of a prepared program; see the ns docstring."
  ([ctx prepared] (run-eval ctx prepared nil false))
  ([ctx prepared edb] (run-eval ctx prepared edb false)))

(defn evaluate-naive
  "Reference evaluator: re-runs every rule until nothing changes."
  ([ctx prepared] (run-eval ctx prepared nil true))
  ([ctx prepared edb] (run-eval ctx prepared edb true)))
