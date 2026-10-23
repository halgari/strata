(ns lang.stratify
  "Relation dependency graph, Tarjan SCC strata and negative-cycle detection
  (spec 6.3). Computed relations are not nodes."
  (:require [lang.errors :refer [error!]]))

(defn- by-name [xs] (sort-by str xs))

(defn- rule-edges
  "[[head body-rel negative?] …] for the stored body literals of a rule."
  [nodes {:keys [rel body aggs]}]
  (for [{:keys [lit] r :rel :as l} body
        :when (and (#{:rel :not} lit) (not (:modes l)) (nodes r))]
    [rel r (boolean (or (= :not lit) (seq aggs)))]))

(defn- tarjan
  "SCCs of the graph (node -> sorted successors), dependencies first.
  Iterative: an explicit stack of [node remaining-successors] frames."
  [nodes succ]
  (let [idx (volatile! {}) low (volatile! {}) on (volatile! #{})
        stack (volatile! []) n (volatile! 0) out (volatile! [])
        enter (fn [v]
                (vswap! idx assoc v @n) (vswap! low assoc v @n) (vswap! n inc)
                (vswap! stack conj v) (vswap! on conj v)
                [v (seq (succ v))])
        finish (fn [v]
                 (when (= (@low v) (@idx v))
                   (loop [scc #{}]
                     (let [w (peek @stack)]
                       (vswap! stack pop) (vswap! on disj w)
                       (if (= w v)
                         (vswap! out conj (conj scc w))
                         (recur (conj scc w)))))))]
    (doseq [root nodes :when (not (contains? @idx root))]
      (loop [frames [(enter root)]]
        (when-let [[v ws] (peek frames)]
          (if-let [[w & more] ws]
            (let [frames (conj (pop frames) [v more])]
              (cond
                (not (contains? @idx w)) (recur (conj frames (enter w)))
                (@on w) (do (vswap! low assoc v (min (@low v) (@idx w)))
                            (recur frames))
                :else (recur frames)))
            (do (finish v)
                (let [frames (pop frames)]
                  (when-let [[u _] (peek frames)]
                    (vswap! low assoc u (min (@low u) (@low v))))
                  (recur frames)))))))
    @out))

(defn- topo-order
  "Orders SCCs so dependencies come first; ties go to the smallest name."
  [sccs scc-of edges]
  (let [keys* (mapv #(str (first (by-name %))) sccs)
        deps (reduce (fn [m [h b _]]
                       (let [ch (scc-of h) cb (scc-of b)]
                         (cond-> m (not= ch cb) (update ch (fnil conj #{}) cb))))
                     {} edges)
        users (reduce-kv (fn [m c ds] (reduce #(update %1 %2 (fnil conj []) c) m ds))
                         {} deps)
        ready (fn [i] [(keys* i) i])]
    (loop [q (into (sorted-set) (comp (remove deps) (map ready)) (range (count sccs)))
           pending (into {} (map (fn [[c ds]] [c (count ds)])) deps)
           order []]
      (if-let [[_ i :as top] (first q)]
        (let [[pending newly] (reduce (fn [[p nw] u]
                                        (let [k (dec (p u))]
                                          [(assoc p u k) (cond-> nw (zero? k) (conj u))]))
                                      [pending []] (users i))]
          (recur (into (disj q top) (map ready) newly) pending (conj order (sccs i))))
        order))))

(defn stratify
  "Strata in evaluation order: [{:rels #{q} :rules [rule…] :recursive? b}].
  stored? is the set of stored relation qnames (rules, facts, externs)."
  [rules stored?]
  (let [nodes (into (set stored?) (map :rel) rules)
        edges (vec (mapcat #(rule-edges nodes %) rules))
        succ-map (reduce (fn [m [h b _]] (update m h (fnil conj #{}) b)) {} edges)
        succ (fn [v] (by-name (get succ-map v)))
        sccs (tarjan (by-name nodes) succ)
        scc-of (into {} (for [[i s] (map-indexed vector sccs) r s] [r i]))
        internal (filter (fn [[h b _]] (= (scc-of h) (scc-of b))) edges)]
    (when-let [[h _ _] (first (filter (fn [[_ _ neg?]] neg?) internal))]
      (let [scc (sccs (scc-of h))]
        (error! :negative-cycle :stratify
                (str "Negation or aggregation through recursion among "
                     (apply str (interpose ", " (by-name scc))))
                {:cycle (vec (by-name scc))})))
    (let [rec? (into #{} (map #(scc-of (first %))) internal)
          rules-by (group-by #(scc-of (:rel %)) rules)
          order (topo-order sccs scc-of edges)]
      (vec (for [scc order :let [c (scc-of (first scc))]]
             {:rels scc
              :rules (vec (get rules-by c))
              :recursive? (or (> (count scc) 1) (contains? rec? c))})))))
