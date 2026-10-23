(ns lang.stratify
  "Relation dependency graph, Tarjan SCC strata and negative-cycle detection
  (spec 6.3). Computed relations are not nodes."
  (:require [lang.errors :refer [error!]]))

(defn- by-name [xs] (sort-by str xs))

(defn- rule-edges
  "[[head body-rel negative?] …] for the stored body literals of a rule."
  [stored? {:keys [rel body aggs]}]
  (for [{:keys [lit] r :rel :as l} body
        :when (and (#{:rel :not} lit) (not (:modes l)) (stored? r))]
    [rel r (boolean (or (= :not lit) (seq aggs)))]))

(defn- tarjan
  "SCCs of the graph (node -> sorted successors), dependencies first."
  [nodes succ]
  (let [idx (volatile! {}) low (volatile! {}) on (volatile! #{})
        stack (volatile! []) n (volatile! 0) out (volatile! [])]
    (letfn [(visit [v]
              (vswap! idx assoc v @n) (vswap! low assoc v @n) (vswap! n inc)
              (vswap! stack conj v) (vswap! on conj v)
              (doseq [w (succ v)]
                (cond
                  (not (contains? @idx w))
                  (do (visit w) (vswap! low assoc v (min (@low v) (@low w))))
                  (@on w)
                  (vswap! low assoc v (min (@low v) (@idx w)))))
              (when (= (@low v) (@idx v))
                (loop [scc #{}]
                  (let [w (peek @stack)]
                    (vswap! stack pop) (vswap! on disj w)
                    (if (= w v)
                      (vswap! out conj (conj scc w))
                      (recur (conj scc w)))))))]
      (doseq [v nodes] (when-not (contains? @idx v) (visit v))))
    @out))

(defn- topo-order
  "Orders SCCs so dependencies come first; ties go to the smallest name."
  [sccs edges]
  (let [comp (into {} (for [[i s] (map-indexed vector sccs) r s] [r i]))
        deps (reduce (fn [m [h b _]]
                       (let [ch (comp h) cb (comp b)]
                         (cond-> m (not= ch cb) (update ch (fnil conj #{}) cb))))
                     {} edges)
        key-of (fn [i] (str (first (by-name (nth sccs i)))))]
    (loop [done #{} order []]
      (if (= (count order) (count sccs))
        (mapv sccs order)
        (let [ready (for [i (range (count sccs))
                          :when (and (not (done i))
                                     (every? done (get deps i)))]
                      i)
              i (first (sort-by key-of ready))]
          (recur (conj done i) (conj order i)))))))

(defn stratify
  "Strata in evaluation order: [{:rels #{q} :rules [rule…] :recursive? b}].
  stored? is the set of stored relation qnames (rules, facts, externs)."
  [rules stored?]
  (let [edges (vec (mapcat #(rule-edges stored? %) rules))
        nodes (vec (by-name (into (set stored?) (map :rel) rules)))
        succ-map (reduce (fn [m [h b _]] (update m h (fnil conj #{}) b)) {} edges)
        succ (fn [v] (by-name (get succ-map v)))
        sccs (tarjan nodes succ)]
    (doseq [scc sccs
            :let [[h b] (first (filter (fn [[h b neg?]] (and neg? (scc h) (scc b))) edges))]
            :when h]
      (error! :negative-cycle :stratify
              (str "Negation or aggregation through recursion among "
                   (apply str (interpose ", " (by-name scc))))
              {:cycle (vec (by-name scc))}))
    (vec (for [scc (topo-order sccs edges)]
           {:rels scc
            :rules (filterv #(scc (:rel %)) rules)
            :recursive? (or (> (count scc) 1)
                            (boolean (some (fn [[h b _]] (and (scc h) (scc b))) edges)))}))))
