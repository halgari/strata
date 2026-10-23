(ns lang.plan
  "Deterministic rule-body planning, delta variants and index requirements
  (spec 6.2). Plans are fixed at load time."
  (:require [lang.errors :refer [error! safe-str]]))

(defn- pat-vars [p]
  (cond
    (contains? p :pvar) #{(:pvar p)}
    (contains? p :pvec) (into (if (:rest p) (pat-vars (:rest p)) #{}) (mapcat pat-vars) (:pvec p))
    (contains? p :pmap) (into #{} (mapcat (comp pat-vars second)) (:pmap p))
    :else #{}))

(defn- term-vars [t]
  (cond (contains? t :var) #{(:var t)}
        (contains? t :expr) (:vars t)
        :else #{}))

(defn- term-bound? [bound t]
  (every? bound (term-vars t)))

(defn- computed-lit? [lit]
  (contains? lit :modes))

(defn- modes-of [computed lit]
  (or (:modes (get computed (:rel lit))) (:modes lit)))

(defn- mask-of [bound lit]
  (mapv #(boolean (or (contains? % :const) (and (contains? % :var) (bound (:var %)))))
        (:args lit)))

(defn- choose-mode
  "Best applicable mode [index mode] (most inputs, then first declared), or nil."
  [bound lit modes]
  (let [args (:args lit)
        ok? (fn [m] (every? #(term-bound? bound (nth args %)) (:in m)))]
    (->> (map-indexed vector modes)
         (filter (comp ok? second))
         (reduce (fn [best c] (if (> (count (:in (second c))) (count (:in (second best)))) c best))
                 nil))))

(defn- closest-mode-missing
  "Variables the least-missing mode still needs."
  [bound lit modes]
  (let [args (:args lit)]
    (or (->> modes
             (map (fn [m] (into #{} (comp (mapcat #(term-vars (nth args %))) (remove bound)) (:in m))))
             (reduce (fn [a b] (if (and a (>= (count b) (count a))) a b)) nil))
        #{})))

(defn- unbound-args [bound lit wild]
  (into #{} (comp (mapcat term-vars) (remove wild) (remove bound)) (:args lit)))

(defn- assess
  "{:pref n :score s :extra {...}} when lit is ready under bound, else
  {:missing #{idx}}."
  [rule computed bound lit]
  (let [wild (:wild rule)]
    (case (:lit lit)
      :when (let [m (into #{} (remove bound) (:vars lit))]
              (if (empty? m) {:pref 1 :score 0} {:missing m}))
      :bind (let [m (into #{} (remove bound) (:vars lit))]
              (if (seq m)
                {:missing m}
                {:pref (if (every? #(or (wild %) (bound %)) (pat-vars (:pat lit))) 1 2) :score 0}))
      :not (if (computed-lit? lit)
             (let [modes (modes-of computed lit)
                   m (unbound-args bound lit wild)
                   [mi mode :as best] (when (empty? m) (choose-mode bound lit modes))]
               (cond
                 (seq m) {:missing m}
                 (nil? best) {:missing (closest-mode-missing bound lit modes)}
                 :else {:pref 1 :score 0 :mode-index mi :mode mode}))
             (let [m (unbound-args bound lit wild)]
               (if (empty? m) {:pref 1 :score 0} {:missing m})))
      :rel (if (computed-lit? lit)
             (let [modes (modes-of computed lit)
                   [mi mode :as best] (choose-mode bound lit modes)]
               (if best
                 {:pref 4 :score 0 :mode-index mi :mode mode}
                 {:missing (closest-mode-missing bound lit modes)}))
             {:pref 3 :score (count (filter true? (mask-of bound lit)))}))))

(defn- bound-after [bound lit a]
  (case (:lit lit)
    :bind (into bound (remove (:wild a)) (pat-vars (:pat lit)))
    :rel (into bound (comp (mapcat term-vars) (remove (:wild a))) (:args lit))
    bound))

(defn- build-step [bound lit idx {:keys [mode-index mode]}]
  (let [args (:args lit)]
    (cond-> (assoc lit :idx idx :bound-before bound)
      mode (assoc :mode mode-index
                  :in-terms (mapv #(vector % (nth args %)) (:in mode))
                  :out-terms (mapv #(vector % (nth args %)) (:out mode)))
      (and (#{:rel :not} (:lit lit)) (not (computed-lit? lit)))
      (assoc :mask (mask-of bound lit)))))

(defn- body-forms
  "Source forms of the rule body, aligned with (:body rule)."
  [rule]
  (let [more (drop 2 (:form rule))
        more (if (map? (first more)) (rest more) more)]
    (vec (rest more))))

(defn- unplannable! [rule computed bound i]
  (let [lit (nth (:body rule) i)
        {:keys [missing]} (assess rule computed bound lit)
        names (into {} (map (fn [[s j]] [j s])) (:var-names rule))
        src (get (body-forms rule) i lit)]
    (error! :unplannable :plan
            (str "Cannot place literal " (safe-str src) " in " (:rel rule)
                 "; unbound variables: " (pr-str (sort (map names missing))))
            {:ns (:ns rule) :line (:line (:loc rule)) :column (:column (:loc rule))
             :form (:form rule)
             :literal (safe-str src)
             :missing (into #{} (map names) missing)})))

(defn plan-body
  "Plans a rule body: {:steps [step…]}. Options: {:pinned lit-idx}."
  [rule computed {:keys [pinned]}]
  (let [body (:body rule)]
    (loop [remaining (vec (if pinned
                            (cons pinned (remove #{pinned} (range (count body))))
                            (range (count body))))
           pinned? (some? pinned)
           bound #{}
           steps []]
      (if (empty? remaining)
        {:steps steps}
        (let [pick (if (or pinned? (:ordered? rule))
                     (let [i (first remaining) a (assess rule computed bound (nth body i))]
                       (when (:pref a) [i a]))
                     (let [k (fn [[_ a]] [(:pref a) (- (:score a))])]
                       (->> (sort remaining)
                            (keep (fn [i] (let [a (assess rule computed bound (nth body i))]
                                            (when (:pref a) [i a]))))
                            (reduce (fn [best c] (if (or (nil? best) (neg? (compare (k c) (k best)))) c best))
                                    nil))))]
          (if-not pick
            (unplannable! rule computed bound (if (or pinned? (:ordered? rule))
                                                (first remaining)
                                                (apply min remaining)))
            (let [[i a] pick
                  lit (nth body i)]
              (recur (vec (remove #{i} remaining))
                     false
                     (bound-after bound lit rule)
                     (conj steps (build-step bound lit i a))))))))))

(defn delta-variants
  "One plan per positive body literal over a recursive relation, with that
  literal pinned first and marked :delta? true."
  [rule recursive-rels]
  (vec (for [[i lit] (map-indexed vector (:body rule))
             :when (and (= :rel (:lit lit)) (contains? recursive-rels (:rel lit)))]
         (-> (plan-body rule {} {:pinned i})
             (assoc-in [:steps 0 :delta?] true)
             (assoc :delta-lit i)))))

(defn index-requirements
  "{qname #{mask…}} for the stored-relation steps of the plans. All-false
  masks are plain scans and need no index."
  [plans]
  (reduce (fn [acc {:keys [rel mask]}]
            (if (some true? mask) (update acc rel (fnil conj #{}) mask) acc))
          {}
          (for [p plans, s (:steps p), :when (:mask s)] s)))
