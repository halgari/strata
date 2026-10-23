(ns strata.builtins.coll
  "Eager collection and sequence built-ins of strata.core (spec 4.5, 4.6)."
  (:require [strata.builtins.core :refer [type-error]]
            [strata.errors :refer [error!]]
            [strata.order :as order]
            [strata.runtime :as rt]
            [strata.values :refer [apply-fn]]))

(set! *warn-on-reflection* true)

;; ---------------------------------------------------------------- helpers

(defn- truthy? [x] (and (some? x) (not (false? x))))

(defn- seqable!
  "x as something seqable: nil, vector, list, set or map. Strings are not collections."
  [x]
  (if (or (nil? x) (coll? x)) x (type-error x "Expected a collection")))

(defn- elems
  "Charges 1 fuel per element of coll, up front, and returns it."
  [ctx coll]
  (seqable! coll)
  (rt/charge! ctx (count coll))
  (order/ordered ctx coll))

(defn- sized
  "Charges 1 fuel per element of a produced vector and checks its size."
  [ctx xs]
  (rt/charge! ctx (count xs))
  (rt/check-size! ctx (count xs))
  xs)

(defn- long! ^long [x]
  (if (instance? Long x) (long x) (type-error x "Expected an integer")))

(defn- vector!
  [x]
  (if (vector? x) x (type-error x "Expected a vector")))

(defn- map!
  [x]
  (if (map? x) x (type-error x "Expected a map")))

(defn- call1 [ctx f x] (apply-fn ctx f [x]))

(defn- mapv-charged
  "Applies f to each element of coll, charging 1 per element."
  [ctx f coll]
  (let [xs (elems ctx coll)]
    (loop [s (seq xs) acc (transient [])]
      (if s
        (recur (next s) (conj! acc (call1 ctx f (first s))))
        (persistent! acc)))))

(defn- ->vec [ctx coll]
  (let [xs (elems ctx coll)]
    (if (vector? xs) xs (vec xs))))

(defn- deep!
  "Meters the deep size of x before it is hashed or compared."
  [ctx x]
  (rt/check-deep! ctx x))

(defn- get* [ctx m k not-found]
  (cond
    (map? m) (get m (deep! ctx k) not-found)
    (set? m) (if (contains? m (deep! ctx k)) k not-found)
    (and (vector? m) (instance? Long k)) (get m k not-found)
    :else not-found))

(defn- assoc1 [ctx coll k v]
  (cond
    (or (nil? coll) (map? coll)) (assoc coll (deep! ctx k) v)
    (vector? coll) (if (and (instance? Long k) (<= 0 (long k) (count coll)))
                     (assoc coll k v)
                     (type-error k "Index out of bounds"))
    :else (type-error coll "Expected a map or vector")))

(defn- assoc-in* [ctx m ks v]
  (rt/charge! ctx 1)
  (if-let [[k & more] (seq ks)]
    (assoc1 ctx m k (assoc-in* ctx (get* ctx m k nil) more v))
    v))

(defn- conj1 [ctx coll x]
  (cond
    (nil? coll) [x]
    (map? coll) (cond
                  (and (vector? x) (= 2 (count x))) (assoc coll (deep! ctx (nth x 0)) (nth x 1))
                  (map? x) (merge coll (deep! ctx x))
                  (nil? x) coll
                  :else (type-error x "Expected a map entry or map"))
    (set? coll) (conj coll (deep! ctx x))
    (coll? coll) (conj coll x)
    :else (type-error coll "Expected a collection")))

(defn- args-map [ctx kvs]
  (when (odd? (count kvs)) (type-error kvs "Expected an even number of arguments"))
  (rt/charge! ctx (count kvs))
  (run! #(deep! ctx %) (take-nth 2 kvs))
  (apply hash-map kvs))

(defn- range-count
  "Number of elements in [start, end) stepping by step; saturates at Long/MAX_VALUE."
  ^long [^long start ^long end ^long step]
  (when (zero? step) (error! :arithmetic-error :run "Range step is zero" {}))
  (let [diff (.subtract (BigInteger/valueOf end) (BigInteger/valueOf start))
        s (BigInteger/valueOf step)
        ;; ceil(diff / step) when diff and step have the same sign, else 0
        n (if (= (pos? step) (pos? (.signum diff)))
            (.divide (.subtract (.add diff s) (BigInteger/valueOf (Long/signum step))) s)
            BigInteger/ZERO)]
    (if (> (.bitLength n) 62) Long/MAX_VALUE (.longValue n))))

(defn- range* [ctx & args]
  (let [[start end step] (case (count args)
                           1 [0 (first args) 1]
                           2 [(first args) (second args) 1]
                           args)
        n (range-count (long! start) (long! end) (long! step))]
    (rt/check-size! ctx n)
    (rt/charge! ctx n)
    (let [start (long start) step (long step)]
      (loop [i 0 cur start acc (transient [])]
        (if (< i n)
          (recur (inc i) (if (< (inc i) n) (+ cur step) cur) (conj! acc cur))
          (persistent! acc))))))

(defn- partition* [ctx all? n step coll]
  (let [n (long! n) step (long! step)
        _ (when (or (<= n 0) (<= step 0)) (type-error n "Expected positive sizes"))
        xs (->vec ctx coll)
        cnt (count xs)]
    (rt/check-size! ctx cnt)
    (loop [i 0 acc (transient [])]
      (if (< i cnt)
        (let [end (if (> n (- cnt i)) cnt (+ i n))]
          (if (or all? (<= n (- cnt i)))
            (let [acc (conj! acc (subvec xs i (min end cnt)))]
              (if (>= step (- cnt i)) (persistent! acc) (recur (+ i step) acc)))
            (persistent! acc)))
        (persistent! acc)))))

(defn- take-while* [ctx f coll]
  (let [xs (elems ctx coll)]
    (loop [s (seq xs) acc (transient [])]
      (if (and s (truthy? (call1 ctx f (first s))))
        (recur (next s) (conj! acc (first s)))
        (persistent! acc)))))

(defn- drop-while* [ctx f coll]
  (let [xs (elems ctx coll)]
    (loop [s (seq xs)]
      (if (and s (truthy? (call1 ctx f (first s))))
        (recur (next s))
        (vec s)))))

(defn- reduce* [ctx f args]
  (let [[init coll] (if (= 2 (count args)) args [::none (first args)])
        xs (seq (elems ctx coll))]
    (cond
      (not= init ::none) (reduce (fn [acc x] (apply-fn ctx f [acc x])) init xs)
      (nil? xs) (apply-fn ctx f [])
      :else (reduce (fn [acc x] (apply-fn ctx f [acc x])) (first xs) (next xs)))))

(defn- rest* [ctx coll]
  (let [xs (->vec ctx coll)]
    (if (seq xs) (subvec xs 1) [])))

(defn- first-of [ctx coll]
  (seqable! coll)
  (rt/charge! ctx 1)
  (if (or (map? coll) (set? coll))
    (first (order/ordered ctx coll))
    (first coll)))

(defn- nth* [ctx coll i not-found]
  (let [i (long! i)]
    (cond
      (nil? coll) not-found
      (vector? coll) (do (rt/charge! ctx 1)
                         (if (< -1 i (count coll)) (nth coll i) not-found))
      (sequential? coll) (do (rt/charge! ctx (inc (max 0 (min i (count coll)))))
                             (if (< -1 i (count coll)) (nth coll i) not-found))
      :else (type-error coll "Expected a sequential collection"))))

(defn- last-of [ctx coll]
  (seqable! coll)
  (rt/charge! ctx (if (vector? coll) 1 (count coll)))
  (let [coll (order/ordered ctx coll)]
    (if (vector? coll) (peek coll) (last coll))))

(defn- subvec* [ctx v start end]
  (vector! v)
  (let [start (long! start) end (if (some? end) (long! end) (count v))]
    (when-not (<= 0 start end (count v)) (type-error start "Index out of bounds"))
    (sized ctx (subvec v start end))))

(defn- merge* [ctx maps]
  (run! #(when-not (or (nil? %) (map? %)) (type-error % "Expected a map")) maps)
  (rt/charge! ctx (reduce + 0 (map count maps)))
  (run! #(deep! ctx %) maps)
  (when (some some? maps)
    (let [r (reduce conj {} (remove nil? maps))]
      (rt/check-size! ctx (count r))
      r)))

(defn- group-by* [ctx f coll]
  (let [xs (elems ctx coll)
        m (reduce (fn [m x] (let [k (call1 ctx f x)]
                              (let [k (deep! ctx k)] (assoc! m k (conj (get m k []) x)))))
                  (transient {}) (seq xs))]
    (let [r (persistent! m)]
      (rt/check-size! ctx (count r))
      r)))

(defn- sort* [ctx coll]
  (let [xs (->vec ctx coll)]
    (rt/check-size! ctx (count xs))
    (vec (order/sort-values ctx xs))))

(defn- sort-by* [ctx f coll]
  (let [xs (->vec ctx coll)
        _ (rt/check-size! ctx (count xs))
        keyed (mapv (fn [x] [(call1 ctx f x) x]) xs)]
    (mapv second (sort-by first (fn [a b] (order/compare-values ctx a b)) keyed))))

(defn- interleave* [ctx colls]
  (let [vs (mapv #(->vec ctx %) colls)]
    (if (empty? vs)
      []
      (let [n (apply min (map count vs))]
        (rt/check-size! ctx (* n (count vs)))
        (rt/charge! ctx (* n (count vs)))
        (vec (for [i (range n) c vs] (nth c i)))))))

(defn- apply* [ctx f args]
  (let [lastc (peek (vec args))
        init (pop (vec args))
        spread (->vec ctx lastc)]
    (rt/check-size! ctx (+ (count init) (count spread)))
    (apply-fn ctx f (into init spread))))

(defn- fn-entry [impl mn mx] {:impl impl :arity [mn mx]})

;; ------------------------------------------------------------------ table

(def fns
  {'get (fn-entry (fn [ctx m k & [nf]] (rt/charge! ctx 1) (get* ctx m k nf)) 2 3)
   'get-in (fn-entry (fn [ctx m ks & [nf]]
                       (let [ks (->vec ctx ks)]
                         (loop [m m ks (seq ks)]
                           (if ks
                             (let [r (get* ctx m (first ks) ::missing)]
                               (if (= r ::missing) nf (recur r (next ks))))
                             m))))
                     2 3)
   'assoc (fn-entry (fn [ctx coll & kvs]
                      (when (odd? (count kvs)) (type-error kvs "Expected key/value pairs"))
                      (rt/charge! ctx (count kvs))
                      (let [r (reduce (fn [c [k v]] (assoc1 ctx c k v)) coll (partition 2 kvs))]
                        (rt/check-size! ctx (count r))
                        r))
                    3 nil)
   'assoc-in (fn-entry (fn [ctx m ks v]
                         (let [r (assoc-in* ctx m (->vec ctx ks) v)]
                           (when (counted? r) (rt/check-size! ctx (count r)))
                           r)) 3 3)
   'dissoc (fn-entry (fn [ctx m & ks]
                       (rt/charge! ctx (count ks))
                       (cond (nil? m) nil
                             (map? m) (do (run! #(deep! ctx %) ks) (apply dissoc m ks))
                             :else (type-error m "Expected a map")))
                     1 nil)
   'update (fn-entry (fn [ctx m k f & args]
                       (rt/charge! ctx (count args))
                       (let [r (assoc1 ctx m k (apply-fn ctx f (into [(get* ctx m k nil)] args)))]
                         (rt/check-size! ctx (count r))
                         r))
                     3 nil)
   'conj (fn-entry (fn [ctx coll & xs]
                     (seqable! coll)
                     (rt/charge! ctx (count xs))
                     (let [r (reduce #(conj1 ctx %1 %2) coll xs)]
                       (rt/check-size! ctx (count r))
                       r))
                   1 nil)
   'into (fn-entry (fn [ctx to from]
                     (seqable! to)
                     (let [xs (->vec ctx from)
                           r (reduce #(conj1 ctx %1 %2) (if (nil? to) [] to) xs)]
                       (rt/check-size! ctx (count r))
                       r))
                   2 2)
   'count (fn-entry (fn [ctx x]
                      (cond (string? x) (do (rt/charge! ctx 1) (count ^String x))
                            :else (do (seqable! x) (rt/charge! ctx 1) (count x))))
                    1 1)
   'nth (fn-entry (fn [ctx coll i & [nf]] (nth* ctx coll i nf)) 2 3)
   'first (fn-entry first-of 1 1)
   'second (fn-entry (fn [ctx coll] (first-of ctx (rest* ctx coll))) 1 1)
   'last (fn-entry last-of 1 1)
   'rest (fn-entry rest* 1 1)
   'next (fn-entry (fn [ctx coll] (let [r (rest* ctx coll)] (when (seq r) r))) 1 1)
   'peek (fn-entry (fn [ctx coll]
                     (rt/charge! ctx 1)
                     (cond (nil? coll) nil
                           (vector? coll) (peek coll)
                           (list? coll) (first coll)
                           :else (type-error coll "Expected a vector or list")))
                   1 1)
   'subvec (fn-entry (fn [ctx v start & [end]] (subvec* ctx v start end)) 2 3)
   'keys (fn-entry (fn [ctx m] (sized ctx (mapv first (order/ordered ctx (map! m))))) 1 1)
   'vals (fn-entry (fn [ctx m] (sized ctx (mapv second (order/ordered ctx (map! m))))) 1 1)
   'contains? (fn-entry (fn [ctx coll k]
                          (rt/charge! ctx 1)
                          (cond (nil? coll) false
                                (or (map? coll) (set? coll)) (contains? coll (deep! ctx k))
                                (vector? coll) (and (instance? Long k) (< -1 (long k) (count coll)))
                                :else (type-error coll "Expected a collection")))
                        2 2)
   'empty? (fn-entry (fn [ctx x]
                       (rt/charge! ctx 1)
                       (cond (string? x) (zero? (count ^String x))
                             :else (empty? (seqable! x))))
                     1 1)
   'not-empty (fn-entry (fn [ctx x] (rt/charge! ctx 1) (when (seq (seqable! x)) x)) 1 1)
   'vec (fn-entry (fn [ctx coll] (->vec ctx coll)) 1 1)
   'set (fn-entry (fn [ctx coll]
                    (let [r (set (deep! ctx (->vec ctx coll)))] (rt/check-size! ctx (count r)) r))
                  1 1)
   'hash-map (fn-entry (fn [ctx & kvs] (args-map ctx kvs)) 0 nil)
   'vector (fn-entry (fn [ctx & xs] (sized ctx (vec xs))) 0 nil)
   'list (fn-entry (fn [ctx & xs] (sized ctx xs) (apply list xs)) 0 nil)
   'merge (fn-entry (fn [ctx & maps] (merge* ctx maps)) 0 nil)
   'select-keys (fn-entry (fn [ctx m ks]
                            (let [ks (->vec ctx ks)]
                              (select-keys (if (nil? m) {} (map! m)) (deep! ctx ks))))
                          2 2)
   'zipmap (fn-entry (fn [ctx ks vs]
                       (let [ks (deep! ctx (->vec ctx ks)) vs (->vec ctx vs)]
                         (rt/check-size! ctx (min (count ks) (count vs)))
                         (zipmap ks vs)))
                     2 2)
   'frequencies (fn-entry (fn [ctx coll]
                            (let [r (frequencies (deep! ctx (->vec ctx coll)))]
                              (rt/check-size! ctx (count r))
                              r))
                          1 1)

   'map (fn-entry (fn [ctx f coll & colls]
                    (if (seq colls)
                      (let [vs (mapv #(->vec ctx %) (cons coll colls))
                            n (apply min (map count vs))]
                        (rt/check-size! ctx n)
                        (mapv (fn [i] (apply-fn ctx f (mapv #(nth % i) vs))) (range n)))
                      (mapv-charged ctx f coll)))
                  2 nil)
   'map-indexed (fn-entry (fn [ctx f coll]
                            (let [xs (->vec ctx coll)]
                              (vec (map-indexed (fn [i x] (apply-fn ctx f [i x])) xs))))
                          2 2)
   'mapcat (fn-entry (fn [ctx f coll]
                       (let [parts (mapv-charged ctx f coll)
                             r (reduce (fn [acc p]
                                   (let [xs (->vec ctx p)]
                                     (rt/check-size! ctx (+ (count acc) (count xs)))
                                     (into acc xs)))
                                 [] parts)]
                         r))
                     2 2)
   'filter (fn-entry (fn [ctx f coll]
                       (let [xs (->vec ctx coll)]
                         (filterv #(truthy? (call1 ctx f %)) xs)))
                     2 2)
   'remove (fn-entry (fn [ctx f coll]
                       (let [xs (->vec ctx coll)]
                         (filterv #(not (truthy? (call1 ctx f %))) xs)))
                     2 2)
   'keep (fn-entry (fn [ctx f coll]
                     (filterv some? (mapv-charged ctx f coll)))
                   2 2)
   'reduce (fn-entry (fn [ctx f & args] (reduce* ctx f args)) 2 3)
   'reduce-kv (fn-entry (fn [ctx f init coll]
                          (cond
                            (map? coll) (do (rt/charge! ctx (count coll))
                                            (reduce (fn [acc [k x]] (apply-fn ctx f [acc k x])) init (order/ordered ctx coll)))
                            (vector? coll) (do (rt/charge! ctx (count coll))
                                               (reduce-kv (fn [acc i x] (apply-fn ctx f [acc i x])) init coll))
                            :else (type-error coll "Expected a map or vector")))
                        3 3)
   'range (fn-entry range* 1 3)
   'take (fn-entry (fn [ctx n coll]
                     (let [n (long! n) xs (->vec ctx coll)]
                       (subvec xs 0 (min (max 0 n) (count xs)))))
                   2 2)
   'drop (fn-entry (fn [ctx n coll]
                     (let [n (long! n) xs (->vec ctx coll)]
                       (if (>= n (count xs)) [] (subvec xs (max 0 n)))))
                   2 2)
   'take-while (fn-entry take-while* 2 2)
   'drop-while (fn-entry drop-while* 2 2)
   'concat (fn-entry (fn [ctx & colls]
                       (let [vs (mapv #(->vec ctx %) colls)]
                         (rt/check-size! ctx (reduce + 0 (map count vs)))
                         (vec (apply concat vs))))
                     0 nil)
   'reverse (fn-entry (fn [ctx coll] (vec (rseq (->vec ctx coll)))) 1 1)
   'sort (fn-entry sort* 1 1)
   'sort-by (fn-entry sort-by* 2 2)
   'group-by (fn-entry group-by* 2 2)
   'partition (fn-entry (fn [ctx n a & more]
                          (if (seq more) (partition* ctx false n a (first more)) (partition* ctx false n n a)))
                        2 3)
   'partition-all (fn-entry (fn [ctx n a & more]
                              (if (seq more) (partition* ctx true n a (first more)) (partition* ctx true n n a)))
                            2 3)
   'distinct (fn-entry (fn [ctx coll]
                         (let [xs (deep! ctx (->vec ctx coll))]
                           (:out (reduce (fn [{:keys [seen] :as st} x]
                                           (if (contains? seen x)
                                             st
                                             {:seen (conj seen x) :out (conj (:out st) x)}))
                                         {:seen #{} :out []} xs))))
                       1 1)
   'some (fn-entry (fn [ctx f coll]
                     (let [xs (elems ctx coll)]
                       (loop [s (seq xs)]
                         (when s
                           (let [r (call1 ctx f (first s))]
                             (if (truthy? r) r (recur (next s))))))))
                   2 2)
   'every? (fn-entry (fn [ctx f coll]
                       (let [xs (elems ctx coll)]
                         (loop [s (seq xs)]
                           (cond (nil? s) true
                                 (truthy? (call1 ctx f (first s))) (recur (next s))
                                 :else false))))
                     2 2)
   'interleave (fn-entry (fn [ctx & colls] (interleave* ctx colls)) 0 nil)
   'apply (fn-entry (fn [ctx f & args] (apply* ctx f args)) 2 nil)})
