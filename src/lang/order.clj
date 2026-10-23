(ns lang.order
  "Total order over language values (spec 5.7)."
  (:require [lang.errors :refer [error!]]
            [lang.runtime :refer [charge!]]
            [lang.values :as v])
  (:import (clojure.lang BigInt)
           (java.math BigDecimal)
           (lang.values Handle Deferred)))

(set! *warn-on-reflection* true)

(defn- rank ^long [x]
  (cond
    (nil? x) 0
    (boolean? x) 1
    (or (number? x) (v/nan? x)) 2
    (char? x) 3
    (string? x) 4
    (keyword? x) 5
    (symbol? x) 6
    (sequential? x) 7
    (map? x) 8
    (set? x) 9
    (v/bytes-val? x) 10
    (v/handle? x) 11
    (v/deferred? x) 12
    :else (error! :type-error :run "Value cannot be ordered" {:value x})))

(defn- sub-rank ^long [x]
  (cond (instance? Long x) 0 (instance? BigInt x) 1 :else 2))

(defn- sign ^long [^long n] (Long/signum n))

(defn- compare-nums ^long [a b]
  (cond
    (and (instance? Long a) (instance? Long b)) (long (Long/compare a b))
    (v/nan? a) (if (v/nan? b) 0 1)
    (v/nan? b) -1
    :else
    (let [c (cond
              (and (instance? Double a) (Double/isInfinite a) (instance? Double b) (Double/isInfinite b))
              (Double/compare a b)
              (and (instance? Double a) (Double/isInfinite a)) (if (pos? (double a)) 1 -1)
              (and (instance? Double b) (Double/isInfinite b)) (if (pos? (double b)) -1 1)
              :else (.compareTo (if (instance? Double a) (BigDecimal. (double a)) (BigDecimal. (.toBigInteger (bigint a))))
                                (if (instance? Double b) (BigDecimal. (double b)) (BigDecimal. (.toBigInteger (bigint b))))))]
      (if (zero? (long c))
        (long (Long/compare (sub-rank a) (sub-rank b)))
        (sign c)))))

(defn- compare-named ^long [a b]
  (let [na (namespace a) nb (namespace b)
        c (cond (and (nil? na) (nil? nb)) 0
                (nil? na) -1
                (nil? nb) 1
                :else (.compareTo ^String na ^String nb))]
    (if (zero? (long c))
      (sign (.compareTo ^String (name a) ^String (name b)))
      (sign c))))

(declare compare-values sort-values)

(defn- compare-seqs ^long [ctx a b]
  (loop [xs (seq a) ys (seq b)]
    (cond
      (and (nil? xs) (nil? ys)) 0
      (nil? xs) -1
      (nil? ys) 1
      :else
      (do (charge! ctx 1)
          (let [c (long (compare-values ctx (first xs) (first ys)))]
            (if (zero? c) (recur (next xs) (next ys)) c))))))

(defn- compare-bytes ^long [a b]
  (let [la (v/bsize a) lb (v/bsize b) n (min la lb)]
    (loop [i 0]
      (if (< i n)
        (let [c (Long/compare (long (v/bget a i)) (long (v/bget b i)))]
          (if (zero? c) (recur (inc i)) (sign c)))
        (long (Long/compare la lb))))))

(defn- sorted-entries [ctx m]
  (sort-values ctx (mapv (fn [[k val]] [k val]) m)))

(defn compare-values
  "Total order over language values. Negative, zero or positive. ctx may be nil."
  ^long [ctx a b]
  (let [ra (rank a) rb (rank b)]
    (if (not= ra rb)
      (long (Long/compare ra rb))
      (do
        (charge! ctx 1)
        (case ra
          0 0
          1 (long (Boolean/compare a b))
          2 (compare-nums a b)
          3 (long (Character/compare a b))
          4 (sign (.compareTo ^String a ^String b))
          (5 6) (compare-named a b)
          7 (compare-seqs ctx a b)
          8 (compare-seqs ctx (sorted-entries ctx a) (sorted-entries ctx b))
          9 (compare-seqs ctx (sort-values ctx (vec a)) (sort-values ctx (vec b)))
          10 (compare-bytes a b)
          11 (compare-values ctx (.-name ^Handle a) (.-name ^Handle b))
          12 (let [^Deferred x a ^Deferred y b]
               (compare-seqs ctx
                             [(.-src-id x) (.-off x) (.-len x) (.-type-id x) (.-args x)]
                             [(.-src-id y) (.-off y) (.-len y) (.-type-id y) (.-args y)])))))))

(defn sort-values
  "Stable sort of coll under compare-values."
  [ctx coll]
  (sort (fn [a b] (compare-values ctx a b)) coll))

(defn ordered
  "coll in a deterministic iteration order: maps become a vector of [k v]
  entries and sets a vector of elements, both in the total order (5.7);
  anything else is returned unchanged."
  [ctx coll]
  (cond
    (map? coll) (vec (sort-values ctx (mapv (fn [[k v]] [k v]) coll)))
    (set? coll) (vec (sort-values ctx coll))
    :else coll))
