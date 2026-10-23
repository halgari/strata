(ns lang.values
  "Language value types: bytes, handles, deferred values, functions, numeric canonicalization."
  (:require [lang.errors :refer [error!]])
  (:import (java.util Arrays)
           (clojure.lang BigInt IHashEq Keyword)
           (java.math BigInteger)))

(set! *warn-on-reflection* true)

;; ---------------------------------------------------------------- bytes

(deftype Bytes [^bytes arr ^long off ^long len ^:unsynchronized-mutable ^int h]
  Object
  (equals [this o]
    (or (identical? this o)
        (and (instance? Bytes o)
             (let [^Bytes b o]
               (and (== len (.-len b))
                    (Arrays/equals arr (int off) (int (+ off len))
                                   ^bytes (.-arr b) (int (.-off b)) (int (+ (.-off b) len))))))))
  (hashCode [_]
    (when (zero? h)
      (set! h (unchecked-int
               (loop [i off r 1]
                 (if (< i (+ off len))
                   (recur (inc i) (unchecked-add-int (unchecked-multiply-int 31 (int r))
                                                     (int (aget arr i))))
                   r)))))
    h)
  IHashEq
  (hasheq [this] (.hashCode this)))

(defn wrap-bytes
  "Wraps a byte array without copying (internal use)."
  [^bytes a]
  (Bytes. a 0 (alength a) 0))

(defn copy-bytes
  "Defensive copy of a host byte array."
  [^bytes a]
  (wrap-bytes (aclone a)))

(defn bytes-val? [x] (instance? Bytes x))

(defn bsize ^long [^Bytes b] (.-len b))

(defn bget
  "Unsigned byte at i, or nil when out of range."
  [^Bytes b i]
  (let [i (long i)]
    (when (and (>= i 0) (< i (.-len b)))
      (bit-and 0xff (long (aget ^bytes (.-arr b) (int (+ (.-off b) i))))))))

(defn bslice
  "Zero-copy slice [start, end), or nil when the range is invalid."
  [^Bytes b start end]
  (let [start (long start) end (long end)]
    (when (and (<= 0 start) (<= start end) (<= end (.-len b)))
      (Bytes. (.-arr b) (+ (.-off b) start) (- end start) 0))))

(defn barray
  "Fresh byte[] with the contents of b."
  ^bytes [^Bytes b]
  (Arrays/copyOfRange ^bytes (.-arr b) (int (.-off b)) (int (+ (.-off b) (.-len b)))))

;; ------------------------------------------------------- handle/deferred/fn

(deftype Handle [name resource]
  Object
  (equals [this o] (or (identical? this o) (and (instance? Handle o) (= name (.-name ^Handle o)))))
  (hashCode [_] (hash name)))

(defn handle? [x] (instance? Handle x))

(deftype Deferred [src-id src off len type-id force-fn args]
  Object
  (equals [this o]
    (or (identical? this o)
        (and (instance? Deferred o)
             (let [^Deferred d o]
               (and (= src-id (.-src-id d)) (= off (.-off d)) (= len (.-len d))
                    (= type-id (.-type-id d)) (= args (.-args d)))))))
  (hashCode [_] (hash [src-id off len type-id args])))

(defn deferred? [x] (instance? Deferred x))
(defn deferred-offset [^Deferred d] (.-off d))
(defn deferred-length [^Deferred d] (.-len d))
(defn deferred-force-fn [^Deferred d] (.-force-fn d))

(deftype LangFn [name impl])

(defn lang-fn? [x] (instance? LangFn x))

(defn apply-fn
  "Applies a language function value. Does not charge fuel."
  [ctx f args]
  (cond
    (instance? LangFn f) ((.-impl ^LangFn f) ctx args)
    (and (instance? Keyword f) (<= 1 (count args) 2)) (apply get (first args) f (rest args))
    :else (error! :type-error :run "Value is not callable" {:value f})))

;; --------------------------------------------------------------- numbers

(deftype NaNValue []
  Object
  (equals [this o] (identical? this o))
  (hashCode [_] 2146959360))

(def nan (NaNValue.))

(defmethod print-method NaNValue [_ ^java.io.Writer w] (.write w "##NaN"))

(defn nan? [x] (identical? x nan))

(defn- canon-big [^BigInteger b]
  (if (< (.bitLength b) 64) (.longValue b) (BigInt/fromBigInteger b)))

(defn canon-num
  "Canonicalizes a number: NaN -> nan, -0.0 -> 0.0, small ints -> long, big ints -> long or BigInt."
  [x]
  (cond
    (instance? Double x) (let [d (double x)]
                           (cond (Double/isNaN d) nan (zero? d) 0.0 :else x))
    (instance? Float x) (canon-num (double x))
    (instance? Long x) x
    (or (instance? Integer x) (instance? Short x) (instance? Byte x)) (long x)
    (instance? BigInt x) (canon-big (.toBigInteger ^BigInt x))
    (instance? BigInteger x) (canon-big x)
    :else (error! :unsupported-value :run "Unsupported number type" {:type (.getName (class x))})))

(defn canon
  "Deep-canonicalizes host data into language values."
  [x]
  (cond
    (or (nil? x) (boolean? x) (string? x) (char? x) (keyword? x) (symbol? x)) x
    (number? x) (canon-num x)
    (vector? x) (mapv canon x)
    (map? x) (reduce-kv (fn [m k v] (assoc m (canon k) (canon v))) {} x)
    (set? x) (into #{} (map canon) x)
    (list? x) (apply list (map canon x))
    (bytes? x) (copy-bytes x)
    (or (instance? Bytes x) (instance? Handle x) (instance? Deferred x) (nan? x)) x
    :else (error! :unsupported-value :run "Unsupported value type" {:type (.getName (class x))})))

(defn storable?
  "True when x contains no LangFn, at any depth."
  [x]
  (cond
    (instance? LangFn x) false
    (map? x) (every? (fn [[k v]] (and (storable? k) (storable? v))) x)
    (coll? x) (every? storable? x)
    :else true))

(defn weight
  "Shallow size weight used for memory accounting."
  ^long [x]
  (cond
    (string? x) (count ^String x)
    (instance? Bytes x) (max 1 (quot (.-len ^Bytes x) 1024))
    (counted? x) (count x)
    (instance? BigInt x) (inc (quot (.bitLength (.toBigInteger ^BigInt x)) 64))
    :else 1))
