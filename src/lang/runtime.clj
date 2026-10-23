(ns lang.runtime
  "Per-run context: fuel, limits, memo, diagnostics, and the isolated big-stack thread."
  (:require [lang.errors :as err])
  (:import (java.util LinkedHashMap)))

(set! *warn-on-reflection* true)

(def default-limits
  {:max-source-bytes 10485760
   :max-form-depth 256
   :fuel 1000000000
   :call-fuel 100000000
   :max-depth 512
   :max-tuples 10000000
   :max-iterations 10000
   :max-bytes 1073741824
   :max-read 268435456
   :max-inflate 268435456
   :max-value-size 10000000
   :max-int-bits 4096
   :max-regex-length 1000
   :max-memo-entries 1000000
   :page-size 65536
   :page-cache-bytes 67108864
   :timeout-ms nil})

(def ^:private max-diag-entries 1000)
(def ^:private clock-interval 65536)

;; Counter fields are single-element long arrays; a run is single-threaded.
(defrecord RunCtx [limits trace on-code-error resources
                   fuel call-fuel depth bytes start since-check
                   memo page-cache diag])

(defn- cell ^longs [^long v] (doto (long-array 1) (aset 0 v)))

(defn make-ctx [opts]
  (let [limits (merge default-limits (:limits opts))
        max-memo (long (:max-memo-entries limits))
        memo (proxy [LinkedHashMap] [16 (float 0.75) true]
               (removeEldestEntry [_] (> (.size ^LinkedHashMap this) max-memo)))]
    (map->RunCtx {:limits limits
                  :trace (:trace opts)
                  :on-code-error (or (:on-code-error opts) :abort)
                  :resources (:resources opts)
                  :fuel (cell (:fuel limits))
                  :call-fuel (cell (:call-fuel limits))
                  :depth (cell 0)
                  :bytes (cell 0)
                  :start (cell (System/currentTimeMillis))
                  :since-check (cell 0)
                  :memo memo
                  :page-cache (atom {})
                  :diag (volatile! {:entries [] :counts {}})})))

(defn limit [ctx k] (get (:limits ctx) k))

(defn- check-clock! [ctx]
  (when-let [t (limit ctx :timeout-ms)]
    (when (> (- (System/currentTimeMillis) (aget ^longs (:start ctx) 0)) (long t))
      (err/error! :timeout :run "Time limit exceeded" {}))))

(defn charge! [ctx ^long n]
  (when ctx
    (let [^longs fuel (:fuel ctx)
          ^longs cf (:call-fuel ctx)
          ^longs sc (:since-check ctx)
          f (- (aget fuel 0) n)
          c (- (aget cf 0) n)
          s (+ (aget sc 0) n)]
      (aset fuel 0 f)
      (aset cf 0 c)
      (when (neg? f) (err/error! :fuel-exhausted :run "Fuel exhausted" {}))
      (when (neg? c) (err/error! :call-fuel-exhausted :run "Call fuel exhausted" {}))
      (if (>= s clock-interval)
        (do (aset sc 0 (long (rem s (long clock-interval))))
            (check-clock! ctx))
        (aset sc 0 s))
      nil)))

(defn charge-total!
  "Charges total fuel only (engine work); runs the same timeout check as charge!."
  [ctx ^long n]
  (when ctx
    (let [^longs fuel (:fuel ctx)
          ^longs sc (:since-check ctx)
          f (- (aget fuel 0) n)
          s (+ (aget sc 0) n)]
      (aset fuel 0 f)
      (when (neg? f) (err/error! :fuel-exhausted :run "Fuel exhausted" {}))
      (if (>= s clock-interval)
        (do (aset sc 0 (long (rem s (long clock-interval))))
            (check-clock! ctx))
        (aset sc 0 s))
      nil)))

(defn with-call-budget [ctx thunk]
  (let [^longs cf (:call-fuel ctx)
        outer (aget cf 0)]
    (aset cf 0 (long (limit ctx :call-fuel)))
    (try (thunk)
         (finally (aset cf 0 outer)))))

(defn with-depth [ctx thunk]
  (let [^longs d (:depth ctx)
        n (inc (aget d 0))]
    (aset d 0 n)
    (try
      (when (> n (long (limit ctx :max-depth)))
        (err/error! :depth-exceeded :run "Maximum depth exceeded" {}))
      (thunk)
      (finally (aset d 0 (dec n))))))

(defn alloc-bytes! [ctx ^long n]
  (let [^longs b (:bytes ctx)
        total (+ (aget b 0) n)]
    (aset b 0 total)
    (when (> total (long (limit ctx :max-bytes)))
      (err/error! :bytes-exhausted :run "Byte budget exhausted" {}))
    nil))

(defn check-size! [ctx ^long n]
  (when (> n (long (limit ctx :max-value-size)))
    (err/error! :value-too-large :run "Value too large" {}))
  nil)

(defn check-int! [ctx x]
  (when (and (instance? clojure.lang.BigInt x)
             (> (.bitLength (.toBigInteger ^clojure.lang.BigInt x))
                (long (limit ctx :max-int-bits))))
    (err/error! :int-too-large :run "Integer too large" {}))
  x)

(defn memo-get [ctx k]
  (.getOrDefault ^LinkedHashMap (:memo ctx) k ::miss))

(defn memo-put! [ctx k v]
  (.put ^LinkedHashMap (:memo ctx) k v)
  v)

(defn diag! [ctx kind data]
  (vswap! (:diag ctx)
          (fn [{:keys [entries counts]}]
            {:entries (if (< (count entries) max-diag-entries)
                        (conj entries {:kind kind :data data})
                        entries)
             :counts (update counts kind (fnil inc 0))}))
  nil)

(defn diagnostics [ctx] @(:diag ctx))

(defn trace! [ctx event]
  (when-let [f (:trace ctx)] (f event))
  nil)

(defn run-isolated [thunk]
  (let [result (volatile! nil)
        failure (volatile! nil)
        t (Thread. nil
                   (fn []
                     (try (vreset! result (thunk))
                          (catch Throwable e (vreset! failure e))))
                   "lang-run" (* 1024 1024 1024))]
    (.start t)
    (.join t)
    (if-let [e @failure]
      (throw (err/map-throwable e :run))
      @result)))
