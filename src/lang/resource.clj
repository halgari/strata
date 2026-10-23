(ns lang.resource
  "Host resources, the per-run page cache, and byte sources."
  (:require [lang.errors :as err]
            [lang.runtime :as rt]
            [lang.values :as v])
  (:import (java.io File RandomAccessFile)
           (java.util Arrays LinkedHashMap)
           (lang.values Bytes Handle)))

(set! *warn-on-reflection* true)

(defprotocol Resource
  (size [r])
  (read-range [r off len]
    "byte[] of exactly len bytes, or nil when the range is negative or past the end."))

(defn- valid-range? [^long total ^long off ^long len]
  (and (>= off 0) (>= len 0) (<= off (- total len))))

(defn bytes-resource [^bytes a]
  (let [a (aclone a)]
    (reify Resource
      (size [_] (alength a))
      (read-range [_ off len]
        (let [off (long off) len (long len)]
          (when (valid-range? (alength a) off len)
            (Arrays/copyOfRange a (int off) (int (+ off len)))))))))

(defn file-resource [^File f]
  (reify Resource
    (size [_] (.length f))
    (read-range [_ off len]
      (let [off (long off) len (long len)]
        (with-open [raf (RandomAccessFile. f "r")]
          (when (valid-range? (.length raf) off len)
            (let [out (byte-array len)]
              (.seek raf off)
              (.readFully raf out)
              out)))))))

(defn open-handle [ctx name]
  (when-let [r (get (:resources ctx) name)]
    (v/->Handle name r)))

;; ------------------------------------------------------------ page cache

(defn- cache-state
  "Lazily installs {:lru LinkedHashMap :total long[1]} in the ctx's page-cache atom."
  [ctx]
  (let [a (:page-cache ctx)]
    (or (:lru @a)
        (:lru (swap! a (fn [m]
                         (if (:lru m)
                           m
                           {:lru (LinkedHashMap. 16 (float 0.75) true)
                            :total (long-array 1)})))))
    @a))

(defn- page ^Bytes [ctx ^Handle h ^long idx ^long psize]
  (let [{:keys [^LinkedHashMap lru ^longs total]} (cache-state ctx)
        k [(.-name h) idx]]
    (or (.get lru k)
        (let [res (.-resource h)
              start (* idx psize)
              len (min psize (- (long (size res)) start))
              arr (read-range res start len)
              b (when arr (v/wrap-bytes arr))
              cap (long (rt/limit ctx :page-cache-bytes))]
          (when b (.put lru k b))
          (when b (aset total 0 (+ (aget total 0) len)))
          (loop []
            (when (and (> (aget total 0) cap) (> (.size lru) 0))
              (let [it (.iterator (.entrySet lru))
                    e ^java.util.Map$Entry (.next it)]
                (aset total 0 (- (aget total 0) (v/bsize ^Bytes (.getValue e))))
                (.remove it)
                (recur))))
          b))))

(defprotocol ByteSource
  (src-size [s ctx])
  (src-read [s ctx off len]
    "Bytes of exactly len bytes at off, or nil when out of range."))

(extend-protocol ByteSource
  Bytes
  (src-size [b _] (v/bsize b))
  (src-read [b _ off len]
    (let [off (long off) len (long len)]
      (when (and (>= off 0) (>= len 0) (<= off (- (v/bsize b) len)))
        (v/bslice b off (+ off len)))))

  Handle
  (src-size [h _] (size (.-resource h)))
  (src-read [h ctx off len]
    (let [off (long off) len (long len)
          total (long (size (.-resource h)))]
      (when (valid-range? total off len)
        (let [psize (long (rt/limit ctx :page-size))
              first-idx (quot off psize)
              last-idx (quot (+ off len -1) psize)]
          (cond
            (zero? len) (v/wrap-bytes (byte-array 0))
            (= first-idx last-idx)
            (when-let [p (page ctx h first-idx psize)]
              (let [rel (- off (* first-idx psize))]
                (v/bslice p rel (+ rel len))))
            :else
            (do
              (rt/alloc-bytes! ctx len)
              (let [out (byte-array len)]
                (loop [idx first-idx pos 0]
                  (if (<= idx last-idx)
                    (when-let [^Bytes p (page ctx h idx psize)]
                      (let [pstart (* idx psize)
                            from (max 0 (- off pstart))
                            n (min (- (v/bsize p) from) (- len pos))]
                        (System/arraycopy (v/barray p) from out pos n)
                        (recur (inc idx) (+ pos n))))
                    (v/wrap-bytes out)))))))))))

(defn src-id [s]
  (if (instance? Handle s)
    [:resource (.-name ^Handle s)]
    [:bytes (hash s) (v/bsize s)]))

(defn force-value
  "Forces a deferred value, memoized per run. Forcing nil yields nil."
  [ctx d]
  (when (some? d)
    (when-not (v/deferred? d)
      (err/error! :type-error :run "Expected a deferred value" {:value d}))
    (let [k [:force (rt/check-deep! ctx d)]
          hit (rt/memo-get ctx k)]
      (if (identical? hit :lang.runtime/miss)
        (rt/memo-put! ctx k ((v/deferred-force-fn d) ctx))
        hit))))
