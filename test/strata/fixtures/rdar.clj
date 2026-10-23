(ns strata.fixtures.rdar
  "Synthetic RDAR (.archive) builder: 40-byte header, zero padding to 0xAC,
  and the index at the end of the file."
  (:import (java.nio ByteBuffer ByteOrder)))

(defn build-rdar
  "opts: :version (default 12), :entries [{:hash u64 :segments [[off zsize size]..]
  :deps [u64..]}..]. Segments and dependencies are numbered in entry order."
  [{:keys [version entries] :or {version 12}}]
  (let [segs (vec (mapcat :segments entries))
        deps (vec (mapcat :deps entries))
        index-size (+ 28 (* 56 (count entries)) (* 16 (count segs)) (* 8 (count deps)))
        index-pos 0xAC
        total (+ index-pos index-size)
        buf (doto (ByteBuffer/allocate total) (.order ByteOrder/LITTLE_ENDIAN))
        p32 (fn [v] (.putInt buf (unchecked-int v)))
        p64 (fn [v] (.putLong buf (unchecked-long (biginteger v))))]
    (.put buf (.getBytes "RDAR" "US-ASCII"))
    (p32 version) (p64 index-pos) (p32 index-size)
    (p64 0) (p32 0) (p64 total)
    (.position buf (int index-pos))
    (p32 8) (p32 (- index-size 8)) (p64 0xC0FFEE)
    (p32 (count entries)) (p32 (count segs)) (p32 (count deps))
    (loop [es entries, s 0, d 0]
      (when-let [[e & more] (seq es)]
        (let [s2 (+ s (count (:segments e)))
              d2 (+ d (count (:deps e)))]
          (p64 (:hash e)) (p64 0)
          (p32 0) (p32 s) (p32 s2) (p32 d) (p32 d2)
          (.put buf (byte-array 20 (byte 7)))
          (recur more s2 d2))))
    (doseq [[off zsize size] segs] (p64 off) (p32 zsize) (p32 size))
    (doseq [d deps] (p64 d))
    (.array buf)))
