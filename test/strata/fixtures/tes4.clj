(ns strata.fixtures.tes4
  "Synthetic Skyrim TES4 plugin builder: header record, masters, GRUPs and
  (optionally compressed) records."
  (:import (java.io ByteArrayOutputStream)
           (java.nio ByteBuffer ByteOrder)
           (java.util.zip Deflater)))

(defn- le [n f]
  (let [b (doto (ByteBuffer/allocate n) (.order ByteOrder/LITTLE_ENDIAN))]
    (f b)
    (.array b)))

(defn- u16 [v] (le 2 #(.putShort ^ByteBuffer % (unchecked-short v))))
(defn- u32 [v] (le 4 #(.putInt ^ByteBuffer % (unchecked-int v))))
(defn- f32 [v] (le 4 #(.putFloat ^ByteBuffer % (float v))))
(defn- ascii [^String s] (.getBytes s "US-ASCII"))

(defn- cat-bytes ^bytes [& parts]
  (let [out (ByteArrayOutputStream.)]
    (doseq [^bytes p parts] (.write out p 0 (alength p)))
    (.toByteArray out)))

(defn- zstring [^String s] (cat-bytes (.getBytes s "windows-1252") (byte-array 1)))

(defn subrecord
  "A plain subrecord; with big? an XXXX record precedes it and its size field is 0."
  ([type data] (subrecord type data false))
  ([type ^bytes data big?]
   (if big?
     (cat-bytes (ascii "XXXX") (u16 4) (u32 (alength data))
                (ascii type) (u16 0) data)
     (cat-bytes (ascii type) (u16 (alength data)) data))))

(defn- deflate ^bytes [^bytes raw]
  (let [d (Deflater.) out (ByteArrayOutputStream.) buf (byte-array 4096)]
    (.setInput d raw)
    (.finish d)
    (while (not (.finished d))
      (.write out buf 0 (.deflate d buf)))
    (.end d)
    (.toByteArray out)))

(defn- record-bytes
  [{:keys [type form-id flags fields compressed? garbage-zlib? xxxx?]
    :or {form-id 0 flags 0}}]
  (let [raw (apply cat-bytes (map (fn [[t d]] (subrecord t d xxxx?)) fields))
        data (cond
               garbage-zlib? (cat-bytes (u32 (alength raw))
                                        (byte-array (map unchecked-byte (range 200 230))))
               compressed? (cat-bytes (u32 (alength raw)) (deflate raw))
               :else raw)
        flags (if (or compressed? garbage-zlib?) (bit-or flags 0x40000) flags)]
    (cat-bytes (ascii type) (u32 (alength data)) (u32 flags) (u32 form-id)
               (u16 0) (u16 0) (u16 44) (u16 0) data)))

(defn- group-bytes [{:keys [label records]}]
  (let [body (apply cat-bytes (map record-bytes records))]
    (cat-bytes (ascii "GRUP") (u32 (+ 24 (alength body))) (ascii label)
               (u32 0) (u16 0) (u16 0) (u32 0) body)))

(defn build-plugin
  "opts: :flags (TES4 record flags), :masters, :author, :groups
  [{:label :records [{:type :form-id :fields [[sub-type bytes]] :compressed?
  :garbage-zlib?}]}], :xxxx? (give every record field an XXXX size prefix)."
  [{:keys [flags masters author groups xxxx?] :or {flags 0 author "tester"}}]
  (let [groups (map (fn [g] (update g :records
                                    (fn [rs] (map #(cond-> % xxxx? (assoc :xxxx? true)) rs))))
                    groups)
        n-records (reduce + (map #(count (:records %)) groups))
        hdr-fields (concat
                    [(subrecord "HEDR" (cat-bytes (f32 1.71) (u32 n-records) (u32 0x800)))
                     (subrecord "CNAM" (zstring author))]
                    (mapcat (fn [m] [(subrecord "MAST" (zstring m))
                                     (subrecord "DATA" (byte-array 8))])
                            masters))
        hdr-data (apply cat-bytes hdr-fields)]
    (apply cat-bytes
           (cat-bytes (ascii "TES4") (u32 (alength hdr-data)) (u32 flags) (u32 0)
                      (u16 0) (u16 0) (u16 44) (u16 0) hdr-data)
           (map group-bytes groups))))
