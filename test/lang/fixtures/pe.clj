(ns lang.fixtures.pe
  "Synthetic PE32 / PE32+ builder with one .idata section holding import and
  delay-import tables."
  (:import (java.nio ByteBuffer ByteOrder)))

(def ^:private section-rva 0x1000)
(def ^:private section-ptr 0x200)
(def ^:private image-base 0x10000000)

(defn build-pe
  "opts: :wide? (PE32+), :imports and :delay-imports (dll names),
  :delay-rva-based? (delay name fields are RVAs, else VAs),
  :bad-import-rvas (count of extra import descriptors whose name RVA lies
  outside every section; placed before the real ones)."
  [{:keys [wide? imports delay-imports delay-rva-based? bad-import-rvas]
    :or {bad-import-rvas 0}}]
  (let [n-imp (+ (count imports) bad-import-rvas)
        imp-size (* 20 (inc n-imp))
        delay-size (* 32 (inc (count delay-imports)))
        names-at (+ imp-size delay-size)
        name-offs (reduce (fn [[m at] n] [(assoc m n at) (+ at (count n) 1)])
                          [{} names-at] (distinct (concat imports delay-imports)))
        offs (first name-offs)
        data-size (second name-offs)
        opt-size (if wide? 240 224)
        buf (doto (ByteBuffer/allocate (+ section-ptr data-size))
              (.order ByteOrder/LITTLE_ENDIAN))
        p8 (fn [at v] (.put buf (int at) (unchecked-byte v)))
        p16 (fn [at v] (.putShort buf (int at) (unchecked-short v)))
        p32 (fn [at v] (.putInt buf (int at) (unchecked-int v)))
        p64 (fn [at v] (.putLong buf (int at) (long v)))
        pe-at 0x80
        coff-at (+ pe-at 4)
        opt-at (+ coff-at 20)
        sec-at (+ opt-at opt-size)
        sec-data section-ptr
        rva #(+ section-rva %)]
    (p8 0 77) (p8 1 90) (p32 0x3C pe-at)
    (doseq [[i b] (map-indexed vector [0x50 0x45 0 0])] (p8 (+ pe-at i) b))
    (p16 coff-at (if wide? 0x8664 0x14c))
    (p16 (+ coff-at 2) 1)
    (p16 (+ coff-at 16) opt-size)
    (p16 (+ coff-at 18) 0x2000)
    (p16 opt-at (if wide? 0x20b 0x10b))
    (p32 (+ opt-at 16) 0)
    (p32 (+ opt-at 20) section-rva)
    (let [dirs-at (if wide?
                    (do (p64 (+ opt-at 24) image-base) 112)
                    (do (p32 (+ opt-at 24) section-rva) (p32 (+ opt-at 28) image-base) 96))]
      (p32 (+ opt-at 32) 0x1000) (p32 (+ opt-at 36) 0x200)
      (p32 (+ opt-at 56) (+ section-rva 0x1000))
      (p32 (+ opt-at 60) 0x200)
      (p32 (+ opt-at (- dirs-at 4)) 16)
      (p32 (+ opt-at dirs-at 8) section-rva)
      (p32 (+ opt-at dirs-at 12) imp-size)
      (when (seq delay-imports)
        (p32 (+ opt-at dirs-at (* 13 8)) (rva imp-size))
        (p32 (+ opt-at dirs-at (* 13 8) 4) delay-size)))
    ;; section header
    (doseq [[i c] (map-indexed vector ".idata")] (p8 (+ sec-at i) (int c)))
    (p32 (+ sec-at 8) data-size)
    (p32 (+ sec-at 12) section-rva)
    (p32 (+ sec-at 16) data-size)
    (p32 (+ sec-at 20) section-ptr)
    ;; import descriptors: bad ones first
    (dotimes [i bad-import-rvas]
      (let [at (+ sec-data (* 20 i))]
        (p32 at (rva 0) ) (p32 (+ at 12) 0x9000)))
    (doseq [[i n] (map-indexed vector imports)]
      (let [at (+ sec-data (* 20 (+ bad-import-rvas i)))]
        (p32 at (rva 0)) (p32 (+ at 12) (rva (offs n)))))
    (doseq [[i n] (map-indexed vector delay-imports)]
      (let [at (+ sec-data imp-size (* 32 i))
            r (rva (offs n))]
        (p32 at (if delay-rva-based? 1 0))
        (p32 (+ at 4) (if delay-rva-based? r (+ image-base r)))))
    (doseq [[n o] offs
            [i c] (map-indexed vector n)]
      (p8 (+ sec-data o i) (int c)))
    (.array buf)))
