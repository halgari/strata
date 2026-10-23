(ns lang.builtins.bytes
  "Byte-buffer built-ins of lang.bytes: reads, decoders, inflate, checksums (spec 4.5, 4.6)."
  (:require [lang.builtins.core :refer [type-error]]
            [lang.runtime :as rt]
            [lang.values :as v :refer [bsize bget bslice wrap-bytes]])
  (:import (java.math BigInteger)
           (java.nio ByteBuffer)
           (java.nio.charset Charset CharacterCodingException CodingErrorAction StandardCharsets)
           (java.security MessageDigest)
           (java.util.zip CRC32 DataFormatException Inflater)
           (lang.values Bytes)))

(set! *warn-on-reflection* true)

;; ---------------------------------------------------------------- helpers

(defn- bytes! ^Bytes [x]
  (if (v/bytes-val? x) x (type-error x "Expected bytes")))

(defn- long! ^long [x]
  (if (instance? Long x) (long x) (type-error x "Expected an integer")))

(defn- charge-size! [ctx ^long n]
  (rt/charge! ctx (max 1 (quot n 1024))))

(defn- in!
  "Type-checks a bytes argument and charges per KB."
  ^Bytes [ctx x]
  (let [b (bytes! x)]
    (charge-size! ctx (bsize b))
    b))

(defn- out-bytes
  "Wraps a fresh array as Bytes, counting it against the byte budget."
  [ctx ^bytes a]
  (rt/alloc-bytes! ctx (alength a))
  (wrap-bytes a))

(defn- u64->num [^long x]
  (v/canon-num (if (neg? x) (BigInteger. (Long/toUnsignedString x)) x)))

;; ------------------------------------------------------------------ reads

(defn- raw
  "Unsigned n-byte value at offset as a (possibly wrapped) long, or nil if out of range."
  [^Bytes b off ^long n be?]
  (let [off (long! off)]
    (when (<= 0 off (- (bsize b) n))
      (loop [i 0 acc 0]
        (if (< i n)
          (let [byte (long (bget b (+ off (if be? i (- n 1 i)))))]
            (recur (inc i) (bit-or (bit-shift-left acc 8) byte)))
          acc)))))

(defn- sign-extend ^long [^long x ^long n]
  (let [s (- 64 (* 8 n))]
    (bit-shift-right (bit-shift-left x s) s)))

(defn- reader [n be? post]
  {:impl (fn [ctx b off]
           (rt/charge! ctx 1)
           (when-some [x (raw (bytes! b) off n be?)]
             (post (long x))))
   :arity [2 2]})

(defn- int-readers [sym n]
  (let [mk (fn [suffix be?]
             [[(symbol (str "u" sym suffix)) (reader n be? (if (= n 8) u64->num identity))]
              [(symbol (str "i" sym suffix)) (reader n be? #(sign-extend % n))]])]
    (into {} (concat (mk "-le" false) (mk "-be" true)))))

(defn- float-readers []
  (let [f32 (fn [^long x] (v/canon-num (Float/intBitsToFloat (unchecked-int x))))
        f64 (fn [^long x] (v/canon-num (Double/longBitsToDouble x)))]
    {'f32-le (reader 4 false f32) 'f32-be (reader 4 true f32)
     'f64-le (reader 8 false f64) 'f64-be (reader 8 true f64)}))

;; --------------------------------------------------------------- decoding

(defn- sub-range
  "The [start, end) view of b described by the optional range arguments, or nil."
  [^Bytes b start end]
  (if (nil? start)
    b
    (bslice b (long! start) (if (some? end) (long! end) (bsize b)))))

(defn- decoder [charset]
  {:impl (fn [ctx b & [start end]]
           (let [b (in! ctx b)]
             (when-some [^Bytes s (sub-range b start end)]
               (rt/check-size! ctx (bsize s))
               (try
                 (.toString (.decode (doto (.newDecoder ^Charset charset)
                                       (.onMalformedInput CodingErrorAction/REPORT)
                                       (.onUnmappableCharacter CodingErrorAction/REPORT))
                                     (ByteBuffer/wrap (v/barray s))))
                 (catch CharacterCodingException _ nil)))))
   :arity [1 3]})

(defn- ascii [ctx b & [start end]]
  (let [b (in! ctx b)]
    (when-some [^Bytes s (sub-range b start end)]
      (rt/check-size! ctx (bsize s))
      (let [a (v/barray s)]
        (when (every? #(>= (long %) 0) a)
          (String. a StandardCharsets/US_ASCII))))))

(defn- hex-digit ^long [^long c]
  (cond (<= 48 c 57) (- c 48)
        (<= 97 c 102) (- c 87)
        (<= 65 c 70) (- c 55)
        :else -1))

(defn- hex-encode [ctx b]
  (let [b (in! ctx b)]
    (rt/check-size! ctx (* 2 (bsize b)))
    (let [sb (StringBuilder. (int (* 2 (bsize b))))]
      (dotimes [i (bsize b)]
        (let [x (long (bget b i))]
          (.append sb (Character/forDigit (int (bit-shift-right x 4)) 16))
          (.append sb (Character/forDigit (int (bit-and x 15)) 16))))
      (.toString sb))))

(defn- hex-decode [ctx s]
  (when-not (string? s) (type-error s "Expected a string"))
  (let [^String s s n (.length s)]
    (rt/charge! ctx (max 1 (quot n 1024)))
    (when (even? n)
      (let [a (byte-array (quot n 2))]
        (when (loop [i 0]
                (if (< i (alength a))
                  (let [hi (hex-digit (long (int (.charAt s (* 2 i)))))
                        lo (hex-digit (long (int (.charAt s (inc (* 2 i))))))]
                    (when (and (>= hi 0) (>= lo 0))
                      (aset a i (unchecked-byte (+ (* 16 hi) lo)))
                      (recur (inc i))))
                  true))
          (out-bytes ctx a))))))

(defn- encode-utf8 [ctx s]
  (when-not (string? s) (type-error s "Expected a string"))
  (charge-size! ctx (.length ^String s))
  (try
    (let [bb (.encode (doto (.newEncoder StandardCharsets/UTF_8)
                        (.onMalformedInput CodingErrorAction/REPORT)
                        (.onUnmappableCharacter CodingErrorAction/REPORT))
                      (java.nio.CharBuffer/wrap ^String s))
          a (byte-array (.remaining bb))]
      (.get bb a)
      (out-bytes ctx a))
    (catch CharacterCodingException _ nil)))

;; ------------------------------------------------------- search and slice

(defn- index-of [ctx b needle & [from]]
  (let [b (in! ctx b)
        from (if (some? from) (max 0 (long! from)) 0)
        n (bsize b)]
    (cond
      (instance? Long needle)
      (when (<= 0 (long needle) 255)
        (loop [i from]
          (when (< i n)
            (if (== (long (bget b i)) (long needle)) i (recur (inc i))))))

      (v/bytes-val? needle)
      (let [^Bytes nd needle m (bsize nd)]
        (charge-size! ctx (* n m))
        (loop [i from]
          (when (<= (+ i m) n)
            (if (loop [j 0]
                  (or (== j m)
                      (and (== (long (bget b (+ i j))) (long (bget nd j))) (recur (inc j)))))
              i
              (recur (inc i))))))

      :else (type-error needle "Expected a byte or bytes"))))

;; ---------------------------------------------------------------- inflate

(defn- inflate [ctx b max-out & [mode]]
  (let [b (in! ctx b)
        max-out (long! max-out)
        nowrap? (cond (nil? mode) false
                      (= mode :raw) true
                      :else (type-error mode "Expected :raw"))
        cap (min max-out (long (rt/limit ctx :max-inflate)))]
    (when (>= cap 0)
      (let [inf (Inflater. nowrap?)
            buf (byte-array (int (min 8192 (inc cap))))
            out (java.io.ByteArrayOutputStream.)]
        (try
          (.setInput inf ^bytes (.-arr b) (int (.-off b)) (int (bsize b)))
          (loop [total 0]
            (let [n (.inflate inf buf)
                  total (+ total n)]
              (rt/alloc-bytes! ctx n)
              (charge-size! ctx n)
              (cond
                (> total cap) nil
                (.finished inf) (do (.write out buf 0 n) (wrap-bytes (.toByteArray out)))
                (and (zero? n) (or (.needsInput inf) (.needsDictionary inf))) nil
                :else (do (.write out buf 0 n) (recur total)))))
          (catch DataFormatException _ nil)
          (finally (.end inf)))))))

;; -------------------------------------------------------------- checksums

(defn- crc32 [ctx b]
  (let [b (in! ctx b)]
    (.getValue (doto (CRC32.) (.update ^bytes (.-arr b) (int (.-off b)) (int (bsize b)))))))

(def ^:private fnv-offset (.longValue (BigInteger. "cbf29ce484222325" 16)))
(def ^:private fnv-prime 0x100000001b3)

(defn- fnv1a64 [ctx b]
  (let [b (in! ctx b)]
    (u64->num
     (loop [i 0 h (long fnv-offset)]
       (if (< i (bsize b))
         (recur (inc i) (unchecked-multiply (bit-xor h (long (bget b i))) (long fnv-prime)))
         h)))))

(defn- sha1 [ctx b]
  (let [b (in! ctx b)]
    (out-bytes ctx (.digest (doto (MessageDigest/getInstance "SHA-1")
                              (.update ^bytes (.-arr b) (int (.-off b)) (int (bsize b))))))))

;; ------------------------------------------------------------------ table

(def fns
  (merge
   {'u8 (reader 1 false identity)
    'i8 (reader 1 false #(sign-extend % 1))}
   (int-readers "16" 2)
   (int-readers "32" 4)
   (int-readers "64" 8)
   (float-readers)
   {'size {:impl (fn [ctx b] (rt/charge! ctx 1) (bsize (bytes! b))) :arity [1 1]}
    'slice {:impl (fn [ctx b start & [end]]
                    (rt/charge! ctx 1)
                    (let [b (bytes! b)]
                      (bslice b (long! start) (if (some? end) (long! end) (bsize b)))))
            :arity [2 3]}
    'index-of {:impl index-of :arity [2 3]}
    'utf8 (decoder StandardCharsets/UTF_8)
    'ascii {:impl ascii :arity [1 3]}
    'latin1 (decoder StandardCharsets/ISO_8859_1)
    'cp1252 (decoder (Charset/forName "windows-1252"))
    'utf16le (decoder StandardCharsets/UTF_16LE)
    'utf16be (decoder StandardCharsets/UTF_16BE)
    'encode-utf8 {:impl encode-utf8 :arity [1 1]}
    'hex-encode {:impl hex-encode :arity [1 1]}
    'hex-decode {:impl hex-decode :arity [1 1]}
    'inflate {:impl inflate :arity [2 3]}
    'crc32 {:impl crc32 :arity [1 1]}
    'fnv1a64 {:impl fnv1a64 :arity [1 1]}
    'sha1 {:impl sha1 :arity [1 1]}}))
