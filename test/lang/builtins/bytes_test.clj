(ns lang.builtins.bytes-test
  (:require [clojure.set]
            [clojure.test :refer [deftest is]]
            [lang.builtins.bytes :as b]
            [lang.builtins.core :as core]
            [lang.runtime :as rt]
            [lang.values :as v])
  (:import (java.util.zip Deflater)))

(defn call* [ctx sym & args]
  (let [{:keys [impl arity]} (get b/fns sym)]
    (assert impl (str "missing " sym))
    (let [[mn mx] arity]
      (assert (and (>= (count args) mn) (or (nil? mx) (<= (count args) mx))) (str "arity " sym)))
    (apply impl ctx args)))

(defn call [sym & args] (apply call* (rt/make-ctx {}) sym args))

(defn kind [f]
  (try (f) nil (catch clojure.lang.ExceptionInfo e (:lang/error (ex-data e)))))

(defn bytes* [xs] (v/wrap-bytes (byte-array (map unchecked-byte xs))))

(defn deflate ^bytes [^bytes data nowrap?]
  (let [d (Deflater. Deflater/DEFAULT_COMPRESSION (boolean nowrap?))
        out (java.io.ByteArrayOutputStream.)
        buf (byte-array 4096)]
    (.setInput d data)
    (.finish d)
    (while (not (.finished d))
      (.write out buf 0 (.deflate d buf)))
    (.end d)
    (.toByteArray out)))

(deftest disjoint-from-core
  (is (empty? (clojure.set/intersection (set (keys b/fns)) (set (keys core/fns))))))

(deftest reads
  (let [bs (bytes* [1 2 3 4])]
    (is (= 0x04030201 (call 'u32-le bs 0)))
    (is (= 0x01020304 (call 'u32-be bs 0)))
    (is (nil? (call 'u32-le bs 1)))
    (is (nil? (call 'u64-le bs 0)))
    (is (nil? (call 'u8 bs -1)))
    (is (= 0x0201 (call 'u16-le bs 0)))
    (is (= 4 (call 'size bs)))
    (is (= (bytes* [2 3]) (call 'slice bs 1 3)))
    (is (nil? (call 'slice bs 3 9)))
    (is (= 2 (call 'index-of bs 3)))
    (is (= 1 (call 'index-of bs (bytes* [2 3]))))
    (is (= :type-error (kind #(call 'u8 "x" 0))))))

(deftest signed
  (let [bs (bytes* [0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff])]
    (is (= -1 (call 'i8 bs 0)))
    (is (= -1 (call 'i16-be bs 0)))
    (is (= -1 (call 'i32-le bs 0)))
    (is (= -1 (call 'i64-le bs 0)))
    (is (= 255 (call 'u8 bs 0)))))

(deftest u64
  (let [bs (bytes* (repeat 8 0xff))]
    (is (= 18446744073709551615N (call 'u64-le bs 0)))
    (is (= 18446744073709551615N (call 'u64-be bs 0)))
    (is (= 5 (call 'u64-le (bytes* [5 0 0 0 0 0 0 0]) 0)))))

(deftest float-reads
  (is (identical? v/nan (call 'f32-le (bytes* [0 0 0xc0 0x7f]) 0)))
  (is (= 1.5 (call 'f32-le (bytes* [0 0 0xc0 0x3f]) 0)))
  (is (= 1.0 (call 'f64-be (bytes* [0x3f 0xf0 0 0 0 0 0 0]) 0)))
  (is (= 0.0 (call 'f64-be (bytes* [0x80 0 0 0 0 0 0 0]) 0))))

(deftest cp1252-high-range
  (is (= "€Ÿ" (call 'cp1252 (bytes* [0x80 0x9f]))))
  (is (nil? (call 'utf8 (bytes* [0xc3]))))
  (is (nil? (call 'ascii (bytes* [0x80]))))
  (is (= "ab" (call 'ascii (bytes* [0x61 0x62]))))
  (is (= "é" (call 'latin1 (bytes* [0xe9]))))
  (is (= "b" (call 'utf8 (bytes* [0x61 0x62 0x63]) 1 2)))
  (is (nil? (call 'utf8 (bytes* [0x61]) 0 5)))
  (is (= "a" (call 'utf16le (bytes* [0x61 0]))))
  (is (= "a" (call 'utf16be (bytes* [0 0x61]))))
  (is (nil? (call 'utf16le (bytes* [0x61]))))
  (is (= (bytes* [0x61 0xc3 0xa9]) (call 'encode-utf8 "aé"))))

(deftest inflate
  (let [data (byte-array (map #(unchecked-byte (mod % 251)) (range 10240)))
        z (v/wrap-bytes (deflate data false))
        raw (v/wrap-bytes (deflate data true))]
    (is (= (v/wrap-bytes data) (call 'inflate z 100000)))
    (is (= (v/wrap-bytes data) (call 'inflate raw 100000 :raw)))
    (is (nil? (call 'inflate z 100)))
    (is (nil? (call 'inflate (bytes* [1 2 3 4 5]) 100)))
    (is (nil? (call 'inflate (v/bslice z 0 20) 100000)))
    (is (nil? (call 'inflate raw 100000)))
    (is (= :type-error (kind #(call 'inflate z "x"))))
    (let [ctx (rt/make-ctx {:limits {:max-inflate 50}})]
      (is (nil? (call* ctx 'inflate z 100000))))))

(deftest inflate-bomb
  (let [z (v/wrap-bytes (deflate (byte-array 1000000) false))
        ctx (rt/make-ctx {})
        t0 (System/nanoTime)]
    (is (nil? (call* ctx 'inflate z 1000)))
    (is (< (/ (- (System/nanoTime) t0) 1e6) 100))
    (is (< (aget ^longs (:bytes ctx) 0) 65536))))

(deftest hashes
  (is (= 0xaf63dc4c8601ec8cN (call 'fnv1a64 (call 'encode-utf8 "a"))))
  (is (= 0xCBF43926 (call 'crc32 (call 'encode-utf8 "123456789"))))
  (is (= "a9993e364706816aba3e25717850c26c9cd0d89d"
         (call 'hex-encode (call 'sha1 (call 'encode-utf8 "abc"))))))

(deftest hex
  (is (= "ab01" (call 'hex-encode (bytes* [0xab 1]))))
  (is (= (bytes* [0xab 1]) (call 'hex-decode "aB01")))
  (is (nil? (call 'hex-decode "zz")))
  (is (nil? (call 'hex-decode "abc"))))
