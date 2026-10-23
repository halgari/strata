(ns lang.resource-test
  (:require [clojure.test :refer [deftest is]]
            [lang.resource :as r]
            [lang.runtime :as rt]
            [lang.values :as v])
  (:import (java.io File)
           (java.nio.file Files)))

(defn- ba [& xs] (byte-array (map unchecked-byte xs)))
(defn- vec* [b] (vec (map #(bit-and 0xff %) b)))
(defn- bv [b] (vec* (v/barray b)))

(defn- counting [res n]
  (reify r/Resource
    (size [_] (r/size res))
    (read-range [_ off len] (swap! n inc) (r/read-range res off len))))

(deftest bytes-resource-read
  (let [res (r/bytes-resource (ba 1 2 3 4))]
    (is (= [2 3] (vec* (r/read-range res 1 2))))
    (is (nil? (r/read-range res 3 2)))
    (is (nil? (r/read-range res -1 2)))
    (is (= 4 (r/size res)))))

(deftest bytes-resource-defensive-copy
  (let [a (ba 1 2 3) res (r/bytes-resource a)]
    (aset a 0 (byte 9))
    (is (= [1] (vec* (r/read-range res 0 1))))))

(deftest file-resource-read
  (let [f (File/createTempFile "res" ".bin")
        data (byte-array (map #(unchecked-byte (mod % 251)) (range 100000)))]
    (try
      (Files/write (.toPath f) data (make-array java.nio.file.OpenOption 0))
      (let [res (r/file-resource f)]
        (is (= 100000 (r/size res)))
        (is (= (vec* (java.util.Arrays/copyOfRange data 99990 100000))
               (vec* (r/read-range res 99990 10))))
        (is (nil? (r/read-range res 99990 11)))
        (is (= (vec* (java.util.Arrays/copyOfRange data 500 1500))
               (vec* (r/read-range res 500 1000)))))
      (finally (.delete f)))))

(defn- ctx-with [limits res]
  (rt/make-ctx {:limits limits :resources {"r" res}}))

(deftest handle-page-cache
  (let [n (atom 0)
        data (byte-array (range 100))
        res (counting (r/bytes-resource data) n)
        ctx (ctx-with {:page-size 16} res)
        h (r/open-handle ctx "r")]
    (is (= (vec (range 10 40)) (bv (r/src-read h ctx 10 30))))
    (reset! n 0)
    (dotimes [_ 10] (r/src-read h ctx 70 1))
    (is (= 1 @n))
    (is (= 100 (r/src-size h ctx)))
    (is (= [:resource "r"] (r/src-id h)))))

(deftest cache-bounded
  (let [n (atom 0)
        res (counting (r/bytes-resource (byte-array 100)) n)
        ctx (ctx-with {:page-size 16 :page-cache-bytes 32} res)
        h (r/open-handle ctx "r")
        rd #(r/src-read h ctx (* 16 %) 1)]
    (rd 0) (rd 1) (rd 0)
    (is (= 2 @n))
    (rd 2)                              ; evicts page 1, the least recently used
    (is (= 3 @n))
    (rd 0)
    (is (= 3 @n))
    (rd 1)
    (is (= 4 @n))))

(deftest cross-page-read-charged
  (let [ctx (rt/make-ctx {:limits {:page-size 16 :max-bytes 20}
                          :resources {"r" (r/bytes-resource (byte-array 100))}})
        h (r/open-handle ctx "r")]
    (is (some? (r/src-read h ctx 0 10)))   ; same-page slice is uncharged
    (is (= :bytes-exhausted
           (try (r/src-read h ctx 0 40) nil
                (catch clojure.lang.ExceptionInfo e (:lang/error (ex-data e))))))))

(deftest open-handle-missing
  (is (nil? (r/open-handle (rt/make-ctx {}) "nope"))))

(deftest eof-read
  (let [res (r/bytes-resource (byte-array 40))
        ctx (ctx-with {:page-size 16} res)
        h (r/open-handle ctx "r")]
    (is (= 0 (v/bsize (r/src-read h ctx 40 0))))
    (is (nil? (r/src-read h ctx 40 1)))
    (is (= 8 (v/bsize (r/src-read h ctx 32 8))))
    (is (nil? (r/src-read h ctx -1 1)))))

(deftest bytes-source
  (let [b (v/wrap-bytes (ba 1 2 3 4))
        ctx (rt/make-ctx {})]
    (is (= 4 (r/src-size b ctx)))
    (is (= [2 3] (bv (r/src-read b ctx 1 2))))
    (is (nil? (r/src-read b ctx 3 2)))
    (is (= b (r/src-id b)))))

(deftest short-reads-do-not-pin-pages
  (let [res (r/bytes-resource (byte-array 200000))
        ctx (rt/make-ctx {:resources {"x" res} :limits {:page-size 65536}})
        h (r/open-handle ctx "x")
        small (r/src-read h ctx 100 8)
        large (r/src-read h ctx 100 30000)]
    (is (= 8 (alength ^bytes (.-arr ^lang.values.Bytes small))) "short read is copied out of the page")
    (is (= 65536 (alength ^bytes (.-arr ^lang.values.Bytes large))) "long single-page read stays zero-copy")
    (is (= 30008 (aget ^longs (:bytes ctx) 0)) "both reads are charged")))

(deftest src-id-is-content-identity
  (let [a (v/wrap-bytes (ba 1 2 3 4))
        b (v/wrap-bytes (ba 4 3 2 1))
        a2 (v/wrap-bytes (ba 1 2 3 4))]
    (is (not= (r/src-id a) (r/src-id b)) "same size, different content")
    (is (= (r/src-id a) (r/src-id a2)) "equal content shares an identity")
    (is (= [:resource "x"] (r/src-id (v/->Handle "x" nil))))))
