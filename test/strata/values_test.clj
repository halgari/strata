(ns strata.values-test
  (:require [clojure.test :refer [deftest is]]
            [strata.values :refer [wrap-bytes copy-bytes bsize bget bslice barray bytes-val?
                                 ->Handle handle? deferred? ->Deferred deferred-offset deferred-length
                                 ->LangFn lang-fn? apply-fn nan nan? canon-num canon storable? weight deep-weight]]))

(defn- err-kind [f]
  (try (f) nil (catch clojure.lang.ExceptionInfo e (:strata/error (ex-data e)))))

(deftest bytes-equality
  (let [a (wrap-bytes (byte-array [1 2 3]))
        b (bslice (wrap-bytes (byte-array [0 1 2 3])) 1 4)]
    (is (= a b))
    (is (= (hash a) (hash b)))
    (is (= (.hashCode ^Object a) (.hashCode ^Object b)))
    (is (contains? #{a} b))
    (is (= 1 (get {a 1} b)))
    (is (= 3 (bsize b)))
    (is (= [1 2 3] (vec (barray b))))
    (is (bytes-val? a))
    (is (not (bytes-val? 1)))))

(deftest bytes-copy
  (let [arr (byte-array [1 2])
        c (copy-bytes arr)]
    (aset arr 0 (byte 9))
    (is (= 1 (bget c 0)))))

(deftest bytes-bounds
  (let [b (wrap-bytes (byte-array [1 2 3]))]
    (is (nil? (bget b 99)))
    (is (nil? (bget b -1)))
    (is (nil? (bslice b 2 1)))
    (is (nil? (bslice b 0 4)))
    (is (= 0 (bsize (bslice b 3 3))))
    (is (= 255 (bget (wrap-bytes (byte-array [-1])) 0)))))

(deftest canon-nan
  (is (identical? nan (canon-num Double/NaN)))
  (is (identical? nan (canon-num (float Float/NaN))))
  (is (= 0.0 (canon-num -0.0)))
  (is (zero? (Double/compare 0.0 (canon-num -0.0))))
  (is (contains? #{(canon-num Double/NaN)} nan))
  (is (nan? nan))
  (is (not (nan? 1.0)))
  (is (= 1.5 (canon-num (float 1.5))))
  (is (= "##NaN" (pr-str nan))))

(deftest canon-ints
  (is (instance? Long (canon-num (biginteger 5))))
  (is (instance? Long (canon-num (byte 1))))
  (is (instance? Long (canon-num (short 1))))
  (is (instance? Long (canon-num (int 1))))
  (is (instance? Long (canon-num (bigint 5))))
  (is (instance? clojure.lang.BigInt (canon-num (bigint "18446744073709551615"))))
  (is (instance? clojure.lang.BigInt (canon-num (biginteger "18446744073709551615"))))
  (is (= Long/MAX_VALUE (canon-num (biginteger Long/MAX_VALUE))))
  (is (= :unsupported-value (err-kind #(canon-num 1/3))))
  (is (= :unsupported-value (err-kind #(canon-num 1.5M)))))

(deftest canon-rejects
  (is (= :unsupported-value (err-kind #(canon (Object.)))))
  (is (= :unsupported-value (err-kind #(canon 1/3))))
  (is (bytes-val? (first (:a (canon {:a [(byte-array [1])]})))))
  (is (= [1 {:a #{"x" \c 'y}} '(2)] (canon [(int 1) {:a #{"x" \c 'y}} '(2)])))
  (is (list? (canon '(1 2))))
  (is (nil? (canon nil)))
  (is (= true (canon true))))

(deftest deferred-identity
  (let [a (->Deferred 1 nil 0 4 :t (fn [_ _] 1) [:x])
        b (->Deferred 1 nil 0 4 :t (fn [_ _] 2) [:x])
        c (->Deferred 1 nil 1 4 :t (fn [_ _] 1) [:x])]
    (is (= a b))
    (is (= (hash a) (hash b)))
    (is (not= a c))
    (is (deferred? a))
    (is (= 1 (deferred-offset c)))
    (is (= 4 (deferred-length c)))))

(deftest handle-identity
  (let [a (->Handle "db" (Object.))
        b (->Handle "db" (Object.))]
    (is (handle? a))
    (is (= a b))
    (is (= (hash a) (hash b)))
    (is (not= a (->Handle "other" nil)))))

(deftest apply-fn-keyword
  (is (= 1 (apply-fn nil :a [{:a 1}])))
  (is (= 7 (apply-fn nil :b [{} 7])))
  (is (= :type-error (err-kind #(apply-fn nil 5 [1]))))
  (is (= :type-error (err-kind #(apply-fn nil :a []))))
  (is (= 3 (apply-fn nil (->LangFn 'f (fn [_ args] (count args))) [1 2 3])))
  (is (lang-fn? (->LangFn 'f identity))))

(deftest storable
  (is (false? (storable? [1 {:a (->LangFn 'f identity)}])))
  (is (false? (storable? #{(->LangFn 'f identity)})))
  (is (true? (storable? [1 {:a "x"} #{2}]))))

(deftest weights
  (is (= 3 (weight "abc")))
  (is (= 1 (weight (wrap-bytes (byte-array 10)))))
  (is (= 4 (weight (wrap-bytes (byte-array 4096)))))
  (is (= 2 (weight [1 2])))
  (is (= 2 (weight (bigint "18446744073709551615"))))
  (is (= 1 (weight 5))))

(deftest deep-weights
  (is (= 1 (deep-weight 5 100)))
  (is (= 3 (deep-weight "abc" 100)))
  (is (= 5 (deep-weight [1 2 [3]] 100)))
  (is (= 5 (deep-weight {:a 1 :b 2} 100)))
  (is (= 6 (deep-weight [(wrap-bytes (byte-array 4096)) 1] 100)))
  (let [x (reduce (fn [x _] [x x]) [1] (range 60))]
    (is (> (deep-weight x 1000) 1000) "shared structure is capped, not walked")))
