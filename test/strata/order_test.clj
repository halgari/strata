(ns strata.order-test
  (:require [clojure.test :refer [deftest is]]
            [clojure.test.check.clojure-test :refer [defspec]]
            [clojure.test.check.generators :as gen]
            [clojure.test.check.properties :as prop]
            [strata.order :refer [compare-values sort-values]]
            [strata.values :refer [nan canon-num]]))

(deftest ranks
  (is (= [nil true 1 \c "s" :k 'sym [1] {} #{}]
         (sort-values nil [:k "s" 1 nil true \c 'sym [1] {} #{}]))))

(deftest numeric-ties
  (is (neg? (compare-values nil 5 5.0)))
  (is (neg? (compare-values nil 5 5N)))
  (is (neg? (compare-values nil 5N 5.0)))
  (is (neg? (compare-values nil 1 2.5)))
  (is (pos? (compare-values nil nan 1e300)))
  (is (zero? (compare-values nil nan nan)))
  (is (neg? (compare-values nil 1e300 Double/POSITIVE_INFINITY)))
  (is (pos? (compare-values nil 9223372036854775807 9.223372036854775E18))))

(deftest maps
  (is (neg? (compare-values nil {:a 1} {:a 2}))))

(deftest misc
  (is (neg? (compare-values nil :b :a/a)) "nil namespace first")
  (is (neg? (compare-values nil [1 2] [1 2 3])))
  (is (zero? (compare-values nil [1] '(1))))
  (is (not (zero? (compare-values nil {1 :a} {1.0 :a}))))
  (is (= :type-error (try (compare-values nil (strata.values/->LangFn 'f nil) 1)
                          (catch clojure.lang.ExceptionInfo e (:strata/error (ex-data e)))))))

(def gen-val
  (gen/recursive-gen
   (fn [inner]
     (gen/one-of [(gen/vector inner 0 4)
                  (gen/map inner inner {:max-elements 3})
                  (gen/set inner {:max-elements 3})]))
   (gen/one-of [gen/small-integer
                (gen/fmap canon-num (gen/double* {:NaN? false :infinite? true}))
                (gen/return nan)
                gen/string-alphanumeric
                gen/keyword
                gen/boolean
                (gen/return nil)])))

(defn- cmp [a b] (compare-values nil a b))
(defn- sgn [n] (Long/signum (long n)))

(defspec antisymmetric-transitive 200
  (prop/for-all [a gen-val b gen-val c gen-val]
    (and (= (sgn (cmp a b)) (- (sgn (cmp b a))))
         (= (zero? (cmp a b)) (= a b))
         (if (and (<= (cmp a b) 0) (<= (cmp b c) 0)) (<= (cmp a c) 0) true))))
