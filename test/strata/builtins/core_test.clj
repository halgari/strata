(ns strata.builtins.core-test
  (:require [clojure.test :refer [deftest is testing]]
            [strata.builtins.core :as core]
            [strata.runtime :as rt]
            [strata.values :as v :refer [nan]]))

(defn call [sym & args]
  (let [{:keys [impl arity]} (get core/fns sym)]
    (assert impl (str "missing " sym))
    (let [[mn mx] arity]
      (assert (and (>= (count args) mn) (or (nil? mx) (<= (count args) mx))) (str "arity " sym)))
    (apply impl (rt/make-ctx {}) args)))

(defn kind [f]
  (try (f) nil (catch clojure.lang.ExceptionInfo e (:strata/error (ex-data e)))))

(deftest promotes
  (is (= 9223372036854775808N (call '+ Long/MAX_VALUE 1)))
  (is (instance? clojure.lang.BigInt (call '+ Long/MAX_VALUE 1)))
  (is (instance? Long (call '- 9223372036854775808N 1)))
  (is (= 0 (call '+)))
  (is (= -5 (call '- 5)))
  (is (= 6 (call '* 1 2 3)))
  (is (= 9223372036854775808N (call 'abs Long/MIN_VALUE)))
  (is (= 9223372036854775808N (call 'quot Long/MIN_VALUE -1)))
  (is (= 2 (call 'min 3 2 5)))
  (is (= 5 (call 'max 3 2 5)))
  (is (= 1 (call 'mod -3 2)))
  (is (= -1 (call 'rem -3 2))))

(deftest int-bound
  (is (= :int-too-large (kind #(call '* (bigint (.pow (biginteger 2) 3000)) (bigint (.pow (biginteger 2) 3000)))))))

(deftest division
  (is (= 2 (call '/ 6 3)))
  (is (instance? Long (call '/ 6 3)))
  (is (= 0.5 (call '/ 1 2)))
  (is (= :arithmetic-error (kind #(call '/ 1 0))))
  (is (= :arithmetic-error (kind #(call 'quot 1 0))))
  (is (= :arithmetic-error (kind #(call 'mod 1 0)))))

(deftest u64-wrap
  (let [a 0xcbf29ce484222325 b 0x100000001b3
        expect (mod (* 0xcbf29ce484222325N 0x100000001b3N) 18446744073709551616N)]
    (is (= expect (call 'u64* a b)))
    (is (= (call 'u64+ 18446744073709551615N 1) 0))
    (is (instance? Long (call 'u64+ 18446744073709551615N 1)))
    (is (= 18446744073709551615N (call 'u64- 0 1)))
    (is (instance? clojure.lang.BigInt (call 'u64- 0 1)))))

(deftest shift-guard
  (let [t0 (System/nanoTime)
        k (kind #(call 'bit-shift-left 1 100000))]
    (is (= :int-too-large k))
    (is (< (/ (- (System/nanoTime) t0) 1e6) 50)))
  (is (= 8 (call 'bit-shift-left 1 3)))
  (is (= 2 (call 'bit-shift-right 8 2)))
  (is (= 255 (call 'unsigned-bit-shift-right -1 56))))

(deftest nan-handling
  (is (v/nan? (call '+ nan 1)))
  (is (true? (call '= nan nan)))
  (is (false? (call 'not= nan nan)))
  (is (false? (call '< nan 1)))
  (is (false? (call '>= 1 nan)))
  (is (v/nan? (call 'max 1 nan))))

(deftest bits
  (is (true? (call 'bit-test 0x40000 18)))
  (is (false? (call 'bit-test 0x40000 17)))
  (is (= 255 (call 'bit-and 18446744073709551615N 0xff)))
  (is (= 6 (call 'bit-xor 5 3)))
  (is (= 7 (call 'bit-or 5 3)))
  (is (= -1 (call 'bit-not 0))))

(deftest comparisons
  (is (true? (call '< 1 2 3)))
  (is (false? (call '< 1 3 2)))
  (is (true? (call '= 5 5N)))
  (is (false? (call '= 1 1.0)))
  (is (neg? (call 'compare 1 2)))
  (is (= :type-error (kind #(call '< "a" 1))))
  (is (true? (call 'zero? 0)))
  (is (true? (call 'even? 4)))
  (is (true? (call 'odd? 18446744073709551615N)))
  (is (true? (call 'pos? 1.5)))
  (is (true? (call 'neg? -1))))

(deftest preds
  (is (true? (call 'nil? nil)))
  (is (true? (call 'some? 1)))
  (is (true? (call 'number? nan)))
  (is (true? (call 'integer? 5N)))
  (is (false? (call 'integer? 5.0)))
  (is (true? (call 'bytes? (v/wrap-bytes (byte-array 1)))))
  (is (true? (call 'coll? [1])))
  (is (false? (call 'not 1)))
  (is (= 3 (call 'identity 3))))

(deftest misc
  (is (nil? (call 'parse-long "x")))
  (is (= 42 (call 'parse-long "42")))
  (is (nil? (call 'parse-long "99999999999999999999")))
  (is (= 1.5 (call 'parse-double "1.5")))
  (is (nil? (call 'parse-double "zz")))
  (is (= :type-error (kind #(call 'parse-long 1))))
  (is (= "a1:b" (call 'str "a" 1 :b)) "keyword str has colon")
  (is (= "##NaN" (call 'str nan)))
  (is (= "" (call 'str nil)))
  (is (= "[1 \"x\" ##NaN]" (call 'str [1 "x" nan])))
  (is (= "foo" (call 'name :foo)))
  (is (= :foo (call 'keyword "foo")))
  (is (= :a/b (call 'keyword "a" "b")))
  (is (= :type-error (kind #(call 'name 1)))))

(deftest str-size
  (let [ctx (rt/make-ctx {:limits {:max-value-size 10}})]
    (is (= :value-too-large
           (kind #((:impl (core/fns 'str)) ctx "abcdefgh" "ijklmnop"))))))

(deftest fuel-by-size
  (let [ctx (rt/make-ctx {:limits {:fuel 5}})]
    (is (= :fuel-exhausted
           (kind #((:impl (core/fns '+)) ctx 1 1 1 1 1 1 1 1))))))

(deftest fix-round-1
  (is (= 4 (call 'dec 5)))
  (is (= 6 (call 'inc 5)))
  (is (instance? Long (call 'dec 5)))
  (is (instance? clojure.lang.BigInt (call 'dec Long/MIN_VALUE)))
  (is (= -9223372036854775809N (call 'dec Long/MIN_VALUE)))
  (is (instance? Long (call 'inc -9223372036854775809N)))
  (is (zero? (call '+ 0.0 -0.0)))
  (is (= "0.0" (str (call '* -1.0 0.0))) "-0.0 canonicalized")
  (let [t0 (System/nanoTime)]
    (is (= :arithmetic-error (kind #(call 'bit-shift-right 1 -2147483647))))
    (is (= :arithmetic-error (kind #(call 'bit-shift-left 1 -1))))
    (is (= :arithmetic-error (kind #(call 'unsigned-bit-shift-right 1 -1))))
    (is (< (/ (- (System/nanoTime) t0) 1e6) 50)))
  (is (= 0 (call 'bit-shift-left 0 100000)))
  (is (= 0 (call 'bit-shift-left 0 (bigint (.pow (biginteger 2) 70)))))
  (doseq [n [(bigint (.pow (biginteger 2) 70)) Long/MAX_VALUE]]
    (is (= :int-too-large (kind #(call 'bit-shift-left 1 n))))
    (is (= 0 (call 'bit-shift-right 5 n)))
    (is (= -1 (call 'bit-shift-right -5 n)))
    (is (= 0 (call 'unsigned-bit-shift-right 5 n)))
    (is (false? (call 'bit-test 5 n)))
    (is (true? (call 'bit-test -5 n)))))
