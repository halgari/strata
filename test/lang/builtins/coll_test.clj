(ns lang.builtins.coll-test
  (:require [clojure.set]
            [clojure.test :refer [deftest is testing]]
            [lang.builtins.coll :as coll]
            [lang.builtins.core :as core]
            [lang.runtime :as rt]
            [lang.values :as v :refer [->LangFn]]))

(defn call* [ctx sym & args]
  (let [{:keys [impl arity]} (get coll/fns sym)]
    (assert impl (str "missing " sym))
    (let [[mn mx] arity]
      (assert (and (>= (count args) mn) (or (nil? mx) (<= (count args) mx))) (str "arity " sym)))
    (apply impl ctx args)))

(defn call [sym & args] (apply call* (rt/make-ctx {}) sym args))

(defn kind [f]
  (try (f) nil (catch clojure.lang.ExceptionInfo e (:lang/error (ex-data e)))))

(def inc-fn (->LangFn 'inc (fn [_ [x]] (inc x))))
(def plus-fn (->LangFn '+ (fn [_ args] (apply + args))))
(def even-fn (->LangFn 'even? (fn [_ [x]] (even? x))))

(deftest disjoint-from-core
  (is (empty? (clojure.set/intersection (set (keys coll/fns)) (set (keys core/fns))))))

(deftest eager
  (is (= [2 3] (call 'map inc-fn [1 2])))
  (is (vector? (call 'map inc-fn [1 2])))
  (is (vector? (call 'filter even-fn '(1 2 3 4))))
  (is (= [2 4] (call 'filter even-fn [1 2 3 4])))
  (is (= [1 3] (call 'remove even-fn [1 2 3 4]))))

(deftest range-guard
  (let [t0 (System/nanoTime)]
    (is (= :value-too-large (kind #(call 'range 1000000000))))
    (is (< (/ (- (System/nanoTime) t0) 1e6) 50))))

(deftest range-forms
  (is (= [0 1 2] (call 'range 3)))
  (is (= [2 3] (call 'range 2 4)))
  (is (= [5 3 1] (call 'range 5 0 -2)))
  (is (= [] (call 'range 0)))
  (is (= :arithmetic-error (kind #(call 'range 0 5 0))))
  (is (= :type-error (kind #(call 'range "a")))))

(deftest fuel-per-element
  (let [ctx (rt/make-ctx {:limits {:fuel 100}})]
    (is (= :fuel-exhausted (kind #(call* ctx 'range 1000))))))

(deftest sort-total-order
  (is (= [nil 1.0 3 "a" :k] (call 'sort [3 "a" 1.0 :k nil])))
  (is (vector? (call 'sort [])))
  (is (= [{:a 1} {:a 2}] (call 'sort-by :a [{:a 2} {:a 1}]))))

(deftest keyword-fns
  (is (= [1 2] (call 'map :a [{:a 1} {:a 2}]))))

(deftest apply-fn
  (is (= 6 (call 'apply plus-fn [1 2 3])))
  (is (= 6 (call 'apply plus-fn 1 [2 3]))))

(deftest nth-safe
  (is (nil? (call 'nth [1] 5)))
  (is (= :d (call 'nth [1] 5 :d)))
  (is (= 1 (call 'nth [1] 0)))
  (is (nil? (call 'nth [1] -1)))
  (is (= :type-error (kind #(call 'nth 5 0)))))

(deftest get-fns
  (is (nil? (call 'get 5 :a)))
  (is (= 1 (call 'get {:a 1} :a)))
  (is (= :x (call 'get {} :a :x)))
  (is (= 2 (call 'get [1 2] 1)))
  (is (= 1 (call 'get-in {:a [0 1]} [:a 1])))
  (is (= {:a {:b 1}} (call 'assoc-in {} [:a :b] 1)))
  (is (= {:a 2} (call 'update {:a 1} :a inc-fn)))
  (is (= [1 5] (call 'assoc [1 2] 1 5)))
  (is (= :type-error (kind #(call 'assoc [1] 5 0)))))

(deftest collections
  (is (= {:b 2} (call 'dissoc {:a 1 :b 2} :a)))
  (is (= [1 2 3] (call 'conj [1] 2 3)))
  (is (= {:a 1 :b 2} (call 'conj {:a 1} [:b 2])))
  (is (= [1 2 3] (call 'into [1] [2 3])))
  (is (= 3 (call 'count [1 2 3])))
  (is (= 2 (call 'count "ab")))
  (is (= 0 (call 'count nil)))
  (is (= [1 2 1] [(call 'first [1 2]) (call 'second [1 2]) (call 'last [2 1])]))
  (is (= [2 3] (call 'rest [1 2 3])))
  (is (nil? (call 'next [1])))
  (is (= 2 (call 'peek [1 2])))
  (is (= [2] (call 'subvec [1 2 3] 1 2)))
  (is (= [2 3] (call 'subvec [1 2 3] 1)))
  (is (= :type-error (kind #(call 'subvec [1 2 3] 2 9))))
  (is (= [:a] (call 'keys {:a 1})))
  (is (= [1] (call 'vals {:a 1})))
  (is (true? (call 'contains? {:a nil} :a)))
  (is (true? (call 'empty? [])))
  (is (nil? (call 'not-empty [])))
  (is (= #{1 2} (call 'set [1 2 1])))
  (is (= {:a 1} (call 'hash-map :a 1)))
  (is (= [1 2] (call 'vector 1 2)))
  (is (= '(1 2) (call 'list 1 2)))
  (is (= {:a 1 :b 2} (call 'merge {:a 1} {:b 2})))
  (is (= {:a 1} (call 'select-keys {:a 1 :b 2} [:a])))
  (is (= {:a 1} (call 'zipmap [:a] [1 2])))
  (is (= {1 2 2 1} (call 'frequencies [1 2 1]))))

(deftest sequences
  (is (= [[0 :a] [1 :b]] (call 'map-indexed (->LangFn 'f (fn [_ args] (vec args))) [:a :b])))
  (is (= [1 1 2 2] (call 'mapcat (->LangFn 'f (fn [_ [x]] [x x])) [1 2])))
  (is (= [2 3] (call 'keep (->LangFn 'f (fn [_ [x]] (when (> x 1) x))) [1 2 3]) ) "keep drops nils; result is [2 3]")
  (is (= 6 (call 'reduce plus-fn [1 2 3])))
  (is (= 16 (call 'reduce plus-fn 10 [1 2 3])))
  (is (= 0 (call (quote reduce) plus-fn [])))
  (is (= 3 (call 'reduce-kv (->LangFn 'f (fn [_ [a _k v]] (+ a v))) 0 {:a 1 :b 2})))
  (is (= [1 2] (call 'take 2 [1 2 3])))
  (is (= [3] (call 'drop 2 [1 2 3])))
  (is (= [2] (call 'take-while even-fn [2 3 4])))
  (is (= [3 4] (call 'drop-while even-fn [2 3 4])))
  (is (= [1 2 3] (call 'concat [1] [2 3])))
  (is (= [2 1] (call 'reverse [1 2])))
  (is (= {true [2] false [1]} (call 'group-by even-fn [1 2])))
  (is (= [[1 2] [3 4]] (call 'partition 2 [1 2 3 4 5])))
  (is (= [[1 2] [3]] (call 'partition-all 2 [1 2 3])))
  (is (= [1 2 3] (call 'distinct [1 2 1 3 2])))
  (is (= 4 (call 'some (->LangFn 'f (fn [_ [x]] (when (even? x) (* 2 x)))) [1 2])))
  (is (true? (call 'every? even-fn [2 4])))
  (is (= [1 :a 2 :b] (call 'interleave [1 2] [:a :b]))))

(deftest type-errors
  (is (= :type-error (kind #(call 'map inc-fn 5))))
  (is (= :type-error (kind #(call 'map 5 [1]))))
  (is (= :type-error (kind #(call 'first 5))))
  (is (= :type-error (kind #(call 'conj 5 1)))))
