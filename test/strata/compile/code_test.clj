(ns strata.compile.code-test
  (:require [clojure.test :refer [deftest is]]
            [strata.runtime :as rt]
            [strata.test-util :refer [run-code]]
            [strata.values :as v]))

(defn- kind [f]
  (try (f) nil (catch clojure.lang.ExceptionInfo e (:strata/error (ex-data e)))))

(deftest factorial
  (let [fs '[(defn fact [n] (if (zero? n) 1 (* n (fact (dec n)))))]]
    (is (= 2432902008176640000 (run-code fs '(fact 20))))
    (is (instance? clojure.lang.BigInt (run-code fs '(fact 25))))))

(deftest loop-recur
  (is (= 45 (run-code [] '(loop [i 0 acc 0] (if (< i 10) (recur (inc i) (+ acc i)) acc))))))

(deftest fn-recur-and-rest
  (is (= 10 (run-code '[(defn sum [n acc] (if (zero? n) acc (recur (dec n) (+ acc n))))]
                      '(sum 4 0))))
  (is (= [1 [2 3]] (run-code '[(defn f [a & more] [a more])] '(f 1 2 3))))
  (is (= [1 nil] (run-code '[(defn f [a & more] [a more])] '(f 1))))
  (is (= :two (run-code '[(defn g ([x] :one) ([x y] :two))] '(g 1 2)))))

(deftest closures
  (let [f (run-code [] '((fn [x] (fn [y] (+ x y))) 1))]
    (is (= 3 (v/apply-fn (rt/make-ctx {}) f [2]))))
  (is (= 120 (run-code [] '((fn fact [n] (if (zero? n) 1 (* n (fact (dec n))))) 5))))
  (is (= [2 3] (run-code [] '(map (fn [x] (inc x)) [1 2])))))

(deftest forward-ref
  (is (= 7 (run-code '[(defn a [] (b)) (defn b [] 7)] '(a)))))

(deftest mutual-recursion
  (let [fs '[(defn even2? [n] (if (zero? n) true (odd2? (dec n))))
             (defn odd2? [n] (if (zero? n) false (even2? (dec n))))]]
    (is (true? (run-code fs '(even2? 100))))
    (is (false? (run-code fs '(odd2? 100))))))

(deftest fuel
  (is (= :fuel-exhausted
         (kind #(run-code [] '(loop [] (recur)) {:limits {:fuel 10000}})))))

(deftest depth
  (is (= :depth-exceeded
         (rt/run-isolated
          #(kind (fn [] (run-code '[(defn r [n] (inc (r n)))] '(r 1))))))))

(deftest destructure-runtime
  (is (= 5 (run-code [] '(let [{:keys [a] :or {a 5}} {}] a))))
  (is (= [1 [3]] (run-code [] '(let [[a _ & r] [1 2 3]] [a r])))))

(deftest case-forms
  (let [fs '[(defn c [x] (case x 1 :one (2 3) :few :many))]]
    (is (= :one (run-code fs '(c 1))))
    (is (= :few (run-code fs '(c 3))))
    (is (= :many (run-code fs '(c 9))))))

(deftest misc
  (is (= :a (run-code [] '(or nil false :a))))
  (is (= 2 (run-code [] '(and 1 2))))
  (is (= 1 (run-code [] '(:a {:a 1}))))
  (is (= 9 (run-code [] '(:a {} 9))))
  (is (= [3 2] (run-code '[(defn f [x] [(inc x) x])] '(let [x 2] (f x)))))
  (is (= :arity-error (kind #(run-code '[(defn f ([x] x) ([x y & z] x))] '((fn [] (f 1)) 1)))))
  (is (= :type-error (kind #(run-code [] '(let [f 5] (f 1))))))
  (is (= :internal-error (kind #(run-code [] '(parse t 1))))))

(deftest builtin-driven-calls-are-bounded
  (is (= :depth-exceeded
         (rt/run-isolated #(kind (fn [] (run-code [] '((fn f [x] (map f [x])) 1)))))))
  (is (= :depth-exceeded
         (rt/run-isolated #(kind (fn [] (run-code '[(defn r [x] (map r [x]))] '(r 1))))))))

(deftest user-fn-calls-charge-fuel
  (is (= :fuel-exhausted
         (kind #(run-code [] '(let [f (fn [x] x)] (loop [i 0] (if (< i 1000) (do (map f [1]) (recur (inc i))) i)))
                          {:limits {:fuel 500}})))))

(deftest case-no-match
  (is (= :no-matching-clause (kind #(run-code [] '(case 5 1 :a 2 :b))))))
