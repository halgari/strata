(ns lang.builtins.string-test
  (:require [clojure.test :refer [deftest is]]
            [lang.builtins.core :as core]
            [lang.builtins.string :as s]
            [lang.runtime :as rt]))

(defn call* [ctx sym & args]
  (let [{:keys [impl arity]} (get s/fns sym)]
    (assert impl (str "missing " sym))
    (let [[mn mx] arity]
      (assert (and (>= (count args) mn) (or (nil? mx) (<= (count args) mx))) (str "arity " sym)))
    (apply impl ctx args)))

(defn call [sym & args] (apply call* (rt/make-ctx {}) sym args))

(defn kind [f]
  (try (f) nil (catch clojure.lang.ExceptionInfo e (:lang/error (ex-data e)))))

(deftest disjoint-from-core
  (is (empty? (clojure.set/intersection (set (keys s/fns)) (set (keys core/fns))))))

(deftest split-literal
  (is (= ["a" "b" "c"] (call 'split "a.b.c" ".")))
  (is (= ["a" "" ""] (call 'split "a.." ".")))
  (is (vector? (call 'split "a" ","))))

(deftest basics
  (is (= ["a" "b"] (call 'split-lines "a\nb")))
  (is (= "a,b" (call 'join "," ["a" "b"])))
  (is (= "ab1" (call 'join ["a" "b" 1])))
  (is (= "x" (call 'trim "  x ")))
  (is (= "x " (call 'triml "  x ")))
  (is (= "  x" (call 'trimr "  x ")))
  (is (= "xxa" (call 'pad-left "a" 3 \x)))
  (is (= "axx" (call 'pad-right "a" 3 "x")))
  (is (= "abc" (call 'pad-left "abc" 2 \x)))
  (is (true? (call 'blank? " ")))
  (is (true? (call 'starts-with? "abc" "ab")))
  (is (true? (call 'ends-with? "abc" "bc")))
  (is (true? (call 'includes? "abc" "b")))
  (is (= 1 (call 'index-of "abcb" "b")))
  (is (= 3 (call 'last-index-of "abcb" "b")))
  (is (nil? (call 'index-of "abc" "z")))
  (is (= "bc" (call 'subs "abc" 1)))
  (is (= "b" (call 'subs "abc" 1 2)))
  (is (nil? (call 'subs "abc" 2 9)))
  (is (= "a-c-" (call 'replace "a.c." "." "-")))
  (is (= "ab" (call 'lower-case "AB")))
  (is (= "AB" (call 'upper-case "ab")))
  (is (= [\a \b] (call 'chars "ab"))))

(deftest regex
  (is (= "12" (call 're-find "\\d+" "ab12")))
  (is (= ["a1" "a" "1"] (call 're-find "(\\w)(\\d)" "a1")))
  (is (nil? (call 're-find "\\d" "ab")))
  (is (= "ab" (call 're-matches "ab" "ab")))
  (is (nil? (call 're-matches "a" "ab")))
  (is (= ["1" "22"] (call 're-seq "\\d+" "1a22")))
  (is (= ["a" "b" ""] (call 're-split "," "a,b,")))
  (is (= :bad-regex (kind #(call 're-find "(" "x"))))
  (is (= :type-error (kind #(call 're-find 1 "x")))))

(deftest pad-guard
  (let [t0 (System/nanoTime)]
    (is (= :value-too-large (kind #(call 'pad-left "" 1000000000 \x))))
    (is (< (/ (- (System/nanoTime) t0) 1e6) 50))))

(deftest regex-fuel
  (let [input (apply str (repeat 5000 "a"))
        run (fn [re] (kind #(rt/run-isolated
                             (fn [] (call* (rt/make-ctx {:limits {:fuel 100000}}) 're-matches re input)))))]
    ;; the JDK memoizes (a|aa)*b, so it may finish within budget; it must never raise a raw error
    (is (contains? #{nil :fuel-exhausted :stack-exhausted} (run "(a|aa)*b")))
    (is (#{:fuel-exhausted :stack-exhausted} (run "(a+)+b")))))

(deftest regex-length
  (is (= :regex-too-long (kind #(call 're-find (apply str (repeat 2000 "a")) "a")))))
