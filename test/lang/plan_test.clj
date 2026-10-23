(ns lang.plan-test
  (:require [clojure.test :refer [deftest is]]
            [lang.analyze.rule :as r]
            [lang.builtins :as b]
            [lang.ns :as ns]
            [lang.plan :as p]))

(defn- def-entry [f]
  (case (first f)
    defrule {:kinds #{:relation} :sub :rule :form f}
    defrel {:kinds #{:relation} :sub :defrel :form f}
    defn {:kinds #{:fn} :sub :defn :form f}))

(defn- prog [& forms]
  (reduce (fn [pr f]
            (ns/add-def pr 'a (second f) (assoc (def-entry f) :qname (symbol "a" (str (second f))))))
          (ns/add-namespace (ns/empty-program @b/registry {'ext {'a 1 'b 1 'c 2 'parent 2}})
                            {:name 'a :attrs {} :requires [{:ns 'ext :as 'ext :refer []}]})
          forms))

(def hex-form
  '(defrel hex [bs s] ([bs -> s] [[(str bs "!")]]) ([s -> bs] [[s]])))
(def g-form '(defrel g [a b] ([a -> b] [[a]])))
(def anc '(defrule ancestor [?a ?b] (ext/parent ?a ?b)))
(def anc2 '(defrule ancestor [?a ?c] (ext/parent ?a ?b) (ancestor ?b ?c)))
(def defs [hex-form g-form anc anc2 '(defn f [x] x)])

(defn- rule [form] (r/analyze-rule (apply prog defs) 'a form))
(defn- steps [form & [opts]] (:steps (p/plan-body (rule form) {} (or opts {}))))
(defn- order [ss] (mapv :idx ss))
(defn- err [f] (try (f) nil (catch clojure.lang.ExceptionInfo e (ex-data e))))

(deftest filters-early
  (is (= [0 2 1] (order (steps '(defrule r [?x ?y] (ext/a ?x) (ext/b ?y) (when (pos? ?x))))))))

(deftest bind-before-scan
  (let [ss (steps '(defrule r [?x ?y] (ext/a ?x) (ext/b ?y) (bind ?k (f ?x)) (ext/c ?k ?y)))]
    (is (= 0 (:idx (first ss))))
    (is (< (.indexOf (order ss) 2) (.indexOf (order ss) 1)))
    (is (= [0 2 3 1] (order ss)) "c has one bound arg, b none")
    (is (= [true false] (:mask (nth ss 2))))))

(deftest mode-choice
  (let [ss (steps '(defrule r [?bs] (ext/a ?s) (hex ?bs ?s)))
        st (second ss)]
    (is (= 1 (:mode st)))
    (is (= [[1 {:var 1}]] (:in-terms st)))
    (is (= [[0 {:var 0}]] (:out-terms st)))
    (is (empty? (:bound-before (first ss))))
    (is (= #{1} (:bound-before st)))))

(deftest mode-prefers-most-inputs
  (let [st (nth (steps '(defrule r [?x] (ext/a ?s) (ext/a ?b) (hex ?b ?s))) 2)]
    (is (= 0 (:mode st)) "both modes apply; tie goes to first declared")))

(deftest unplannable
  (let [e (err #(steps '(defrule r [?y] (g ?x ?y))))]
    (is (= :unplannable (:lang/error e)))
    (is (= :plan (:lang/phase e)))
    (is (= '#{?x} (get-in e [:data :missing])))
    (is (string? (get-in e [:data :literal])))))

(deftest negation-needs-bound
  (is (= [1 0] (order (steps '(defrule r [?x] (not (ext/b ?x)) (ext/a ?x))))))
  (is (= [0 2 1] (order (steps '(defrule r [?x] (ext/c ?x _) (ext/a ?x) (not (ext/c _ ?x))))))
      "a ready not is a filter and beats later scans")
  (let [e (err #(steps '(defrule r [?x] (not (ext/b ?x)))))]
    (is (= '#{?x} (get-in e [:data :missing])))))

(deftest ordered
  (is (= [0 1] (order (steps '(defrule r {:ordered true} [?x] (ext/a ?x) (when (pos? ?x))))))
      "textual order kept")
  (is (= [0 1 2] (order (steps '(defrule r {:ordered true} [?x] (ext/b ?y) (ext/a ?x) (when (pos? ?x))))))
      "no reordering of scans")
  (let [e (err #(steps '(defrule r {:ordered true} [?x] (when (pos? ?x)) (ext/a ?x))))]
    (is (= :unplannable (:lang/error e)))
    (is (= '#{?x} (get-in e [:data :missing])))))

(deftest delta
  (let [r (rule anc2)
        vs (p/delta-variants r '#{a/ancestor})]
    (is (= 1 (count vs)))
    (let [s (first (:steps (first vs)))]
      (is (:delta? s))
      (is (= 'a/ancestor (:rel s))))
    (is (= [1 0] (order (:steps (first vs)))))))

(deftest index-reqs
  (let [r (rule anc2)
        plans [(p/plan-body r {} {})]
        reqs (p/index-requirements plans)]
    (is (= #{[true false]} (get reqs 'a/ancestor)))
    (is (nil? (get reqs 'ext/parent)))))

(deftest negated-computed
  (let [ss (steps '(defrule r [?x] (ext/a ?b) (ext/a ?s) (not (hex ?b ?s))))
        st (nth ss 2)]
    (is (= :not (:lit st)))
    (is (= 0 (:mode st)))
    (is (= [[0 {:var 1}]] (:in-terms st))))
  (is (= '#{?s} (get-in (err #(steps '(defrule r [?x] (ext/a ?b) (not (hex ?b ?s)))))
                        [:data :missing]))))
