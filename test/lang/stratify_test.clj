(ns lang.stratify-test
  (:require [clojure.test :refer [deftest is]]
            [lang.stratify :refer [stratify]]))

(defn- r
  ([head & lits] {:rel head :head [] :aggs [] :body (vec lits)}))
(defn- pos [q] {:lit :rel :rel q})
(defn- neg [q] {:lit :not :rel q})
(defn- err [f] (try (f) nil (catch clojure.lang.ExceptionInfo e (ex-data e))))

(deftest linear
  (is (= [#{'c} #{'b} #{'a}]
         (map :rels (stratify [(r 'a (pos 'b)) (r 'b (pos 'c))] #{'a 'b 'c})))))

(deftest recursive-scc
  (let [rules [(r 'ancestor (pos 'parent)) (r 'ancestor (pos 'parent) (pos 'ancestor))]
        ss (stratify rules #{'parent 'ancestor})]
    (is (= [#{'parent} #{'ancestor}] (map :rels ss)))
    (is (= [false true] (map :recursive? ss)))
    (is (= 2 (count (:rules (second ss)))))))

(deftest negation-ok
  (let [ss (stratify [(r 'p (pos 'q) (neg 'r))] #{'p 'q 'r})
        pos-of (fn [x] (first (keep-indexed #(when ((:rels %2) x) %1) ss)))]
    (is (< (pos-of 'r) (pos-of 'p)))
    (is (= ['q 'r 'p] (mapv #(first (:rels %)) ss)))))

(deftest computed-not-nodes
  (is (= [#{'a}] (map :rels (stratify [(r 'a {:lit :rel :rel 'f :modes [{}]})] #{'a})))))

(deftest negative-cycle
  (let [e (err #(stratify [(r 'p (neg 'q)) (r 'q (pos 'p))] #{'p 'q}))]
    (is (= :negative-cycle (:lang/error e)))
    (is (= :stratify (:lang/phase e)))
    (is (= ['p 'q] (get-in e [:data :cycle])))))

(deftest aggregate-cycle
  (let [e (err #(stratify [(assoc (r 'p (pos 'p)) :aggs [{}])] #{'p}))]
    (is (= :negative-cycle (:lang/error e)))))

(deftest aggregate-ok
  (is (= [#{'q} #{'p}]
         (map :rels (stratify [(assoc (r 'p (pos 'q)) :aggs [{}])] #{'p 'q})))))

(deftest long-chain
  (let [n 10000
        rel (fn [i] (symbol (str "r" i)))
        rules (for [i (range (dec n))] (r (rel i) (pos (rel (inc i)))))
        t (System/nanoTime)
        ss (stratify rules (set (map rel (range n))))]
    (is (= n (count ss)))
    (is (= #{(rel (dec n))} (:rels (first ss))))
    (is (< (/ (- (System/nanoTime) t) 1e9) 5))))

(deftest direct-negative-self-cycle
  (is (= :negative-cycle (:lang/error (err #(stratify [(r 'p (neg 'p))] #{'p}))))))

(deftest negative-edge-to-lower-stratum-in-positive-cycle
  (let [ss (stratify [(r 'a (pos 'b) (neg 'z)) (r 'b (pos 'a))] #{'a 'b 'z})]
    (is (= [#{'z} #{'a 'b}] (map :rels ss)))
    (is (= [false true] (map :recursive? ss)))))

(deftest tie-break-by-name
  (is (= ['a 'b 'c 'top]
         (mapv #(first (:rels %))
               (stratify [(r 'top (pos 'c) (pos 'a) (pos 'b))] #{'top 'a 'b 'c})))))
