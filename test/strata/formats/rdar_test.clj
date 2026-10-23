(ns strata.formats.rdar-test
  (:require [clojure.java.io :as io]
            [clojure.test :refer [deftest is]]
            [strata.api :as strata]
            [strata.fixtures.rdar :refer [build-rdar]]))

(def ^:private prog
  (delay (strata/load {:sources {'formats.rdar (slurp (io/resource "formats/rdar.edn"))}
                     :builtins '#{strata.string strata.bytes strata.io}
                     :externs {'host.input {'file 1}}})))

(defn- run
  ([files] (run files nil))
  ([files limits]
   (strata/run @prog (cond-> {:facts {'host.input/file (mapv (comp vector key) files)}
                            :resources (update-vals files strata/bytes-resource)}
                     limits (assoc :limits limits)))))

(def ^:private big-hash 0xF000000000000001)

(deftest header-index
  (let [db (run {"a.archive" (build-rdar {:entries [{:hash 5 :segments [[1 2 3]]}
                                                    {:hash big-hash :segments [[4 5 6]] :deps [9]}
                                                    {:hash 7}]})})
        rows (strata/query db '(formats.rdar/archive-file "a.archive" ?i ?h))]
    (is (= #{[0 5] [1 17293822569102704641N] [2 7]}
           (set (map (juxt #(% '?i) #(% '?h)) rows))))
    (is (= clojure.lang.BigInt (class (some #(when (= 1 (% '?i)) (% '?h)) rows))))))

(deftest segments-by-range
  (let [db (run {"a.archive" (build-rdar {:entries [{:hash 1 :segments [[10 1 2] [20 3 4]]}
                                                    {:hash 2}
                                                    {:hash 3 :segments [[30 5 6]]}]})})
        rows (strata/query db '(formats.rdar/file-segment-of "a.archive" ?i ?s))]
    (is (= #{[0 {:offset 10 :zsize 1 :size 2}] [0 {:offset 20 :zsize 3 :size 4}]
             [2 {:offset 30 :zsize 5 :size 6}]}
           (set (map (juxt #(% '?i) #(% '?s)) rows))))))

(deftest wrong-version
  (let [db (run {"a.archive" (build-rdar {:version 13 :entries [{:hash 1}]})})]
    (is (empty? (strata/query db '(formats.rdar/archive "a.archive" ?a))))))

(deftest between-not-cross-product
  (let [n 2000
        db (run {"a.archive" (build-rdar {:entries (for [i (range n)]
                                                     {:hash i :segments [[i 1 1]]})})}
                {:fuel 50000000})
        rows (strata/query db '(formats.rdar/file-segment-of "a.archive" ?i ?s))]
    (is (= n (count rows)))))
