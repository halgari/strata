(ns strata.api-test
  (:require [clojure.test :refer [deftest is testing]]
            [strata.api :as strata]
            [strata.test :as lt]))

(defn- err [f]
  (try (f) nil (catch clojure.lang.ExceptionInfo ex (ex-data ex))))

(def src
  "(ns a (:require [ext :refer [edge blob]] [strata.bytes :as b]))
   (defrule path [?x ?y] (edge ?x ?y))
   (defrule path [?x ?z] (path ?x ?y) (edge ?y ?z))
   (defrel plus1 [x y] ([x -> y] [[(+ x 1)]]))
   (defstruct png-like [magic :u8 len :u8])
   (defrel hex [bs s] ([bs -> s] [[(b/hex-encode bs)]]) ([s -> bs] (when-let [x (b/hex-decode s)] [[x]])))
   (defrule hdrs [?m] (blob ?b) (png-like ?b 0 ?h _) (bind {:magic ?m} ?h))")

(def prog (strata/load {:sources {'a src} :builtins '#{strata.bytes}
                      :externs {'ext {'edge 2 'blob 1}}}))

(defn- db [facts & [opts]] (strata/run prog (merge {:facts facts} opts)))

(deftest query-binding-maps
  (let [d (db {'ext/edge [["x" "y"] ["y" "z"]]})]
    (is (= #{{}} (strata/query d '(a/path "x" "y"))) "constants filter")
    (is (= #{} (strata/query d '(a/path "y" "x"))))
    (is (= #{{'?y "y"} {'?y "z"}} (strata/query d '(a/path "x" ?y))) "transitive")
    (is (= #{{'?a "x"}} (strata/query d '(a/path ?a "y"))))
    (is (= #{} (strata/query d '(ext/edge ?a ?a))) "repeated var")
    (is (= #{} (strata/query d '(ext/edge ?a ?b "y"))) "arity mismatch yields nothing")
    (is (= #{["x" "y"] ["y" "z"] ["x" "z"]} (strata/relation d 'a/path)))))

(deftest query-computed-rejected
  (let [d (db {})]
    (is (= :not-a-stored-relation (:strata/error (err #(strata/query d '(a/plus1 1 ?y))))))
    (is (= :not-a-stored-relation (:strata/error (err #(strata/query d '(path ?x ?y))))))))

(deftest nil-tuples-are-empty
  (is (= #{} (strata/relation (db {'ext/edge nil}) 'a/path))))

(deftest bad-host-facts
  (doseq [facts [{'ext/edge [[1]]} {'ext/nope [[1]]} {'ext/blob [[(Object.)]]}]]
    (let [e (err #(db facts))]
      (is (= :bad-fact (:strata/error e)) (pr-str facts))
      (is (= :run (:strata/phase e)))
      (is (= (pr-str (key (first facts))) (get-in e [:data :rel]))))))

(deftest byte-array-facts
  (let [d (db {'ext/blob [[(byte-array [7 9 0])]]})]
    (is (= #{[7]} (strata/relation d 'a/hdrs)))
    (is (every? #(instance? strata.values.Bytes (first %)) (strata/relation d 'ext/blob)))))

(deftest host-parse
  (let [r (strata/bytes-resource (byte-array [7 9 0]))]
    (is (= {:magic 7 :len 9} (:value (strata/parse prog 'a/png-like r))))
    (is (nil? (strata/parse prog 'a/png-like (strata/bytes-resource (byte-array [7])))))
    (let [x (strata/parse-explain prog 'a/png-like (strata/bytes-resource (byte-array [7])))]
      (is (false? (:ok x)))
      (is (= 1 (:offset x)))
      (is (keyword? (:reason x)))
      (is (= [:len] (mapv #(if (vector? %) (first %) %) (:path x)))))))

(deftest check-modes
  (let [bad-prog (strata/load {:sources {'a "(ns a (:require [strata.bytes :as b]))
         (defrel hex [bs s] ([bs -> s] [[(b/hex-encode bs)]]) ([s -> bs] (when-let [x (b/hex-decode s)] [[x]])))"}
                             :builtins '#{strata.bytes}})
        bs (byte-array [0xab 1])]
    (is (seq (lt/check-modes bad-prog 'a/hex [[bs "AB01"]])))
    (is (= [0] (mapv :mode (lt/check-modes bad-prog 'a/hex [[bs "AB01"]]))))
    (is (empty? (lt/check-modes bad-prog 'a/hex [[bs "ab01"]])))))

(deftest trace-events
  (let [evs (atom [])]
    (db {'ext/edge [["x" "y"]] 'ext/blob [[(byte-array [7 9])]]} {:trace #(swap! evs conj %)})
    (is (some #(and (= :rule-fired (:event %)) (= 'a/path (:rel %))) @evs))
    (is (some #(= :parse (:event %)) @evs))))

(deftest stats-and-diagnostics
  (let [d (db {'ext/edge [["x" "y"]]})]
    (is (map? (strata/stats d)))
    (is (map? (strata/diagnostics d)))))

(def src2
  "(ns c (:require [ext :refer [n]] [strata.io :as io]))
   (defstruct par [k] [xs [:array :u8 k]])
   (deftype word :u16)
   (defrule h [?h] (n ?x) (bind ?h (io/open ?x)))")

(deftest host-parse-errors
  (let [p2 (strata/load {:sources {'c src2} :builtins '#{strata.io} :externs {'ext {'n 1}}})
        r (strata/bytes-resource (byte-array [1 2]))
        kind #(:strata/error (err %))]
    (is (= :unknown-struct (kind #(strata/parse p2 'c/nope r))))
    (is (= :unknown-struct (kind #(strata/parse p2 'c/word r))))
    (is (= :type-arity (kind #(strata/parse p2 'c/par r))))
    (is (= :bad-resource (kind #(strata/parse prog 'a/png-like nil))))
    (is (= :bad-resource (kind #(strata/parse-explain prog 'a/png-like "x"))))))

(deftest db-with-handle-tuple
  (let [p2 (strata/load {:sources {'c src2} :builtins '#{strata.io} :externs {'ext {'n 1}}})
        d (strata/run p2 {:facts {'ext/n [["f"]]} :resources {"f" (strata/bytes-resource (byte-array [1]))}})
        [[h]] (seq (strata/relation d 'c/h))]
    (is (= "f" (.-name ^strata.values.Handle h)))
    (is (not-any? #(instance? strata.runtime.RunCtx %) (vals d)))))

(deftest query-constants-canonicalized
  (let [d (db {'ext/blob [[(byte-array [1 2])]] 'ext/edge [[1 2]]})]
    (is (= #{{}} (strata/query d (list 'ext/edge 1N 2))))
    (is (= #{{}} (strata/query d (list 'ext/blob (byte-array [1 2])))))))

(deftest check-modes-bad-sample
  (is (= :bad-sample (:strata/error (err #(lt/check-modes prog 'a/hex [["only-one"]]))))))

(deftest unknown-options-rejected
  (let [src {'a "(ns a) (defrule r [1])"}]
    (testing "load"
      (is (= :bad-option (:strata/error (err #(strata/load {:sources src :timeout-ms 5})))))
      (is (= :bad-option (:strata/error (err #(strata/load {:sources src :limits {:fuell 1}}))))))
    (testing "run"
      (let [p (strata/load {:sources src})]
        (is (= :bad-option (:strata/error (err #(strata/run p {:limits {:max-tupels 1}})))))
        (is (= #{[1]} (strata/relation (strata/run p {:limits {:max-tuples 5}}) 'a/r)))))))

(deftest warnings-and-tainted-exposed
  (let [p (strata/load {:sources {'a "(ns a) (defrule r [1])"}})]
    (is (= [] (strata/warnings p)))
    (is (= #{} (strata/tainted (strata/run p {}))))))

(deftest core-relations-opt-out-of-memo
  (let [rels (vals (get-in @@(requiring-resolve 'strata.builtins/registry) ['strata.core :relation]))]
    (is (seq rels))
    (is (every? #(false? (:memo? %)) rels))))
