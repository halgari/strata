(ns lang.api-test
  (:require [clojure.test :refer [deftest is testing]]
            [lang.api :as lang]
            [lang.test :as lt]))

(defn- err [f]
  (try (f) nil (catch clojure.lang.ExceptionInfo ex (ex-data ex))))

(def src
  "(ns a (:require [ext :refer [edge blob]] [lang.bytes :as b]))
   (defrule path [?x ?y] (edge ?x ?y))
   (defrule path [?x ?z] (path ?x ?y) (edge ?y ?z))
   (defrel plus1 [x y] ([x -> y] [[(+ x 1)]]))
   (defstruct png-like [magic :u8 len :u8])
   (defrel hex [bs s] ([bs -> s] [[(b/hex-encode bs)]]) ([s -> bs] (when-let [x (b/hex-decode s)] [[x]])))
   (defrule hdrs [?m] (blob ?b) (png-like ?b 0 ?h _) (bind {:magic ?m} ?h))")

(def prog (lang/load {:sources {'a src} :builtins '#{lang.bytes}
                      :externs {'ext {'edge 2 'blob 1}}}))

(defn- db [facts & [opts]] (lang/run prog (merge {:facts facts} opts)))

(deftest query-binding-maps
  (let [d (db {'ext/edge [["x" "y"] ["y" "z"]]})]
    (is (= #{{}} (lang/query d '(a/path "x" "y"))) "constants filter")
    (is (= #{} (lang/query d '(a/path "y" "x"))))
    (is (= #{{'?y "y"} {'?y "z"}} (lang/query d '(a/path "x" ?y))) "transitive")
    (is (= #{{'?a "x"}} (lang/query d '(a/path ?a "y"))))
    (is (= #{} (lang/query d '(ext/edge ?a ?a))) "repeated var")
    (is (= #{} (lang/query d '(ext/edge ?a ?b "y"))) "arity mismatch yields nothing")
    (is (= #{["x" "y"] ["y" "z"] ["x" "z"]} (lang/relation d 'a/path)))))

(deftest query-computed-rejected
  (let [d (db {})]
    (is (= :not-a-stored-relation (:lang/error (err #(lang/query d '(a/plus1 1 ?y))))))
    (is (= :not-a-stored-relation (:lang/error (err #(lang/query d '(path ?x ?y))))))))

(deftest nil-tuples-are-empty
  (is (= #{} (lang/relation (db {'ext/edge nil}) 'a/path))))

(deftest bad-host-facts
  (doseq [facts [{'ext/edge [[1]]} {'ext/nope [[1]]} {'ext/blob [[(Object.)]]}]]
    (let [e (err #(db facts))]
      (is (= :bad-fact (:lang/error e)) (pr-str facts))
      (is (= :run (:lang/phase e)))
      (is (= (pr-str (key (first facts))) (get-in e [:data :rel]))))))

(deftest byte-array-facts
  (let [d (db {'ext/blob [[(byte-array [7 9 0])]]})]
    (is (= #{[7]} (lang/relation d 'a/hdrs)))
    (is (every? #(instance? lang.values.Bytes (first %)) (lang/relation d 'ext/blob)))))

(deftest host-parse
  (let [r (lang/bytes-resource (byte-array [7 9 0]))]
    (is (= {:magic 7 :len 9} (:value (lang/parse prog 'a/png-like r))))
    (is (nil? (lang/parse prog 'a/png-like (lang/bytes-resource (byte-array [7])))))
    (let [x (lang/parse-explain prog 'a/png-like (lang/bytes-resource (byte-array [7])))]
      (is (false? (:ok x)))
      (is (= 1 (:offset x)))
      (is (keyword? (:reason x)))
      (is (= [:len] (mapv #(if (vector? %) (first %) %) (:path x)))))))

(deftest check-modes
  (let [bad-prog (lang/load {:sources {'a "(ns a (:require [lang.bytes :as b]))
         (defrel hex [bs s] ([bs -> s] [[(b/hex-encode bs)]]) ([s -> bs] (when-let [x (b/hex-decode s)] [[x]])))"}
                             :builtins '#{lang.bytes}})
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
    (is (map? (lang/stats d)))
    (is (map? (lang/diagnostics d)))))

(def src2
  "(ns c (:require [ext :refer [n]] [lang.io :as io]))
   (defstruct par [k] [xs [:array :u8 k]])
   (deftype word :u16)
   (defrule h [?h] (n ?x) (bind ?h (io/open ?x)))")

(deftest host-parse-errors
  (let [p2 (lang/load {:sources {'c src2} :builtins '#{lang.io} :externs {'ext {'n 1}}})
        r (lang/bytes-resource (byte-array [1 2]))
        kind #(:lang/error (err %))]
    (is (= :unknown-struct (kind #(lang/parse p2 'c/nope r))))
    (is (= :unknown-struct (kind #(lang/parse p2 'c/word r))))
    (is (= :type-arity (kind #(lang/parse p2 'c/par r))))
    (is (= :bad-resource (kind #(lang/parse prog 'a/png-like nil))))
    (is (= :bad-resource (kind #(lang/parse-explain prog 'a/png-like "x"))))))

(deftest db-with-handle-tuple
  (let [p2 (lang/load {:sources {'c src2} :builtins '#{lang.io} :externs {'ext {'n 1}}})
        d (lang/run p2 {:facts {'ext/n [["f"]]} :resources {"f" (lang/bytes-resource (byte-array [1]))}})
        [[h]] (seq (lang/relation d 'c/h))]
    (is (= "f" (.-name ^lang.values.Handle h)))
    (is (not-any? #(instance? lang.runtime.RunCtx %) (vals d)))))

(deftest query-constants-canonicalized
  (let [d (db {'ext/blob [[(byte-array [1 2])]] 'ext/edge [[1 2]]})]
    (is (= #{{}} (lang/query d (list 'ext/edge 1N 2))))
    (is (= #{{}} (lang/query d (list 'ext/blob (byte-array [1 2])))))))

(deftest check-modes-bad-sample
  (is (= :bad-sample (:lang/error (err #(lt/check-modes prog 'a/hex [["only-one"]]))))))

(deftest unknown-options-rejected
  (let [src {'a "(ns a) (defrule r [1])"}]
    (testing "load"
      (is (= :bad-option (:lang/error (err #(lang/load {:sources src :timeout-ms 5})))))
      (is (= :bad-option (:lang/error (err #(lang/load {:sources src :limits {:fuell 1}}))))))
    (testing "run"
      (let [p (lang/load {:sources src})]
        (is (= :bad-option (:lang/error (err #(lang/run p {:limits {:max-tupels 1}})))))
        (is (= #{[1]} (lang/relation (lang/run p {:limits {:max-tuples 5}}) 'a/r)))))))

(deftest warnings-and-tainted-exposed
  (let [p (lang/load {:sources {'a "(ns a) (defrule r [1])"}})]
    (is (= [] (lang/warnings p)))
    (is (= #{} (lang/tainted (lang/run p {}))))))

(deftest core-relations-opt-out-of-memo
  (let [rels (vals (get-in @@(requiring-resolve 'lang.builtins/registry) ['lang.core :relation]))]
    (is (seq rels))
    (is (every? #(false? (:memo? %)) rels))))
