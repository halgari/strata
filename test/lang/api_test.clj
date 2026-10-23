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
   (defrel hex2 [bs s] ([bs -> s] [[(b/hex-encode bs)]]) ([s -> bs] (when-let [x (b/hex-decode s)] [[x]])))
   (defrule hdrs [?m] (blob ?b) (png-like ?b 0 ?h _) (bind {:magic ?m} ?h))")

(def prog (lang/load {:sources {'a src} :builtins '#{lang.bytes}
                      :externs {'ext {'edge 2 'blob 1}}
                      :registry :ignored :unchecked? true}))

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
      (is (= (key (first facts)) (get-in e [:data :rel]))))))

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
