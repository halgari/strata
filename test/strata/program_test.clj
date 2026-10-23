(ns strata.program-test
  (:require [clojure.test :refer [deftest is testing]]
            [strata.program :as p]))

(defn- err [f]
  (try (f) nil (catch clojure.lang.ExceptionInfo ex (ex-data ex))))

(def lib-src
  "(ns lib)
   (defn twice [x] (* 2 x))
   (defstruct hdr [magic :u8 len :u8])")

(def app-src
  "(ns app (:require [lib :as l] [ext :refer [edge blob]]))
   (defrel plus1 [x y] ([x -> y] [[(+ x 1)]]))
   (defrule path [?a ?b] (edge ?a ?b))
   (defrule path [?a ?c] (path ?a ?b) (edge ?b ?c))
   (defrule doubled [?a ?d] (edge ?a _) (bind ?d (l/twice ?a)))
   (defrule next [?a ?b] (edge ?a _) (plus1 ?a ?b))
   (defrule header [?m ?n] (blob ?b) (l/hdr ?b 0 ?h _) (bind {:magic ?m :len ?n} ?h))")

(def externs {'ext {'edge 2 'blob 1}})

(defn- load* [sources & [opts]]
  (p/load-program (merge {:sources sources :externs externs} opts)))

(def prog (load* {'lib lib-src 'app app-src}))

(defn- rel [res sym] (get-in res [:relations (symbol "app" (str sym))] #{}))

(deftest load-and-run
  (let [res (p/run-program prog {:facts {'ext/edge [[1 2] [2 3]]
                                         'ext/blob [[(byte-array [7 9 0])]]}})]
    (is (= #{[1 2] [2 3] [1 3]} (rel res 'path)))
    (is (= #{[1 2] [2 4]} (rel res 'doubled)))
    (is (= #{[1 2] [2 3]} (rel res 'next)))
    (is (= #{[7 9]} (rel res 'header)))
    (is (= #{} (:tainted res)))
    (is (map? (:stats res)))
    (is (= [] (:warnings prog)))
    (is (map? (:fn-table prog)))
    (is (map? (:struct-table prog)))))

(deftest program-reusable-threads
  (let [run (fn [n] (p/run-program prog {:facts {'ext/edge (mapv (fn [i] [i (inc i)]) (range n))}}))
        results (mapv #(future (rel (run %) 'path)) [2 3 4 5])]
    (is (= [3 6 10 15] (mapv (comp count deref) results)))
    (is (= #{[0 1] [1 2] [0 2]} @(first results)))))

(def skip-src
  "(ns app (:require [ext :refer [n]]))
   (defrel inc1 [x y] ([x -> y] [[(+ x 1)]]))
   (defrule out [?x ?y] (n ?x) (inc1 ?x ?y))
   (defrule big [?y] (out _ ?y))
   (defrule safe [?x] (n ?x) (not (out ?x _)))
   (defrule total [(count ?x)] (out ?x _))")

(def skip-externs {'ext {'n 1}})

(deftest skip-mode
  (let [pr (p/load-program {:sources {'app (subs skip-src 0 (.indexOf ^String skip-src "(defrule safe"))}
                            :externs skip-externs})
        facts {'ext/n [[1] ["a"] [3]]}]
    (is (= :type-error (:strata/error (err #(p/run-program pr {:facts facts})))))
    (let [res (p/run-program pr {:facts facts :on-code-error :skip})]
      (is (= #{[1 2] [3 4]} (rel res 'out)))
      (is (= 1 (get-in res [:diagnostics :counts :type-error])))
      (is (= #{'app/out 'app/big} (:tainted res))))))

(defn- skip-run [src facts]
  (let [pr (p/load-program {:sources {'app src} :externs skip-externs})]
    (err #(p/run-program pr {:facts facts :on-code-error :skip}))))

(def bad-facts {'ext/n [[1] ["a"] [3]]})
(def hdr "(ns app (:require [ext :refer [n]]))
          (defrel inc1 [x y] ([x -> y] [[(+ x 1)]]))
          (defrule out [?x ?y] (n ?x) (inc1 ?x ?y))\n")

(deftest tainted-negation
  (testing "not over a tainted relation"
    (is (= :tainted-negation
           (:strata/error (skip-run (str hdr "(defrule safe [?x] (n ?x) (not (out ?x _)))") bad-facts)))))
  (testing "aggregate over a tainted relation"
    (is (= :tainted-negation
           (:strata/error (skip-run (str hdr "(defrule total [(count ?x)] (out ?x _))") bad-facts)))))
  (testing "transitively tainted relation"
    (is (= :tainted-negation
           (:strata/error (skip-run (str hdr "(defrule big [?y] (out _ ?y))
                                            (defrule safe [?x] (n ?x) (not (big ?x)))")
                                  bad-facts)))))
  (testing "skipped call inside a negated computed literal"
    (is (= :tainted-negation
           (:strata/error (skip-run (str hdr "(defrule safe [?x] (n ?x) (not (inc1 ?x _)))") bad-facts)))))
  (testing "no error, no taint"
    (let [pr (p/load-program {:sources {'app (str hdr "(defrule safe [?x] (n ?x) (not (out ?x _)))")}
                              :externs skip-externs})
          res (p/run-program pr {:facts {'ext/n [[1]]} :on-code-error :skip})]
      (is (= #{} (:tainted res)))
      (is (= #{} (rel res 'safe))))))

(deftest parse-in-code
  (let [pr (load* {'app "(ns app (:require [ext :refer [blob]]))
                         (defstruct hdr [magic :u8 len :u8])
                         (defn magic [b] (:magic (:value (parse hdr b 0))))
                         (defrel hdr-end [b e] ([b -> e] [[(:end (parse hdr b 0))]]))
                         (defrule m [?m ?e] (blob ?b) (bind ?m (magic ?b)) (hdr-end ?b ?e))"})
        res (p/run-program pr {:facts {'ext/blob [[(byte-array [7 9 0])]]}})]
    (is (= #{[7 2]} (rel res 'm)))))

(deftest plans-keep-every-clause
  (is (= 2 (count (get-in prog [:plans 'app/path]))))
  (is (= 1 (count (get-in prog [:plans 'app/doubled])))))

(deftest hooks-not-public
  (let [pr (p/load-program {:sources {'app "(ns app) (defrule r [1])"} :unchecked? true
                            :registry {}})]
    (is (= #{[1]} (rel (p/run-program pr {}) 'r)))))

(deftest limits-never-skipped
  (let [pr (p/load-program {:sources {'app "(ns app (:require [ext :refer [n]]))
                                           (defrel spin [x y] ([x -> y] [[(loop [i 0] (recur (+ i 1)))]]))
                                           (defrule out [?x ?y] (n ?x) (spin ?x ?y))"}
                            :externs skip-externs})]
    (is (= :call-fuel-exhausted
           (:strata/error (err #(p/run-program pr {:facts {'ext/n [[1]]}
                                                 :limits {:call-fuel 1000}
                                                 :on-code-error :skip})))))
    (is (= :fuel-exhausted
           (:strata/error (err #(p/run-program pr {:facts {'ext/n [[1]]}
                                                 :limits {:fuel 1000}
                                                 :on-code-error :skip})))))))

(deftest skipped-when-and-bind
  (let [pr (p/load-program {:sources {'app "(ns app (:require [ext :refer [n]]))
                                           (defrule w [?x] (n ?x) (when (> ?x 1)))
                                           (defrule b [?y] (n ?x) (bind ?y (+ ?x 1)))"}
                            :externs skip-externs})
        res (p/run-program pr {:facts {'ext/n [[2] [nil]]} :on-code-error :skip})]
    (is (= #{[2]} (rel res 'w)))
    (is (= #{[3]} (rel res 'b)))
    (is (= #{'app/w 'app/b} (:tainted res)))
    (is (= 2 (get-in res [:diagnostics :counts :type-error])))))

(deftest bad-forms-and-facts
  (testing "unsupported top-level form"
    (let [e (err #(load* {'app "(ns app) (println 1)"}))]
      (is (= :bad-form (:strata/error e)))
      (is (= :analyze (:strata/phase e)))
      (is (= 1 (:line e)))))
  (testing "second ns form"
    (is (= :bad-form (:strata/error (err #(load* {'app "(ns app) (ns other)"}))))))
  (testing "host facts"
    (let [bad (fn [facts] (err #(p/run-program prog {:facts facts})))]
      (is (= :bad-fact (:strata/error (bad {'ext/edge {1 2}}))))
      (is (= {:rel "ext/nope"} (:data (bad {'ext/nope [[1]]}))))
      (is (= :bad-fact (:strata/error (bad {'ext/edge [[1]]}))))
      (is (= :bad-fact (:strata/error (bad {'ext/edge [1]}))))
      (is (= :bad-fact (:strata/error (bad {'ext/edge [[1 (Object.)]]}))))
      (is (= :run (:strata/phase (bad {'ext/edge [[1]]}))))))
  (testing "facts accept lists and canonicalize"
    (let [res (p/run-program prog {:facts {'ext/edge [(list 1 2.0)]}})]
      (is (= #{[1 2.0]} (get-in res [:relations 'ext/edge]))))))

(deftest shadow-warnings-reported
  (let [pr (load* {'app "(ns app) (defn inc [x] x)"})]
    (is (= [{:ns 'app :sym 'inc :position :fn}] (:warnings pr)))))

(deftest cross-namespace-forward-refs
  (let [pr (load* {'a "(ns a (:require [b :as b])) (defn f [x] (b/g x))"
                   'b "(ns b) (defn g [x] (+ x 1))
                       (defrule s [1])
                       (defrule r [?y] (s ?x) (bind ?y (g2 ?x)))
                       (defn g2 [x] (g x))"})]
    (is (= #{[2]} (get-in (p/run-program pr {}) [:relations 'b/r])))))
