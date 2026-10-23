(ns lang.engine-test
  (:require [clojure.test :refer [deftest is testing]]
            [clojure.test.check.clojure-test :refer [defspec]]
            [clojure.test.check.generators :as gen]
            [clojure.test.check.properties :as prop]
            [lang.analyze.code :as ac]
            [lang.analyze.rule :as r]
            [lang.analyze.struct :as as]
            [lang.builtins :as b]
            [lang.compile.code :as cc]
            [lang.compile.struct :as cs]
            [lang.engine :as e]
            [lang.ns :as ns]
            [lang.runtime :as rt]))

;; Temporary pipeline helper; Task 21 (lang.program) replaces it.

(defn- def-entry [f]
  (case (first f)
    defrule {:kinds #{:relation} :sub :rule}
    defrel {:kinds #{:relation} :sub :defrel}
    defstruct {:kinds #{:relation :type} :sub :struct}
    defn {:kinds #{:fn} :sub :defn}))

(def ^:dynamic *ticks* nil)

(defn- build
  "Runs the load pipeline over forms. edb is {rel-sym coll-of-tuples}; an
  unqualified key becomes an extern ext/<sym>, a qualified one is passed
  through. Returns {:prepared :edb}."
  [forms edb {:keys [arities]}]
  (let [ext (into {} (keep (fn [[k ts]]
                             (when-not (namespace k)
                               [k (or (get arities k) (count (first ts)))])))
                  edb)
        nsf (list 'ns 'user (list :require ['ext :refer (vec (keys ext))]))
        parsed (ns/parse-ns-form nsf)
        registry (assoc-in @b/registry ['lang.core :fn 'tick!]
                           {:impl (fn [_ x] (when *ticks* (swap! *ticks* inc)) x) :arity [1 1]})
        prog (reduce (fn [p f]
                       (ns/add-def p 'user (second f)
                                   (assoc (def-entry f) :form f
                                          :qname (symbol "user" (str (second f))))))
                     (ns/add-namespace (ns/empty-program registry {'ext ext}) parsed)
                     forms)
        fn-table (atom {})
        struct-table (atom {})
        _ (doseq [f forms :when (= 'defn (first f))]
            (let [a (ac/analyze-defn prog 'user f)]
              (swap! fn-table assoc (:qname a) (cc/compile-defn a fn-table))))
        _ (doseq [f forms :when (= 'defstruct (first f))]
            (let [c (cs/compile-struct (as/analyze-struct prog 'user f) struct-table fn-table)]
              (swap! struct-table assoc (:qname c) c)))
        analyzed-rels (for [f forms :when (= 'defrel (first f))] (r/analyze-defrel prog 'user f))
        rules (vec (for [f forms :when (= 'defrule (first f))] (r/analyze-rule prog 'user f)))
        _ (r/check-program prog (concat analyzed-rels rules))
        computed (merge (into {} (map (fn [[_ en]] [(:qname en) en])) (get-in registry ['lang.core :relation]))
                        (into {} (map (fn [a] (let [en (r/compile-defrel a fn-table)] [(:qname en) en])))
                              analyzed-rels)
                        (into {} (map (fn [[q c]] [q (cs/struct-relation c)])) @struct-table))
        stored (into (set (map #(symbol "ext" (str %)) (keys ext))) (map :rel) rules)]
    {:prepared (e/prepare {:rules rules :computed computed :fn-table fn-table :stored? stored})
     :edb (into {} (map (fn [[k ts]] [(if (namespace k) k (symbol "ext" (str k))) ts])) edb)}))

(defn run-prog
  ([forms edb] (run-prog forms edb {}))
  ([forms edb {:keys [limits naive?] :as opts}]
   (let [{:keys [prepared edb]} (build forms edb opts)
         ctx (rt/make-ctx {:limits limits})]
     ((if naive? e/evaluate-naive e/evaluate) ctx prepared edb))))

(defn- err [f]
  (try (f) nil (catch clojure.lang.ExceptionInfo ex (ex-data ex))))

(defn- rel [res sym] (get res (symbol "user" (str sym)) #{}))

(def anc-rules
  ['(defrule ancestor [?a ?b] (parent ?a ?b))
   '(defrule ancestor [?a ?c] (parent ?a ?b) (ancestor ?b ?c))])

(deftest transitive-closure
  (let [edb {'parent (mapv (fn [i] [i (inc i)]) (range 50))}
        res (run-prog anc-rules edb)]
    (is (= 1275 (count (rel res 'ancestor))))
    (is (= res (run-prog anc-rules edb {:naive? true})))))

(deftest negation
  (let [res (run-prog ['(defrule orphan [?x] (person ?x) (not (parent _ ?x)))]
                      {'person [[1] [2] [3]] 'parent [[1 2]]})]
    (is (= #{[1] [3]} (rel res 'orphan)))))

(deftest negation-over-recursion
  (let [res (run-prog (conj anc-rules
                            '(defrule root [?x] (node ?x) (not (ancestor _ ?x))))
                      {'node [[0] [1] [2] [3]] 'parent [[0 1] [1 2]]})]
    (is (= #{[0] [3]} (rel res 'root)))))

(deftest negated-computed
  (let [res (run-prog ['(defrel even [x] ([x ->] (= 0 (rem x 2))))
                       '(defrule odd [?x] (n ?x) (not (even ?x)))]
                      {'n [[1] [2] [3]]})]
    (is (= #{[1] [3]} (rel res 'odd)))))

(deftest aggregates
  (let [pay {'payment [[1 10] [2 10] [3 5]]}
        run (fn [rule] (rel (run-prog [rule] pay) 'a))]
    (is (= #{[25]} (run '(defrule a [(sum ?x)] (payment _ ?x)))))
    (is (= #{[3]} (run '(defrule a [(count ?x)] (payment _ ?x)))))
    (is (= #{[2]} (run '(defrule a [(count-distinct ?x)] (payment _ ?x)))))
    (is (= #{[5 10]} (run '(defrule a [(min ?x) (max ?x)] (payment _ ?x)))))
    (is (= #{[#{5 10}]} (run '(defrule a [(collect ?x)] (payment _ ?x)))))
    (is (= #{[10 2] [5 1]} (run '(defrule a [?x (count ?i)] (payment ?i ?x)))))
    (is (= #{[[3 1 2]]} (run '(defrule a [(collect-by ?x ?i)] (payment ?i ?x)))))))

(deftest aggregates-ordering
  (let [items {'item [[3 :c] [1 :a] [2 :b]]}]
    (is (= #{[[:a :b :c]]}
           (rel (run-prog ['(defrule a [(collect-by ?k ?v)] (item ?k ?v))] items) 'a)))
    (is (= #{[{1 :a 2 :b 3 :c}]}
           (rel (run-prog ['(defrule a [(collect-map ?k ?v)] (item ?k ?v))] items) 'a)))
    (is (= :collect-map-conflict
           (:lang/error (err #(run-prog ['(defrule a [(collect-map ?k ?v)] (item ?k ?v))]
                                        {'item [[1 :a] [1 :b]]})))))
    (is (= :type-error
           (:lang/error (err #(run-prog ['(defrule a [(sum ?v)] (item _ ?v))] items)))))))

(deftest empty-group
  (is (= #{} (rel (run-prog ['(defrule c [(count ?x)] (nothing ?x))]
                            {'nothing []} {:arities {'nothing 1}})
                  'c))))

(deftest bind-nil
  (let [edb {'holder [[{:a 1}]]}]
    (is (= #{} (rel (run-prog ['(defrule r [?v] (holder ?m) (bind ?v (:missing ?m)))] edb) 'r)))
    (is (= #{[nil]} (rel (run-prog ['(defrule r [?v] (holder ?m) (bind-nil ?v (:missing ?m)))] edb) 'r)))
    (is (= #{[1]} (rel (run-prog ['(defrule r [?v] (holder ?m) (bind {:a ?v} ?m))] edb) 'r)))
    (is (= #{} (rel (run-prog ['(defrule r [?v] (holder ?m) (bind {:a ?v :b ?w} ?m))] edb) 'r)))
    (is (= #{[1 2 [3]]}
           (rel (run-prog ['(defrule r [?a ?b ?c] (holder ?m) (bind [?a ?b & ?c] (:v ?m)))]
                          {'holder [[{:v [1 2 3]}]]})
                'r)))))

(deftest computed-and-expr-inputs
  (let [res (run-prog ['(defrule items [?x] (holder ?m) (elem (:xs ?m) ?x))]
                      {'holder [[{:xs [1 2 3]}]]})]
    (is (= #{[1] [2] [3]} (rel res 'items)))))

(deftest defrel-memo
  (binding [*ticks* (atom 0)]
    (let [res (run-prog ['(defrel dbl [x y] ([x -> y] [[(tick! (* 2 x))]]))
                         '(defrule v [1])
                         '(defrule v [?y] (v ?x) (dbl ?x ?y) (when (< ?y 100)))
                         '(defrule w [?y] (v ?x) (dbl ?x ?y))]
                        {})]
      (is (= #{[1] [2] [4] [8] [16] [32] [64]} (rel res 'v)))
      (is (= 7 @*ticks*)))))

(deftest fuel-on-joins
  (let [tuples (mapv vector (range 300))
        e (err #(run-prog ['(defrule r [1] (a ?x) (b ?y) (c ?z))]
                          {'a tuples 'b tuples 'c tuples}
                          {:limits {:fuel 1000000}}))]
    (is (= :fuel-exhausted (:lang/error e)))))

(deftest nontermination-guard
  (let [e (err #(run-prog ['(defrule n [0])
                           '(defrule n [?y] (n ?x) (bind ?y (inc ?x)))]
                          {} {:limits {:max-tuples 1000 :max-iterations 100}}))]
    (is (#{:tuple-limit :iteration-limit} (:lang/error e)))
    (is (= 'user/n (get-in e [:data :rel]))))
  (let [e (err #(run-prog ['(defrule n [0])
                           '(defrule n [?y] (n ?x) (bind ?y (inc ?x)))]
                          {} {:limits {:max-iterations 20}}))]
    (is (= :iteration-limit (:lang/error e)))
    (is (= 'user/n (get-in e [:data :rel])))))

(deftest nan-terminates
  (let [res (run-prog ['(defrule v [0.0])
                       '(defrule v [?y] (v ?x) (bind ?y (+ ?x (- ##Inf ##Inf))))]
                      {})]
    (is (= 2 (count (rel res 'v))))))

(deftest duplicate-facts-collapse
  (let [forms ['(defrule q [1 2])
               '(defrule c [(count ?x)] (q ?x ?y))]
        res (run-prog forms {'user/q [[1 2]]})]
    (is (= #{[1 2]} (rel res 'q)))
    (is (= #{[1]} (rel res 'c)))))

(deftest unstorable
  (is (= :unstorable-value
         (:lang/error (err #(run-prog ['(defrule f [?g] (holder ?m) (bind ?g (fn [x] x)))]
                                      {'holder [[1]]}))))))

(deftest stats-recorded
  (let [{:keys [prepared edb]} (build anc-rules {'parent [[1 2] [2 3]]} {})
        ctx (rt/make-ctx {})]
    (e/evaluate ctx prepared edb)
    (let [s (get-in (rt/diagnostics ctx) [:entries 0 :data])]
      (is (= 3 (get-in s [:tuples 'user/ancestor])))
      (is (pos? (get-in s [:iterations 'user/ancestor]))))))

;; ---------------------------------------------------------------- properties

(def ^:private gen-prog
  (gen/let [n (gen/choose 2 4)
            rules (gen/vector
                   (gen/let [h (gen/choose 0 3)
                             kind (gen/elements [:copy :swap :join])
                             a (gen/choose -1 3)
                             c (gen/choose -1 3)]
                     [(mod h n) kind (if (neg? a) 'e (mod a n)) (if (neg? c) 'e (mod c n))])
                   2 8)
            edges (gen/vector (gen/tuple (gen/choose 0 5) (gen/choose 0 5)) 1 12)]
    {:rules (cons [0 :copy 'e 'e] rules) :edges edges}))

(defn- rname [x] (if (= 'e x) 'e (symbol (str "r" x))))

(defn- rule-form [[h kind a c]]
  (case kind
    :copy (list 'defrule (rname h) '[?x ?y] (list (rname a) '?x '?y))
    :swap (list 'defrule (rname h) '[?y ?x] (list (rname a) '?x '?y))
    :join (list 'defrule (rname h) '[?x ?z] (list (rname a) '?x '?y) (list (rname c) '?y '?z))))

(defspec semi-naive=naive 100
  (prop/for-all [{:keys [rules edges]} gen-prog]
    (let [heads (set (map first rules))
          fix (fn [x] (if (contains? heads x) x 'e))
          forms (mapv (fn [[h k a c]] (rule-form [h k (fix a) (fix c)])) rules)
          {:keys [prepared edb]} (build forms {'e edges} {})]
      (= (e/evaluate (rt/make-ctx {}) prepared edb)
         (e/evaluate-naive (rt/make-ctx {}) prepared edb)))))

(defspec fact-order-independent 50
  (prop/for-all [ms (gen/vector (gen/tuple (gen/choose 0 40)
                                           (gen/elements [0.1 0.2 0.3 1e16 -1e16 1.5 2.25]))
                                1 12)
                 seed gen/nat]
    (let [forms ['(defrule total [(sum ?a)] (m _ ?a))
                 '(defrule path [?x ?y] (m ?x ?y))
                 '(defrule path [?x ?z] (path ?x ?y) (m ?y ?z))]
          shuffled (shuffle ms)]
      (= (run-prog forms {'m ms}) (run-prog forms {'m shuffled})))))
