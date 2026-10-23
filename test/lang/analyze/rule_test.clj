(ns lang.analyze.rule-test
  (:require [clojure.test :refer [deftest is testing]]
            [lang.analyze.rule :as r]
            [lang.builtins :as b]
            [lang.compile.code :as cc]
            [lang.ns :as ns]
            [lang.runtime :as rt]))

(defn- err [f]
  (try (f) nil (catch clojure.lang.ExceptionInfo e (ex-data e))))

(defn- def-entry [f]
  (case (first f)
    defrule {:kinds #{:relation} :sub :rule :form f}
    defrel {:kinds #{:relation} :sub :defrel :form f}
    defn {:kinds #{:fn} :sub :defn :form f}
    defstruct {:kinds #{:relation :type} :sub :struct :form f}))

(defn- prog [& forms]
  (reduce (fn [p f]
            (ns/add-def p 'a (second f) (assoc (def-entry f) :qname (symbol "a" (str (second f))))))
          (ns/add-namespace (ns/empty-program @b/registry {'ext {'e 2}})
                            {:name 'a :attrs {} :requires [{:ns 'ext :as 'ext :refer []}]})
          forms))

(defn- an [p form] (r/analyze-rule p 'a form))

(defn- check-kind [forms & rules]
  (let [p (apply prog forms)]
    (:lang/error (err #(r/check-program p (map (partial an p) rules))))))

(def s-rule '(defrule s [?a ?b ?c] (ext/e ?a ?b) (ext/e ?b ?c)))

(deftest terms
  (let [p (prog s-rule)
        a (an p '(defrule r [?x] (s ?x _ _)))
        args (:args (first (:body a)))]
    (is (= {:var 0} (first args)))
    (is (not= (second args) (nth args 2)))
    (is (= 3 (:nvars a)))
    (is (= 'a/r (:rel a)))
    (is (= {:var 0} (first (:head a))))
    (is (nil? (check-kind [s-rule] '(defrule r [?x] (s ?x _ _)))))
    (is (= [{:const "png"} {:const 1} {:const [1 :a]}]
           (:args (first (:body (an p '(defrule r [?x] (s "png" 1 [1 :a]))))))))))

(deftest expr-input
  (let [p (prog)
        a (an p '(defrule r [?d] (ext/e ?t _) (elem (:descs ?t) ?d)))
        lit (second (:body a))
        t (:t (:var-names a))]
    (is (:computed? lit))
    (is (= 'lang.core/elem (:rel lit)))
    (is (= :expr (key (first (select-keys (first (:args lit)) [:expr])))))
    (is (= #{(get (:var-names a) '?t)} (:vars (first (:args lit)))))
    (is (some? (get-in a [:var-locals (get (:var-names a) '?t)])))
    (is (nil? (check-kind [] '(defrule r [?d] (ext/e ?t _) (elem (:descs ?t) ?d)))))
    (is (= :expression-in-stored-literal
           (check-kind [] '(defrule r [?d] (ext/e ?t ?d) (elem ?t (inc ?d)))))
        "output position")))

(deftest expr-in-stored
  (is (= :expression-in-stored-literal
         (check-kind [s-rule] '(defrule r [?x] (ext/e ?x ?y) (s (inc ?x) ?y ?y)))))
  (is (= :expression-in-stored-literal
         (check-kind [] '(defrule r [(inc ?x)] (ext/e ?x ?y))))))

(deftest undefined-relation
  (let [p (prog)
        e (err #(r/check-program p [(an p '(defrule r [?x] (nope ?x)))]))]
    (is (= :undefined-relation (:lang/error e)))
    (is (= :check (:lang/phase e)))
    (is (= {:sym 'nope} (:data e)))))

(deftest fn-as-relation
  (is (= :fn-as-relation (check-kind ['(defn f [x] x)] '(defrule r [?x] (ext/e ?x _) (f ?x))))))

(deftest arity
  (is (= :arity-mismatch (check-kind [s-rule] '(defrule r [?x] (s ?x ?x)))))
  (is (= :arity-mismatch (check-kind [s-rule] '(defrule r [?x] (ext/e ?x)))))
  (is (= :arity-mismatch (check-kind [s-rule] '(defrule s [?x] (ext/e ?x ?x)))))
  (is (= :arity-mismatch (check-kind [] '(defrule r [?x] (elem ?x)))))
  (is (= :arity-mismatch
         (check-kind ['(defstruct hdr [n] [a :u8])] '(defrule r [?x] (hdr ?x ?x ?x ?x))))))

(deftest unsafe-head
  (is (= :unsafe-head-var (check-kind [s-rule] '(defrule r [?x ?y] (s ?x _ _)))))
  (is (= :unsafe-head-var (check-kind [] '(defrule r [?x ?y] (ext/e ?x _) (elem ?y ?z)))))
  (is (= :unsafe-head-var (check-kind [] '(defrule r [?x ?y] (ext/e ?x _) (when (pos? ?y))))))
  (is (nil? (check-kind [] '(defrule r [?x ?y] (ext/e ?x _) (bind [?y] [?x]))))))

(deftest negation
  (is (= :unbound-in-negation
         (check-kind [s-rule] '(defrule r [?x] (ext/e ?x _) (not (s ?x ?y _))))))
  (is (nil? (check-kind [s-rule] '(defrule r [?x] (ext/e ?x _) (not (s ?x _ _))))))
  (testing "not before its binder"
    (is (nil? (check-kind [s-rule] '(defrule r [?x] (not (s ?x _ _)) (ext/e ?x _)))))
    (is (= :unbound-in-negation
           (check-kind [s-rule] '(defrule r {:ordered true} [?x] (not (s ?x _ _)) (ext/e ?x _))))))
  (testing "negating a computed relation is a filter"
    (let [f '(defrel ok [a b] ([a b ->] (< a b)))
          rule '(defrule r [?x ?y] (ext/e ?x ?y) (not (ok ?x ?y)))
          p (prog f)]
      (is (nil? (check-kind [f] rule)))
      (is (= :not (:lit (second (:body (an p rule)))))))
    (is (nil? (check-kind [] '(defrule r [?x] (ext/e ?x ?c) (not (elem ?c ?x)))))))
  (testing "alias foreign rule and ordered"
    (is (= :foreign-rule (check-kind [] '(defrule ext/foo [?x] (ext/e ?x _)))))))

(deftest defrel-dup-params
  (is (= :bad-form (:lang/error (err #(r/analyze-defrel (prog) 'a '(defrel d [a a] ([a ->] 1))))))))

(deftest bind-patterns
  (let [p (prog)
        a (an p '(defrule r [?a] (ext/e ?m _) (bind {:a ?a :b [?c & ?d]} ?m)))
        lit (second (:body a))
        n (:var-names a)]
    (is (= :bind (:lit lit)))
    (is (false? (:nil-ok? lit)))
    (is (= {:pmap [[:a {:pvar (n '?a)}]
                   [:b {:pvec [{:pvar (n '?c)}] :rest {:pvar (n '?d)}}]]}
           (:pat lit)))
    (is (true? (:nil-ok? (second (:body (an p '(defrule r [?a] (ext/e ?m _) (bind-nil ?a ?m))))))))
    (is (= {:pconst 5} (:pat (first (:body (an p '(defrule r [?a] (bind 5 ?a))))))))))

(deftest aggregate-one-clause
  (let [c1 '(defrule c [?k (count ?x)] (ext/e ?k ?x))]
    (is (nil? (check-kind [c1] c1)))
    (is (= {:pos 1 :agg 'count :args [1]} (first (:aggs (an (prog c1) c1)))))
    (let [c2 '(defrule c [?k (count ?x)] (ext/e ?x ?k))]
      (is (= :aggregate-multiple-clauses
             (:lang/error (err #(let [p (-> (prog c1) (ns/add-def 'a 'c (assoc (def-entry c2) :qname 'a/c)))]
                                  (r/check-program p [(an p c1) (an p c2)])))))))))

(deftest facts
  (let [m '(defrule m ["png" 1])
        a (an (prog m) m)]
    (is (empty? (:body a)))
    (is (nil? (check-kind [m] m))))
  (is (= :fact-not-ground (check-kind [] '(defrule m [?x]))))
  (is (= :wildcard-in-head (check-kind [] '(defrule m [_] (ext/e _ _))))))

(deftest foreign-rule
  (is (= :foreign-rule (check-kind [] '(defrule other/foo [?x] (ext/e ?x _))))))

(deftest bad-forms
  (is (= :bad-form (:lang/error (err #(an (prog) '(defrule r {:ordered 1} [?x]))))))
  (is (true? (:ordered? (an (prog) '(defrule r {:ordered true} [?x] (ext/e ?x _)))))))

(def hex-form
  '(defrel hex [bs s]
     ([bs -> s] [[(str bs "!")]])
     ([s -> bs] (when-let [x (and (not= s "") s)] [[x]]))))

(deftest defrel-modes
  (let [p (prog hex-form)
        a (r/analyze-defrel p 'a hex-form)]
    (is (= 'a/hex (:qname a)))
    (is (= [{:in [0] :out [1]} {:in [1] :out [0]}] (mapv #(select-keys % [:in :out]) (:modes a))))
    (is (nil? (err #(r/check-program p [a]))))
    (let [entry (r/compile-defrel a (atom {}))
          ctx (rt/make-ctx {})]
      (is (= 2 (:arity entry)))
      (is (= [["x!"]] ((:impl (first (:modes entry))) ctx ["x"])))
      (is (= [] ((:impl (second (:modes entry))) ctx [""]))))
    (let [bad '(defrel h2 [a b] ([a ->] true))
          e (err #(r/check-program p [(r/analyze-defrel p 'a bad)]))]
      (is (= :mode-coverage (:lang/error e)))
      (is (= :check (:lang/phase e))))
    (is (= :vector (-> a :modes first :body :op)) "bodies are analyzed")))

(deftest defrel-literal
  (is (nil? (check-kind [hex-form] '(defrule r [?s] (ext/e ?b _) (hex (str ?b) ?s)))))
  (is (= :arity-mismatch (check-kind [hex-form] '(defrule r [?s] (hex ?s))))))

(deftest defrel-bad-result
  (let [f '(defrel bad [a b] ([a -> b] 5) ([b -> a] [[1 2]]) ([a b ->] 5))
        p (prog f)
        entry (r/compile-defrel (r/analyze-defrel p 'a f) (atom {}))
        ctx (rt/make-ctx {})
        run (fn [i in] (err #((:impl (nth (:modes entry) i)) ctx in)))]
    (is (= :bad-relation-result (:lang/error (run 0 [1]))))
    (is (= :bad-relation-result (:lang/error (run 1 [1]))))
    (is (nil? (run 2 [1 2])))))
