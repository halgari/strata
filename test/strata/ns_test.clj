(ns strata.ns-test
  (:require [clojure.test :refer [deftest is testing]]
            [strata.builtins :as b]
            [strata.ns :as ns]))

(defn- err [f]
  (try (f) nil (catch clojure.lang.ExceptionInfo e (ex-data e))))

(def stub-registry
  {'strata.core {:fn {'force {:impl identity :arity [1 1]}}
               :relation {'force {:qname 'strata.core/force :arity 2}
                          'elem {:qname 'strata.core/elem :arity 2}}
               :aggregate '#{count}}})

(defn- prog [] (ns/empty-program stub-registry {'host.input {'bytes 2}}))

(deftest parse-ns
  (is (= {:name 'a.b
          :attrs {:endian :be}
          :requires [{:ns 'strata.string :as 'str :refer []}
                     {:ns 'c.d :as nil :refer '[x y]}]}
         (ns/parse-ns-form '(ns a.b {:endian :be}
                              (:require [strata.string :as str] [c.d :refer [x y]])))))
  (is (= :bad-ns-form (:strata/error (err #(ns/parse-ns-form '(ns a (:use b)))))))
  (is (= :bad-ns-form (:strata/error (err #(ns/parse-ns-form '(ns a {:endian :middle})))))))

(deftest order
  (is (= '[b a] (ns/order-namespaces '{a [(ns a (:require [b]))] b [(ns b)]} {:builtins #{}})))
  (let [e (err #(ns/order-namespaces '{a [(ns a (:require [b]))] b [(ns b (:require [a]))]} {}))]
    (is (= :require-cycle (:strata/error e)))
    (is (= "[a b a]" (get-in e [:data :chain]))))
  (is (= :withheld-namespace
         (:strata/error (err #(ns/order-namespaces '{a [(ns a (:require [strata.io :as io]))]}
                                                 {:builtins '#{strata.string}})))))
  (is (= '[a] (ns/order-namespaces '{a [(ns a (:require [strata.core] [host.input]))]}
                                   {:builtins #{} :externs '{host.input {bytes 2}}})))
  (is (= :reserved-namespace
         (:strata/error (err #(ns/order-namespaces '{strata.x [(ns strata.x)]} {})))))
  (is (= :unknown-namespace
         (:strata/error (err #(ns/order-namespaces '{a [(ns a (:require [zzz]))]} {})))))
  (is (= :ns-name-mismatch
         (:strata/error (err #(ns/order-namespaces '{a [(ns other)]} {})))))
  (is (= :name-collision
         (:strata/error (err #(ns/order-namespaces '{a [(ns a)]} {:externs '{a {r 1}}})))))
  (is (= :name-collision
         (:strata/error (err #(ns/order-namespaces {} {:externs '{strata.io {r 1}}}))))))

(deftest positional-resolution
  (let [p (prog)
        f (ns/resolve-name p 'a 'force :fn)
        r (ns/resolve-name p 'a 'force :relation)]
    (is (and f r (not= f r)))
    (is (= 'strata.core/force (:qname f)))
    (is (true? (:builtin? r)))
    (is (= {:qname 'strata.core/count :def {:kind :aggregate} :builtin? true}
           (ns/resolve-name p 'a 'count :aggregate)))
    (is (nil? (ns/resolve-name p 'a 'count :fn)))
    (is (some? (ns/resolve-name p 'a 'core/force :fn)))
    (is (= {:qname 'host.input/bytes :def {:kinds #{:relation} :sub :extern :arity 2} :builtin? false}
           (ns/resolve-name (ns/add-namespace p {:name 'a :attrs {} :requires [{:ns 'host.input :as 'in :refer []}]})
                            'a 'in/bytes :relation)))))

(deftest kinds
  (let [p (-> (prog) (ns/add-def 'a 'foo {:kinds #{:fn} :sub :defn :qname 'a/foo :form '(defn foo [])}))]
    (is (= :kind-conflict
           (:strata/error (err #(ns/add-def p 'a 'foo {:kinds #{:relation} :sub :rule :qname 'a/foo :form '(defrule foo)})))))
    (is (= :duplicate-definition
           (:strata/error (err #(ns/add-def p 'a 'foo {:kinds #{:fn} :sub :defn :qname 'a/foo :form '(defn foo [])}))))))
  (let [p (-> (prog)
              (ns/add-def 'a 'r {:kinds #{:relation} :sub :rule :qname 'a/r :form '(defrule r 1)})
              (ns/add-def 'a 'r {:kinds #{:relation} :sub :rule :qname 'a/r :form '(defrule r 2)}))]
    (is (= '[(defrule r 1) (defrule r 2)] (get-in p [:namespaces 'a :defs 'r :clauses]))))
  (let [p (ns/add-def (prog) 'a 's {:kinds #{:relation :type} :sub :struct :qname 'a/s :form '(defstruct s)})]
    (is (some? (ns/resolve-name p 'a 's :relation)))
    (is (some? (ns/resolve-name p 'a 's :type)))
    (is (nil? (ns/resolve-name p 'a 's :fn)))))

(deftest alias-and-refer
  (let [p (-> (prog)
              (ns/add-def 'c.d 'x {:kinds #{:fn} :sub :defn :qname 'c.d/x :form '(defn x [])})
              (ns/add-def 'c.d 'y {:kinds #{:fn} :sub :defn :qname 'c.d/y :form '(defn y [])})
              (ns/add-namespace (ns/parse-ns-form '(ns c.d)))
              (ns/add-namespace (ns/parse-ns-form '(ns a (:require [c.d :as cd :refer [x]])))))]
    (is (= 'c.d/y (:qname (ns/resolve-name p 'a 'cd/y :fn))))
    (is (= 'c.d/y (:qname (ns/resolve-name p 'a 'c.d/y :fn))))
    (is (= 'c.d/x (:qname (ns/resolve-name p 'a 'x :fn))))
    (is (nil? (ns/resolve-name p 'a 'y :fn)))
    (is (nil? (ns/resolve-name p 'a 'nope/y :fn)))))

(deftest shadow-warning
  (let [p (-> (prog)
              (ns/add-def 'a 'elem {:kinds #{:relation} :sub :defrel :qname 'a/elem :form '(defrel elem)})
              (ns/add-def 'a 'other {:kinds #{:relation} :sub :defrel :qname 'a/other :form '(defrel other)}))]
    (is (= [{:ns 'a :sym 'elem :position :relation}] (vec (ns/shadow-warnings p))))
    (is (= 'a/elem (:qname (ns/resolve-name p 'a 'elem :relation))))))

(deftest builtins-registry
  (let [r @b/registry]
    (is (= '#{strata.core strata.string strata.bytes strata.io} (set (keys r))))
    (is (contains? (get-in r ['strata.core :aggregate]) 'count))
    (is (contains? b/special-forms 'parse-explain))))
