(ns lang.test-util
  "Shared helpers for tests that run code-language programs."
  (:require [lang.analyze.code :as ac]
            [lang.builtins :as b]
            [lang.compile.code :as cc]
            [lang.ns :as ns]
            [lang.runtime :as rt]))

(defn run-code
  "Loads one namespace of forms (an ns form followed by defns; the ns form is
  optional and defaults to (ns user)), then evaluates expr with a fresh ctx.
  opts: {:limits {…}}."
  ([forms expr] (run-code forms expr {}))
  ([forms expr opts]
   (let [[nsf forms] (if (and (seq? (first forms)) (= 'ns (ffirst forms)))
                       [(first forms) (rest forms)]
                       ['(ns user) forms])
         parsed (ns/parse-ns-form nsf)
         nm (:name parsed)
         defn-name (fn [f] (second f))
         prog (reduce (fn [p f]
                        (ns/add-def p nm (defn-name f)
                                    {:kinds #{:fn} :sub :defn :form f
                                     :qname (symbol (str nm) (str (defn-name f)))}))
                      (ns/add-namespace (ns/empty-program @b/registry {}) parsed)
                      forms)
         fn-table (atom {})]
     (doseq [f forms]
       (let [a (ac/analyze-defn prog nm f)]
         (swap! fn-table assoc (:qname a) (cc/compile-defn a fn-table))))
     (let [ctx (rt/make-ctx opts)
           compiled (cc/compile-node (ac/analyze prog nm expr (ac/new-scope)) fn-table)]
       (cc/eval-code ctx compiled {})))))
