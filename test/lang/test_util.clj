(ns lang.test-util
  "Shared helpers for tests that run code-language programs."
  (:require [lang.analyze.code :as ac]
            [lang.builtins :as b]
            [lang.analyze.struct :as as]
            [lang.compile.code :as cc]
            [lang.compile.struct :as cs]
            [lang.ns :as ns]
            [lang.runtime :as rt]
            [lang.values :as v]))

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

(defn- def-entry [f]
  (case (first f)
    defstruct {:kinds #{:relation :type} :sub :struct}
    deftype {:kinds #{:type} :sub :deftype}
    defn {:kinds #{:fn} :sub :defn}))

(defn parse-src
  "Loads forms (optional leading ns form, then defstruct / deftype / defn),
  then parses byte-vec with the struct named struct-sym at offset 0. Returns
  {:value :end} or nil. opts: {:limits {…} :args [...] :off n :explain? bool :relation? bool};
  :explain? returns explain-parse's result, :relation? the relation impl's."
  ([forms struct-sym byte-vec] (parse-src forms struct-sym byte-vec {}))
  ([forms struct-sym byte-vec opts]
   (let [[nsf forms] (if (and (seq? (first forms)) (= 'ns (ffirst forms)))
                       [(first forms) (rest forms)]
                       ['(ns user) forms])
         parsed (ns/parse-ns-form nsf)
         nm (:name parsed)
         prog (reduce (fn [p f]
                        (ns/add-def p nm (second f)
                                    (assoc (def-entry f) :form f
                                           :qname (symbol (str nm) (str (second f))))))
                      (ns/add-namespace (ns/empty-program @b/registry {}) parsed)
                      forms)
         fn-table (atom {})
         struct-table (atom {})]
     (doseq [f forms :when (= 'defn (first f))]
       (let [a (ac/analyze-defn prog nm f)]
         (swap! fn-table assoc (:qname a) (cc/compile-defn a fn-table))))
     (doseq [f forms :when (#{'defstruct 'deftype} (first f))]
       (let [c (if (= 'defstruct (first f))
                 (cs/compile-struct (as/analyze-struct prog nm f) struct-table fn-table)
                 (cs/compile-deftype (as/analyze-deftype prog nm f) struct-table fn-table))]
         (swap! struct-table assoc (:qname c) c)))
     (let [ctx (rt/make-ctx opts)
           compiled (get @struct-table (symbol (str nm) (str struct-sym)))
           src (v/wrap-bytes (byte-array (map unchecked-byte byte-vec)))
           args (vec (:args opts))
           off (:off opts 0)]
       (rt/run-isolated
        #(cond
           (:explain? opts) (cs/explain-parse ctx compiled src off args)
           (:relation? opts) ((:impl (first (:modes (cs/struct-relation compiled)))) ctx (into [src off] args))
           :else ((:parse compiled) ctx src off args)))))))
