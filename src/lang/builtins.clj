(ns lang.builtins
  "Registry of built-in namespaces (spec 2.5)."
  (:require [lang.builtins.coll]
            [lang.builtins.string]
            [lang.builtins.bytes]
            [lang.builtins.core]))

(def special-forms
  '#{let fn if if-let when when-let when-not cond case do loop recur
     and or quote -> ->> parse parse-explain})

(def builtin-namespaces '#{lang.core lang.string lang.bytes lang.io})

(def ^:private aggregates
  '#{count count-distinct sum min max collect collect-by collect-map})

;; Each entry is [ns-sym kind entries-map]. Later builtin tasks require their
;; namespace and add one line here, e.g. ['lang.core :fn lang.builtins.core/fns].
(def ^:private sources
  [['lang.core :fn lang.builtins.core/fns]
   ['lang.string :fn lang.builtins.string/fns]
   ['lang.bytes :fn lang.builtins.bytes/fns]
   ['lang.core :fn lang.builtins.coll/fns]])

(defn- assemble []
  (reduce (fn [reg [ns-sym kind entries]]
            (update-in reg [ns-sym kind] merge entries))
          (into {}
                (map (fn [n] [n {:fn {} :relation {} :aggregate (if (= n 'lang.core) aggregates #{})}]))
                builtin-namespaces)
          sources))

(def registry (delay (assemble)))
