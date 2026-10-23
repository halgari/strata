(ns strata.builtins
  "Registry of built-in namespaces (spec 2.5)."
  (:require [strata.builtins.coll]
            [strata.builtins.string]
            [strata.builtins.bytes]
            [strata.builtins.core]
            [strata.builtins.io]
            [strata.errors :refer [error!]]
            [strata.resource :as res]
            [strata.runtime :as rt]))

(def special-forms
  '#{let fn if if-let when when-let when-not cond case do loop recur
     and or quote -> ->> parse parse-explain})

(def builtin-namespaces '#{strata.core strata.string strata.bytes strata.io})

(def ^:private aggregates
  '#{count count-distinct sum min max collect collect-by collect-map})

;; ---------------------------------------------------------------- core relations

(defn- rel-entry
  "A computed relation entry with one mode binding in-idxs and producing out-idxs."
  [qname arity in out impl]
  {:qname qname :arity arity :memo? false :modes [{:in in :out out :impl impl}]})

(defn- bad-arg! [x what]
  (error! :type-error :run (str "Expected " what) {:value x}))

(defn- charged-count [ctx coll]
  (rt/charge! ctx (count coll))
  coll)

(defn- int! [x]
  (if (instance? Long x) (long x) (error! :type-error :run "Expected an integer" {:value x})))

(def ^:private core-relations
  {'elem (rel-entry 'strata.core/elem 2 [0] [1]
                    (fn [ctx [coll]]
                      (cond
                        (nil? coll) []
                        (or (sequential? coll) (set? coll))
                        (mapv vector (charged-count ctx coll))
                        (map? coll) (mapv (fn [e] [(vec e)]) (charged-count ctx coll))
                        :else (bad-arg! coll "a collection"))))
   'indexed (rel-entry 'strata.core/indexed 3 [0] [1 2]
                       (fn [ctx [coll]]
                         (cond
                           (nil? coll) []
                           (sequential? coll) (vec (map-indexed vector (charged-count ctx coll)))
                           :else (bad-arg! coll "a vector or list"))))
   'entry (rel-entry 'strata.core/entry 3 [0] [1 2]
                     (fn [ctx [m]]
                       (cond
                         (nil? m) []
                         (map? m) (mapv vec (charged-count ctx m))
                         :else (bad-arg! m "a map"))))
   'force (rel-entry 'strata.core/force 2 [0] [1]
                     (fn [ctx [d]]
                       (rt/charge! ctx 1)
                       (let [x (res/force-value ctx d)]
                         (if (nil? x) [] [[x]]))))
   'between (rel-entry 'strata.core/between 3 [0 1] [2]
                       (fn [ctx [lo hi]]
                         (if (or (nil? lo) (nil? hi))
                           []
                           (let [lo (int! lo) hi (int! hi)]
                             (rt/charge! ctx (min Long/MAX_VALUE (max 0 (-' hi lo))))
                             (map vector (range lo hi))))))})

;; Each entry is [ns-sym kind entries-map]. Later builtin tasks require their
;; namespace and add one line here, e.g. ['strata.core :fn strata.builtins.core/fns].
(def ^:private sources
  [['strata.core :fn strata.builtins.core/fns]
   ['strata.string :fn strata.builtins.string/fns]
   ['strata.bytes :fn strata.builtins.bytes/fns]
   ['strata.core :fn strata.builtins.coll/fns]
   ['strata.core :relation core-relations]
   ['strata.io :fn strata.builtins.io/fns]])

(defn- assemble []
  (reduce (fn [reg [ns-sym kind entries]]
            (update-in reg [ns-sym kind] merge entries))
          (into {}
                (map (fn [n] [n {:fn {} :relation {} :aggregate (if (= n 'strata.core) aggregates #{})}]))
                builtin-namespaces)
          sources))

(def registry (delay (assemble)))
