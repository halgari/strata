(ns lang.api
  "Public host API (spec 7.1): load, run, query, relation, stats, diagnostics,
  and host-side parse for testing parsers."
  (:refer-clojure :exclude [load])
  (:require [lang.compile.struct :as cs]
            [lang.errors :refer [error!]]
            [lang.program :as p]
            [lang.resource :as res]
            [lang.runtime :as rt]
            [lang.values :as v]))

(def bytes-resource res/bytes-resource)
(def file-resource res/file-resource)

(def ^:private load-opt-keys #{:sources :builtins :externs :limits})

(defn load
  "Compiles host sources into an immutable program. Accepts :sources
  :builtins :externs :limits; any other option, or an unknown :limits key,
  is a :bad-option error."
  [opts]
  (when-let [bad (seq (remove load-opt-keys (keys opts)))]
    (error! :bad-option :load "Unknown load option" {:options (vec bad)}))
  (rt/check-limits! :load (:limits opts))
  (p/load-program opts))

(defn- stored-rels [prog]
  (-> (set (keys (:plans prog)))
      (into (keys (:facts prog)))
      (into (for [[n rels] (:externs prog), r (keys rels)] (symbol (str n) (str r))))))

(def ^:private run-opt-keys #{:facts :resources :limits :trace :on-code-error})

(defn run
  "Evaluates prog over {:facts :resources :limits :trace :on-code-error} and
  returns the db {:relations :diagnostics :stats :tainted :stored}. A nil
  tuple collection for a declared extern counts as empty. The db holds no
  open handles, page cache or run context; tuples may still carry inert
  Handle values that reference the host Resource objects."
  [prog opts]
  (when-let [bad (seq (remove run-opt-keys (keys opts)))]
    (error! :bad-option :run "Unknown run option" {:options (vec bad)}))
  (rt/check-limits! :run (:limits opts))
  (-> (p/run-program prog (update opts :facts
                                  (fn [fs] (into {} (map (fn [[q ts]] [q (if (nil? ts) [] ts)])) fs))))
      (assoc :stored (stored-rels prog))))

(defn relation
  "The set of tuples of relation qsym in db."
  [db qsym]
  (get-in db [:relations qsym] #{}))

(defn warnings
  "Non-fatal load warnings of prog (e.g. shadowed names)."
  [prog]
  (:warnings prog))

(defn stats [db] (:stats db))
(defn tainted
  "Relations affected by skipped code errors (see :on-code-error :skip)."
  [db]
  (:tainted db))
(defn diagnostics [db] (:diagnostics db))

(defn- var-sym? [t] (and (symbol? t) (= \? (first (name t)))))

(defn query
  "Matches pattern (rel-sym term…) against a stored relation. Terms are ?vars,
  _ or constants. Returns a set of {?var value} maps."
  [db pattern]
  (let [[q & terms] pattern]
    (when-not (and (symbol? q) (namespace q) (contains? (:stored db) q))
      (error! :not-a-stored-relation :run "Query must name a stored relation" {:rel q}))
    (set (keep (fn [t]
                 (when (= (count t) (count terms))
                   (reduce (fn [m [term v]]
                             (cond
                               (= '_ term) m
                               (var-sym? term) (if (contains? m term)
                                                 (if (= (m term) v) m (reduced nil))
                                                 (assoc m term v))
                               (= (v/canon term) v) m
                               :else (reduced nil)))
                           {} (map vector terms t))))
               (relation db q)))))

(defn- host-parse [prog qsym resource f]
  (let [compiled (get (:struct-table prog) qsym)]
    (when-not (:parse compiled)
      (error! :unknown-struct :run "Not a struct" {:rel qsym}))
    (when (pos? (:arity compiled 0))
      (error! :type-arity :run "Parameterized structs cannot be parsed from the host" {:rel qsym}))
    (when-not (satisfies? res/Resource resource)
      (error! :bad-resource :run "Expected a Resource" {:rel qsym}))
    (rt/run-isolated
     (fn []
       (let [ctx (rt/make-ctx {:limits (:limits prog) :resources {"resource" resource}})]
         (try (f ctx compiled (res/open-handle ctx "resource"))
              (finally (reset! (:page-cache ctx) {}))))))))

(defn parse
  "Parses resource with struct qsym at offset 0: {:value :end}, or nil."
  [prog qsym resource]
  (host-parse prog qsym resource (fn [ctx c src] ((:parse c) ctx src 0 []))))

(defn parse-explain
  "Like parse, but returns {:ok true :value :end} or {:ok false :path :offset :reason}."
  [prog qsym resource]
  (host-parse prog qsym resource (fn [ctx c src] (cs/explain-parse ctx c src 0 []))))
