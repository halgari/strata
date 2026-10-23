(ns strata.reader
  "EDN-only source reader: tag policy, syntax whitelist, size and depth limits."
  (:require [clojure.tools.reader :as r]
            [clojure.tools.reader.reader-types :as rt]
            [strata.errors :refer [error!]]))

(def ^:private default-max-bytes 10485760)
(def ^:private default-max-depth 256)
(def ^:private allowed-meta #{:line :column :end-line :end-column :file})

(defn- fail! [kind msg data] (error! kind :read msg data))

(defn- unsupported! [ns-name ch line col]
  (fail! :unsupported-syntax (str "Unsupported syntax: " ch)
         {:ns ns-name :line line :column col}))

(defn- tag-fail! [ns-name tag]
  (fail! :tagged-literal "Tagged literals are not allowed"
         {:ns ns-name :tag (str tag)}))

(defn- prescan!
  "Single pass over the source: enforces depth and rejects non-EDN syntax.
   Ignores strings, character literals and ; comments."
  [^String src ns-name max-depth]
  (let [n (count src)]
    (loop [i 0, line 1, col 1, depth 0, st :code]
      (when (< i n)
        (let [c (.charAt src i)
              nl? (= c \newline)
              peek (when (< (inc i) n) (.charAt src (inc i)))
              [st' depth']
              (case st
                :string (cond (= c \\) [:string-esc depth]
                              (= c \") [:code depth]
                              :else [:string depth])
                :string-esc [:string depth]
                :comment [(if (or nl? (= c \return)) :code :comment) depth]
                :char [:code depth]
                :code
                (case c
                  \" [:string depth]
                  \; [:comment depth]
                  \\ [:char depth]
                  (\( \[ \{) (let [d (inc depth)]
                               (when (> d max-depth)
                                 (fail! :form-too-deep "Form nesting too deep"
                                        {:ns ns-name :line line :column col}))
                               [:code d])
                  (\) \] \}) [:code (max 0 (dec depth))]
                  (\@ \` \~ \^ \') (unsupported! ns-name c line col)
                  \: (if (= peek \:)
                       (unsupported! ns-name "::" line col)
                       [:code depth])
                  \# (if (and peek (#{\( \" \' \= \? \: \!} peek))
                       (unsupported! ns-name (str c peek) line col)
                       [:code depth])
                  [:code depth]))]
          (recur (inc i) (if nl? (inc line) line) (if nl? 1 (inc col)) depth' st'))))))

(defn- plain-leaf? [x]
  (or (nil? x) (boolean? x) (instance? Long x) (instance? Double x)
      (instance? clojure.lang.BigInt x) (string? x) (char? x)
      (keyword? x) (symbol? x)))

(defn- check-forms!
  "Walks forms: rejects tagged literals and excess collection depth; any leaf
   that is not a plain EDN value; with check-meta? also rejects reader
   metadata beyond source locations."
  [forms ns-name max-depth check-meta?]
  (letfn [(walk [x d]
            (when (tagged-literal? x) (tag-fail! ns-name (:tag x)))
            (when (and check-meta? (seq (apply dissoc (meta x) allowed-meta)))
              (fail! :unsupported-syntax "Unsupported syntax: metadata" {:ns ns-name}))
            (cond
              (or (seq? x) (vector? x) (set? x) (map? x))
              (do (when (> d max-depth)
                    (fail! :form-too-deep "Form nesting too deep" {:ns ns-name}))
                  (if (map? x)
                    (doseq [[k v] x] (walk k (inc d)) (walk v (inc d)))
                    (doseq [e x] (walk e (inc d)))))
              (not (plain-leaf? x))
              (fail! :unsupported-syntax "Unsupported value" {:ns ns-name})
              (coll? x) (fail! :unsupported-syntax "Unsupported value" {:ns ns-name})))]
    (try (doseq [f forms] (walk f 1))
         (catch StackOverflowError _
           (fail! :form-too-deep "Form nesting too deep" {:ns ns-name})))
    forms))

(defn- read-string-forms [^String src ns-name]
  (let [tag-fn (fn [tag _] (throw (ex-info "tag" {::tag tag})))
        builtin (fn [tag] (fn [_] (tag-fn tag nil)))
        eof (Object.)
        rdr (rt/indexing-push-back-reader src)]
    (binding [r/*read-eval* false
              r/*data-readers* {'inst (builtin 'inst) 'uuid (builtin 'uuid)}
              r/*default-data-reader-fn* tag-fn]
      (try
        (loop [acc []]
          (let [f (r/read {:eof eof :read-cond nil} rdr)]
            (if (identical? f eof) acc (recur (conj acc f)))))
        (catch clojure.lang.ExceptionInfo e
          (let [d (ex-data e)]
            (cond
              (contains? d ::tag) (tag-fail! ns-name (::tag d))
              (:strata/error d) (throw e)
              :else (fail! :read-error "Read error"
                           {:ns ns-name :line (:line d) :column (or (:column d) (:col d))}))))
        (catch StackOverflowError _
          (fail! :form-too-deep "Form nesting too deep" {:ns ns-name}))
        (catch Exception _
          (fail! :read-error "Read error" {:ns ns-name}))))))

(defn read-forms
  "Reads source (String or sequential of forms) into a vector of forms."
  [source {:keys [ns-name max-source-bytes max-form-depth]}]
  (let [max-bytes (or max-source-bytes default-max-bytes)
        max-depth (or max-form-depth default-max-depth)]
    (when-not (or (string? source) (sequential? source))
      (fail! :bad-source "Source must be a string or a sequence of forms" {:ns ns-name}))
    (if (string? source)
      (do
        (when (> (alength (.getBytes ^String source "UTF-8")) max-bytes)
          (fail! :source-too-large "Source too large" {:ns ns-name :max max-bytes}))
        (prescan! source ns-name max-depth)
        (check-forms! (read-string-forms source ns-name) ns-name max-depth true))
      (check-forms! (vec source) ns-name max-depth false))))
