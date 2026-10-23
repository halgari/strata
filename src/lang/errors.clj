(ns lang.errors
  "Structured language errors. Messages from host throwables are never exposed.")

(def ^:private max-str 2048)

(defn safe-str
  "Bounded printed representation of x."
  [x]
  (let [s (binding [*print-length* 20
                    *print-level* 4]
            (pr-str x))]
    (if (> (count s) max-str)
      (str (subs s 0 max-str) "…")
      s)))

(defn loc-of
  "Source location {:line :column} from form metadata, or {}."
  [form]
  (let [m (meta form)]
    (cond-> {}
      (:line m) (assoc :line (:line m))
      (:column m) (assoc :column (:column m)))))

(defn error!
  "Throws a language error as an ex-info."
  [kind phase msg data]
  (throw (ex-info msg
                  (merge {:lang/error kind :lang/phase phase :message msg}
                         (select-keys data [:ns :line :column])
                         {:form (safe-str (:form data))
                          :data (dissoc data :ns :line :column :form)}))))

(defn lang-error? [x]
  (boolean (and (instance? clojure.lang.ExceptionInfo x)
                (contains? (ex-data x) :lang/error))))

(def ^:private kind-messages
  {:stack-exhausted "Stack exhausted"
   :type-error "Type error"
   :arity-error "Wrong number of arguments"
   :arithmetic-error "Arithmetic error"
   :out-of-memory "Out of memory"
   :internal-error "Internal error"})

(defn- kind-of [^Throwable t]
  (cond
    (instance? StackOverflowError t) :stack-exhausted
    (instance? clojure.lang.ArityException t) :arity-error
    (instance? ClassCastException t) :type-error
    (instance? ArithmeticException t) :arithmetic-error
    (instance? OutOfMemoryError t) :out-of-memory
    :else :internal-error))

(defn map-throwable
  "Converts any throwable to a language error; lang errors pass through."
  [^Throwable t phase]
  (if (lang-error? t)
    t
    (let [kind (kind-of t)
          msg (kind-messages kind)]
      (ex-info msg {:lang/error kind :lang/phase phase :message msg :form "" :data {}}))))
