(ns lang.builtins.string
  "String built-ins of lang.string, including fuel-metered regex (spec 4.6)."
  (:require [clojure.string :as str]
            [lang.builtins.core :as core :refer [type-error]]
            [lang.errors :refer [error!]]
            [lang.runtime :as rt])
  (:import (java.util.regex Matcher Pattern PatternSyntaxException)))

(set! *warn-on-reflection* true)

;; ---------------------------------------------------------------- helpers

(defn- str! ^String [x]
  (if (string? x) x (type-error x "Expected a string")))

(defn- long! ^long [x]
  (if (instance? Long x) (long x) (type-error x "Expected an integer")))

(defn- in!
  "Type-checks a string argument and charges 1 fuel per character."
  ^String [ctx x]
  (let [s (str! x)]
    (rt/charge! ctx (.length s))
    s))

(defn- sized
  "Checks the size of a string result and charges for its characters."
  [ctx ^String s]
  (rt/check-size! ctx (.length s))
  (rt/charge! ctx (.length s))
  s)

(defn- sized-vec [ctx v]
  (rt/check-size! ctx (count v))
  (rt/charge! ctx (count v))
  v)

(defn- opt-index [^long i] (when-not (neg? i) i))

;; ------------------------------------------------------------------ regex

(defn- metered
  "A CharSequence over s whose charAt charges 1 fuel and checks for interrupts."
  ^CharSequence [ctx ^String s]
  (reify CharSequence
    (length [_] (.length s))
    (charAt [_ i]
      (rt/charge! ctx 1)
      (when (Thread/interrupted)
        (error! :timeout :run "Interrupted" {}))
      (.charAt s i))
    (subSequence [_ a b] (.subSequence s a b))
    (toString [_] s)))

(defn- compile-re ^Pattern [ctx p]
  (let [p (str! p)]
    (when (> (.length p) (long (rt/limit ctx :max-regex-length)))
      (error! :regex-too-long :run "Regex too long" {}))
    (rt/charge! ctx (.length p))
    (try (Pattern/compile p)
         (catch PatternSyntaxException _
           (error! :bad-regex :run "Invalid regular expression" {})))))

(defn- groups [^Matcher m]
  (if (zero? (.groupCount m))
    (.group m)
    (into [] (map #(.group m (int %))) (range (inc (.groupCount m))))))

(defn- re-find* [ctx p s]
  (let [pat (compile-re ctx p)
        m (.matcher pat (metered ctx (str! s)))]
    (when (.find m) (groups m))))

(defn- re-matches* [ctx p s]
  (let [pat (compile-re ctx p)
        m (.matcher pat (metered ctx (str! s)))]
    (when (.matches m) (groups m))))

(defn- re-seq* [ctx p s]
  (let [pat (compile-re ctx p)
        m (.matcher pat (metered ctx (str! s)))]
    (loop [acc (transient [])]
      (if (.find m)
        (do (rt/check-size! ctx (count acc))
            (recur (conj! acc (groups m))))
        (persistent! acc)))))

(defn- re-split* [ctx p s]
  (let [pat (compile-re ctx p)
        parts (.split pat (metered ctx (str! s)) -1)]
    (sized-vec ctx (vec parts))))

;; ----------------------------------------------------------------- others

(defn- split* [ctx s sep]
  (let [s (in! ctx s)
        sep (str! sep)]
    (sized-vec ctx (vec (.split (Pattern/compile (Pattern/quote sep)) s -1)))))

(defn- join* [ctx a b]
  (let [[sep coll] (if (some? b) [(str! a) b] ["" a])
        sb (StringBuilder.)
        render (:impl (get core/fns 'str))]
    (when-not (or (nil? coll) (coll? coll)) (type-error coll "Expected a collection"))
    (loop [xs (seq coll) first? true]
      (when xs
        (when-not first? (.append sb ^String sep))
        (.append sb ^String (render ctx (first xs)))
        (rt/check-size! ctx (.length sb))
        (recur (next xs) false)))
    (sized ctx (.toString sb))))

(defn- ch! ^String [c]
  (cond (char? c) (str c)
        (and (string? c) (= 1 (count ^String c))) c
        :else (type-error c "Expected a single character")))

(defn- pad [left?]
  (fn [ctx s n c]
    (let [s (in! ctx s)
          n (long! n)
          c (ch! c)]
      (rt/check-size! ctx n)
      (let [missing (- n (.length s))]
        (if (pos? missing)
          (let [fill (str/join (repeat missing c))]
            (rt/charge! ctx missing)
            (if left? (str fill s) (str s fill)))
          s)))))

(defn- subs* [ctx s start end]
  (let [s (in! ctx s)
        start (long! start)
        end (if (some? end) (long! end) (.length s))]
    (when (and (<= 0 start) (<= start end) (<= end (.length s)))
      (.substring s (int start) (int end)))))

(defn- replace* [ctx s match rep]
  (let [s (in! ctx s) match (str! match) rep (str! rep)]
    (if (.isEmpty match)
      s
      (let [sb (StringBuilder.)]
        (loop [from 0]
          (let [i (.indexOf s match (int (long from)))]
            (if (neg? i)
              (.append sb s (int from) (.length s))
              (do (.append sb s (int from) (int i))
                  (.append sb rep)
                  (rt/check-size! ctx (.length sb))
                  (recur (+ i (.length match)))))))
        (sized ctx (.toString sb))))))

(defn- search [last?]
  (fn [ctx s sub from]
    (let [s (in! ctx s) sub (str! sub)]
      (if last?
        (opt-index (.lastIndexOf s sub (int (if (some? from) (long! from) (.length s)))))
        (opt-index (.indexOf s sub (int (if (some? from) (long! from) 0))))))))

(defn- fn-s
  "A one-string-argument entry."
  [f]
  {:impl (fn [ctx s] (f (in! ctx s))) :arity [1 1]})

(defn- test2 [f]
  {:impl (fn [ctx s x] (let [s (in! ctx s)] (boolean (f s (str! x))))) :arity [2 2]})

;; ------------------------------------------------------------------ table

(def fns
  {'split {:impl split* :arity [2 2]}
   'split-lines {:impl (fn [ctx s] (sized-vec ctx (str/split-lines (in! ctx s)))) :arity [1 1]}
   'join {:impl (fn [ctx a & [b]] (join* ctx a b)) :arity [1 2]}
   'trim (fn-s str/trim)
   'triml (fn-s str/triml)
   'trimr (fn-s str/trimr)
   'pad-left {:impl (pad true) :arity [3 3]}
   'pad-right {:impl (pad false) :arity [3 3]}
   'blank? (fn-s str/blank?)
   'starts-with? (test2 #(.startsWith ^String %1 ^String %2))
   'ends-with? (test2 #(.endsWith ^String %1 ^String %2))
   'includes? (test2 #(.contains ^String %1 ^CharSequence %2))
   'index-of {:impl (fn [ctx s sub & [from]] ((search false) ctx s sub from)) :arity [2 3]}
   'last-index-of {:impl (fn [ctx s sub & [from]] ((search true) ctx s sub from)) :arity [2 3]}
   'subs {:impl (fn [ctx s start & [end]] (subs* ctx s start end)) :arity [2 3]}
   'replace {:impl replace* :arity [3 3]}
   'lower-case (fn-s #(.toLowerCase ^String %))
   'upper-case (fn-s #(.toUpperCase ^String %))
   'chars {:impl (fn [ctx s] (sized-vec ctx (vec (in! ctx s)))) :arity [1 1]}
   're-find {:impl re-find* :arity [2 2]}
   're-matches {:impl re-matches* :arity [2 2]}
   're-seq {:impl re-seq* :arity [2 2]}
   're-split {:impl re-split* :arity [2 2]}})
