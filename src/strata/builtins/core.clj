(ns strata.builtins.core
  "Scalar built-ins of strata.core: arithmetic, bits, u64, comparison, predicates (spec 4.6)."
  (:require [strata.errors :refer [error!]]
            [strata.order :as order]
            [strata.resource :as res]
            [strata.runtime :as rt]
            [strata.values :as v :refer [nan nan?]])
  (:import (clojure.lang BigInt)
           (java.math BigInteger)
           (strata.values Handle)))

(set! *warn-on-reflection* true)

;; ---------------------------------------------------------------- helpers

(defn type-error [x msg] (error! :type-error :run msg {:value x}))

(defn- num! [x]
  (if (or (number? x) (nan? x)) x (type-error x "Expected a number")))

(defn- integral? [x] (or (instance? Long x) (instance? BigInt x)))

(defn- int! [x]
  (if (integral? x) x (type-error x "Expected an integer")))

(defn- charge-args! [ctx args]
  (rt/charge! ctx (reduce (fn [^long acc x] (+ acc (v/weight x))) 0 args)))

(defn- finish [ctx x]
  (rt/check-int! ctx (v/canon-num x)))

(defn- numeric
  "Type-checks and charges args, short-circuits on NaN, else folds f (a promoting
  binary op) from init (or the first arg)."
  [ctx args init f]
  (run! num! args)
  (charge-args! ctx args)
  (if (some nan? args)
    nan
    (let [step (fn [a b] (finish ctx (f a b)))]
      (if (some? init)
        (reduce step init args)
        (reduce step (finish ctx (first args)) (rest args))))))

(defn- zero-divisor! [d]
  (when (zero? (double (if (instance? BigInt d) (.doubleValue ^BigInt d) d)))
    (error! :arithmetic-error :run "Division by zero" {})))

(defn- quot* [a b]
  (zero-divisor! b)
  (if (and (instance? Long a) (instance? Long b) (not (and (== (long a) Long/MIN_VALUE) (== (long b) -1))))
    (quot a b)
    (if (and (integral? a) (integral? b))
      (quot (bigint a) (bigint b))
      (quot a b))))

(defn- rem* [a b]
  (zero-divisor! b)
  (if (and (integral? a) (integral? b)) (rem (bigint a) (bigint b)) (rem a b)))

(defn- mod* [a b]
  (zero-divisor! b)
  (if (and (integral? a) (integral? b)) (mod (bigint a) (bigint b)) (mod a b)))

(defn- div* [a b]
  (zero-divisor! b)
  (if (and (integral? a) (integral? b))
    (if (zero? (rem* a b)) (quot* a b) (/ (double a) (double b)))
    (/ (double a) (double b))))

(defn- ->big ^BigInteger [x]
  (biginteger (int! x)))

(defn- shift-count
  "Non-negative shift count as a long; a BigInt count (always >= 2^63) clamps to Long/MAX_VALUE."
  ^long [n]
  (int! n)
  (when (neg? n) (error! :arithmetic-error :run "Negative shift count" {}))
  (if (instance? BigInt n) Long/MAX_VALUE (long n)))

(defn- shift-right* [^BigInteger b ^long n]
  (if (>= n (.bitLength b))
    (if (neg? (.signum b)) (BigInteger/valueOf -1) BigInteger/ZERO)
    (.shiftRight b (int n))))

(def ^:private u64-mask (.subtract (.shiftLeft BigInteger/ONE 64) BigInteger/ONE))

(defn- u64-op [f]
  (fn [ctx a b]
    (charge-args! ctx [a b])
    (v/canon-num (.and ^BigInteger (f (->big a) (->big b)) u64-mask))))

(defn- bit-op [f]
  (fn [ctx & args]
    (charge-args! ctx args)
    (finish ctx (reduce f (map ->big args)))))

(defn- shift-left [ctx x n]
  (charge-args! ctx [x n])
  (let [b (->big x) n (shift-count n) lim (long (rt/limit ctx :max-int-bits))]
    (cond
      (zero? (.signum b)) 0
      (or (> n lim) (> (+ (.bitLength b) n) lim)) (error! :int-too-large :run "Integer too large" {})
      :else (finish ctx (.shiftLeft b (int n))))))

(defn- shift-right [ctx x n]
  (charge-args! ctx [x n])
  (finish ctx (shift-right* (->big x) (shift-count n))))

(defn- unsigned-shift-right [ctx x n]
  (charge-args! ctx [x n])
  (int! x)
  (let [n (shift-count n)]
    (cond
      (instance? Long x) (if (>= n 64) 0 (unsigned-bit-shift-right (long x) n))
      (neg? (.signum (->big x))) (error! :arithmetic-error :run "Unsigned shift of negative big integer" {})
      :else (finish ctx (shift-right* (->big x) n)))))

(defn- chain-compare
  "Numeric-only chain comparison; false when any operand is NaN."
  [ctx args f]
  (run! num! args)
  (charge-args! ctx args)
  (if (some nan? args) false (boolean (apply f args))))

(defn- pred-num [f]
  (fn [ctx x]
    (rt/charge! ctx 1)
    (num! x)
    (if (nan? x) false (boolean (f x)))))

;; ------------------------------------------------------------------- str

(declare render!)

(defn- append! [ctx ^StringBuilder sb ^String s]
  (rt/charge! ctx (count s))
  (.append sb s)
  (rt/check-size! ctx (.length sb)))

(defn- render-seq! [ctx sb open close xs]
  (append! ctx sb open)
  (loop [xs (seq xs) first? true]
    (when xs
      (when-not first? (append! ctx sb " "))
      (render! ctx sb true (first xs))
      (recur (next xs) false)))
  (append! ctx sb close))

(defn- render! [ctx ^StringBuilder sb quote? x]
  (cond
    (nil? x) (append! ctx sb (if quote? "nil" ""))
    (string? x) (append! ctx sb (if quote? (pr-str x) x))
    (nan? x) (append! ctx sb "##NaN")
    (v/bytes-val? x) (append! ctx sb (str "#bytes[" (v/bsize x) "]"))
    (v/handle? x) (append! ctx sb (str "#handle[" (.-name ^Handle x) "]"))
    (v/deferred? x) (append! ctx sb (str "#deferred[" (v/deferred-offset x) " " (v/deferred-length x) "]"))
    (v/lang-fn? x) (append! ctx sb "#fn")
    (map? x) (do (append! ctx sb "{")
                 (loop [es (seq (order/ordered ctx x)) first? true]
                   (when es
                     (when-not first? (append! ctx sb ", "))
                     (render! ctx sb true (nth (first es) 0))
                     (append! ctx sb " ")
                     (render! ctx sb true (nth (first es) 1))
                     (recur (next es) false)))
                 (append! ctx sb "}"))
    (set? x) (render-seq! ctx sb "#{" "}" (order/ordered ctx x))
    (vector? x) (render-seq! ctx sb "[" "]" x)
    (sequential? x) (render-seq! ctx sb "(" ")" x)
    :else (append! ctx sb (if (char? x) (if quote? (pr-str x) (str x)) (str x)))))

(defn- str* [ctx & args]
  (charge-args! ctx args)
  (let [sb (StringBuilder.)]
    (run! #(render! ctx sb false %) args)
    (.toString sb)))

;; ------------------------------------------------------------------ table

(defn- fn1 [f] {:impl (fn [_ctx x] (f x)) :arity [1 1]})

(def fns
  {'+ {:impl (fn [ctx & args] (numeric ctx args 0 +')) :arity [0 nil]}
   '- {:impl (fn [ctx & args]
               (if (next args)
                 (numeric ctx args nil -')
                 (numeric ctx [(first args)] 0 -')))
       :arity [1 nil]}
   '* {:impl (fn [ctx & args] (numeric ctx args 1 *')) :arity [0 nil]}
   '/ {:impl (fn [ctx & args]
               (if (next args)
                 (numeric ctx args nil div*)
                 (numeric ctx [(first args)] 1 div*)))
       :arity [1 nil]}
   'quot {:impl (fn [ctx a b] (numeric ctx [a b] nil quot*)) :arity [2 2]}
   'rem {:impl (fn [ctx a b] (numeric ctx [a b] nil rem*)) :arity [2 2]}
   'mod {:impl (fn [ctx a b] (numeric ctx [a b] nil mod*)) :arity [2 2]}
   'inc {:impl (fn [ctx x] (numeric ctx [x] 0 (fn [_ b] (+' b 1)))) :arity [1 1]}
   'dec {:impl (fn [ctx x] (numeric ctx [x] 0 (fn [_ b] (-' b 1)))) :arity [1 1]}
   'abs {:impl (fn [ctx x] (numeric ctx [x] 0 (fn [_ b] (if (neg? b) (-' b) b)))) :arity [1 1]}
   'min {:impl (fn [ctx & args]
                 (run! num! args) (charge-args! ctx args)
                 (if (some nan? args) nan
                     (reduce (fn [a b] (if (pos? (order/compare-values ctx a b)) b a)) args)))
         :arity [1 nil]}
   'max {:impl (fn [ctx & args]
                 (run! num! args) (charge-args! ctx args)
                 (if (some nan? args) nan
                     (reduce (fn [a b] (if (neg? (order/compare-values ctx a b)) b a)) args)))
         :arity [1 nil]}

   'u64+ {:impl (u64-op #(.add ^BigInteger %1 ^BigInteger %2)) :arity [2 2]}
   'u64- {:impl (u64-op #(.subtract ^BigInteger %1 ^BigInteger %2)) :arity [2 2]}
   'u64* {:impl (u64-op #(.multiply ^BigInteger %1 ^BigInteger %2)) :arity [2 2]}

   'bit-and {:impl (bit-op #(.and ^BigInteger %1 ^BigInteger %2)) :arity [2 nil]}
   'bit-or {:impl (bit-op #(.or ^BigInteger %1 ^BigInteger %2)) :arity [2 nil]}
   'bit-xor {:impl (bit-op #(.xor ^BigInteger %1 ^BigInteger %2)) :arity [2 nil]}
   'bit-not {:impl (fn [ctx x] (charge-args! ctx [x]) (finish ctx (.not (->big x)))) :arity [1 1]}
   'bit-shift-left {:impl shift-left :arity [2 2]}
   'bit-shift-right {:impl shift-right :arity [2 2]}
   'unsigned-bit-shift-right {:impl unsigned-shift-right :arity [2 2]}
   'bit-test {:impl (fn [ctx x n]
                      (charge-args! ctx [x n])
                      (let [n (shift-count n) b (->big x)]
                        (if (>= n (.bitLength b)) (neg? (.signum b)) (.testBit b (int n)))))
              :arity [2 2]}

   '= {:impl (fn [ctx & args] (charge-args! ctx args) (run! #(rt/check-deep! ctx %) args) (boolean (apply = args))) :arity [1 nil]}
   'not= {:impl (fn [ctx & args] (charge-args! ctx args) (run! #(rt/check-deep! ctx %) args) (not (apply = args))) :arity [1 nil]}
   '< {:impl (fn [ctx & args] (chain-compare ctx args <)) :arity [1 nil]}
   '<= {:impl (fn [ctx & args] (chain-compare ctx args <=)) :arity [1 nil]}
   '> {:impl (fn [ctx & args] (chain-compare ctx args >)) :arity [1 nil]}
   '>= {:impl (fn [ctx & args] (chain-compare ctx args >=)) :arity [1 nil]}
   'compare {:impl (fn [ctx a b] (charge-args! ctx [a b]) (rt/check-deep! ctx a) (rt/check-deep! ctx b) (order/compare-values ctx a b)) :arity [2 2]}
   'zero? {:impl (pred-num zero?) :arity [1 1]}
   'pos? {:impl (pred-num pos?) :arity [1 1]}
   'neg? {:impl (pred-num neg?) :arity [1 1]}
   'even? {:impl (fn [ctx x] (rt/charge! ctx 1) (even? (int! x))) :arity [1 1]}
   'odd? {:impl (fn [ctx x] (rt/charge! ctx 1) (odd? (int! x))) :arity [1 1]}

   'nil? (fn1 nil?)
   'some? (fn1 some?)
   'string? (fn1 string?)
   'number? (fn1 #(or (number? %) (nan? %)))
   'integer? (fn1 integral?)
   'keyword? (fn1 keyword?)
   'map? (fn1 map?)
   'vector? (fn1 vector?)
   'set? (fn1 set?)
   'coll? (fn1 coll?)
   'bytes? (fn1 v/bytes-val?)
   'deferred? (fn1 v/deferred?)
   'identity (fn1 identity)
   'not (fn1 not)

   'str {:impl str* :arity [0 nil]}
   'name {:impl (fn [ctx x]
                  (charge-args! ctx [x])
                  (if (or (string? x) (keyword? x) (symbol? x)) (name x) (type-error x "Expected a name")))
          :arity [1 1]}
   'keyword {:impl (fn [ctx a & more]
                     (charge-args! ctx (cons a more))
                     (if more
                       (let [b (first more)]
                         (if (and (string? a) (string? b)) (keyword a b) (type-error a "Expected strings")))
                       (cond (keyword? a) a
                             (string? a) (keyword a)
                             (symbol? a) (keyword (namespace a) (name a))
                             :else (type-error a "Expected a string"))))
             :arity [1 2]}
   'parse-long {:impl (fn [ctx s]
                        (when-not (string? s) (type-error s "Expected a string"))
                        (rt/charge! ctx (count ^String s))
                        (parse-long s))
                :arity [1 1]}
   'parse-double {:impl (fn [ctx s]
                          (when-not (string? s) (type-error s "Expected a string"))
                          (rt/charge! ctx (count ^String s))
                          (some-> (parse-double s) v/canon-num))
                  :arity [1 1]}
   'force {:impl (fn [ctx d] (rt/charge! ctx 1) (res/force-value ctx d)) :arity [1 1]}
   'deferred-offset {:impl (fn [_ d] (if (v/deferred? d) (v/deferred-offset d) (type-error d "Expected a deferred value")))
                     :arity [1 1]}
   'deferred-length {:impl (fn [_ d] (if (v/deferred? d) (v/deferred-length d) (type-error d "Expected a deferred value")))
                     :arity [1 1]}})
