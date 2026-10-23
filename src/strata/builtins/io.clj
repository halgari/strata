(ns strata.builtins.io
  "Host resource built-ins of strata.io (spec 4.6): open, size, read-bytes, read-all."
  (:require [strata.errors :refer [error!]]
            [strata.resource :as res]
            [strata.runtime :as rt]
            [strata.values :as v]))

(set! *warn-on-reflection* true)

(defn- type-error [x msg] (error! :type-error :run msg {:value x}))

(defn- handle! [h]
  (if (v/handle? h) h (type-error h "Expected a handle")))

(defn- long! ^long [x]
  (if (instance? Long x) (long x) (type-error x "Expected an integer")))

(defn- size [ctx h]
  (rt/charge! ctx 1)
  (long (res/src-size (handle! h) ctx)))

(defn- read-bytes
  "Bytes at [off, off+len), or nil on a negative argument or a short read.
  Handle reads go through strata.resource, which enforces :max-read and
  charges the allocation itself."
  [ctx h off len]
  (let [h (handle! h) off (long! off) len (long! len)]
    (rt/charge! ctx 1)
    (when (and (>= off 0) (>= len 0))
      (res/src-read h ctx off len))))

(def fns
  {'open {:impl (fn [ctx name]
                  (rt/charge! ctx 1)
                  (if (string? name) (res/open-handle ctx name) (type-error name "Expected a string")))
          :arity [1 1]}
   'size {:impl size :arity [1 1]}
   'read-bytes {:impl read-bytes :arity [3 3]}
   'read-all {:impl (fn [ctx h] (read-bytes ctx h 0 (size ctx h))) :arity [1 1]}})
