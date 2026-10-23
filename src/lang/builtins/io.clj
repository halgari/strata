(ns lang.builtins.io
  "Host resource built-ins of lang.io (spec 4.6): open, size, read-bytes, read-all."
  (:require [lang.errors :refer [error!]]
            [lang.resource :as res]
            [lang.runtime :as rt]
            [lang.values :as v]))

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
  Handle reads go through the page cache, which accounts for any assembled
  allocation itself, so there is no extra alloc-bytes! charge here."
  [ctx h off len]
  (let [h (handle! h) off (long! off) len (long! len)]
    (rt/charge! ctx 1)
    (when (and (>= off 0) (>= len 0))
      (when (> len (long (rt/limit ctx :max-read)))
        (error! :read-too-large :run "Read exceeds the maximum read size" {:len len}))
      (res/src-read h ctx off len))))

(def fns
  {'open {:impl (fn [ctx name]
                  (rt/charge! ctx 1)
                  (if (string? name) (res/open-handle ctx name) (type-error name "Expected a string")))
          :arity [1 1]}
   'size {:impl size :arity [1 1]}
   'read-bytes {:impl read-bytes :arity [3 3]}
   'read-all {:impl (fn [ctx h] (read-bytes ctx h 0 (size ctx h))) :arity [1 1]}})
