(ns lang.runtime-test
  (:require [clojure.test :refer [deftest is]]
            [lang.runtime :as rt]))

(defn- kind [thunk]
  (try (thunk) nil
       (catch clojure.lang.ExceptionInfo e (:lang/error (ex-data e)))))

(deftest fuel-exhausts
  (let [ctx (rt/make-ctx {:limits {:fuel 10}})]
    (is (= :fuel-exhausted (kind #(rt/charge! ctx 11))))))

(deftest charge-nil-ctx
  (is (nil? (rt/charge! nil 5))))

(deftest call-budget
  (let [ctx (rt/make-ctx {:limits {:call-fuel 5}})]
    (is (= :call-fuel-exhausted
           (kind #(rt/with-call-budget ctx (fn [] (rt/charge! ctx 6))))))
    (rt/with-call-budget ctx (fn [] (rt/charge! ctx 3)))
    (is (nil? (kind #(rt/charge! ctx 5))))
    (is (= :call-fuel-exhausted (kind #(rt/charge! ctx 1))))))

(deftest depth
  (let [ctx (rt/make-ctx {})
        nest (fn nest [n] (if (zero? n) :ok (rt/with-depth ctx #(nest (dec n)))))]
    (is (= :ok (nest 512)))
    (is (= :depth-exceeded (kind #(nest 513))))
    (is (= :ok (nest 512)))))

(deftest memo-lru
  (let [ctx (rt/make-ctx {:limits {:max-memo-entries 2}})]
    (rt/memo-put! ctx :a 1)
    (rt/memo-put! ctx :b 2)
    (rt/memo-put! ctx :c 3)
    (is (= ::rt/miss (rt/memo-get ctx :a)))
    (is (= 3 (rt/memo-get ctx :c)))
    (rt/memo-put! ctx :n nil)
    (is (nil? (rt/memo-get ctx :n)))))

(deftest int-bits
  (let [ctx (rt/make-ctx {})
        big (bigint (.shiftLeft (biginteger 1) 5000))]
    (is (= :int-too-large (kind #(rt/check-int! ctx big))))
    (is (= 5 (rt/check-int! ctx 5)))
    (is (= (bigint 7) (rt/check-int! ctx (bigint 7))))))

(deftest bytes-and-size
  (let [ctx (rt/make-ctx {:limits {:max-bytes 10 :max-value-size 5}})]
    (rt/alloc-bytes! ctx 10)
    (is (= :bytes-exhausted (kind #(rt/alloc-bytes! ctx 1))))
    (is (nil? (kind #(rt/check-size! ctx 5))))
    (is (= :value-too-large (kind #(rt/check-size! ctx 6))))))

(deftest diagnostics-and-trace
  (let [events (atom [])
        ctx (rt/make-ctx {:trace #(swap! events conj %)})]
    (rt/diag! ctx :skipped {:x 1})
    (rt/diag! ctx :skipped {:x 2})
    (is (= 2 (get-in (rt/diagnostics ctx) [:counts :skipped])))
    (is (= 2 (count (:entries (rt/diagnostics ctx)))))
    (dotimes [i 1100] (rt/diag! ctx :k {:i i}))
    (is (= 1000 (count (:entries (rt/diagnostics ctx)))))
    (is (= 1100 (get-in (rt/diagnostics ctx) [:counts :k])))
    (rt/trace! ctx :ev)
    (is (= [:ev] @events))
    (is (nil? (rt/trace! (rt/make-ctx {}) :ev)))
    (is (= 65536 (rt/limit ctx :page-size)))))

(deftest isolated-stack
  (is (= 100000 (rt/run-isolated
                 #(letfn [(f [n] (if (zero? n) 0 (inc (f (dec n)))))] (f 100000)))))
  (is (= :stack-exhausted
         (kind #(rt/run-isolated
                 (fn [] (letfn [(f [n] (inc (f (inc n))))] (f 0)))))))
  (is (= :boom (kind #(rt/run-isolated (fn [] (lang.errors/error! :boom :run "x" {})))))))

(deftest timeout
  (let [ctx (rt/make-ctx {:limits {:timeout-ms 1}})]
    (Thread/sleep 5)
    (is (= :timeout (kind #(dotimes [_ 10] (rt/charge! ctx 70000)))))))
