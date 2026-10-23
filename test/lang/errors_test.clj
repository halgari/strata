(ns lang.errors-test
  (:require [clojure.string :as str]
            [clojure.test :refer [deftest is]]
            [lang.errors :refer [error! lang-error? safe-str map-throwable]]))

(deftest error-shape
  (let [d (try (error! :unresolved-symbol :resolve "Unknown symbol foo"
                       {:ns 'a.b :line 3 :column 5 :form '(foo 1) :sym 'foo})
               (catch Exception e (ex-data e)))]
    (is (= :unresolved-symbol (:lang/error d)))
    (is (= :resolve (:lang/phase d)))
    (is (= 3 (:line d)))
    (is (= "(foo 1)" (:form d)))
    (is (= {:sym "foo"} (:data d)))))

(deftest safe-str-truncates
  (is (<= (count (safe-str (range 100000))) 2049))
  (is (str/includes? (safe-str (vec (range 30))) "...")))

(deftest map-throwable-hides-messages
  (let [e (map-throwable (ClassCastException. "/secret/path") :run)]
    (is (= :type-error (:lang/error (ex-data e))))
    (is (not (str/includes? (ex-message e) "secret"))))
  (let [e (map-throwable (StackOverflowError. "secret") :run)]
    (is (= :stack-exhausted (:lang/error (ex-data e))))
    (is (not (str/includes? (ex-message e) "secret")))))

(deftest lang-error-passthrough
  (let [e (try (error! :x :run "m" {}) (catch Exception e e))]
    (is (lang-error? e))
    (is (identical? e (map-throwable e :run)))
    (is (not (lang-error? (RuntimeException. "x"))))))
