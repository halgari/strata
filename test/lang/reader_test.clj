(ns lang.reader-test
  (:require [clojure.test :refer [deftest is testing]]
            [lang.reader :refer [read-forms]]))

(defn- err [src & [opts]]
  (try (read-forms src (or opts {})) nil
       (catch clojure.lang.ExceptionInfo e (ex-data e))))

(deftest reads-with-locations
  (let [fs (read-forms "(ns a)\n(defrule x [1])" {})]
    (is (= 2 (count fs)))
    (is (= 2 (:line (meta (second fs)))))
    (is (= 2 (:line (meta (first (rest (nth fs 1)))))) "symbol x has no meta but list does")))

(deftest rejects-tags
  (doseq [s ["#inst \"2020\"" "#foo 1" "#uuid \"00000000-0000-0000-0000-000000000000\""]]
    (is (= :tagged-literal (:lang/error (err s))) s)))

(deftest rejects-clojure-only-syntax
  (doseq [s ["#(inc %)" "@x" "`x" "#\"re\"" "^:foo [1]" "::k" "#'x" "~x" "#?(:clj 1)" "#=(+ 1 2)"]]
    (let [d (err s)]
      (is (some? d) s)
      (is (= :read (:lang/phase d)) s)))
  (is (= :unsupported-syntax (:lang/error (err "(a\n  @x)"))))
  (is (= [2 3] ((juxt :line :column) (err "(a\n  @x)")))))

(deftest unsupported-chars-in-strings-comments-ok
  (is (= ["#(@^`~ ::" 'a] (read-forms "\"#(@^`~ ::\" ; ^ @ # (\n a" {})))
  (is (= [\@ \[] (read-forms "\\@ \\[" {}))))

(deftest discard-and-sets-ok
  (is (= [#{1} 2] (read-forms "#_ 1 #{1} 2" {}))))

(deftest read-error
  (let [d (err "(a\n b")]
    (is (= :read-error (:lang/error d)))
    (is (= :read (:lang/phase d)))
    (is (= "Read error" (:message d)))
    (is (= 2 (:line d)))
    (is (pos-int? (:column d)))))

(deftest adversarial-regressions
  (doseq [s ["#! \"\n@x `y #(a %) #\"re\" #'v ::k\n;\"\n"
             ";x\r@y `z #\"re\"\n"
             "\"a\\\"\" @x"
             "\\\" @x"
             "\\; @x"
             "#"
             "#_ #_ 1 2 @x"
             "'x"
             "#\"a\""
             "1M" "1/2" "#=(+ 1 2)"]]
    (let [d (err s)]
      (is (some? d) s)
      (is (= :read (:lang/phase d)) s)))
  (is (= [(symbol "a")] (read-forms "#_ #_ 1 2 a" {})))
  (is (= :form-too-deep (:lang/error (err (apply str (repeat 100000 "[")) {:max-form-depth 100000}))))
  (is (= :form-too-deep (:lang/error (err (let [d (reduce (fn [a _] [a]) [] (range 100000))] [d]) {:max-form-depth 1000000}))))
  (is (= :bad-source (:lang/error (err 42))))
  (is (= :form-too-deep (:lang/error (err (str (apply str (repeat 256 "[")) (apply str (repeat 256 "]")) ) {:max-form-depth 255}))))
  (is (some? (read-forms (str (apply str (repeat 256 "[")) "1" (apply str (repeat 256 "]"))) {:max-form-depth 256}))))

(deftest depth-limit
  (let [deep (str (apply str (repeat 300 "[")) (apply str (repeat 300 "]")))]
    (is (= :form-too-deep (:lang/error (err deep {:max-form-depth 256}))))
    (is (= :form-too-deep (:lang/error (err deep))))
    (is (some? (read-forms (str "\"" (apply str (repeat 300 "[")) "\"") {:max-form-depth 256})))
    (is (some? (read-forms "\\[ \\[ ; [[[\n [[1]]" {:max-form-depth 4})))))

(deftest size-limit
  (is (= :source-too-large (:lang/error (err "(ns aaaaaaaaaaaaaaa)" {:max-source-bytes 10}))))
  (is (= :source-too-large (:lang/error (err "ééééééé" {:max-source-bytes 10})))))

(deftest forms-input
  (is (= ['(ns a) '(defn f [x] x)] (read-forms ['(ns a) '(defn f [x] x)] {})))
  (is (= :tagged-literal (:lang/error (err [(tagged-literal 'foo 1)]))))
  (is (= :form-too-deep (:lang/error (err [[[[1]]]] {:max-form-depth 2})))))
