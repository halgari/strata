(ns lang.sandbox-test
  "Sandbox and robustness suite, driven only through lang.api (spec 7.4, 8)."
  (:require [clojure.java.io :as io]
            [clojure.string :as str]
            [clojure.test :refer [deftest is testing]]
            [lang.api :as lang])
  (:import (java.nio.file Files)
           (java.nio.file.attribute FileAttribute)
           (java.util.zip Deflater)))

(defn- err [f]
  (try (f) nil (catch clojure.lang.ExceptionInfo ex (ex-data ex))))

(def ^:private externs {'host.input {'go 1 'blob 1}})
(def ^:private go-facts {'host.input/go [[1]]})

(defn- prog
  "Loads one namespace `t` requiring host.input as `in` and lang.bytes as `b`."
  [body & [opts]]
  (lang/load (merge {:sources {'t (str "(ns t (:require [host.input :as in] [lang.bytes :as b]))\n" body)}
                     :builtins '#{lang.bytes lang.io}
                     :externs externs}
                    opts)))

(defn- run [p & [opts]]
  (lang/run p (merge {:facts go-facts} opts)))

(defn- run-err [body & [load-opts run-opts]]
  (err #(run (prog body load-opts) run-opts)))

(deftest no-interop
  (doseq [form ["(System/exit 0)" "(.getRuntime Runtime)" "(new java.io.File \"x\")"
                "(clojure.core/eval 1)" "(java.lang.Thread/sleep 1)"]]
    (let [e (err #(prog (str "(defn f [x] " form ")")))]
      (is (= :unresolved-symbol (:lang/error e)) form)
      (is (not= :run (:lang/phase e)) form))))

(deftest no-tags
  (doseq [form ["#=(+ 1 2)" "#java.io.File \"x\""]]
    (let [e (err #(prog (str "(defn f [x] " form ")")))]
      (is (= :read (:lang/phase e)) form))))

(def ^:private spin-rule
  "(defrule r [?y] (in/go ?x) (spin ?x ?y))")

(deftest infinite-loop
  (let [e (run-err (str "(defrel spin [x y] ([x -> y] (loop [] (recur))))" spin-rule))]
    (is (#{:fuel-exhausted :call-fuel-exhausted} (:lang/error e)))
    (is (= :run (:lang/phase e)))))

(deftest bigint-blowup
  (testing "huge shift"
    (is (= :int-too-large
           (:lang/error (run-err (str "(defrel spin [x y] ([x -> y] [[(bit-shift-left 1 100000)]]))" spin-rule))))))
  (testing "repeated squaring"
    (is (= :int-too-large
           (:lang/error (run-err (str "(defrel spin [x y] ([x -> y] [[(loop [n 3 i 0] (if (< i 100) (recur (* n n) (inc i)) n))]]))"
                                      spin-rule)))))))

(defn- deflate [^bytes in]
  (let [d (Deflater.) out (java.io.ByteArrayOutputStream.) buf (byte-array 65536)]
    (.setInput d in) (.finish d)
    (while (not (.finished d))
      (.write out buf 0 (.deflate d buf)))
    (.end d)
    (.toByteArray out)))

(deftest inflate-bomb
  (let [bomb (deflate (byte-array (* 100 1024 1024)))
        p (prog "(defrel inf [b o] ([b -> o] (let [x (b/inflate b 1000000000)] [[(if x 1 0)]])))
                 (defrule r [?o] (in/blob ?b) (inf ?b ?o))")
        db (lang/run p {:facts {'host.input/blob [[bomb]]} :limits {:max-inflate (* 1024 1024)}})]
    (is (= #{[0]} (lang/relation db 't/r)))))

(deftest deep-source
  (let [n 10000
        e (err #(prog (str "(defn f [x] " (apply str (repeat n "[")) (apply str (repeat n "]")) ")")))]
    (is (= :form-too-deep (:lang/error e)))))

(deftest deep-recursion
  (is (= :depth-exceeded
         (:lang/error (run-err (str "(defn down [n] (+ 1 (down (+ n 1))))
                                     (defrel spin [x y] ([x -> y] [[(down x)]]))" spin-rule))))))

(deftest deep-struct
  (let [p (prog "(defstruct node [more :u8 child [:if (= more 1) node]])
                 (defrule r [?v] (in/blob ?b) (node ?b 0 ?v _))")
        e (err #(lang/run p {:facts {'host.input/blob [[(byte-array 10000 (byte 1))]]}}))]
    (is (= :depth-exceeded (:lang/error e)))))

(deftest cross-product
  (let [p (prog "(defrule r [?a ?b ?c] (in/go ?a) (in/go ?b) (in/go ?c))")
        e (err #(lang/run p {:facts {'host.input/go (mapv vector (range 300))}
                             :limits {:fuel 100000}}))]
    (is (= :fuel-exhausted (:lang/error e)))))

(deftest error-no-host-paths
  (let [dir (Files/createTempDirectory "secret-dir" (make-array FileAttribute 0))
        f (io/file (.toFile dir) "x.bin")]
    (try
      (spit f "abc")
      (let [p (prog "(defrel bad [x y] ([x -> y] [[(+ x \"a\")]]))
                     (defrule r [?y] (in/go ?x) (bad ?x ?y))")
            e (try (lang/run p {:facts go-facts
                                :resources {"x" (lang/file-resource f)}})
                   nil
                   (catch Throwable t t))
            s (str (pr-str (ex-data e)) (ex-message e))]
        (is (some? e))
        (is (= :type-error (:lang/error (ex-data e))))
        (is (not (str/includes? s "secret-dir"))))
      (finally
        (io/delete-file f true)
        (io/delete-file (.toFile dir) true)))))

(deftest timeout
  (let [e (run-err (str "(defrel spin [x y] ([x -> y] (loop [] (recur))))" spin-rule)
                   nil {:limits {:timeout-ms 50 :fuel (long 1e15) :call-fuel (long 1e15)}})]
    (is (= :timeout (:lang/error e)))))

(deftest index-of-huge-from
  (let [r (fn [from]
            (let [db (run (prog (str "(defrel f [x y] ([x -> y] [[(b/index-of (b/hex-decode \"0102\") (b/hex-decode \"02\") " from ")]]))
                                      (defrule r [?y] (in/go ?x) (f ?x ?y))")))]
              (lang/relation db 't/r)))]
    (is (= #{[1]} (r 0)))
    (is (= #{[nil]} (r Long/MAX_VALUE)))
    (is (= #{[nil]} (r (dec Long/MAX_VALUE))))))
