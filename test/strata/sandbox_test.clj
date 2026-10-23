(ns strata.sandbox-test
  "Sandbox and robustness suite, driven only through strata.api (spec 7.4, 8)."
  (:require [clojure.java.io :as io]
            [clojure.string :as str]
            [clojure.test :refer [deftest is testing]]
            [strata.api :as strata])
  (:import (java.nio.file Files)
           (java.nio.file.attribute FileAttribute)
           (java.util.zip Deflater)))

(def ^:private externs {'host.input {'go 1 'blob 1}})
(def ^:private go-facts {'host.input/go [[1]]})

(defn- prog
  "Loads one namespace `t` requiring host.input as `in` and strata.bytes as `b`."
  [body & [opts]]
  (strata/load (merge {:sources {'t (str "(ns t (:require [host.input :as in] [strata.bytes :as b]))\n" body)}
                     :builtins '#{strata.bytes strata.io}
                     :externs externs}
                    opts)))

(defn- run [p & [opts]]
  (strata/run p (merge {:facts go-facts} opts)))

;; Hostile runs execute on a future so a hang fails the test instead of the suite.
(defn- bounded [f]
  (let [r (deref (future (try (f) (catch Throwable t t))) 5000 ::hung)]
    (is (not= ::hung r) "finished within 5 s")
    r))

(defn- err [f]
  (let [r (bounded f)]
    (when (instance? clojure.lang.ExceptionInfo r) (ex-data r))))

(defn- run-err [body & [load-opts run-opts]]
  (err #(run (prog body load-opts) run-opts)))

(deftest no-interop
  (doseq [form ["(System/exit 0)" "(.getRuntime Runtime)" "(new java.io.File \"x\")"
                "(clojure.core/eval 1)" "(java.lang.Thread/sleep 1)"]]
    (let [e (err #(prog (str "(defn f [x] " form ")")))]
      (is (= :unresolved-symbol (:strata/error e)) form)
      (is (not= :run (:strata/phase e)) form))))

(deftest no-tags
  (doseq [form ["#=(+ 1 2)" "#java.io.File \"x\""]]
    (let [e (err #(prog (str "(defn f [x] " form ")")))]
      (is (= :read (:strata/phase e)) form)
      (is (keyword? (:strata/error e)) form))))

(def ^:private spin-rule
  "(defrule r [?y] (in/go ?x) (spin ?x ?y))")

(deftest infinite-loop
  (let [e (run-err (str "(defrel spin [x y] ([x -> y] (loop [] (recur))))" spin-rule) nil {:limits {:fuel 1000000}})]
    (is (#{:fuel-exhausted :call-fuel-exhausted} (:strata/error e)))
    (is (= :run (:strata/phase e)))))

(deftest bigint-blowup
  (testing "huge shift"
    (is (= :int-too-large
           (:strata/error (run-err (str "(defrel spin [x y] ([x -> y] [[(bit-shift-left 1 100000)]]))" spin-rule))))))
  (testing "repeated squaring"
    (is (= :int-too-large
           (:strata/error (run-err (str "(defrel spin [x y] ([x -> y] [[(loop [n 3 i 0] (if (< i 100) (recur (* n n) (inc i)) n))]]))"
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
        db (strata/run p {:facts {'host.input/blob [[bomb]]} :limits {:max-inflate (* 1024 1024)}})]
    (is (= #{[0]} (strata/relation db 't/r))))
  (testing "positive control: a small valid payload inflates"
    (let [p (prog "(defrel inf [b o] ([b -> o] (let [x (b/inflate b 1000000)] [[(b/size x)]])))
                   (defrule r [?o] (in/blob ?b) (inf ?b ?o))")
          db (strata/run p {:facts {'host.input/blob [[(deflate (byte-array 1000))]]}
                          :limits {:max-inflate (* 1024 1024)}})]
      (is (= #{[1000]} (strata/relation db 't/r))))))

(deftest deep-source
  (let [n 10000
        e (err #(prog (str "(defn f [x] " (apply str (repeat n "[")) (apply str (repeat n "]")) ")")))]
    (is (= :form-too-deep (:strata/error e)))
    (is (= :read (:strata/phase e)))))

(deftest deep-recursion
  (is (= :depth-exceeded
         (:strata/error (run-err (str "(defn down [n] (+ 1 (down (+ n 1))))
                                     (defrel spin [x y] ([x -> y] [[(down x)]]))" spin-rule))))))

(deftest deep-struct
  (let [p (prog "(defstruct node [more :u8 child [:if (= more 1) node]])
                 (defrule r [?v] (in/blob ?b) (node ?b 0 ?v _))")
        e (err #(strata/run p {:facts {'host.input/blob [[(byte-array 10000 (byte 1))]]}}))]
    (is (= :depth-exceeded (:strata/error e)))
    (is (= :run (:strata/phase e)))))

(deftest cross-product
  (let [p (prog "(defrule r [?a ?b ?c] (in/go ?a) (in/go ?b) (in/go ?c))")
        e (err #(strata/run p {:facts {'host.input/go (mapv vector (range 300))}
                             :limits {:fuel 100000}}))]
    (is (= :fuel-exhausted (:strata/error e)))))

(defn- cause-chain [^Throwable t]
  (take-while some? (iterate #(.getCause ^Throwable %) t)))

(defn- leak-text [^Throwable t]
  (apply str (for [c (cause-chain t)] (str (pr-str (ex-data c)) (ex-message c) (pr-str c)))))

(deftest error-no-host-paths
  (let [dir (Files/createTempDirectory "secret-dir" (make-array FileAttribute 0))
        f (io/file (.toFile dir) "x.bin")
        opts {:facts go-facts :resources {"x" (strata/file-resource f)}}
        open "(defrel h [n b] ([n -> b] [[(io/open \"x\")]]))\n"]
    (try
      (spit f "abc")
      (let [ns-head "(ns t (:require [host.input :as in] [strata.io :as io] [strata.bytes :as b]))\n"
            load* (fn [body] (strata/load {:sources {'t (str ns-head open body)}
                                         :builtins '#{strata.bytes strata.io} :externs externs}))]
        (testing "positive control: the resource is readable"
          (let [db (strata/run (load* "(defrel sz [n s] ([n -> s] (let [h (io/open \"x\")] [[(b/size (io/read-all h))]])))
                                     (defrule r [?s] (in/go ?x) (sz ?x ?s))") opts)]
            (is (= #{[3]} (strata/relation db 't/r)))))
        (doseq [[label body]
                {"type error on read bytes"
                 "(defrel bad [n y] ([n -> y] (let [h (io/open \"x\")] [[(+ (io/read-all h) 1)]])))
                  (defrule r [?y] (in/go ?x) (bad ?x ?y))"
                 "program error in struct parse over handle"
                 "(defstruct s [n :u8 xs [:array :u8 (+ n \"a\")]])
                  (defrule r [?v] (in/go ?x) (h ?x ?b) (s ?b 0 ?v _))"}]
          (let [t (bounded #(strata/run (load* body) opts))]
            (testing label
              (is (instance? clojure.lang.ExceptionInfo t))
              (is (= :run (:strata/phase (ex-data t))))
              (is (not (str/includes? (leak-text t) "secret-dir")))
              (is (not (str/includes? (leak-text t) (.getName (.toFile dir)))))))))
      (finally
        (io/delete-file f true)
        (io/delete-file (.toFile dir) true)))))

(deftest unknown-run-option
  (let [p (prog "(defrule r [?y] (in/go ?y))")
        e (err #(strata/run p {:facts go-facts :timeout-ms 50}))]
    (is (= :bad-option (:strata/error e)))
    (is (= :run (:strata/phase e)))))

(deftest timeout
  (let [t0 (System/nanoTime)
        e (run-err (str "(defrel spin [x y] ([x -> y] (loop [] (recur))))" spin-rule)
                   nil {:limits {:timeout-ms 50 :fuel (long 1e15) :call-fuel (long 1e15)}})]
    (is (= :timeout (:strata/error e)))
    (is (< (/ (- (System/nanoTime) t0) 1e6) 2500) "stops well under the 5 s bound")))

(deftest index-of-huge-from
  (let [r (fn [from]
            (let [db (run (prog (str "(defrel f [x y] ([x -> y] [[(b/index-of (b/hex-decode \"0102\") (b/hex-decode \"02\") " from ")]]))
                                      (defrule r [?y] (in/go ?x) (f ?x ?y))")))]
              (strata/relation db 't/r)))]
    (is (= #{[1]} (r 0)))
    (is (= #{[nil]} (r Long/MAX_VALUE)))
    (is (= #{[nil]} (r (dec Long/MAX_VALUE))))))

;; ------------------------------------------------ final review: deep metering

(def ^:private mk-shared
  "A 2^60-node logical value built from 60 shared steps."
  "(defn mk [] (loop [x [1] i 0] (if (< i 60) (recur [x x] (inc i)) x)))\n")

(defn- elapsed-ms [t0] (/ (- (System/nanoTime) t0) 1e6))

(deftest deep-equality-metered
  (let [t0 (System/nanoTime)
        e (run-err (str mk-shared
                        "(defrel eq [x o] ([x -> o] [[(= (mk) (mk))]]))
                         (defrule r [?o] (in/go ?x) (eq ?x ?o))"))]
    (is (= :value-too-large (:strata/error e)))
    (is (< (elapsed-ms t0) 2000))))

(deftest deep-value-insert-rejected
  (let [t0 (System/nanoTime)
        e (run-err (str mk-shared
                        "(defrel mkv [x o] ([x -> o] [[(mk)]]))
                         (defrule r [?o] (in/go ?x) (mkv ?x ?o))"))]
    (is (= :value-too-large (:strata/error e)))
    (is (< (elapsed-ms t0) 2000)))
  (testing "a bound expression result is checked before it joins stored tuples"
    (let [e (run-err (str mk-shared
                          "(defrule s [?y] (in/go ?y))
                           (defrule r [?y] (in/go ?x) (bind ?a (mk)) (s ?a) (in/go ?y))"))]
      (is (= :value-too-large (:strata/error e))))))

(deftest large-bytes-inserts-honor-timeout
  (let [t0 (System/nanoTime)
        p (prog "(defrel sl [b i o] ([b i -> o] [[(b/slice b i (+ i 4000000))]]))
                 (defrule r [?s] (in/blob ?b) (between 0 3000 ?i) (sl ?b ?i ?s))")
        e (err #(strata/run p {:facts {'host.input/blob [[(byte-array 8000000)]]}
                             :limits {:timeout-ms 1000 :fuel (long 1e15) :call-fuel (long 1e15)}}))]
    (is (#{:timeout :fuel-exhausted} (:strata/error e)))
    (is (< (elapsed-ms t0) 5000))))

;; ------------------------------------------------ final review: memory bounds

(deftest huge-array-count-rejected
  (let [p (prog "(defstruct big [xs [:array [:calc 1] 50000000]])
                 (defrule r [?v] (in/blob ?b) (big ?b 0 ?v _))")
        e (err #(strata/run p {:facts {'host.input/blob [[(byte-array 8)]]}}))]
    (is (= :value-too-large (:strata/error e)))))

(deftest aggregate-results-bounded
  (doseq [[label agg] {"collect" "(collect ?i)" "collect-by" "(collect-by ?i ?i)" "collect-map" "(collect-map ?i ?i)"}]
    (let [e (run-err (str "(defrule r [" agg "] (in/go _) (between 0 5000 ?i))")
                     nil {:limits {:max-value-size 1000}})]
      (is (= :value-too-large (:strata/error e)) label))))

(deftest aggregate-assignments-count-as-tuples
  (let [e (run-err "(defrule r [(count ?i)] (in/go _) (between 0 90000000 ?i))"
                   nil {:limits {:max-tuples 1000000}})]
    (is (= :tuple-limit (:strata/error e)))
    (is (= "t/r" (get-in e [:data :rel])))))

(deftest small-reads-charge-bytes
  (let [page 64
        res (strata/bytes-resource (byte-array (* 30000 page)))
        p (strata/load {:builtins '#{strata.bytes strata.io} :externs externs
                      :sources {'t "(ns t (:require [host.input :as in] [strata.io :as io] [strata.bytes :as b]))\n(defrel h [n b] ([n -> b] [[(io/open \"x\")]]))
                 (defrel rd [h i o] ([h i -> o] [[(io/read-bytes h (* i 64) 8)]]))
                 (defrule r [?v] (in/go ?x) (h ?x ?hd) (between 0 30000 ?i) (rd ?hd ?i ?v))"}})
        e (err #(strata/run p {:facts go-facts :resources {"x" res}
                             :limits {:page-size page :max-bytes 100000}}))]
    (is (= :bytes-exhausted (:strata/error e)))))

(deftest max-read-applies-to-struct-reads
  (let [res (strata/bytes-resource (byte-array 4096))
        p (strata/load {:sources {'t "(ns t (:require [host.input :as in] [strata.io :as io]))
                 (defstruct s [b [:bytes 2048]])
                 (defrel h [n b] ([n -> b] [[(io/open \"x\")]]))
                 (defrule r [?v] (in/go ?x) (h ?x ?hd) (s ?hd 0 ?v _))"}
                      :builtins '#{strata.io} :externs externs})
        e (err #(strata/run p {:facts go-facts :resources {"x" res} :limits {:max-read 1024}}))]
    (is (= :read-too-large (:strata/error e)))))

;; ------------------------------------------------ final review: struct decode charging

(deftest struct-decode-is-metered
  ;; The source is a handle (weight 1), so only the decode itself can be charged.
  (let [t0 (System/nanoTime)
        p (strata/load {:sources {'t "(ns t (:require [host.input :as in] [strata.io :as io]))
                 (defrel h [n b] ([n -> b] [[(io/open \"x\")]]))
                 (defrel dec [b i o] ([b i -> o] [[(if (parse [:string 8000000 :ascii] b 0) 1 0)]]))
                 (defrule r [?o] (in/go ?x) (h ?x ?hd) (between 0 300 ?i) (dec ?hd ?i ?o))"}
                      :builtins '#{strata.io} :externs externs})
        res (strata/bytes-resource (byte-array 8000000 (byte 97)))
        e (err #(strata/run p {:facts go-facts :resources {"x" res}
                             :limits {:timeout-ms 500 :fuel (long 1e15) :call-fuel (long 1e15)
                                      :max-bytes (long 1e12) :max-read 100000000}}))]
    (is (#{:timeout :fuel-exhausted} (:strata/error e)))
    (is (< (elapsed-ms t0) 5000))))

;; ------------------------------------------------ final review: determinism, errors, threading

(deftest map-iteration-is-order-independent
  (let [p (prog "(defrule ks [?k ?v ?s] (in/blob ?m) (bind ?k (keys ?m)) (bind ?v (vals ?m)) (bind ?s (str ?m)))
                 (defrule fst [?e] (in/blob ?m) (bind ?e (first ?m)))")
        rel (fn [facts rel-name] (strata/relation (strata/run p {:facts {'host.input/blob (mapv vector facts)}}) rel-name))
        a (array-map :a 1 :b 2 :c 3)
        b (array-map :c 3 :b 2 :a 1)]
    (is (= #{[[:a :b :c] [1 2 3] "{:a 1, :b 2, :c 3}"]} (rel [a] 't/ks)))
    (is (= (rel [a] 't/ks) (rel [b] 't/ks)))
    (is (= #{[[:a 1]]} (rel [a] 't/fst) (rel [b] 't/fst)))
    (is (= (rel [a b] 't/ks) (rel [b a] 't/ks)))))

(deftest language-built-maps-iterate-in-order
  (let [db (run (prog "(defrule r [?k ?s] (in/go _)
                         (bind ?m (assoc (assoc {} :b 1) :a 2))
                         (bind ?k (keys ?m))
                         (bind ?s (str (conj #{3 1 2} 0))))"))]
    (is (= #{[[:a :b] "#{0 1 2 3}"]} (strata/relation db 't/r)))))

(deftest stats-survive-many-skipped-errors
  (let [p (prog "(defrule r [?y] (in/blob ?x) (bind ?y (+ ?x \"a\")))")
        db (strata/run p {:facts {'host.input/blob (mapv vector (range 1500))}
                        :on-code-error :skip})]
    (is (= 1000 (count (:entries (strata/diagnostics db)))))
    (is (= 1500 (get-in (strata/diagnostics db) [:counts :type-error])))
    (is (= 0 (get-in (strata/stats db) [:tuples 't/r])))
    (is (= #{'t/r} (strata/tainted db)))))

(deftest error-data-values-are-strings
  (let [e (run-err "(defrel f [x y] ([x -> y] [[(+ 1 [1 2 3])]]))
                    (defrule r [?y] (in/go ?x) (f ?x ?y))")]
    (is (= :type-error (:strata/error e)))
    (is (seq (:data e)))
    (is (every? string? (vals (:data e))))))

(deftest skippable-kinds-extended
  (let [p (strata/load {:sources {'t "(ns t (:require [host.input :as in] [strata.string :as s]))
                                    (defrule c [?y] (in/go ?x) (bind ?y (case ?x 5 1)))
                                    (defrule g [?y] (in/go ?x) (bind ?y (s/re-find \"(\" \"x\")))"}
                      :builtins '#{strata.string} :externs externs})
        db (strata/run p {:facts go-facts :on-code-error :skip})]
    (is (= {:no-matching-clause 1 :bad-regex 1} (:counts (strata/diagnostics db))))
    (is (= #{'t/c 't/g} (strata/tainted db)))))

(deftest conj-into-type-errors
  (doseq [expr ["(conj 0 1)" "(into 5 [])" "(conj 5)"]]
    (let [e (run-err (str "(defrel f [x y] ([x -> y] [[" expr "]]))
                           (defrule r [?y] (in/go ?x) (f ?x ?y))"))]
      (is (= :type-error (:strata/error e)) expr)))
  (let [db (run (prog "(defrule r [?a ?b] (in/go _) (bind ?a (drop 9223372036854775807 nil))
                                           (bind ?b (take 9223372036854775807 [1 2])))"))]
    (is (= #{[[] [1 2]]} (strata/relation db 't/r)))))

(deftest lazy-seqs-are-accepted-as-host-values
  (let [db (run (prog "(defrule r [?v] (in/blob ?v))") {:facts {'host.input/blob [[(map inc (range 3))] [(cons 1 [2])]]}})]
    (is (= #{[[1 2 3]] [[1 2]]} (strata/relation db 't/r)))))

(deftest interrupting-the-caller-cancels-the-run
  (let [p (prog (str "(defrel spin [x y] ([x -> y] (loop [] (recur))))" spin-rule)
                {})
        result (promise)
        caller (Thread. (fn []
                          (deliver result
                                   (try (strata/run p {:facts go-facts
                                                     :limits {:fuel Long/MAX_VALUE :call-fuel Long/MAX_VALUE}})
                                        (catch Throwable t t)))))
        workers (fn [] (filter #(and (= "strata-run" (.getName ^Thread %)) (.isAlive ^Thread %))
                               (keys (Thread/getAllStackTraces))))]
    (.start caller)
    (Thread/sleep 300)
    (is (seq (workers)) "worker is running")
    (.interrupt caller)
    (let [r (deref result 5000 ::hung)]
      (is (not= ::hung r))
      (is (= :interrupted (:strata/error (ex-data r)))))
    (is (loop [n 50] (cond (empty? (workers)) true
                           (zero? n) false
                           :else (do (Thread/sleep 100) (recur (dec n)))))
        "worker stops")))
