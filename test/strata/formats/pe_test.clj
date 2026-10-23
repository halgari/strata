(ns strata.formats.pe-test
  (:require [clojure.java.io :as io]
            [clojure.test :refer [deftest is testing]]
            [strata.api :as strata]
            [strata.fixtures.pe :refer [build-pe]]))

(def prog
  (delay (strata/load {:sources {'formats.pe (slurp (io/resource "formats/pe.edn"))}
                     :builtins '#{strata.string strata.bytes strata.io}
                     :externs {'host.input {'file 1}}})))

(defn- run [files]
  (strata/run @prog {:facts {'host.input/file (mapv (comp vector key) files)}
                   :resources (update-vals files strata/bytes-resource)}))

(defn- imp [db f]
  (set (map (fn [m] [(m '?dll) (m '?k)])
            (strata/query db (list 'formats.pe/imported-dll f '?dll '?k)))))

(defn- pe-files [opts]
  {"a.dll" (build-pe (assoc opts :imports ["B.dll" "kernel32.dll"]))
   "b.dll" (build-pe (assoc opts :imports ["c.dll"]))})

(deftest pe32-imports
  (is (= #{["B.dll" :import] ["kernel32.dll" :import]}
         (imp (run (pe-files {})) "a.dll"))))

(deftest pe32plus
  (is (= #{["B.dll" :import] ["kernel32.dll" :import]}
         (imp (run (pe-files {:wide? true})) "a.dll"))))

(deftest delay-imports
  (doseq [wide? [false true] rva? [false true]]
    (testing (pr-str {:wide? wide? :rva? rva?})
      (let [db (run {"a.dll" (build-pe {:wide? wide? :imports ["B.dll"]
                                        :delay-imports ["d1.dll" "D2.dll"]
                                        :delay-rva-based? rva?})})]
        (is (= #{["B.dll" :import] ["d1.dll" :delay] ["D2.dll" :delay]}
               (imp db "a.dll")))))))

(deftest closure-and-missing
  (let [db (run (pe-files {}))
        rel (fn [r] (set (map (fn [m] [(m '?f) (m '?d)])
                              (strata/query db (list r '?f '?d)))))]
    (is (contains? (rel 'formats.pe/depends-on) ["a.dll" "c.dll"]))
    (is (contains? (rel 'formats.pe/missing-dll) ["a.dll" "kernel32.dll"]))
    (is (contains? (rel 'formats.pe/missing-dll) ["a.dll" "c.dll"]))
    (is (not-any? #(= "B.dll" (second %)) (rel 'formats.pe/missing-dll)))))

(deftest corrupt-name-rva
  (let [db (run {"a.dll" (build-pe {:imports ["B.dll" "kernel32.dll"] :bad-import-rvas 1})})]
    (is (= #{["B.dll" :import] ["kernel32.dll" :import]} (imp db "a.dll")))))

(deftest not-a-pe
  (let [junk (byte-array (map unchecked-byte (repeatedly 600 #(rand-int 256))))
        junk (doto junk (aset 0 (byte 1)))
        db (run {"x.dll" junk})]
    (is (empty? (strata/query db '(formats.pe/headers ?f ?s ?p))))
    (is (empty? (strata/query db '(formats.pe/imported-dll ?f ?d ?k))))))

(deftest real-dll
  (when-let [p (System/getenv "LANG_TEST_DLL")]
    (let [db (strata/run @prog {:facts {'host.input/file [["real"]]}
                              :resources {"real" (strata/file-resource (io/file p))}})]
      (is (seq (strata/query db '(formats.pe/imported-dll "real" ?d ?k)))))))
