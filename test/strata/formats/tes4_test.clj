(ns strata.formats.tes4-test
  (:require [clojure.java.io :as io]
            [clojure.test :refer [deftest is testing]]
            [strata.api :as strata]
            [strata.fixtures.tes4 :refer [build-plugin]]))

;; Test-only rules that force record fields, layered on the unmodified program.
(def ^:private probe-src
  "(ns probe
     (:require [formats.tes4 :as t] [strata.bytes :as b]))
   (defrule forced [?f ?at ?type ?i ?stype ?len]
     (t/node ?f ?at ?type ?body)
     (when (not= ?type \"GRUP\"))
     (force (:fields ?body) ?rf)
     (indexed (:fs ?rf) ?i ?fld)
     (bind {:type ?stype :data ?d} ?fld)
     (bind ?len (b/size ?d)))
   (defrule forced-record [?f ?at]
     (t/node ?f ?at ?type ?body)
     (when (not= ?type \"GRUP\"))
     (force (:fields ?body) _))")

(defn- load-prog [sources]
  (strata/load {:sources sources
              :builtins '#{strata.string strata.bytes strata.io}
              :externs {'host.input {'file 1}}}))

(def ^:private tes4-src (slurp (io/resource "formats/tes4.edn")))
(def ^:private plain-prog (delay (load-prog {'formats.tes4 tes4-src})))
(def ^:private probe-prog (delay (load-prog {'formats.tes4 tes4-src 'probe probe-src})))

(defn- run-with [prog files trace]
  (strata/run prog (cond-> {:facts {'host.input/file (mapv (comp vector key) files)}
                          :resources (update-vals files strata/bytes-resource)}
                   trace (assoc :trace trace))))

(defn- run [files] (run-with @plain-prog files nil))
(defn- run-probe [files] (run-with @probe-prog files nil))

(defn- q1 [db pat k]
  (set (map #(% k) (strata/query db pat))))

(def ^:private weap
  (fn [id] {:type "WEAP" :form-id id :fields [["EDID" (.getBytes "Sword")]]}))

(deftest header
  (let [db (run {"a.esp" (build-plugin {:masters ["Skyrim.esm"]
                                        :groups [{:label "WEAP" :records [(weap 1) (weap 2)]}]})})
        m (first (strata/query db '(formats.tes4/hedr "a.esp" ?v ?n)))]
    (is (< (Math/abs (- (double (m '?v)) (double (float 1.71)))) 1e-6))
    (is (= 2 (m '?n)))))

(deftest masters-order
  (let [ms ["Skyrim.esm" "Update.esm" "Dawnguard.esm"]
        db (run {"a.esp" (build-plugin {:masters ms})})]
    (is (= [ms] (mapv #(vec (% '?ms)) (strata/query db '(formats.tes4/masters "a.esp" ?ms)))))))

(deftest light-flag-and-ext
  (let [db (run {"a.esp" (build-plugin {:flags 0x200})
                 "b.ESL" (build-plugin {})
                 "c.esp" (build-plugin {:flags 0x1})})
        light (q1 db '(formats.tes4/light ?f) '?f)]
    (is (= #{"a.esp" "b.ESL"} light))))

(deftest missing-master
  (let [db (run {"a.esp" (build-plugin {:masters ["skyrim.ESM" "Gone.esm"]})
                 "Skyrim.esm" (build-plugin {:flags 0x1})})]
    (is (= #{["a.esp" "Gone.esm"]}
           (set (map (juxt #(% '?f) #(% '?m))
                     (strata/query db '(formats.tes4/missing-master ?f ?m))))))))

(def ^:private counted-plugin
  (build-plugin {:masters ["Skyrim.esm"]
                 :groups [{:label "WEAP" :records [(weap 1) (weap 2) (weap 3)]}
                          {:label "ARMO" :records [{:type "ARMO" :form-id 9 :compressed? true
                                                    :fields [["EDID" (.getBytes "Helm")]]}]}]}))

(deftest record-count
  (let [db (run {"a.esp" counted-plugin})]
    (is (= #{["WEAP" 3] ["ARMO" 1]}
           (set (map (juxt #(% '?type) #(% '?n))
                     (strata/query db '(formats.tes4/record-count "a.esp" ?type ?n))))))))

(def ^:private header-fields-off
  ;; the TES4 record's subrecord data starts right after its 24-byte header
  24)

(defn- fields-offsets [events]
  (mapv :off (filter #(and (= :parse (:event %))
                           (= 'formats.tes4/record-fields (:type %)))
                     events)))

(deftest lazy
  (let [events (atom [])
        db (run-with @plain-prog {"a.esp" counted-plugin} #(swap! events conj %))]
    (is (seq (strata/query db '(formats.tes4/record-count "a.esp" ?t ?n))))
    ;; the header-field rules force the TES4 header; no other record is forced
    (is (= [header-fields-off] (fields-offsets @events))))
  (testing "positive control: forcing rules do produce record-fields events"
    (let [events (atom [])]
      (run-with @probe-prog {"a.esp" counted-plugin} #(swap! events conj %))
      (is (seq (remove #{header-fields-off} (fields-offsets @events)))))))

(deftest xxxx
  (let [data (byte-array 70000)
        db (run-probe {"a.esp" (build-plugin {:groups [{:label "STAT"
                                                  :records [{:type "STAT" :form-id 5
                                                             :fields [["MODL" data]]}]}]
                                        :xxxx? true})})
        rows (strata/query db '(probe/forced "a.esp" ?at "STAT" 0 ?stype ?len))]
    (is (= #{["MODL" 70000]} (set (map (juxt #(% '?stype) #(% '?len)) rows))))))

(deftest corrupt-compressed
  (let [db (run-probe {"a.esp" (build-plugin
                                {:groups [{:label "WEAP"
                                           :records [(weap 1)
                                                     {:type "ARMO" :form-id 2 :garbage-zlib? true
                                                      :fields [["EDID" (.getBytes "Bad")]]}]}]})})
        nodes (fn [t] (set (map #(% '?at) (strata/query db (list 'formats.tes4/node "a.esp" '?at t '_)))))
        forced (set (map #(% '?at) (strata/query db '(probe/forced-record "a.esp" ?at))))]
    (is (= #{["WEAP" 1] ["ARMO" 1]}
           (set (map (juxt #(% '?type) #(% '?n))
                     (strata/query db '(formats.tes4/record-count "a.esp" ?type ?n))))))
    (is (= 1 (count (nodes "WEAP"))))
    (is (= 1 (count (nodes "ARMO"))))
    ;; force yields no tuple when the deferred parse fails
    (is (= (nodes "WEAP") forced))
    (is (empty? (strata/query db '(probe/forced "a.esp" ?at "ARMO" ?i ?s ?l))))))
