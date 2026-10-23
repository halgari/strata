(ns lang.formats.tes4-test
  (:require [clojure.java.io :as io]
            [clojure.test :refer [deftest is]]
            [lang.api :as lang]
            [lang.fixtures.tes4 :refer [build-plugin]]))

;; Test-only rules that force record fields, layered on the unmodified program.
(def ^:private probe-src
  "(ns probe
     (:require [formats.tes4 :as t] [lang.bytes :as b]))
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

(def ^:private prog
  (delay (lang/load {:sources {'formats.tes4 (slurp (io/resource "formats/tes4.edn"))
                               'probe probe-src}
                     :builtins '#{lang.string lang.bytes lang.io}
                     :externs {'host.input {'file 1}}})))

(def ^:private plain-prog
  (delay (lang/load {:sources {'formats.tes4 (slurp (io/resource "formats/tes4.edn"))}
                     :builtins '#{lang.string lang.bytes lang.io}
                     :externs {'host.input {'file 1}}})))

(defn- run
  ([files] (run files nil))
  ([files trace]
   (lang/run (if trace @plain-prog @prog) (cond-> {:facts {'host.input/file (mapv (comp vector key) files)}
                            :resources (update-vals files lang/bytes-resource)}
                     trace (assoc :trace trace)))))

(defn- q1 [db pat k]
  (set (map #(% k) (lang/query db pat))))

(def ^:private weap
  (fn [id] {:type "WEAP" :form-id id :fields [["EDID" (.getBytes "Sword")]]}))

(deftest header
  (let [db (run {"a.esp" (build-plugin {:masters ["Skyrim.esm"]
                                        :groups [{:label "WEAP" :records [(weap 1) (weap 2)]}]})})
        m (first (lang/query db '(formats.tes4/hedr "a.esp" ?v ?n)))]
    (is (< (Math/abs (- (double (m '?v)) (double (float 1.71)))) 1e-6))
    (is (= 2 (m '?n)))))

(deftest masters-order
  (let [ms ["Skyrim.esm" "Update.esm" "Dawnguard.esm"]
        db (run {"a.esp" (build-plugin {:masters ms})})]
    (is (= [ms] (mapv #(vec (% '?ms)) (lang/query db '(formats.tes4/masters "a.esp" ?ms)))))))

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
                     (lang/query db '(formats.tes4/missing-master ?f ?m))))))))

(def ^:private counted-plugin
  (build-plugin {:masters ["Skyrim.esm"]
                 :groups [{:label "WEAP" :records [(weap 1) (weap 2) (weap 3)]}
                          {:label "ARMO" :records [{:type "ARMO" :form-id 9 :compressed? true
                                                    :fields [["EDID" (.getBytes "Helm")]]}]}]}))

(deftest record-count
  (let [db (run {"a.esp" counted-plugin})]
    (is (= #{["WEAP" 3] ["ARMO" 1]}
           (set (map (juxt #(% '?type) #(% '?n))
                     (lang/query db '(formats.tes4/record-count "a.esp" ?type ?n))))))))

(deftest lazy
  (let [events (atom [])
        db (run {"a.esp" counted-plugin} #(swap! events conj %))]
    (is (seq (lang/query db '(formats.tes4/record-count "a.esp" ?t ?n))))
    (is (seq (filter #(= :parse (:event %)) @events)))
    (is (some #(= 'formats.tes4/plugin (:type %)) @events))
    ;; the header-field rules force the TES4 header (offset 24); no other record is forced
    (is (= [24] (mapv :off (filter #(= 'formats.tes4/record-fields (:type %)) @events))))))

(deftest xxxx
  (let [data (byte-array 70000)
        db (run {"a.esp" (build-plugin {:groups [{:label "STAT"
                                                  :records [{:type "STAT" :form-id 5
                                                             :fields [["MODL" data]]}]}]
                                        :xxxx? true})})
        rows (lang/query db '(probe/forced "a.esp" ?at "STAT" 0 ?stype ?len))]
    (is (= #{["MODL" 70000]} (set (map (juxt #(% '?stype) #(% '?len)) rows))))))

(deftest corrupt-compressed
  (let [db (run {"a.esp" (build-plugin
                          {:groups [{:label "WEAP"
                                     :records [(weap 1)
                                               {:type "ARMO" :form-id 2 :garbage-zlib? true
                                                :fields [["EDID" (.getBytes "Bad")]]}]}]})})]
    (is (= #{["WEAP" 1] ["ARMO" 1]}
           (set (map (juxt #(% '?type) #(% '?n))
                     (lang/query db '(formats.tes4/record-count "a.esp" ?type ?n))))))
    (is (= #{["WEAP"]}
           (set (map (juxt #(% '?type))
                     (lang/query db '(probe/forced "a.esp" ?at ?type 0 "EDID" ?len))))))
    (is (empty? (lang/query db '(probe/forced "a.esp" ?at "ARMO" ?i ?s ?l))))))
