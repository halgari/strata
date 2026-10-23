(ns lang.test
  "Helpers for testing programs (spec 4.2, 10.2)."
  (:require [lang.errors :refer [error!]]
            [lang.runtime :as rt]
            [lang.values :as v]))

(defn check-modes
  "Runs every mode of the code relation qsym on each sample tuple (a full
  tuple). A mode fails when the sample's outputs are not among the results
  from its inputs. Returns a seq of {:mode i :tuple t} failures."
  [prog qsym samples]
  (let [entry (get (:computed prog) qsym)]
    (when-not entry
      (error! :not-a-code-relation :run "Not a code relation" {:rel qsym}))
    (rt/run-isolated
     (fn []
       (let [ctx (rt/make-ctx {:limits (:limits prog)})
             arity (:arity entry)]
         (vec
          (for [sample samples
                :let [_ (when-not (and (sequential? sample) (= arity (count sample)))
                          (error! :bad-sample :run "Sample arity does not match the relation" {:rel qsym}))
                      t (v/canon (vec sample))]
                [i {:keys [in out impl]}] (map-indexed vector (:modes entry))
                :let [result (rt/with-call-budget ctx #(impl ctx (mapv t in)))
                      ok? (if (empty? out)
                            (boolean result)
                            (contains? (set result) (mapv t out)))]
                :when (not ok?)]
            {:mode i :tuple t})))))))
