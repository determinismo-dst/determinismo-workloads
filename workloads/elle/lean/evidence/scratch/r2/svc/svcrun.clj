;; Runs the service's own `check` (service/elle_service.clj) on JSON-lines bodies, and real Elle
;; 0.2.8 on the same history as EDN when one is given.
;; Usage: clojure -M svcrun.clj IN.edn OUT.edn
;; IN.edn: [{:id n :model "list-append"|"rw-register"|"closed-predicate" :consistency ".."
;;           :lk bool :body "json lines" :history [ops...] or nil} ...]
(require '[elle-service :as svc]
         '[clojure.edn :as edn]
         '[clojure.java.io :as io]
         '[jepsen.history :as h]
         '[elle.list-append :as la]
         '[elle.rw-register :as rr]
         '[elle.closed-predicate :as cp])

(defn norm [v] (if (keyword? v) (name v) v))

(defn elle-answer [model consistency lk history]
  (try
    (let [checker ({"list-append" la/check "rw-register" rr/check "closed-predicate" cp/check} model)
          opts (cond-> {:consistency-models [(keyword consistency)]} lk (assoc :linearizable-keys? true))
          r (checker opts (h/history history))]
      {:valid (norm (:valid? r)) :types (vec (sort (map name (:anomaly-types r))))
       :not (vec (sort (map name (:not r))))})
    (catch Throwable t {:error (str (.getName (class t)) ": " (.getMessage t))})))

(let [[in out] *command-line-args*
      cases (edn/read-string (slurp in))]
  (with-open [w (io/writer out)]
    (binding [*out* w]
      (doseq [{:keys [id model consistency lk body history]} cases]
        (let [ans (try (let [a (svc/check body model consistency lk)]
                         {:valid (norm (:valid a)) :types (vec (sort (:anomaly_types a)))
                          :not (vec (sort (:not a))) :window (:window_ns a)
                          :text-length (count (:anomalies a))})
                       (catch Throwable t {:error (str (.getName (class t)) ": " (.getMessage t))}))]
          (prn {:id id :service ans :elle (when history (elle-answer model consistency lk history))}))))))
(shutdown-agents)
(System/exit 0)
