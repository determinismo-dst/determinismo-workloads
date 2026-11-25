;; Runs real Elle (upstream/, commit 4e359e5) on histories written by the Lean replica.
;; Usage: java -cp CP clojure.main runner/run.clj IN.edn OUT.edn
;; IN.edn: a vector of {:id n, :workload :list-append|:rw-register|:closed-predicate,
;;                      :opts {...}, :history [op ...]}
;; OUT.edn: one map per line: {:id n, :valid? .., :anomaly-types .., :not .., :also-not ..}
;; or {:id n, :error "..."}.
(require '[clojure.edn :as edn]
         '[clojure.pprint :refer [pprint]]
         '[jepsen.history :as h]
         '[elle.list-append :as la]
         '[elle.rw-register :as rr]
         '[elle.closed-predicate :as cp]
         '[elle.txn :as ct]
         '[elle.consistency-model :as cm]
         '[elle.core])

(defn run-one [{:keys [id workload opts history]}]
  (try
    (let [hist (h/history history)
          res  (case workload
                 :list-append      (la/check opts hist)
                 :rw-register      (rr/check opts hist)
                 :closed-predicate (cp/check opts hist)
                 :monotonic (elle.core/check {:analyzer elle.core/monotonic-key-graph} hist)
                 :monotonic-realtime (elle.core/check
                                       {:analyzer (elle.core/combine elle.core/monotonic-key-graph
                                                                     elle.core/realtime-graph)}
                                       hist))]
      {:id id
       :valid? (:valid? res)
       :anomaly-types (vec (sort (map name (:anomaly-types res))))
       :not (vec (sort (map name (:not res))))
       :also-not (vec (sort (map name (:also-not res))))
       :anomalies (into (sorted-map)
                        (for [[t cs] (:anomalies res)]
                          [(name t)
                           (if (sequential? cs)
                             (vec (for [c cs]
                                    (cond (:cycle c) {:cycle (mapv :index (:cycle c))
                                                      :steps (mapv (fn [s] [(:type s) (:key s) (:value s) (:value' s)]) (:steps c))
                                                      :type (:type c)}
                                          (:scc c) {:scc (:scc c)}
                                          :else (dissoc c :op :writer :txns :mop))))
                             cs)]))})
    (catch Throwable e
      {:id id :error (str (.getName (class e)) ": " (.getMessage e))
       :data (when (instance? clojure.lang.ExceptionInfo e)
               (select-keys (ex-data e) [:valid? :type :message]))})))

(let [[in out] *command-line-args*
      cases (edn/read-string (slurp in))]
  (with-open [w (clojure.java.io/writer out)]
    (when (some #{:meta} (map :workload cases))
      nil)
    (binding [*out* w]
      (prn {:id :meta
            :cycle-anomaly-specs (mapv name (keys ct/cycle-anomaly-specs))
            :prohibited-serializable (mapv name (cm/anomalies-prohibited-by [:serializable]))})
      (doseq [c cases]
        (prn (run-one c)))))
  (shutdown-agents)
  (System/exit 0))
