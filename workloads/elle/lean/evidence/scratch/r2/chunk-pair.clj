;; jepsen.history's pair index over chunks: a process invoking twice, the two invocations in one
;; chunk or on either side of the boundary at 16384. Then Elle's list-append check on each.
(require '[jepsen.history :as h] '[elle.list-append :as la])
(defn filler [n]
  ;; n ops: invoke/ok pairs of process 9, appending unique values to key 5 (each read by nobody)
  (vec (mapcat (fn [i] [{:process 9 :type :invoke :f :txn :value [[:append 5 i]]}
                        {:process 9 :type :ok :f :txn :value [[:append 5 i]]}])
               (range (quot n 2)))))
(def tail-ops
  [{:process 8 :type :invoke :f :txn :value [[:append 6 1]]}
   {:process 0 :type :invoke :f :txn :value [[:append 0 1]]}
   {:process 0 :type :invoke :f :txn :value [[:append 0 2]]}
   {:process 0 :type :ok :f :txn :value [[:append 0 2]]}
   {:process 8 :type :ok :f :txn :value [[:append 6 1]]}
   {:process 1 :type :invoke :f :txn :value [[:r 0 nil]]}
   {:process 1 :type :ok :f :txn :value [[:r 0 [1 2]]]}])
(defn run [label n]
  (let [ops (into (filler n) tail-ops)
        hist (h/history ops)
        pre (inc n)
        first-inv (h/get-index hist pre)]
    (println label "ops" (count ops) "first double invocation at index" pre
             "(chunk" (quot pre 16384) ", second in chunk" (quot (inc pre) 16384) ")" (:process first-inv) (:type first-inv))
    (try (println "  completion of index" pre ":" (some-> (h/completion hist first-inv) :index))
         (catch Throwable t (println "  pair index throws:" (or (:type (ex-data t)) (str t)))))
    (try (let [r (la/check {:consistency-models [:serializable]} (h/history ops))]
           (println "  elle:" (:valid? r) (vec (sort (keys (:anomalies r))))))
         (catch Throwable t (println "  elle throws:" (or (:type (ex-data t)) (str t)))))))
(run "within one chunk:" 16380)
(run "across the boundary:" 16382)
(shutdown-agents)
(System/exit 0)
