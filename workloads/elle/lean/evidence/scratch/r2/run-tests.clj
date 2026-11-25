;; Runs Elle's test suite (upstream/test) and prints each test var's outcome, so a baseline and a
;; patched run (patched namespaces ahead on the classpath) can be compared line by line.
;; Usage: java -cp PATCH:CP clojure.main run-tests.clj [ns ...]
(require '[clojure.test :as t])
(def nss (or (seq (map symbol *command-line-args*))
             '[elle.bfs-test elle.closed-predicate-test elle.consistency-model-test elle.core-test
               elle.graph-test elle.list-append-test elle.rels-test elle.rw-register-test
               elle.txn-test elle.util-test]))
(def outcome (atom {}))
(def current (atom nil))
(defmethod t/report :begin-test-var [m] (reset! current (symbol (str (:var m)))))
(defmethod t/report :pass [m] (t/inc-report-counter :pass))
(defmethod t/report :fail [m]
  (t/inc-report-counter :fail)
  (swap! outcome update @current (fnil conj []) [:fail (:message m)
                                                 (let [s (pr-str (:actual m))] (subs s 0 (min 600 (count s))))]))
(defmethod t/report :error [m]
  (t/inc-report-counter :error)
  (swap! outcome update @current (fnil conj []) [:error (str (:actual m))]))
(doseq [n nss]
  (try (require n)
       (catch Throwable e (println "LOAD-ERROR" n (str e)))))
; Elle's default selector (project.clj:35): no :perf, :interactive or :overflow tests.
(defn default? [v] (let [m (meta v)] (not (or (:perf m) (:interactive m) (:overflow m)))))
(let [selected (for [n nss :when (find-ns n)
                     v (sort-by str (vals (ns-interns n)))
                     :when (and (:test (meta v)) (default? v))] v)
      res (binding [t/*report-counters* (ref t/*initial-report-counters*)]
            (t/test-vars selected)
            @t/*report-counters*)
      vars (sort (map #(symbol (str %)) selected))]
  (doseq [v vars]
    (let [o (get @outcome v)]
      (println (if o "BAD " "ok  ") v (if o (pr-str (map (juxt first (comp #(subs % 0 (min 300 (count %))) str second)) o)) ""))))
  (println "TOTAL" (select-keys res [:test :pass :fail :error])))
(shutdown-agents)
(System/exit 0)
