;; SPDX-License-Identifier: MIT
(ns datalevin-workload
  "Datalevin's consensus-lease HA cluster (datalevin 1.2.10, doc/ha.md) as a determinismo program
  in Clojure (determinismo.workload over libdeterminismo): three servers (node/datalevin_node.clj),
  each an HA node of the database `det` and a SOFAJRaft control-plane voter, and a client node
  where these commands run, with Datalevin's remote client.

  What it promises (doc/ha.md): one write leader per database, admitted only under a lease it
  proves fresh; with the default promotion lag of 0, a failover never promotes a node missing
  an acknowledged write (the leader confirms each write group's LSN with the authority before
  acknowledging it); followers serve reads, possibly behind. Each transaction runs on the leader
  (an explicit transaction: `open-transact` finds it across the endpoints).

  Its scenario:
    append   Elle list-append over explicit transactions, strict serializable; once faults
             stop, every acknowledged append is in its key's final read.
  Its faults: the servers' power losses (partial persistence: its WAL, LMDB's data file,
  SOFAJRaft's log), kills, graceful stops, pauses, partitions, clock skew under the 1 s budget
  (past it Datalevin pauses failover by design), and thread pausing in the code HA's safety runs
  through (the JVM SDK's coverage agent on datalevin.ha, .server, .txlog, .kv and the rest of
  that path, and SOFAJRaft).

  Datalevin is loaded in the guest only (its client resolved at run time): on the host the
  program describes itself without it."
  (:require [determinismo.workload :as w])
  (:import (java.nio.file Files Path)))

(set! *warn-on-reflection* true)

(def nodes ["dl1" "dl2" "dl3"])
(def db-name "det")
(def server-port 8898)
(def password "det")

(defn- uri [node] (str "dtlv://datalevin:" password "@" node ":" server-port "/" db-name))

;; Datalevin's client, resolved in the guest.
(defn- dl [sym] (requiring-resolve (symbol "datalevin.core" (name sym))))

(defn- connect
  "A connection through a node (any: an explicit transaction finds the leader). Without the
  schema, which each server's own open sets (node/datalevin_node.clj): given one, connecting
  transacted it, a write that failed while no node led (\"Write outcome is unknown\", trial
  run 1107)."
  [node]
  ((dl 'get-conn) (uri node) nil {:client-opts {:pool-size 1 :time-out 10000}}))

(defn- close [conn] (try ((dl 'close) conn) (catch Throwable _ nil)))

;; List append ---------------------------------------------------------------------------------

(def mops-max 4)
(def keys-window 4)
(def window-s 10)
;; Up to 120 transactions a start, four drivers at most at once: each start is a JVM and a
;; login, and a login is an argon2id hash of 128 MiB on the server (two at a time), costly in
;; the VM: eight drivers starting at once kept every server hashing, and trial run 1118's
;; timeline (no faults) ran 40 virtual seconds in 13 minutes.
(def ops-max 120)

(defn- now-s [] (quot (System/nanoTime) 1000000000))

(defn- draw
  "A transaction: 1 to 4 micro-operations on a window of 4 keys that moves every 10 s, each
  append's value unique for its key (the driver, its transaction, the operation)."
  [id sequence]
  (let [base (quot (now-s) window-s)]
    ;; Count, kinds and keys by swarm testing (stretches of single operations, appends only, one
    ;; hot key), where uniform draws kept them even (the review-inputs pass, 2026-11-08).
    (vec (for [index (range (inc (w/swarm-index "append.mops" mops-max)))]
           (if (zero? (w/swarm-index "append.mop" 2))
             [:append (+ base (w/swarm-index "append.key" keys-window)) (bit-or (bit-shift-left id 20) (bit-shift-left sequence 4) index)]
             [:r (+ base (w/swarm-index "append.key" keys-window)) nil])))))

(defn- read-list
  "A key's list: its appends' values in the order they were transacted (transaction, then
  entity: one transaction's appends get ascending entity ids)."
  [db k]
  (let [datoms (dl 'datoms)]
    (->> (datoms db :ave :append/key k)
         (keep (fn [key-datom]
                 (when-let [value-datom (first (datoms db :eav (:e key-datom) :append/value))]
                   [(:tx key-datom) (:e key-datom) (:v value-datom)])))
         (sort-by (juxt first second))
         (mapv #(nth % 2)))))

(defn- execute
  "The transaction's micro-operations in one explicit transaction: reads see the lists as of
  its start plus its own earlier appends; its appends transacted together at its end."
  [conn mops]
  (let [transact! (dl 'transact!)]
    ((dl 'with-transaction-fn)
     conn
     (reify java.util.function.Function
       (apply [_ tx-conn]
         (let [db @tx-conn
               [_ done] (reduce (fn [[lists done] [f k v :as mop]]
                                  (let [current (if (contains? lists k) (lists k) (read-list db k))]
                                    (if (= f :append)
                                      [(assoc lists k (conj current v)) (conj done mop)]
                                      [lists (conj done [:r k current])])))
                                [{} []]
                                mops)
               data (vec (for [[f k v] mops :when (= f :append)] {:append/key k :append/value v}))]
           (when (seq data) (transact! tx-conn data))
           done))))))

(defn- append-driver
  "A process bound to one node's connection, transactions one at a time, a new process (and a
  new connection) after an unknown outcome. Every failure is unknown: a definite one is told
  apart only where Datalevin says the transaction was refused before it applied. Connections
  failing for 15 s in a row end it (the composer starts it again): its slot is not held through
  a cluster restarting (trial run 1101: 41 refused connections, 5 starts in 300 s), nor given up
  inside a server's restart (6 to 15 s; trial run 1107's drivers quit after three, 1.5 s)."
  [_]
  (let [id (w/random-below (bit-shift-left 1 40))
        ops (inc (w/random-below ops-max))
        started (System/nanoTime)]
    ;; Its start, and each connection's, timed: a JVM loading Datalevin's client, then a login
    ;; the server verifies with argon2id one at a time (trial run 1099's drivers did nothing in
    ;; 48 s of a drive phase).
    (dl 'get-conn)
    (w/event "driver_loaded" {:ms (quot (- (System/nanoTime) started) 1000000)})
    (loop [sequence 0 process (w/elle-process) conn nil failing-since nil]
      (when (and (< sequence ops)
                 (or (nil? failing-since) (< (- (System/nanoTime) failing-since) 15000000000)))
        (let [node (w/choice nodes)
              asked (System/nanoTime)
              conn (or conn (try (let [made (connect node)]
                                   (w/event "connected" {:node node :ms (quot (- (System/nanoTime) asked) 1000000)})
                                   made)
                                 (catch Throwable e
                                   (w/event "connect_failed" {:node node :error (str (class e)) :message (ex-message e)})
                                   nil)))]
          (if-not conn
            (do (w/sleep-ms 500) (recur sequence process nil (or failing-since (System/nanoTime))))
            (let [mops (draw id sequence)
                  _ (w/elle-note :elle process :invoke mops)
                  outcome (try [:ok (execute conn mops)]
                               (catch Throwable e [:info e]))]
              (if (= :ok (first outcome))
                (w/elle-note :elle process :ok (second outcome))
                (let [^Throwable e (second outcome)]
                  (w/elle-note :elle process :info mops)
                  (w/event "txn_unknown" {:node node :error (str (class e)) :message (ex-message e)
                                          :data (pr-str (ex-data e))})))
              (w/sometimes (= :ok (first outcome)) "a transaction commits" {})
              (w/sleep-ms (w/random-below 100))
              (if (= :ok (first outcome))
                (recur (inc sequence) process conn nil)
                (do (close conn) (recur (inc sequence) (w/elle-process) nil nil))))))))))

(defn- committed
  "Each key's appends acknowledged in the history (ok lines)."
  []
  (let [path (Path/of "/opt/determinismo/records/elle.jsonl" (make-array String 0))]
    (if-not (Files/exists path (make-array java.nio.file.LinkOption 0))
      {}
      (reduce (fn [result {:keys [type value]}]
                (if (= type "ok")
                  (reduce (fn [result [f k v]] (if (= f "append") (update result k (fnil conj #{}) v) result)) result value)
                  result))
              {}
              (w/records (Files/readString path))))))

(defn- final-reads
  "Faults over: every acknowledged append is in its key's list, read in an explicit
  transaction on the leader (through any node that answers)."
  [_]
  (let [appends (committed)
        ;; One connection for every key's read, another after a failure: each is a login, an
        ;; argon2id hash on the server (trial run 1116's reads, a connection each, timed out).
        held (atom nil)
        ;; Every key's reads within 10 minutes of the faults' end: a cluster that never answers
        ;; again is judged so (each key's 30 attempts made hunt run 1145's last for hours).
        deadline (+ (System/nanoTime) (* 600 1000000000))
        late? #(>= (System/nanoTime) deadline)
        read-key (fn [k]
                   (loop [attempt 0]
                     (let [node (w/choice nodes)
                           ;; The key's list ([:r k list] back from execute), or nil.
                           result (try (let [conn (or @held (reset! held (connect node)))]
                                         (nth (first (execute conn [[:r k nil]])) 2))
                                       (catch Throwable e
                                         (w/event "final_read_failed" {:node node :key k :error (str (class e)) :message (ex-message e)})
                                         (some-> @held close)
                                         (reset! held nil)
                                         nil))]
                       (cond
                         result (set result)
                         ;; Backing off to 8 s: a failed read's new connection is a login.
                         (and (< attempt 30) (not (late?)))
                         (do (w/sleep-ms (min 8000 (bit-shift-left 1000 (min 3 attempt))))
                             (recur (inc attempt)))
                         :else nil))))
        judged (reduce (fn [judged [k values]]
                         (if-let [read (when-not (late?) (read-key k))]
                           (let [missing (remove read values)]
                             (w/always (empty? missing) "every acknowledged append is in the final read"
                                       {:key k :missing (vec (take 16 missing))})
                             (inc judged))
                           judged))
                       0 appends)]
    (some-> @held close)
    (when (late?) (w/event "final_reads_deadline" {:judged judged :keys (count appends)}))
    (w/sometimes (pos? judged) "the final reads reach the leader once faults stop" {:keys (count appends)})
    (when (and (seq appends) (zero? judged))
      (w/unreachable "the cluster answers once faults stop" {:keys (count appends)}))))

;; The system ---------------------------------------------------------------------------------

(def ^:private image {:context "." :dockerfile "workloads/datalevin/Dockerfile"})

(def fault-pacing
  "Faults in bursts of up to 5 s, then quiet for up to 120 s: a restarted server listens 18 s
  after its start, then logs in (an argon2id hash), opens its HA database once a quorum of
  voters has (their SOFAJRaft group re-forming), elects (5 s timeout) and leases (3 s): 30 to
  40 s, and bursts of 10 s killed a server three times in two seconds, quiet stretches of 30 s
  on average too short for any of it (trial run 1131: no restarted server opened its HA
  database, no commit)."
  {:active-ms-max 5000 :quiet-ms-max 120000})

(defn- server [node-name after]
  [node-name (cond-> {:build image
                      :command ["server" (name node-name)]
                      :ready {:tcp server-port :timeout-s 300}
                      :memory-max-mib 2048
                      :faults {:restart true :crash true :stop true :clock-skew true :clock-skew-ms-max 800}
                      ;; Datalevin leaves each database's VERSION file unsynced (README, found): on
                      ;; a strict disk a power loss at any age left it empty, the database never
                      ;; opened again. A drawn flusher (schema.Node.writeback_s), off in stretches,
                      ;; where the bug shows; its exit fails the run.
                      :writeback-s 30}
               after (assoc :after [after]))])

(def program
  {:profiles [{:name "default"
               :nodes [(server :dl1 nil)
                       (server :dl2 :dl1)
                       (server :dl3 :dl2)
                       ;; The client prepares the program (its namespaces compiled), waits for
                       ;; the cluster to take a write (await-cluster), then serves its REPL, ready
                       ;; once it listens: all in the setup's snapshot.
                       [:client {:build image
                                 :command ["client"]
                                 :ready {:tcp 7888 :timeout-s 600}
                                 :after [:dl3]
                                 :faults {:pause false :isolate false :partition false :sync-stall false
                                          :disk-lost-writes false :degrade false :runner-links false
                                          :throttle false :process-pause false :interleave false}}]]}]
   :node :client
   :program "/opt/workload/run"
   :scenarios [{:name "append" :parallel-max 4 :pacing fault-pacing
                :commands [(w/parallel-driver "txn" append-driver)
                           (w/eventually "final-reads" final-reads)]}]
   :checks {:elle (w/elle-check {:consistency "strict-serializable"})}})

(defn- await-cluster
  "During setup, before the client is ready: a write committed through any node (key -1, which
  no driver draws), so every timeline starts from a cluster that has a leader. The servers are
  ready once they listen, before their HA database opens (it needs a quorum of voters): trial
  run 1112's opened in its timeline, under its faults."
  []
  (loop [attempt 1]
    (let [node (nth nodes (mod attempt (count nodes)))
          done (try (let [conn (connect node)]
                      (try ((dl 'transact!) conn [{:append/key -1 :append/value attempt}]) true
                           (finally (close conn))))
                    (catch Throwable e
                      (println "await: through" node "not yet:" (ex-message e))
                      false))]
      (if done
        (println "await: the cluster took a write through" node "(attempt" (str attempt ")"))
        (do (Thread/sleep 2000) (recur (inc attempt)))))))

(defn -main [& arguments]
  (if (= ["await"] arguments)
    (do (await-cluster) (shutdown-agents) (System/exit 0))
    (w/main program arguments)))
