;; SPDX-License-Identifier: MIT
(ns datalevin-node
  "A Datalevin server of the consensus-lease HA cluster (doc/ha.md): `datalevin.server` serving
  on 8898, the database `det` opened in HA mode on it, its SOFAJRaft control-plane voter on 7801.
  Node `dlN` is HA node N of three, every one a promotable voter.

  The database's HA options reach the server through `*server-runtime-opts-fn*`, so a database
  the server opens again after a restart (a client's connection, its own recovery) is opened in
  HA mode as well; the node then opens it once itself, which starts its lease authority. The
  options are Datalevin's own Jepsen suite's (jepsen/src/datalevin/jepsen/remote.clj,
  base-ha-opts): a 1 s lease renewal, a 3 s lease, a 1 s clock-skew budget, promotion only fully
  caught up, and a fencing hook that does nothing (safety then rests on the lease alone)."
  (:require [datalevin.client :as cl]
            [datalevin.server :as srv]
            [datalevin.server.auth :as auth])
  (:import (java.net InetAddress)))

(def db-name "det")
(def server-port 8898)
(def raft-port 7801)
(def nodes ["dl1" "dl2" "dl3"])
;; The servers' admin password: Datalevin refuses to bind a non-loopback address with its
;; built-in default (DATALEVIN_DEFAULT_PASSWORD, set in the image).
(def password (or (System/getenv "DATALEVIN_DEFAULT_PASSWORD") "datalevin"))

(defn address
  "A node's IPv4 address, from the hosts file: SOFAJRaft peer ids are addresses."
  [node]
  (.getHostAddress (InetAddress/getByName node)))

(defn ha-opts [node-id]
  (let [members (vec (for [[index node] (map-indexed vector nodes)]
                       {:node-id (inc index) :endpoint (str (address node) ":" server-port)}))
        voters (vec (for [[index node] (map-indexed vector nodes)]
                      {:peer-id (str (address node) ":" raft-port) :ha-node-id (inc index) :promotable? true}))]
    {:wal? true
     :db-identity db-name
     :ha-mode :consensus-lease
     :ha-lease-renew-ms 1000
     :ha-lease-timeout-ms 3000
     :ha-promotion-base-delay-ms 100
     :ha-promotion-rank-delay-ms 200
     :ha-max-promotion-lag-lsn 0
     :ha-clock-skew-budget-ms 1000
     :ha-fencing-hook {:cmd ["/bin/sh" "-c" "exit 0"] :timeout-ms 1000 :retries 0 :retry-delay-ms 0}
     ;; The servers' own traffic logs in with the built-in default account's password unless
     ;; told (doc/ha.md): ours is DATALEVIN_DEFAULT_PASSWORD's, and without these every peer's
     ;; login failed (trial run 1111: "Failed to authenticate", no leader, no write).
     :ha-client-credentials {:username "datalevin" :password password}
     :ha-members members
     :ha-node-id node-id
     :ha-control-plane {:backend :sofa-jraft
                        :group-id db-name
                        :local-peer-id (str (address (nth nodes (dec node-id))) ":" raft-port)
                        :voters voters
                        :rpc-timeout-ms 5000
                        :election-timeout-ms 5000
                        :operation-timeout-ms 30000}}))

(def schema
  {:append/key {:db/valueType :db.type/long :db/index true}
   :append/value {:db/valueType :db.type/long}})

(defn- logins-cheaper
  "The test's machine: a login's argon2id at one pass over 8 MiB, not Datalevin's four over
  128 MiB (auth.clj's defaults, not configurable). Three servers share the VM's one CPU, where
  each has its own cores in production: a login took 0.65 s of it, and after the faults the
  servers' HA traffic to each other, logging in again as its requests timed out, kept two of
  them hashing (trial run 1133: about 200 s of CPU in 230 s, every final read timed out), the
  overload sustaining itself. Both copies of the function (datalevin.server keeps its own,
  which creates the account) rebound before the server starts: the account is stored and
  checked at the same cost."
  []
  (let [original auth/password-hashing
        cheaper (fn ([password salt] (original password salt {:ops-limit 1 :mem-limit 8192}))
                  ([password salt opts]
                   (original password salt (merge opts {:ops-limit 1 :mem-limit 8192}))))]
    (alter-var-root #'auth/password-hashing (constantly cheaper))
    (alter-var-root #'srv/password-hashing (constantly cheaper))))

(defn -main [node]
  (let [node-id (inc (.indexOf ^java.util.List nodes node))
        _ (assert (pos? node-id) (str "no node " node))
        opts (ha-opts node-id)]
    (logins-cheaper)
    (alter-var-root #'srv/*server-runtime-opts-fn*
                    (constantly (fn [_ name _ _] (when (= name db-name) opts))))
    (let [server (srv/create {:host "0.0.0.0" :port server-port :root "/data/datalevin"})]
      (srv/start server)
      (println "datalevin-node: serving on" server-port "as HA node" node-id)
      ;; Its database opened here (its authority started), again every second until it opens:
      ;; the voters come up one after another, and a quorum forms while their attempts overlap
      ;; (backed off to 15 s, no restarted server's open ever succeeded, trial run 1128). One
      ;; client for every attempt, a new one only once its connection broke: each client is a
      ;; login, an argon2id hash of 0.65 s of the VM's one CPU, and three servers logging in
      ;; every second kept it hashing (trial run 1123's final reads, every read timed out).
      (loop [attempt 1 client nil]
        (let [client (or client
                         (try (cl/new-client (str "dtlv://datalevin:" password "@127.0.0.1:" server-port)
                                             {:pool-size 1 :time-out 10000})
                              (catch Throwable e
                                (println "datalevin-node: connecting failed (attempt" attempt "):"
                                         (.getName (class e)) (ex-message e))
                                nil)))
              outcome (if-not client
                        :retry
                        (try (cl/open-database client db-name "datalog" schema opts)
                             :opened
                             (catch Throwable e
                               (println "datalevin-node: opening" db-name "failed (attempt" attempt "):"
                                        (.getName (class e)) (ex-message e))
                               (if (re-find #"(?i)closed|connect|reset" (str (ex-message e))) :reconnect :retry))))]
          (case outcome
            :opened (println "datalevin-node: opened" db-name "in HA mode")
            :reconnect (do (try (cl/disconnect client) (catch Throwable _ nil))
                           (Thread/sleep 1000) (recur (inc attempt) nil))
            (do (Thread/sleep 1000) (recur (inc attempt) client)))))
      @(promise))))
