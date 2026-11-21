# SPDX-License-Identifier: MIT
# Datalevin 1.2.10 (EPL-2.0, from Clojars at build time) on JDK 25: one image for its three HA
# servers (node/datalevin_node.clj) and the client node, where the test program
# (workload/datalevin_workload.clj, Clojure on sdk/clojure's determinismo.workload) runs its
# commands with Datalevin's remote client. The JVM SDK's coverage agent on datalevin.* (and
# SOFAJRaft's com.alipay.sofa.jraft) in the servers: thread pausing pauses their code.
FROM docker.io/library/clojure:temurin-25-tools-deps-1.12.6.1673-trixie-slim
COPY --from=determinismo-sdk java/Determinismo.java java/DeterminismoCatalog.java java/DeterminismoCoverage.java java/DeterminismoCoverageInstrument.java /opt/agent/sdk/
RUN mkdir -p /opt/agent/classes && javac -d /opt/agent/classes /opt/agent/sdk/*.java \
 && printf 'Premain-Class: DeterminismoCoverage\n' > /opt/agent/manifest \
 && jar cfm /opt/determinismo-coverage.jar /opt/agent/manifest -C /opt/agent/classes .
COPY workloads/datalevin/deps.edn /opt/datalevin/deps.edn
RUN cd /opt/datalevin && clojure -P && clojure -Spath > /opt/datalevin/classpath
# Datalevin compiled ahead of time (its jar holds its namespaces as source: loading datalevin.core
# took 27 s on srv4's host, the guest's drivers spent their whole lives in it): compiling it and
# its server compiles every namespace they load, as a jar first on every classpath of the image.
# A jar, not the directory: the guest's image has every file at time 0 (mkfs.erofs -T0), and
# Clojure loads a class only when it is newer than its source (the jar entry's time, 2026): in
# trial run 1101 the servers compiled Datalevin from source at every start (a replay's dump,
# `RT.loadResourceScript` under datalevin.bits). A jar's entries carry their own times.
# Then the JDK's AOT cache of what a command loads (JEP 514: classes loaded and linked; 6 s to
# 2.6 s on one of srv4's cores), the drivers' JVMs starting from it: trial run 1101's took 107 s
# of a timeline to load Datalevin's client, eight at once beside three servers. The cache needs
# jars only on its classpath, a prefix of each command's, and refuses a jar whose time changed
# since ("timestamp has changed"): trained with the jars at time 0, as the guest has them (56 s
# to load in trial run 1107, the cache refused; 3.0 s against 5.8 s on one core so). The servers
# have a cache of their own, their classes on the HA path instrumented ahead of time (the JVM
# SDK's coverage, `instrument`): an agent transforming them at load kept the cache from helping
# (a server: 16.5 s to load with the agent, 4.7 s with the cache and no agent).
RUN mkdir -p /opt/datalevin/classes && cd /opt/datalevin \
 && java --add-opens=java.base/java.nio=ALL-UNNAMED --add-opens=java.base/sun.nio.ch=ALL-UNNAMED \
      -cp "/opt/datalevin/classes:$(cat /opt/datalevin/classpath)" clojure.main \
      -e "(binding [*compile-path* \"/opt/datalevin/classes\"] (compile 'datalevin.core) (compile 'datalevin.server))" \
 && jar cf /opt/datalevin/aot.jar -C /opt/datalevin/classes . && rm -rf /opt/datalevin/classes \
 && echo "/opt/datalevin/aot.jar:$(cat /opt/datalevin/classpath)" > /opt/datalevin/classpath \
 && find /root/.m2 /opt/datalevin -name '*.jar' -exec touch -d @0 {} + \
 && java --add-opens=java.base/java.nio=ALL-UNNAMED --add-opens=java.base/sun.nio.ch=ALL-UNNAMED \
      --enable-native-access=ALL-UNNAMED -XX:+UseSerialGC -XX:TieredStopAtLevel=1 -Xmx256m \
      -XX:AOTCacheOutput=/opt/datalevin/client.aot -cp "$(cat /opt/datalevin/classpath)" clojure.main \
      -e "(require 'datalevin.core)" \
 && jraft=$(tr : '\n' < /opt/datalevin/classpath | grep '/jraft-core-') \
 && java -cp "/opt/determinismo-coverage.jar:$(cat /opt/datalevin/classpath)" DeterminismoCoverage \
      instrument datalevin.ha,datalevin.server,datalevin.tx_group,datalevin.txlog,datalevin.kv,datalevin.storage,datalevin.lmdb,datalevin.remote,datalevin.client,datalevin.protocol,com.alipay.sofa.jraft \
      /opt/datalevin/aot.jar /opt/datalevin/aot-instrumented.jar "$jraft" /opt/datalevin/jraft-instrumented.jar \
 && echo "/opt/determinismo-coverage.jar:$(sed -e 's#/opt/datalevin/aot.jar#/opt/datalevin/aot-instrumented.jar#' \
      -e "s#$jraft#/opt/datalevin/jraft-instrumented.jar#" /opt/datalevin/classpath)" > /opt/datalevin/server-classpath \
 && find /opt/datalevin /opt/determinismo-coverage.jar -name '*.jar' -exec touch -d @0 {} + \
 && java --add-opens=java.base/java.nio=ALL-UNNAMED --add-opens=java.base/sun.nio.ch=ALL-UNNAMED \
      --enable-native-access=ALL-UNNAMED -Xmx1100m -XX:+UseSerialGC \
      -XX:AOTCacheOutput=/opt/datalevin/server.aot -cp "$(cat /opt/datalevin/server-classpath)" clojure.main \
      -e "(require 'datalevin.server) (require 'datalevin.core)" 
COPY workloads/datalevin/node /opt/datalevin/node
COPY --from=determinismo-sdk clojure /opt/workload/src
COPY workloads/datalevin/workload/datalevin_workload.clj /opt/workload/src/
COPY workloads/datalevin/start.sh /opt/start.sh
RUN chmod +x /opt/start.sh && ln -s /opt/start.sh /opt/workload/run
# Datalevin refuses to bind a non-loopback address with its built-in admin password.
ENV DATALEVIN_DEFAULT_PASSWORD=det
ENTRYPOINT ["/opt/start.sh"]
