# SPDX-License-Identifier: MIT
# jank's compiler and C++ interop under determinismo (README.md): jank from its repository,
# Leiningen with lein-jank, Babashka (jank-build runs packages' jank-build.bb), and Hegel for jank
# (hegel-jank/: hegel-sys with libhegel's prebuilt library, checked against its release's
# checksums, and the hegel binding), installed as the determinismo SDK is. The node runs the
# workload's drivers (jank run-main, its command kept as the lein run would start it) with
# --perf: jank's JIT writes a jitdump file naming what it compiles, which det-profile reads
# (determinismo stacks, profiles).
# Which jank (ARG JANK, the workload's profiles): coverage (the default), jank built from source with
# determinismo's trace-pc-guard coverage (jank-coverage/build.sh packs it on Debian 13, so the
# stage is Debian 13); package, jank's PPA build (Ubuntu 24.04), which has no coverage: the
# explorer is blind on it (phoenixNAP run 1908: no new behavior after its first generation).
ARG JANK=coverage
FROM docker.io/library/ubuntu:24.04 AS jank-package
RUN apt-get update -q \
 && DEBIAN_FRONTEND=noninteractive apt-get install -y -q --no-install-recommends ca-certificates curl gnupg \
 && curl -fsS https://ppa.jank-lang.org/KEY.gpg | gpg --dearmor > /etc/apt/trusted.gpg.d/jank.gpg \
 && echo "deb [signed-by=/etc/apt/trusted.gpg.d/jank.gpg] https://ppa.jank-lang.org noble main" \
      > /etc/apt/sources.list.d/jank.list \
 && apt-get update -q \
 && DEBIAN_FRONTEND=noninteractive apt-get install -y -q jank gdb \
 && rm -rf /var/lib/apt/lists/*
FROM docker.io/library/debian:trixie AS jank-coverage
# What the instrumented jank and its LLVM link against (ldd on the build host, by package).
RUN apt-get update -q \
 && DEBIAN_FRONTEND=noninteractive apt-get install -y -q --no-install-recommends \
      ca-certificates curl gnupg gdb build-essential \
      libstdc++6 libgcc-s1 zlib1g liblzma5 libxml2 \
 && rm -rf /var/lib/apt/lists/*
# jank-coverage/build.sh's tarball (jank's LLVM and jank at its pinned commit, with coverage and the
# SDK's assertions), kept on this repository's release: hours of building, so fetched, checksummed.
ARG JANK_COVERAGE_URL=https://github.com/determinismo-dst/determinismo-workloads/releases/download/jank-coverage-44eea86f7/jank-install.tar
ARG JANK_COVERAGE_SHA256=a47c536e4eb9523b3aa160d99d2623fd1e1934d0602f33d55cfb2bcbddbddf4c
RUN curl -fsSL -o /tmp/jank-install.tar "$JANK_COVERAGE_URL" \
 && echo "${JANK_COVERAGE_SHA256}  /tmp/jank-install.tar" | sha256sum -c -
# A program run, not --help (which exits 1): the libraries load, and jank compiles and runs.
RUN tar -xf /tmp/jank-install.tar -C / && rm /tmp/jank-install.tar \
 && echo '(println :jank-runs)' > /tmp/check.jank && jank run /tmp/check.jank | grep -q jank-runs && rm /tmp/check.jank
FROM jank-${JANK} AS jank

FROM jank AS build
RUN apt-get update -q \
 && DEBIAN_FRONTEND=noninteractive apt-get install -y -q --no-install-recommends \
      ca-certificates curl git openjdk-21-jdk-headless build-essential \
 && rm -rf /var/lib/apt/lists/*
ENV HOME=/root LEIN_ROOT=1
RUN curl -fsSL -o /usr/local/bin/lein https://raw.githubusercontent.com/technomancy/leiningen/2.11.2/bin/lein \
 && chmod +x /usr/local/bin/lein && lein version
RUN curl -fsSL https://github.com/babashka/babashka/releases/download/v1.13.225/babashka-1.13.225-linux-amd64-static.tar.gz \
      | tar -xz -C /usr/local/bin bb && bb --version
# Hegel for jank: the raw package (libhegel fetched and checked by its fetch.sh) and the binding.
COPY workloads/jank-interop/hegel-jank /work/libs/hegel-jank
RUN /work/libs/hegel-jank/hegel-sys/fetch.sh \
 && cd /work/libs/hegel-jank/hegel-sys && lein install && cd ../hegel && lein install
COPY --from=determinismo-sdk jank /work/sdk/jank
RUN cd /work/sdk/jank/determinismo-sys && lein install && cd ../determinismo && lein install
COPY workloads/jank-interop /work/workloads/jank-interop
WORKDIR /work/workloads/jank-interop
RUN lein deps
# The drivers' command, as lein runs them (jank run-main with the project's flags), --perf added.
RUN lein with-profile +guest run -m jank-interop.workload --verbose --disable-sandbox < /dev/null > /tmp/lein-run.log 2>&1; \
    grep '^> jank run-main' /tmp/lein-run.log | head -1 | sed 's/^> //; s/ --$//; s/^jank /jank --perf /' > run-command \
 && grep -q 'jank-interop.workload' run-command \
 && mkdir -p /opt/workload \
 && printf '#!/bin/sh\ncd /work/workloads/jank-interop\nexec %s -- "$@"\n' "$(cat run-command)" > /opt/workload/run \
 && chmod +x /opt/workload/run && cat /opt/workload/run

FROM jank
ENV HOME=/root
COPY --from=build /root/.m2 /root/.m2
COPY --from=build /root/.cache /root/.cache
COPY --from=build /work /work
COPY --from=build /opt/workload /opt/workload
WORKDIR /work/workloads/jank-interop
ENTRYPOINT ["sleep", "infinity"]
