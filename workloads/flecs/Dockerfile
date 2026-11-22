# SPDX-License-Identifier: MIT
# Flecs v4.2.0 (MIT; SanderMertens/flecs at 6566d4b, checksummed) under its stress harness
# (stress.c), built from source by clang: Flecs's sanitize checks on (FLECS_SANITIZE), trace-pc-guard
# coverage with the C SDK's callbacks (stress.c holds the SDK's implementation), frame pointers
# (determinismo's stacks unwind by them), undefined behavior trapping (as Zig's ReleaseSafe C
# did), line tables, the binary unstripped in /symbols. assertions.patch adds the SDK's
# assertions to Flecs's own source (assertions only, Flecs's behavior unchanged).
FROM docker.io/library/debian:bookworm-slim AS flecs
ARG FLECS_COMMIT=6566d4b7bdc597d0b74d5e0a4104d4ae6ac49402
ARG FLECS_SHA256=545e50b4118974cc8d89c57e3bcb5464b0a32afd23434403e9d6de16615503d6
RUN apt-get update -q \
 && DEBIAN_FRONTEND=noninteractive apt-get install -y -q --no-install-recommends \
      clang git ca-certificates curl \
 && rm -rf /var/lib/apt/lists/*
RUN curl -fsSL -o /tmp/flecs.tar.gz "https://github.com/SanderMertens/flecs/archive/${FLECS_COMMIT}.tar.gz" \
 && echo "${FLECS_SHA256}  /tmp/flecs.tar.gz" | sha256sum -c - \
 && mkdir -p /src/flecs && tar -xzf /tmp/flecs.tar.gz -C /src/flecs --strip-components=1 && rm /tmp/flecs.tar.gz
COPY --from=determinismo-sdk c/determinismo.h c/coverage-flags.sh /sdk/
COPY workloads/flecs/assertions.patch /src/assertions.patch
RUN cd /src/flecs && git apply /src/assertions.patch
COPY workloads/flecs/stress.c /src/stress.c
# What is instrumented: the source files the node's coverage set holds (a build argument from the
# test program's profile: Flecs's and the harness's, under /src), matched against the paths the
# compiler is given: absolute ones.
ARG DETERMINISMO_COVERAGE
RUN cd /src && flags="$(sh /sdk/coverage-flags.sh /sdk/lists) -fno-sanitize-link-runtime" \
 && common="-std=gnu11 -O2 -gline-tables-only -fno-omit-frame-pointer -DFLECS_SANITIZE \
      -fsanitize=undefined -fsanitize-trap=undefined -I/sdk -I/src/flecs/distr" \
 && clang $common $flags -c /src/flecs/distr/flecs.c -o flecs.o \
 && clang $common $flags -Wall -Wextra -DDETERMINISMO_COVERAGE -c /src/stress.c -o stress.o \
 && clang -Wl,--build-id -o /flecs-stress stress.o flecs.o -lpthread -lm

FROM docker.io/library/debian:bookworm-slim
COPY --from=flecs /flecs-stress /usr/local/bin/flecs-stress
COPY --from=flecs /flecs-stress /symbols/flecs-stress
ENTRYPOINT ["/usr/local/bin/flecs-stress"]
