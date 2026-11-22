;; SPDX-License-Identifier: MIT
;; Raw package for libhegel (Hegel's engine, its C ABI: https://github.com/hegeldev/hegel), as
;; jank commons packages C libraries: its header and prebuilt libraries in the jar (fetch.sh puts
;; them here from the release, checked against its checksums; a build script has no network),
;; jank-build.bb declaring this platform's.
(defproject hegel-jank/hegel-sys "0.51.1-0"
  :description "Raw package for libhegel 0.51.1, Hegel's property-based testing engine."
  :url "https://github.com/hegeldev/hegel"
  :license {:name "MIT" :url "https://github.com/hegeldev/hegel/blob/main/LICENSE"}
  :plugins [[org.jank-lang/lein-jank "2026.10-1"]]
  :middleware [leiningen.jank/middleware]
  :build-dependencies [[org.jank-lang.commons/jank-build "2026.10-1"]]
  :verbatim-paths ["include/hegel.h"
                   "lib/linux-amd64/libhegel.so"
                   "lib/linux-arm64/libhegel.so"
                   "lib/darwin-arm64/libhegel.dylib"
                   "LICENSE-libhegel"])
