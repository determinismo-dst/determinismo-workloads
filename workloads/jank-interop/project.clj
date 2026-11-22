;; SPDX-License-Identifier: MIT
;; jank's compiler and C++ interop under determinismo, Hegel generating the cases: README.md.
(defproject jank-interop "0.1-SNAPSHOT"
  :description "Generated cpp/raw functions and jank forms, evaluated as the REPL does."
  :license {:name "MIT"}
  :dependencies [[hegel-jank/hegel "0.1.0"]]
  :plugins [[org.jank-lang/lein-jank "2026.10-1"]]
  :middleware [leiningen.jank/middleware]
  :main jank-interop.workload
  :profiles {:base {:jank {:target-dir "target/debug"
                           :optimization-level 0}}
             :guest {:dependencies [[org.determinismo/determinismo "0.1.0"]]}})
