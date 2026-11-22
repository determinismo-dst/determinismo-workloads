;; SPDX-License-Identifier: MIT
;; Hegel for jank: property-based testing on Hegel's engine (libhegel, its C ABI, through jank's
;; C++ interop): README.md.
(defproject hegel-jank/hegel "0.1.0"
  :description "Hegel property-based testing for jank."
  :url "https://hegel.dev"
  :license {:name "MIT"}
  :dependencies [[hegel-jank/hegel-sys "0.51.1-0"]]
  :plugins [[org.jank-lang/lein-jank "2026.10-1"]]
  :middleware [leiningen.jank/middleware])
