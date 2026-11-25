; SPDX-License-Identifier: MIT
; A module for round 5's error tests (vB2 loads fixture a, vB3 fixture b): its namespace is
; created, then its top level throws. Both jank (which loads .cljc modules) and Clojure read it
; from tests/jank_lean/. Two files, because a failed load still records the lib in *loaded-libs*
; (the ns form does, on both sides), so a second require of the same lib loads nothing.
(ns jank-lean.r5-errors-fixture-a)

(def loaded-before-the-error 1)

(throw (ex-info "r5 errors fixture a" {:vb3 1}))
