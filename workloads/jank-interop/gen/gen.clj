;; SPDX-License-Identifier: MIT
;; gen.clj: generated differential tests of jank against Clojure. Random forms from a typed
;; grammar over clojure.core (a seed, deterministic), each evaluated on Clojure 1.12 for its
;; expected outcome, written as a jank test namespace whose assertions say what Clojure said. A
;; failure on jank is a deviation, found without anyone writing its case (ephyra's method, as
;; jankifier's second source of findings beside the Lean replica's rounds).
;;
;;   clojure -M gen.clj <seed> <forms> <out dir>
;;
;; Kept: forms whose Clojure result is deterministic (two evaluations print the same; a lazy
;; result is realized, by printing it, inside the guarded evaluation), finite,
;; and reads back equal to itself, or that throw (any exception, both times). Each test holds ten
;; forms; each form is read and evaluated at run time (`ev`), so a form jank refuses fails its
;; own assertion, not the namespace. Output: <out>/jank_gen/gen_<seed>_test.jank and
;; <out>/gen-<seed>-forms.edn (every form with Clojure's outcome).
(ns gen
  (:require [clojure.string :as string]
            [clojure.java.io :as io]))

(def ^:dynamic ^java.util.Random *rng* nil)

(defn- below [n] (.nextInt *rng* (int n)))
(defn- pick [xs] (nth xs (below (count xs))))
(defn- chance [p] (< (.nextDouble *rng*) p))

;; Leaves, by type, with the edge values bugs sit at.
(def int-leaves [0 1 -1 2 3 -3 7 10 127 128 255 256 -128 1000 Long/MAX_VALUE Long/MIN_VALUE])
(def double-leaves [0.0 -0.0 1.5 -2.25 0.1 1e10 1e-5 3.0])
(def strs ["" "a" "abc" "a b" "é" "Ab-C" "x,y,z" " t "])
(def kws [:a :b :c :k/v :x])
(def scalars-extra [nil true false \a \z 'sym])

(declare gen-int gen-num gen-coll gen-str gen-any gen-map gen-pred gen-fn1 gen-printable)

(defn- gen-int [d]
  (if (or (<= d 0) (chance 0.4))
    (pick int-leaves)
    (let [k (below 10)]
      (case k
        0 (list (pick '[+ - *]) (gen-int (dec d)) (gen-int (dec d)))
        1 (list (pick '[inc dec]) (gen-int (dec d)))
        2 (list 'count (gen-coll (dec d)))
        3 (list (pick '[max min]) (gen-int (dec d)) (gen-int (dec d)))
        4 (list (pick '[quot rem mod]) (gen-int (dec d)) (pick [1 2 3 7 -2]))
        5 (list 'reduce '+ 0 (gen-coll (dec d)))
        6 (list 'first (list 'vector (gen-int (dec d))))
        7 (list 'count (gen-str (dec d)))
        8 (list 'nth (list 'vector (gen-int (dec d)) (gen-int (dec d))) (below 2))
        9 (list 'compare (gen-int (dec d)) (gen-int (dec d)))))))

(defn- gen-num [d]
  (if (chance 0.3) (pick double-leaves) (gen-int d)))

;; What str and pr-str may print: never a map or a set, whose element order Clojure leaves
;; unspecified (an order jank may rightly choose differently).
(defn- gen-printable [d]
  (case (below 6)
    0 (gen-int d) 1 (gen-num d) 2 (gen-str d) 3 (gen-coll d) 4 (pick kws) 5 (pick scalars-extra)))

(defn- gen-str [d]
  (if (or (<= d 0) (chance 0.4))
    (pick strs)
    (case (below 7)
      0 (list 'str (gen-printable (dec d)) (gen-printable (dec d)))
      1 (list (pick '[clojure.string/upper-case clojure.string/lower-case clojure.string/trim clojure.string/reverse]) (gen-str (dec d)))
      2 (list 'clojure.string/join (pick ["" "," "-"]) (gen-coll (dec d)))
      3 (list 'subs (pick ["abcdef" "hello" "é-è"]) (below 3))
      4 (list 'name (pick kws))
      5 (list 'pr-str (gen-printable (dec d)))
      6 (list 'clojure.string/replace (gen-str (dec d)) (pick ["a" "b" " "]) (pick ["" "X"])))))

(defn- gen-pred []
  (pick '[odd? even? pos? neg? zero? nil? some? number? string? keyword? vector? map? set? seq? coll?
          (fn [x] (and (number? x) (> x 2)))]))

(defn- gen-fn1 []
  (pick '[inc dec str identity (fn [x] (* x 2)) (fn [x] [x x]) keyword? (fn [x] (if (odd? x) :odd :even))]))

(defn- gen-coll [d]
  (if (or (<= d 0) (chance 0.3))
    (pick [[] [1 2 3] [3 1 2] '(list 1 2) [0 -1 7 7] (vec (range 5)) [1 1 1]])
    (case (below 14)
      0 (vec (repeatedly (below 4) #(gen-int (dec d))))
      1 (list 'map (pick '[inc dec (fn [x] (* x 2))]) (gen-coll (dec d)))
      2 (list 'filter (pick '[odd? even? pos? neg? zero?]) (gen-coll (dec d)))
      3 (list 'remove (pick '[odd? even? pos?]) (gen-coll (dec d)))
      4 (list (pick '[reverse sort distinct rest butlast seq vec]) (gen-coll (dec d)))
      5 (list (pick '[take drop]) (below 4) (gen-coll (dec d)))
      6 (list 'concat (gen-coll (dec d)) (gen-coll (dec d)))
      7 (list 'conj (gen-coll (dec d)) (gen-int (dec d)))
      ;; gen-coll stays ordered: a set made here would feed sequence functions its unspecified order.
      8 (list 'into (pick [[] '(list)]) (gen-coll (dec d)))
      9 (list 'interleave (gen-coll (dec d)) (gen-coll (dec d)))
      10 (list (pick '[partition partition-all]) (inc (below 3)) (gen-coll (dec d)))
      11 (list 'mapv (gen-fn1) (gen-coll (dec d)))
      12 (list 'sort-by 'str (list 'keys (gen-map (dec d))))
      13 (list 'sort-by (pick '[- identity]) (gen-coll (dec d))))))

(defn- gen-map [d]
  (if (or (<= d 0) (chance 0.3))
    (pick [{} {:a 1} {:a 1 :b 2} {:k/v "x" :a [1]}])
    (case (below 7)
      0 (list 'assoc (gen-map (dec d)) (pick kws) (gen-int (dec d)))
      1 (list 'dissoc (gen-map (dec d)) (pick kws))
      2 (list 'merge (gen-map (dec d)) (gen-map (dec d)))
      3 (list 'zipmap (vec (take (inc (below 3)) kws)) (gen-coll (dec d)))
      4 (list 'frequencies (gen-coll (dec d)))
      5 (list 'select-keys (gen-map (dec d)) (vec (take (below 3) kws)))
      6 (list 'group-by (pick '[odd? even? pos?]) (gen-coll (dec d))))))

(defn- gen-any [d]
  (case (below 13)
    12 (list 'into #{} (gen-coll (dec d)))
    0 (gen-int d) 1 (gen-num d) 2 (gen-str d) 3 (gen-coll d) 4 (gen-map d)
    5 (pick kws) 6 (pick scalars-extra)
    7 (list (gen-pred) (gen-any (dec d)))
    8 (list 'get (gen-map (dec d)) (pick kws))
    9 (list 'let ['x (gen-int (dec d))] (list (pick '[+ * max]) 'x (gen-int (dec d))))
    10 (list 'if (list (gen-pred) (gen-any (dec d))) (gen-any (dec d)) (gen-any (dec d)))
    11 (list (pick '[some every?]) (pick '[odd? even? pos?]) (gen-coll (dec d)))))

(defn- outcome
  "Clojure's outcome for a form: [:value v], [:throws class-name] or [:skip why]."
  [form]
  (let [run (fn [] (let [f (future (try (let [v (eval form)] (pr-str v) [:value v]) (catch Throwable e [:throws (.getName (class e))])))
                         r (deref f 2000 [:skip "timeout"])]
                     (when (= r [:skip "timeout"]) (future-cancel f))
                     r))
        a (run)
        b (run)]
    (cond
      (= :skip (first a)) a
      (not= (pr-str a) (pr-str b)) [:skip "not deterministic"]
      (= :throws (first a)) a
      :else (let [v (second a)
                  printed (pr-str v)]
              (cond
                (> (count printed) 2000) [:skip "large"]
                (fn? v) [:skip "a fn"]
                (not (try (= v (read-string printed)) (catch Throwable _ false))) [:skip "no read-back"]
                :else a)))))

(defn -main [& [seed n out]]
  (let [seed (Long/parseLong (or seed "1"))
        n (Long/parseLong (or n "500"))
        out (or out ".")
        forms (binding [*rng* (java.util.Random. seed)]
                (loop [kept [] tries 0]
                  (if (or (>= (count kept) n) (> tries (* 20 n)))
                    kept
                    (let [form (gen-any 4)
                          o (outcome form)]
                      (recur (if (= :skip (first o)) kept (conj kept {:form form :outcome o})) (inc tries))))))
        groups (partition-all 10 forms)
        ns-name (str "jank-gen.gen-" seed "-test")
        file (io/file out "jank_gen" (str "gen_" seed "_test.jank"))
        assertion (fn [{:keys [form outcome]}]
                    (let [code (pr-str (pr-str form))]
                      (if (= :value (first outcome))
                        (str "  (is (= (quote " (binding [*print-meta* false] (pr-str (second outcome))) ") (ev " code ")))")
                        (str "  (is (threw? (ev " code ")) " (pr-str (str "Clojure throws " (second outcome))) ")"))))]
    (io/make-parents file)
    (spit file
          (str ";; SPDX-License-Identifier: MIT\n"
               ";; Generated by workloads/jank-interop/gen/gen.clj, seed " seed ": each assertion is Clojure 1.12's\n"
               ";; outcome for a random form, so a failure on jank is a deviation. Do not edit.\n"
               "(ns " ns-name "\n  (:require [clojure.test :refer [deftest is]]\n            [clojure.string]))\n\n"
               "(defn- ev\n  \"The form's value, or [:jank-gen/threw what] for any throw jank's handlers can see (an\n   object, a native exception or a jank::error_ref): `is` catches objects only, and an\n   uncaught error would end the test before its other forms. An object's message only:\n   printing an ex-info makes jank crash as it exits (jankifier's S1).\"\n  [s]\n"
               "  (try (eval (read-string s))\n       (catch cpp/jank.runtime.object_ref e [:jank-gen/threw (ex-message e)])\n"
               "       (catch cpp/std.exception e [:jank-gen/threw (str (.what e))])\n"
               "       (catch cpp/jank.error_ref e [:jank-gen/threw (str (.-message (cpp/* e)))])))\n\n"
               "(defn- threw? [v] (and (vector? v) (= :jank-gen/threw (first v))))\n\n"
               (string/join "\n\n"
                            (map-indexed (fn [i group]
                                           (str (format "(deftest g%04d\n" i) (string/join "\n" (map assertion group)) ")"))
                                         groups))
               "\n"))
    (spit (io/file out (str "gen-" seed "-forms.edn")) (with-out-str (doseq [f forms] (prn f))))
    (println (count forms) "forms," (count groups) "tests, in" (str file))
    (shutdown-agents)))

(apply -main *command-line-args*)
