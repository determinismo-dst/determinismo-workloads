;; SPDX-License-Identifier: MIT
;; gen.clj: generated differential tests of jank against Clojure (ephyra's method, as jankifier's
;; second source of findings beside the Lean replica's rounds). Three stages, each run through
;; determinismo-ci between them:
;;
;;   clojure -M gen.clj gen <seed> <forms>          random forms from a typed grammar over
;;       clojure.core (the seed decides them), Clojure 1.12's outcome for each as the expected one:
;;       tests/jank_gen/gen_<seed>_test.jank, results/gen-<seed>-forms.edn
;;   clojure -M gen.clj shrink <seed> <failures.json>   each form jank answered wrongly (or every
;;       form of a test that crashed or hung), its subforms as cases of their own:
;;       tests/jank_gen/shrink_<seed>_test.jank, results/shrink-<seed>-cases.edn
;;   clojure -M gen.clj group <seed> <failures.json>    the shrink run's minimal failing subforms
;;       grouped by signature (head, how jank differs): results/gen-<seed>-groups.md
;;
;; Kept: forms whose Clojure outcome is deterministic (two evaluations print the same, a lazy
;; result realized inside the guard), short, and reads back equal, or that throw both times. Ten
;; cases a test, one assertion over them: the runner reports a test's first failure only.
(ns gen
  (:require [clojure.string :as string]
            [clojure.java.io :as io]
            [clojure.data.json :as json]))

(def ^:dynamic ^java.util.Random *rng* nil)

(defn- below [n] (.nextInt *rng* (int n)))
(defn- pick [xs] (nth xs (below (count xs))))
(defn- chance [p] (< (.nextDouble *rng*) p))

;; The grammar's version: 1 draws seeds 1 and 2 as they were written (the same seed, the same
;; files); 2 adds what seeds 1 and 2 found the replica missed around: bit and unchecked
;; arithmetic, the primed (promoting) operators, ratios, doubles' special values, and strings
;; past ASCII (two-byte letters and surrogate pairs) through every function that indexes them.
(def ^:dynamic *grammar* 2)
(defn- g2? [] (>= *grammar* 2))
(def strs-2 ["ü" "a😀b" "😀" "日本語" "e\u0301"])
(def shifts [0 1 31 32 63 64 65 -1])

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
    (let [k (below (if (g2?) 16 10))]
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
        9 (list 'compare (gen-int (dec d)) (gen-int (dec d)))
        10 (list (pick '[bit-and bit-or bit-xor bit-and-not]) (gen-int (dec d)) (gen-int (dec d)))
        11 (list (pick '[bit-shift-left bit-shift-right unsigned-bit-shift-right]) (gen-int (dec d)) (pick shifts))
        12 (list (pick '[unchecked-add unchecked-subtract unchecked-multiply]) (gen-int (dec d)) (gen-int (dec d)))
        13 (list (pick '[+' -' *']) (gen-int (dec d)) (gen-int (dec d)))
        14 (list (pick '[inc' dec' abs unchecked-inc unchecked-dec unchecked-negate -]) (gen-int (dec d)))
        15 (list 'compare (gen-str (dec d)) (gen-str (dec d)))))))

(defn- gen-num [d]
  (if (and (g2?) (chance 0.25))
    (case (below 6)
      0 (pick '[##Inf ##-Inf 1/3 -2/7 1.0E308 4.9E-324])
      1 (list '/ (gen-int (dec d)) (pick [3 7 -2 4]))
      2 (list (pick '[double float long int]) (pick '[1/3 2.5 -2.5 1e10 9.999]))
      3 (list (pick '[== < <= compare]) (pick [1 0 -1 2]) (pick [1.0 0.0 -0.0 2.5]))
      4 (list (pick '[quot rem mod]) (pick [7.5 -7.5 1/3 10]) (pick [2 -2 0.5]))
      5 (list (pick '[min max]) (pick [1 1.0 -0.0 0]) (pick [1.0 1 0.0 0])))
    (if (chance 0.3) (pick double-leaves) (gen-int d))))

;; What str and pr-str may print: never a map or a set, whose element order Clojure leaves
;; unspecified (an order jank may rightly choose differently).
(defn- gen-printable [d]
  (case (below 6)
    0 (gen-int d) 1 (gen-num d) 2 (gen-str d) 3 (gen-coll d) 4 (pick kws) 5 (pick scalars-extra)))

(defn- gen-str [d]
  (if (or (<= d 0) (chance 0.4))
    (if (and (g2?) (chance 0.4)) (pick strs-2) (pick strs))
    (case (below (if (g2?) 11 7))
      0 (list 'str (gen-printable (dec d)) (gen-printable (dec d)))
      1 (list (pick '[clojure.string/upper-case clojure.string/lower-case clojure.string/trim clojure.string/reverse]) (gen-str (dec d)))
      2 (list 'clojure.string/join (pick ["" "," "-"]) (gen-coll (dec d)))
      3 (list 'subs (pick ["abcdef" "hello" "é-è"]) (below 3))
      4 (list 'name (pick kws))
      5 (list 'pr-str (gen-printable (dec d)))
      6 (list 'clojure.string/replace (gen-str (dec d)) (pick ["a" "b" " "]) (pick ["" "X"]))
      7 (list 'subs (pick strs-2) (below 3) (+ 1 (below 3)))
      8 (list 'str (list (pick '[clojure.string/index-of clojure.string/last-index-of]) (gen-str (dec d)) (pick ["a" "😀" "b" "語"])))
      9 (list 'apply 'str (list (pick '[reverse seq rest butlast]) (pick strs-2)))
      10 (list 'str (list (pick '[nth get]) (pick strs-2) (below 3)) (list (pick '[clojure.string/capitalize clojure.string/upper-case]) (pick strs-2))))))

(defn- gen-pred []
  (if (and (g2?) (chance 0.2))
    (pick '[ratio? integer? double? rational? float? int? nat-int? pos-int? char? NaN? infinite?
            (fn [x] (and (string? x) (clojure.string/blank? x)))])
    (pick '[odd? even? pos? neg? zero? nil? some? number? string? keyword? vector? map? set? seq? coll?
            (fn [x] (and (number? x) (> x 2)))])))

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

;; Grammar 3 (seeds 4 on): what seeds 1-3 left unreached, without the deviations they found
;; (jankifier's R5, LG1-LG3, LU74, D2): no Long/MIN_VALUE literal, `count` only through `long`, shifts
;; below 64, no unchecked-* and no integer `/`, strings ASCII only; sequences, maps, sets, higher-order
;; functions and ASCII string functions instead.
(def int3-leaves [0 1 -1 2 3 -3 7 10 127 128 255 -128 1000 Long/MAX_VALUE])
(def strs3 ["" "a" "abc" "a b" "Ab-C" "x,y,z" " t " "hello world" "a\nb"])

(declare gen-int3 gen-coll3 gen-map3 gen-set3 gen-str3 gen-any3)

(defn- gen-int3 [d]
  (if (or (<= d 0) (chance 0.4))
    (pick int3-leaves)
    (case (below 12)
      0 (list (pick '[+' -' *']) (gen-int3 (dec d)) (gen-int3 (dec d)))
      1 (list (pick '[inc' dec' abs -]) (gen-int3 (dec d)))
      2 (list 'long (list 'count (gen-coll3 (dec d))))
      3 (list (pick '[max min]) (gen-int3 (dec d)) (gen-int3 (dec d)))
      4 (list (pick '[quot rem mod]) (gen-int3 (dec d)) (pick [1 2 3 7 -2]))
      5 (list (pick '[bit-and bit-or bit-xor bit-and-not]) (gen-int3 (dec d)) (gen-int3 (dec d)))
      6 (list (pick '[bit-shift-left bit-shift-right unsigned-bit-shift-right bit-set bit-clear bit-flip]) (gen-int3 (dec d)) (below 63))
      7 (list 'reduce (pick '[+' max min]) 0 (gen-coll3 (dec d)))
      8 (list 'apply (pick '[max min +']) 0 (gen-coll3 (dec d)))
      9 (list (pick '[first last second peek]) (list 'vec (list 'cons 0 (gen-coll3 (dec d)))))
      10 (list 'get (gen-map3 (dec d)) (pick [:a :b :x]) -5)
      11 (list (pick '[max-key min-key]) (pick '[- identity abs]) (gen-int3 (dec d)) (gen-int3 (dec d)) (gen-int3 (dec d))))))

(defn- gen-coll3 [d]
  (if (or (<= d 0) (chance 0.3))
    (pick [[] [1 2 3] [3 1 2] '(list 1 2) [0 -1 7 7] (vec (range 5)) [1 1 1] [5 4 4 2 9 0]])
    (case (below 24)
      0 (vec (repeatedly (below 4) #(gen-int3 (dec d))))
      1 (list 'map-indexed 'vector (gen-coll3 (dec d)))
      2 (list 'keep-indexed '(fn [i x] (when (even? i) x)) (gen-coll3 (dec d)))
      3 (list 'partition-by (pick '[odd? pos? identity]) (gen-coll3 (dec d)))
      4 (list 'reductions (pick '[+' max min]) (gen-coll3 (dec d)))
      5 (list (pick '[dedupe distinct reverse sort rest butlast]) (gen-coll3 (dec d)))
      6 (list (pick '[take-while drop-while filter remove]) (pick '[pos? odd? even? neg?]) (gen-coll3 (dec d)))
      7 (list 'interpose 0 (gen-coll3 (dec d)))
      8 (list 'flatten (list 'list (gen-coll3 (dec d)) (list 'list (gen-coll3 (dec d)))))
      9 (list 'mapcat '(fn [x] [x x]) (gen-coll3 (dec d)))
      10 (list (pick '[split-at split-with]) (if (chance 0.5) (below 4) '(fn [x] (< x 3))) (gen-coll3 (dec d)))
      11 (list 'sort (pick '[> < compare]) (gen-coll3 (dec d)))
      12 (list 'range (- (below 6) 3) (+ 3 (below 6)) (pick [1 2 3 -1]))
      13 (list 'take (below 7) (list 'cycle (list 'cons 1 (gen-coll3 (dec d)))))
      14 (list 'subvec [0 1 2 3 4 5] (below 3) (+ 3 (below 4)))
      15 (list (pick '[nthnext nthrest drop take take-last drop-last]) (gen-coll3 (dec d)) (below 4))
      16 (list 'map (pick '[+ max min vector]) (gen-coll3 (dec d)) (gen-coll3 (dec d)))
      17 (list 'map (list (pick '[juxt comp]) 'inc (pick '[dec - identity])) (gen-coll3 (dec d)))
      18 (list 'sort-by 'first (list 'map 'vector (gen-coll3 (dec d)) (list 'range)))
      19 (list 'vals (list 'into '(sorted-map) (list 'zipmap [:a :b :c :d] (gen-coll3 (dec d)))))
      20 (list 'keys (list 'into '(sorted-map) (gen-map3 (dec d))))
      21 (list 'seq (list 'into '(sorted-set) (gen-coll3 (dec d))))
      22 (list (pick '[partition partition-all]) (inc (below 3)) (inc (below 2)) (gen-coll3 (dec d)))
      23 (list 'filter (list (pick '[every-pred some-fn]) 'odd? 'pos?) (gen-coll3 (dec d))))))

(defn- gen-map3 [d]
  (if (or (<= d 0) (chance 0.3))
    (pick [{} {:a 1} {:a 1 :b 2} {:a 1 :x {:y 2}}])
    (case (below 10)
      0 (list 'merge-with (pick '[+' max min]) (gen-map3 (dec d)) (gen-map3 (dec d)))
      1 (list 'update (gen-map3 (dec d)) (pick [:a :b]) '(fnil inc' 0))
      2 (list 'assoc-in (gen-map3 (dec d)) [:x :y] (gen-int3 (dec d)))
      3 (list 'update-in (gen-map3 (dec d)) [(pick [:a :x]) :z] '(fnil inc' 0))
      4 (list 'select-keys (gen-map3 (dec d)) (vec (take (below 3) [:a :b :x])))
      5 (list 'clojure.set/rename-keys (gen-map3 (dec d)) {:a :z})
      6 (list 'frequencies (gen-coll3 (dec d)))
      7 (list 'group-by (pick '[odd? even? pos?]) (gen-coll3 (dec d)))
      8 (list 'zipmap [:a :b :c] (gen-coll3 (dec d)))
      9 (list 'reduce-kv '(fn [m k v] (assoc m k [v])) {} (gen-map3 (dec d))))))

(defn- gen-set3 [d]
  (if (or (<= d 0) (chance 0.3))
    (pick [#{} #{1} #{1 2 3} #{:a :b}])
    (case (below 6)
      0 (list (pick '[clojure.set/union clojure.set/intersection clojure.set/difference]) (gen-set3 (dec d)) (gen-set3 (dec d)))
      1 (list 'set (gen-coll3 (dec d)))
      2 (list 'disj (gen-set3 (dec d)) (pick [1 2 :a]))
      3 (list 'conj (gen-set3 (dec d)) (gen-int3 (dec d)))
      4 (list 'clojure.set/select 'odd? (list 'set (gen-coll3 (dec d))))
      5 (list 'into #{} (list 'map 'inc (gen-coll3 (dec d)))))))

(defn- gen-str3 [d]
  (if (or (<= d 0) (chance 0.4))
    (pick strs3)
    (case (below 10)
      0 (list 'str (gen-int3 (dec d)) (pick [":" "" "-"]) (gen-str3 (dec d)))
      1 (list (pick '[clojure.string/upper-case clojure.string/lower-case clojure.string/trim clojure.string/capitalize clojure.string/triml clojure.string/trimr]) (gen-str3 (dec d)))
      2 (list 'clojure.string/join (pick ["" "," "-"]) (gen-coll3 (dec d)))
      3 (list 'subs (pick ["abcdef" "hello world"]) (below 3) (+ 3 (below 3)))
      4 (list 'apply 'str (list 'interpose "," (gen-coll3 (dec d))))
      5 (list 'clojure.string/replace (gen-str3 (dec d)) (pick ["a" "b" " " "l"]) (pick ["" "X" "--"]))
      6 (list 'str (list (pick '[clojure.string/index-of clojure.string/last-index-of]) (gen-str3 (dec d)) (pick ["a" "b" "l" " "])))
      7 (list 'str (list (pick '[clojure.string/includes? clojure.string/starts-with? clojure.string/ends-with?]) (gen-str3 (dec d)) (pick ["a" "" "b" "ld"])))
      8 (list 'pr-str (list (pick '[clojure.string/split-lines clojure.string/blank?]) (gen-str3 (dec d))))
      9 (list 'clojure.string/join "|" (list 'clojure.string/split (gen-str3 (dec d)) (pick [#"," #" " #"b"]))))))

(defn- gen-any3 [d]
  (case (below 10)
    0 (gen-int3 d) 1 (gen-coll3 d) 2 (gen-map3 d) 3 (gen-set3 d) 4 (gen-str3 d)
    5 (list (pick '[empty? not-empty boolean seq]) (gen-coll3 (dec d)))
    6 (list (pick '[contains? get find]) (gen-map3 (dec d)) (pick [:a :b :x]))
    7 (list (pick '[some every? not-any? not-every?]) (pick '[odd? even? pos? #{1 2}]) (gen-coll3 (dec d)))
    8 (list 'if (list (pick '[empty? seq]) (gen-coll3 (dec d))) (gen-any3 (dec d)) (gen-any3 (dec d)))
    9 (list 'let ['x (gen-int3 (dec d)) 'c (gen-coll3 (dec d))] (list (pick '[conj cons]) 'x 'c))))

(defn- outcome
  "Clojure's outcome for a form: [:value v], [:throws class-name] or [:skip why]. A lazy result
   is realized (printed) inside the guarded evaluation, as the jank side's `ev` does."
  [form]
  (let [run (fn [] (let [f (future (try (let [v (eval form)] (pr-str v) [:value v])
                                        (catch Throwable e [:throws (.getName (class e))])))
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
                ;; Short, so that a test's mismatches (jank's values) fit an event's details.
                (> (count printed) 300) [:skip "large"]
                (fn? v) [:skip "a fn"]
                (not (try (= v (read-string printed)) (catch Throwable _ false))) [:skip "no read-back"]
                :else a)))))

(defn- case-row
  "A case as the jank file holds it: [code :value v] or [code :throws class-name]."
  [{:keys [form outcome]}]
  [(pr-str form) (if (= :value (first outcome)) :value :throws) (second outcome)])

(def ^:private preamble
  (str "(defn- ev\n"
       "  \"The form's value, realized, or [:jank-gen/threw what] for any throw jank's handlers can\n"
       "   see (an object, a native exception or a jank::error_ref): every form gets its own\n"
       "   verdict. An object's message only: printing an ex-info makes jank crash as it exits\n"
       "   (jankifier's S1). A thrown string is its own message: ex-message of one throws in jank\n"
       "   (jankifier's LU62), which ended the test with no verdict (an overflowing inc throws one).\"\n"
       "  [s]\n"
       "  (try (let [v (eval (read-string s))] (pr-str v) v)\n"
       "       (catch cpp/jank.runtime.object_ref e [:jank-gen/threw (if (string? e) e (ex-message e))])\n"
       "       (catch cpp/std.exception e [:jank-gen/threw (str (.what e))])\n"
       "       (catch cpp/jank.error_ref e [:jank-gen/threw (str (.-message (cpp/* e)))])))\n\n"
       "(defn- threw? [v] (and (vector? v) (= :jank-gen/threw (first v))))\n\n"
       "(defn- mismatches\n"
       "  \"The cases jank answers differently from Clojure, as {:i index :jank outcome}: one\n"
       "   assertion a test, so that its failure (the runner reports a test's first) names them all.\"\n"
       "  [cases]\n"
       "  (vec (remove nil? (map-indexed (fn [i [code kind v]]\n"
       "                                   (let [got (ev code)\n"
       "                                         same (try (if (= kind :throws) (threw? got) (= v got))\n"
       "                                                   (catch cpp/jank.runtime.object_ref _ false))]\n"
       "                                     (when-not same {:i i :jank got})))\n"
       "                                 cases))))\n\n"))

(defn- write-namespace!
  "A jank test namespace: one deftest per [test-name rows], each one assertion over its rows."
  [file ns-name header tests]
  (io/make-parents file)
  (spit file
        (str ";; SPDX-License-Identifier: MIT\n" header
             "(ns " ns-name "\n  (:require [clojure.test :refer [deftest is]]\n            [clojure.string]))\n\n"
             preamble
             (string/join "\n\n"
                          (for [[test-name rows] tests]
                            (str "(deftest " test-name "\n  (let [found (mismatches (quote [\n"
                                 (string/join "\n" (map #(str "      " (binding [*print-meta* false] (pr-str %))) rows))
                                 "]))]\n    (is (= [] found))))")))
             "\n")))

(defn- generate [seed n out]
  (let [forms (binding [*rng* (java.util.Random. seed)]
                (loop [kept [] tries 0]
                  (if (or (>= (count kept) n) (> tries (* 20 n)))
                    kept
                    (let [form (if (>= *grammar* 3) (gen-any3 4) (gen-any 4))
                          ;; A bare literal tests only the reader: forms with a call at least.
                          o (if (some seq? (tree-seq coll? seq form)) (outcome form) [:skip "no call"])]
                      (recur (if (= :skip (first o)) kept (conj kept {:form form :outcome o})) (inc tries))))))
        tests (map-indexed (fn [i group] [(format "g%04d" i) (mapv case-row group)]) (partition-all 10 forms))
        file (io/file out "tests" "jank_gen" (str "gen_" seed "_test.jank"))]
    (write-namespace! file (str "jank-gen.gen-" seed "-test")
                      (str ";; Generated by workloads/jank-interop/gen/gen.clj, seed " seed ": each case's expected\n"
                           ";; outcome is Clojure 1.12's for a random form, so a mismatch on jank is a deviation.\n")
                      tests)
    (spit (io/file out "results" (str "gen-" seed "-forms.edn"))
          (with-out-str (doseq [[i f] (map-indexed vector forms)]
                          (prn (assoc f :test (format "g%04d" (quot i 10)) :i (mod i 10))))))
    (println (count forms) "forms," (count tests) "tests, in" (str file))))

;; The run's failures: a JSON object {"<ns>::<test>": "<what the runner said>"} (serve's SQL over the
;; run's assert events, as README says). A said text holding "actual: (not (= [] [...]))" names
;; the mismatches; any other (a crash, a hang) leaves all of that test's cases suspect.
(defn- read-failures [file]
  (into {}
        (for [[k said] (json/read-str (slurp file))]
          (let [test-name (last (string/split k #"::|/"))
                at (string/index-of said "actual: (not (= [] ")
                found (when at
                        (try (read-string (subs said (+ at (count "actual: (not (= [] "))))
                             (catch Throwable _ nil)))]
            [test-name (if (vector? found) found :unknown)]))))

(defn- subforms
  "Every list or vector inside a form (itself included) that stands alone: no `x` free of its let
   or fn, no fn form itself (its value, a fn, is never compared)."
  [form]
  (let [binds? #(and (seq? %) (#{'let 'fn} (first %)))
        free-x? (fn free-x? [f] (cond (= f 'x) true
                                      (binds? f) false
                                      (coll? f) (some free-x? f)
                                      :else false))
        all (tree-seq #(and (coll? %) (not (map? %)) (not (and (seq? %) (= 'fn (first %))))) seq form)]
    (distinct (filter #(and (or (seq? %) (vector? %)) (not (and (seq? %) (= 'fn (first %)))) (not (free-x? %))
                            (some seq? (tree-seq coll? seq %)))
                      all))))

(defn- shrink
  "Each suspect form's subforms, Clojure's outcome for each, as a test namespace of their own: the
   smallest one jank still answers wrongly is the deviation's minimal case."
  [seed failures-file out]
  (let [forms (map read-string (string/split-lines (slurp (io/file out "results" (str "gen-" seed "-forms.edn")))))
        failures (read-failures failures-file)
        suspect (filter (fn [{:keys [test i]}]
                          (let [f (get failures test)]
                            (or (= f :unknown) (some #(= i (:i %)) f))))
                        forms)
        tests (for [{:keys [test i form]} suspect]
                [(str "s" (subs test 1) "-" i)
                 (vec (for [sub (subforms form)
                            :let [o (outcome sub)]
                            :when (not= :skip (first o))]
                        (case-row {:form sub :outcome o})))])
        file (io/file out "tests" "jank_gen" (str "shrink_" seed "_test.jank"))]
    (write-namespace! file (str "jank-gen.shrink-" seed "-test")
                      (str ";; Generated by workloads/jank-interop/gen/gen.clj from seed " seed "'s failures: each\n"
                           ";; suspect form's subforms, so the smallest one jank answers wrongly is its minimal case.\n")
                      tests)
    (spit (io/file out "results" (str "shrink-" seed "-cases.edn"))
          (with-out-str (doseq [[t rows] tests] (prn [t rows]))))
    (println (count suspect) "suspect forms," (reduce + (map (comp count second) tests)) "subform cases, in" (str file))))

(defn- contains-form? [outer inner]
  (and (not= outer inner) (some #(= inner %) (tree-seq coll? seq outer))))

(defn- group
  "The shrink run's verdicts grouped by signature: a minimal failing subform (no failing subform
   inside it), its head and how jank differs. Writes results/gen-<seed>-groups.md."
  [seed failures-file out]
  (let [cases (map read-string (string/split-lines (slurp (io/file out "results" (str "shrink-" seed "-cases.edn")))))
        failures (read-failures failures-file)
        rows (for [[t tcases] cases
                   :let [f (get failures t)
                         failed (cond (nil? f) {}
                                      ;; Each suspect form ran in a process of its own: a crash or a
                                      ;; hang is the whole form's (case 0, the form itself).
                                      (= f :unknown) {0 :unknown}
                                      :else (into {} (map (juxt :i :jank) f)))
                         bad (for [[i jank] failed] (let [[code kind v] (nth tcases i)] {:form (read-string code) :code code :kind kind :clojure v :jank jank}))]
                   b bad
                   :when (not-any? #(contains-form? (:form b) (:form %)) bad)]
               (assoc b :test t))
        kind-of (fn [{:keys [kind jank]}]
                  (cond (= jank :unknown) "no verdict (crash or hang)"
                        (and (= kind :value) (vector? jank) (= :jank-gen/threw (first jank))) "jank throws, Clojure returns"
                        (= kind :throws) "jank returns, Clojure throws"
                        :else "jank returns another value"))
        sig (fn [r] [(let [f (:form r)] (if (seq? f) (str (first f)) "vector")) (kind-of r)])
        groups (sort-by (comp - count val) (group-by sig (distinct rows)))
        file (io/file out "results" (str "gen-" seed "-groups.md"))]
    (spit file
          (str "# Seed " seed ": deviations by signature\n\n"
               (string/join "\n"
                            (for [[[head kind] rs] groups
                                  :let [r (first (sort-by (comp count :code) rs))]]
                              (str "## `" head "`: " kind " (" (count rs) ")\n\n```clojure\n" (:code r)
                                   "\n;; Clojure: " (pr-str (:clojure r)) "\n;; jank:    " (pr-str (:jank r)) "\n```\n")))))
    (println (count groups) "signatures from" (count rows) "minimal cases, in" (str file))))

(defn -main [& [mode & args]]
  ;; Maps printed whole, never as #:ns{...}: clojure.main prints namespaced maps so, and jank's
  ;; reader refuses that syntax (jankifier's R17, known), which failed every test of a namespace
  ;; holding one expected value of it (seed 2, 2026-11-26).
  (binding [*print-namespace-maps* false]
  (case mode
    "gen" (let [[seed n] args
                seed (Long/parseLong seed)]
            ;; Seeds 1 and 2 were drawn by grammar 1, seed 3 by grammar 2: kept so, the same seed the
            ;; same files; seeds 4 on, grammar 3.
            (binding [*grammar* (cond (<= seed 2) 1 (= seed 3) 2 :else 3)]
              (generate seed (Long/parseLong n) ".")))
    "shrink" (let [[seed failures] args] (shrink (Long/parseLong seed) failures "."))
    "group" (let [[seed failures] args] (group (Long/parseLong seed) failures "."))
    (println "clojure -M gen.clj gen <seed> <forms> | shrink <seed> <failures.json> | group <seed> <failures.json>")))
  (shutdown-agents))

(apply -main *command-line-args*)
