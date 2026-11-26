# Seed 3: deviations by signature

## `unchecked-multiply`: jank throws, Clojure returns (10)

```clojure
(unchecked-multiply 10 10)
;; Clojure: 100
;; jank:    [:jank-gen/threw "TODO: port unchecked-multiply"]
```

## `count`: jank returns another value (8)

```clojure
(count "é")
;; Clojure: 1
;; jank:    2
```

## `unchecked-subtract`: jank throws, Clojure returns (6)

```clojure
(unchecked-subtract 0 3)
;; Clojure: -3
;; jank:    [:jank-gen/threw "TODO: port unchecked-subtract"]
```

## `unchecked-add`: jank throws, Clojure returns (6)

```clojure
(unchecked-add -1 256)
;; Clojure: 255
;; jank:    [:jank-gen/threw "TODO: port unchecked-add"]
```

## `subs`: jank returns another value (5)

```clojure
(subs "é-è" 2)
;; Clojure: "è"
;; jank:    "-è"
```

## `let`: jank returns, Clojure throws (5)

```clojure
(let [x 3] (+ x 9223372036854775807))
;; Clojure: "java.lang.ArithmeticException"
;; jank:    -9223372036854775806
```

## `get`: jank returns another value (4)

```clojure
(get "😀" 2)
;; Clojure: nil
;; jank:    \�
```

## `subs`: jank returns, Clojure throws (4)

```clojure
(subs "ü" 0 2)
;; Clojure: "java.lang.StringIndexOutOfBoundsException"
;; jank:    "ü"
```

## `/`: jank returns another value (3)

```clojure
(/ (count [0 1 2 3 4]) 3)
;; Clojure: 5/3
;; jank:    1
```

## `unchecked-dec`: jank throws, Clojure returns (3)

```clojure
(unchecked-dec 255)
;; Clojure: 254
;; jank:    [:jank-gen/threw "TODO: port unchecked-dec"]
```

## `compare`: jank returns another value (3)

```clojure
(compare "日本語" "")
;; Clojure: 3
;; jank:    9
```

## `+`: jank returns, Clojure throws (2)

```clojure
(+ 1000 (dec 9223372036854775807))
;; Clojure: "java.lang.ArithmeticException"
;; jank:    -9223372036854774810
```

## `*`: jank returns, Clojure throws (2)

```clojure
(* -128 9223372036854775807)
;; Clojure: "java.lang.ArithmeticException"
;; jank:    128
```

## `nth`: jank returns another value (2)

```clojure
(nth "ü" 0)
;; Clojure: \ü
;; jank:    \�
```

## `quot`: jank returns another value (2)

```clojure
(quot 7.5 -2)
;; Clojure: -3.0
;; jank:    -3
```

## `abs`: jank returns another value (1)

```clojure
(abs -9223372036854775808)
;; Clojure: -9223372036854775808
;; jank:    9223372036854775808N
```

## `unchecked-negate`: jank throws, Clojure returns (1)

```clojure
(unchecked-negate -128)
;; Clojure: 128
;; jank:    [:jank-gen/threw "TODO: port unchecked-negate"]
```

## `into`: jank returns another value (1)

```clojure
(into #{} (concat (conj (mapv str []) (bit-shift-left -9223372036854775808 64)) (sort-by str (keys (group-by even? (list 1 2))))))
;; Clojure: #{-9223372036854775808 true false}
;; jank:    #{-9223372036854775808 true false}
```

## `max`: jank returns another value (1)

```clojure
(max -0.0 0)
;; Clojure: 0
;; jank:    -0.0
```

## `sort-by`: jank returns, Clojure throws (1)

```clojure
(sort-by - [-9223372036854775808 1])
;; Clojure: "java.lang.ArithmeticException"
;; jank:    (1 -9223372036854775808N)
```

## `clojure.string/join`: jank returns another value (1)

```clojure
(clojure.string/join "-" (interleave (conj (take 1 [0 1 2 3 4]) 128) (partition-all 1 (concat [1 1 1] [0 -1 7 7]))))
;; Clojure: "128-clojure.lang.LazySeq@20-0-clojure.lang.LazySeq@20"
;; jank:    "128-(1)-0-(1)"
```

## `rest`: jank returns another value (1)

```clojure
(rest "😀")
;; Clojure: (\?)
;; jank:    ()
```

## `pr-str`: jank returns another value (1)

```clojure
(pr-str 1.0E-5)
;; Clojure: "1.0E-5"
;; jank:    "1e-05"
```

## `let`: no verdict (crash or hang) (1)

```clojure
(let [x (count (apply str (reverse "a😀b")))] (max x (min (first (vector (- 3 1000))) 1)))
;; Clojure: 4
;; jank:    :unknown
```
