# Seed 1: deviations by signature

## `let`: jank returns, Clojure throws (6)

```clojure
(let [x -9223372036854775808] (* x -1))
;; Clojure: "java.lang.ArithmeticException"
;; jank:    9223372036854775808N
```

## `*`: jank returns, Clojure throws (5)

```clojure
(* -3 9223372036854775807)
;; Clojure: "java.lang.ArithmeticException"
;; jank:    -9223372036854775805
```

## `max`: jank returns another value (4)

```clojure
(max (max (count [0 1 2 3 4]) 127) -1)
;; Clojure: 127
;; jank:    -1
```

## `let`: jank returns another value (3)

```clojure
(let [x -1] (max x (count (subs "abcdef" 0))))
;; Clojure: 6
;; jank:    -1
```

## `subs`: jank returns another value (2)

```clojure
(subs "é-è" 2)
;; Clojure: "è"
;; jank:    "-è"
```

## `count`: jank returns another value (2)

```clojure
(count "é")
;; Clojure: 1
;; jank:    2
```

## `sort-by`: jank throws, Clojure returns (1)

```clojure
(sort-by identity (mapv keyword? [1 2 3]))
;; Clojure: (false false false)
;; jank:    [:jank-gen/threw "Objects of type `boolean` are not comparable to `boolean`."]
```

## `str`: jank returns another value (1)

```clojure
(str 127 (map dec [1 1 1]))
;; Clojure: "127clojure.lang.LazySeq@745f"
;; jank:    "127(0 0 0)"
```

## `dec`: jank returns, Clojure throws (1)

```clojure
(dec -9223372036854775808)
;; Clojure: "java.lang.ArithmeticException"
;; jank:    -9223372036854775809N
```

## `-`: jank returns, Clojure throws (1)

```clojure
(- -9223372036854775808 128)
;; Clojure: "java.lang.ArithmeticException"
;; jank:    -9223372036854775936N
```
