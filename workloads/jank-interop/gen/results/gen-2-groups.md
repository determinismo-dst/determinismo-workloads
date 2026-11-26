# Seed 2: deviations by signature

## `subs`: jank returns another value (3)

```clojure
(subs "é-è" 2)
;; Clojure: "è"
;; jank:    "-è"
```

## `let`: jank returns, Clojure throws (3)

```clojure
(let [x 9223372036854775807] (* x 128))
;; Clojure: "java.lang.ArithmeticException"
;; jank:    -128
```

## `*`: jank returns, Clojure throws (2)

```clojure
(* 9223372036854775807 10)
;; Clojure: "java.lang.ArithmeticException"
;; jank:    -10
```

## `str`: jank returns another value (2)

```clojure
(str (interleave [] []) (clojure.string/trim " t "))
;; Clojure: "clojure.lang.LazySeq@1t"
;; jank:    "()t"
```

## `-`: jank returns, Clojure throws (1)

```clojure
(- -9223372036854775808 1)
;; Clojure: "java.lang.ArithmeticException"
;; jank:    -9223372036854775809N
```

## `clojure.string/join`: jank returns another value (1)

```clojure
(clojure.string/join "," (partition-all 1 (conj [1 2 3] 7)))
;; Clojure: "clojure.lang.LazySeq@20,clojure.lang.LazySeq@21,clojure.lang.LazySeq@22,clojure.lang.LazySeq@26"
;; jank:    "(1),(2),(3),(7)"
```

## `sort-by`: jank returns, Clojure throws (1)

```clojure
(sort-by - [(nth (vector -128 -9223372036854775808) 1) 3 (compare -1 127)])
;; Clojure: "java.lang.ArithmeticException"
;; jank:    (3 -1 -9223372036854775808N)
```

## `dec`: jank returns, Clojure throws (1)

```clojure
(dec -9223372036854775808)
;; Clojure: "java.lang.ArithmeticException"
;; jank:    -9223372036854775809N
```
