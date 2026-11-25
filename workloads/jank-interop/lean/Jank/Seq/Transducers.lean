import Determinismo

/-!
# Transducers: core.jank's stateful transducers, `transduce`, `reduce`, beside Clojure's

Each transducer below is the jank code of core.jank (its 1-arity `[rf]` closure), its state the
`volatile!`s it allocates; Clojure's is core.clj's (an `ArrayList` where jank uses a volatile
vector). They differ in one place: `partition-by` (core.jank 3291). Clojure clears its buffer
before calling `rf` with a finished partition and adds the new input only when `rf` did not stop
the reduction; jank resets its buffer only when `rf` did not stop it, so after an early stop the
finished partition is still buffered and the completion arity sends it to `rf` again.

`transduce` (core.jank 1156): `(let [f (xform rf) ret (reduce f init coll)] (f ret))`;
`reduce` with init → seq.cpp:908 (stops at a `reduced`, unwrapping it once).
-/

namespace Jank.Seq.Transducers

open Determinismo

/-- A value: an integer or a vector (a partition). -/
inductive TV where
  | int (i : Int)
  | vec (xs : List TV)
  deriving Repr, Inhabited

mutual
/-- Value equality (`=` on integers and vectors), structural so that the kernel evaluates it. -/
def TV.eqb : TV → TV → Bool
  | .int a, .int b => a == b
  | .vec xs, .vec ys => TV.eqbL xs ys
  | _, _ => false
def TV.eqbL : List TV → List TV → Bool
  | [], [] => true
  | x :: xs, y :: ys => TV.eqb x y && TV.eqbL xs ys
  | _, _ => false
end

instance : BEq TV := ⟨TV.eqb⟩

partial def TV.code : TV → String
  | .int i => toString i
  | .vec xs => "[" ++ " ".intercalate (xs.map TV.code) ++ "]"

/-- A reduction's value: the accumulated vector, wrapped in `reduced` `red` times. -/
structure R where
  acc : List TV
  red : Nat := 0
  deriving Repr

instance : BEq R := ⟨fun a b => TV.eqbL a.acc b.acc && a.red == b.red⟩

def isReduced (r : R) : Bool := r.red > 0
/-- `(reduced x)`. -/
def reduced (r : R) : R := { r with red := r.red + 1 }
/-- `(deref r)` of a reduced. -/
def deref (r : R) : R := { r with red := r.red - 1 }
/-- core.jank 1112 `ensure-reduced`. -/
def ensureReduced (r : R) : R := if isReduced r then r else reduced r
/-- core.jank 1119 `unreduced`. -/
def unreduced (r : R) : R := if isReduced r then deref r else r

inductive Impl where
  | jank | clj
  deriving Repr, BEq

/-- The transducers drawn, with fixed functions: `inc`, `odd?`, `#(< % 2)`, ... -/
inductive XF where
  | map | filter | take (n : Int) | drop (n : Int) | takeWhile | dropWhile | takeNth (n : Int)
  | partitionAll (n : Nat) | partitionBy | dedupe | distinct | keep | mapIndexed | interpose | cat
  deriving Repr, BEq, Inhabited

def XF.code : XF → String
  | .map => "(map inc)" | .filter => "(filter odd?)" | .take n => s!"(take {n})"
  | .drop n => s!"(drop {n})" | .takeWhile => "(take-while #(< % 2))"
  | .dropWhile => "(drop-while #(< % 1))" | .takeNth n => s!"(take-nth {n})"
  | .partitionAll n => s!"(partition-all {n})" | .partitionBy => "(partition-by odd?)"
  | .dedupe => "(dedupe)" | .distinct => "(distinct)" | .keep => "(keep #(when (odd? %) (* 10 %)))"
  | .mapIndexed => "(map-indexed #(+ (* 10 %1) %2))" | .interpose => "(interpose 9)" | .cat => "cat"

/-- A transducer's volatiles: a counter (`nv`, `iv`, `i`), a buffer (`part`, `vv`), a previous
value (`pv`; none: `::none`), a flag (`dv`, `started`), a seen set. -/
structure XS where
  n : Int := 0
  buf : List TV := []
  prev : Option TV := none
  flag : Bool := false
  seen : List TV := []
  deriving Repr, Inhabited

def XF.init : XF → XS
  | .take n | .drop n => { n }
  | .takeNth _ | .mapIndexed => { n := -1 }
  | .dropWhile => { flag := true }
  | _ => {}

def ival : TV → Int
  | .int i => i
  | _ => 0

def odd (v : TV) : Bool := ival v % 2 != 0

/-- A number for `inc`, `odd?`, `<`, `*`: a vector there throws (as in both). -/
def num : TV → Except String Int
  | .int i => .ok i
  | .vec _ => .error "a vector where a number is required"

/-- The reducing function at the end: `conj` onto a vector, returning `(reduced acc)` once it
holds `stop` items (a reducing function that stops early). -/
structure Rf where
  stop : Option Nat
  deriving Repr

def Rf.step (rf : Rf) (r : R) (x : TV) : R :=
  let acc := r.acc ++ [x]
  match rf.stop with
  | some k => if acc.length ≥ k then reduced { acc } else { acc }
  | none => { acc }

mutual
/-- The 2-arity `([result input] ...)` of the pipeline `xfs` (outermost first). -/
def step (impl : Impl) (rf : Rf) : Nat → List XF → List XS → R → TV → Except String (List XS × R)
  | 0, _, _, _, _ => .error "fuel"
  | _ + 1, [], _, r, x => .ok ([], rf.step r x)
  | f + 1, xf :: rest, st :: sts, r, x => do
    let down := fun (sts : List XS) (r : R) (x : TV) => step impl rf f rest sts r x
    match xf with
    -- core.jank 2892 map: `(rf result (f input))`
    | .map => let i ← num x; let (s', r) ← down sts r (.int (i + 1)); pure (st :: s', r)
    -- core.jank 3864 filter
    | .filter => let _ ← num x; if odd x then do let (s', r) ← down sts r x; pure (st :: s', r) else pure (st :: sts, r)
    -- core.jank 3050 take: n = @nv, nn = (vswap! nv dec); result = (if (pos? n) (rf result input) result);
    -- (if (not (pos? nn)) (ensure-reduced result) result)
    | .take _ =>
      let n := st.n
      let nn := n - 1
      let st := { st with n := nn }
      let (s', r) ← if n > 0 then down sts r x else pure (sts, r)
      pure (st :: s', if !(nn > 0) then ensureReduced r else r)
    -- core.jank 3101 drop: n = @nv; (vswap! nv dec); (if (pos? n) result (rf result input))
    | .drop _ =>
      let n := st.n
      let st := { st with n := n - 1 }
      if n > 0 then pure (st :: sts, r) else do let (s', r) ← down sts r x; pure (st :: s', r)
    -- core.jank 3082 take-while: (if (pred input) (rf result input) (reduced result))
    | .takeWhile => let i ← num x; if i < 2 then do let (s', r) ← down sts r x; pure (st :: s', r)
                    else pure (st :: sts, reduced r)
    -- core.jank 3129 drop-while: drop? = @dv; (if (and drop? (pred input)) result (do (vreset! dv nil) (rf result input)))
    | .dropWhile => let i ← num x; if st.flag && i < 1 then pure (st :: sts, r)
                    else do let (s', r) ← down sts r x; pure ({ st with flag := false } :: s', r)
    -- core.jank 2870 take-nth: i = (vswap! iv inc); (if (zero? (rem i n)) (rf result input) result)
    | .takeNth n =>
      let i := st.n + 1
      let st := { st with n := i }
      if n == 0 then throw "UB: (rem i 0)"
      if i.tmod n == 0 then do let (s', r) ← down sts r x; pure (st :: s', r) else pure (st :: sts, r)
    -- core.jank 3277 partition-all: p = (vswap! part conj input); (if (= n (count p)) (do (vreset! part []) (rf result p)) result)
    -- Clojure: (.add a input) (if (= n (.size a)) (let [v (vec a)] (.clear a) (rf result v)) result): the same
    | .partitionAll n =>
      let p := st.buf ++ [x]
      if p.length == n then do let (s', r) ← down sts r (.vec p); pure ({ st with buf := [] } :: s', r)
      else pure ({ st with buf := p } :: sts, r)
    | .partitionBy =>
      let _ ← num x
      let pval := st.prev
      let val := TV.int (if odd x then 1 else 0)
      let st := { st with prev := some val }
      if pval.isNone || pval == some val then pure ({ st with buf := st.buf ++ [x] } :: sts, r)
      else
        let v := st.buf
        match impl with
        | .jank => do
          -- core.jank 3313: ret = (rf result v); (when-not (reduced? ret) (vreset! vv [input])); ret
          let (s', ret) ← down sts r (.vec v)
          pure ((if isReduced ret then st else { st with buf := [x] }) :: s', ret)
        | .clj => do
          -- core.clj 7337: (.clear a); ret = (rf result v); (when-not (reduced? ret) (.add a input)); ret
          let st := { st with buf := [] }
          let (s', ret) ← down sts r (.vec v)
          pure ((if isReduced ret then st else { st with buf := [x] }) :: s', ret)
    -- core.jank 3917 dedupe: prior = @pv; (vreset! pv input); (if (= prior input) result (rf result input))
    | .dedupe =>
      let prior := st.prev
      let st := { st with prev := some x }
      if prior == some x then pure (st :: sts, r) else do let (s', r) ← down sts r x; pure (st :: s', r)
    -- core.jank 3830 distinct
    | .distinct =>
      if st.seen.contains x then pure (st :: sts, r)
      else do let (s', r) ← down sts r x; pure ({ st with seen := st.seen ++ [x] } :: s', r)
    -- core.jank 2985 keep: v = (f input); (if (nil? v) result (rf result v))
    | .keep => let _ ← num x; if odd x then do let (s', r) ← down sts r (.int (ival x * 10)); pure (st :: s', r)
               else pure (st :: sts, r)
    -- core.jank 2958 map-indexed: (rf result (f (vswap! i inc) input))
    | .mapIndexed =>
      let _ ← num x
      let i := st.n + 1
      let (s', r) ← down sts r (.int (10 * i + ival x))
      pure ({ st with n := i } :: s', r)
    -- core.jank 3195 interpose: started? (let [sepr (rf result sep)] (if (reduced? sepr) sepr (rf sepr input)))
    | .interpose =>
      if st.flag then do
        let (s1, sepr) ← down sts r (.int 9)
        if isReduced sepr then pure (st :: s1, sepr)
        else do let (s2, r) ← down s1 sepr x; pure (st :: s2, r)
      else do let (s', r) ← down sts r x; pure ({ st with flag := true } :: s', r)
    -- core.jank 1180 cat: (reduce (preserving-reduced rf) result input)
    | .cat => match x with
      | .vec ys => do
        let (s', r) ← reduceVia impl rf f rest sts r ys
        pure (st :: s', r)
      | .int _ => throw "cat of a number: not seqable"
  | _ + 1, _ :: _, [], _, _ => .error "state"

/-- seq.cpp:908 `reduce` over a vector with `(preserving-reduced rf)` (core.jank 1173): a
`reduced` from rf is wrapped again; reduce stops and unwraps one layer. -/
def reduceVia (impl : Impl) (rf : Rf) : Nat → List XF → List XS → R → List TV → Except String (List XS × R)
  | 0, _, _, _, _ => .error "fuel"
  | _ + 1, _, sts, r, [] => .ok (sts, r)
  | f + 1, xfs, sts, r, y :: ys => do
    let (sts, ret) ← step impl rf f xfs sts r y
    let ret := if isReduced ret then reduced ret else ret
    if isReduced ret then pure (sts, deref ret) else reduceVia impl rf f xfs sts ret ys
end

/-- The completion arity `([result] ...)`. -/
def complete (impl : Impl) (rf : Rf) : List XF → List XS → R → Except String R
  | [], _, r => .ok r
  | xf :: rest, st :: sts, r => do
    match xf with
    -- core.jank 3270: p = @part; result = (if (empty? p) result (unreduced (rf result p))); (rf result)
    | .partitionAll _ =>
      if st.buf.isEmpty then complete impl rf rest sts r
      else do
        let (sts, r') ← step impl rf 64 rest sts r (.vec st.buf)
        complete impl rf rest sts (unreduced r')
    -- core.jank 3303 (jank) / core.clj 7320 (Clojure): the buffer, when not empty, sent to rf
    | .partitionBy =>
      if st.buf.isEmpty then complete impl rf rest sts r
      else do
        let (sts, r') ← step impl rf 64 rest sts r (.vec st.buf)
        complete impl rf rest sts (unreduced r')
    | _ => complete impl rf rest sts r
  | _ :: _, [], _ => .error "state"

/-- core.jank 1156 `transduce` with init `[]`: `(reduce f init coll)` (seq.cpp:908: stop at a
`reduced`, unwrap it), then `(f ret)`. -/
def transduce (impl : Impl) (rf : Rf) (xfs : List XF) (coll : List TV) : Except String (List TV) := do
  let rec go : List XS → R → List TV → Except String (List XS × R)
    | sts, r, [] => .ok (sts, r)
    | sts, r, x :: xs => do
      let (sts, r) ← step impl rf 64 xfs sts r x
      if isReduced r then pure (sts, deref r) else go sts r xs
  let (sts, r) ← go (xfs.map XF.init) {acc := []} coll
  let r ← complete impl rf xfs sts r
  pure (unreduced r).acc

/-! ## The world: a pipeline, an input, a reducing function drawn -/

structure World where
  decisions : Decisions := {}

instance : Chaotic World where
  decisions w := w.decisions
  setDecisions w d := { w with decisions := d }

def xforms : List XF :=
  [.map, .filter, .take 2, .drop 1, .takeWhile, .dropWhile, .takeNth 2, .partitionAll 2,
   .partitionBy, .dedupe, .distinct, .keep, .mapIndexed, .interpose, .cat]

structure Question where
  xfs : List XF
  coll : List Int
  stop : Option Nat
  deriving Repr

def Question.program (q : Question) : String :=
  let xf := match q.xfs with
    | [x] => x.code
    | xs => "(comp " ++ " ".intercalate (xs.map XF.code) ++ ")"
  let rf := match q.stop with
    | none => "conj"
    | some k => s!"(fn ([acc] acc) ([acc x] (let [a (conj acc x)] (if (>= (count a) {k}) (reduced a) a))))"
  s!"(transduce {xf} {rf} [] {q.coll})"

def showRes (e : Except String (List TV)) : String :=
  match e with
  | .ok xs => "[" ++ " ".intercalate (xs.map TV.code) ++ "]"
  | .error m => s!"throws ({m})"

def Question.verdict (q : Question) : Option String :=
  let coll := q.coll.map TV.int
  let j := transduce .jank ⟨q.stop⟩ q.xfs coll
  let c := transduce .clj ⟨q.stop⟩ q.xfs coll
  let same := match j, c with
    | .ok a, .ok b => TV.eqbL a b
    | .error _, .error _ => true
    | _, _ => false
  if same then none else some s!"{q.program}: Clojure {showRes c}, jank {showRes j}"

def drawQuestion : EStateM Stop World Question := do
  let k := (← decide (σ := World) "xf.count" 2) + 1
  let mut xfs := []
  for i in List.range k do
    xfs := xfs ++ [(← pick (σ := World) s!"xf.{i}" xforms).getD .map]
  let len ← decide (σ := World) "coll.length" 5
  let mut coll := []
  for i in List.range len do
    coll := coll ++ [Int.ofNat (← decide (σ := World) s!"coll.{i}" 3)]
  let stop ← decide (σ := World) "rf.stop" 3
  return { xfs, coll, stop := if stop == 0 then none else some stop }

def body : EStateM Stop World Unit := do
  let q ← drawQuestion
  if let some d := q.verdict then violate (σ := World) "transduce agrees with Clojure" d

def run (source : Source) : Ended :=
  match body.run { decisions := { source } } with
  | .ok _ w => { taken := w.decisions.taken, violation := none }
  | .error (.violation p d) w => { taken := w.decisions.taken, violation := some (p, d) }
  | .error .limit w => { taken := w.decisions.taken, violation := none }
  | .error (.nodeDown _) w => { taken := w.decisions.taken, violation := none }

/-- `(transduce (partition-by odd?) rf [] [1 2])` with an rf that stops after one item: Clojure
`[[1]]`; jank `[[1] [1]]`. -/
theorem partition_by_sends_twice :
    transduce .jank ⟨some 1⟩ [.partitionBy] [.int 1, .int 2] = .ok [.vec [.int 1], .vec [.int 1]] ∧
    transduce .clj ⟨some 1⟩ [.partitionBy] [.int 1, .int 2] = .ok [.vec [.int 1]] := by
  constructor <;> rfl

end Jank.Seq.Transducers
