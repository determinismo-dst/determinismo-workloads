import Jank.R3.Search.Common
import Jank.Analyzer.Search

open Jank.R3.Search (mixSeed)

/-!
# Round 3: the analyzer's programs, widened

Round 2's grammar (`Jank.Analyzer.genExpr`) bounded programs by depth. Its tiny grammar at depth 2
has about 4·10^16 programs (`counts` below, checked against `estimate`), so `exhaust` stopping at
1.5 M was not a partial run of a completable world. This module replaces the bound:

- `Grammar.budget`: at most `budget` compound forms in the whole program (`depth` still caps the
  nesting). Budget 1 is round 2's depth 1; budget 2 is every depth-2 program with one compound
  child, every program with two compound forms side by side, and so on. Each program has one
  decision path, so `exhaust` over a budget is a complete enumeration.
- New forms the replica models but round 2 never drew: `and`/`or` (macros), two-binding
  `let*`, `letfn*`, variadic `fn*`, vector/map/set literals with computed elements, `try` without
  `catch`, `(do (def name e) name)`, the non-star macros `let`/`loop`/`fn`, and the calls `<`,
  `*`, `pos?`, `nil?`, `count`, `first`, `rest`, `str`, `list`.
- Kinds are named, so a world enables a subset; `innerKinds` restricts the forms under the top.

The property is round 2's (`Outcome.agrees` of the replica's jank run and the Clojure spec), with
each run's analyzer-path tags; a world sets tags aside (`known`).
-/

namespace Jank.R3.Search.Analyzer

open Determinismo Jank.Analyzer

structure GW where
  decisions : Decisions := {}
  budget : Nat := 0

instance : Chaotic GW where
  decisions w := w.decisions
  setDecisions w d := { w with decisions := d }

abbrev GM := EStateM Stop GW

def choose (name : String) (n : Nat) : GM Nat := decide (σ := GW) name n

/-- A world's grammar. -/
structure Grammar where
  lits : List Obj := literals
  names : List String := namePool
  /-- Compound kinds allowed at the top. -/
  kinds : List String
  /-- Compound kinds allowed below the top (default: `kinds`). -/
  innerKinds : Option (List String) := none
  /-- Compound forms in the whole program, at most. -/
  budget : Nat := 1
  /-- Nesting, at most. -/
  depth : Nat := 2
  /-- Leaves may be a second literal option (round 2's `gen.literal2`, kept for comparison). -/
  doubleLiteral : Bool := false

def roundTwoKinds : List String :=
  ["if", "do", "let", "loop", "fn", "macro", "private", "call", "quote", "case"]

def newKinds : List String :=
  ["and", "or", "let2", "letfn", "variadic", "vec", "map", "set", "try", "def", "let-m", "loop-m",
   "fn-m", "call2", "multi", "var"]

def allKinds : List String := roundTwoKinds ++ newKinds

def leafGen (g : Grammar) (scope : List String) : GM Obj := do
  let lits := g.lits.length
  let nOpts := (if g.doubleLiteral then 2 * lits else lits) + scope.length
  let k ← choose "gen.leaf" nOpts
  if k < lits then pure (g.lits.getD k .nil)
  else if g.doubleLiteral && k < 2 * lits then pure (g.lits.getD (k - lits) .nil)
  else pure (S (scope.getD (k - (if g.doubleLiteral then 2 * lits else lits)) "x"))

/-- A form of nesting at most `d` with `scope` locals; `top` for the outermost form. -/
partial def gen (g : Grammar) (d : Nat) (scope : List String) (top : Bool) : GM Obj := do
  let w ← get
  let kinds := if top then g.kinds else g.innerKinds.getD g.kinds
  if d == 0 || w.budget == 0 || kinds.isEmpty then return ← leafGen g scope
  -- Option 0: a leaf; then each compound kind.
  let k ← choose "gen.kind" (kinds.length + 1)
  if k == 0 then return ← leafGen g scope
  let kind := kinds.getD (k - 1) "if"
  modify fun w => { w with budget := w.budget - 1 }
  let sub := fun (sc : List String) => gen g (d - 1) sc false
  let name := fun (label : String) => do pure (g.names.getD (← choose label g.names.length) "x")
  match kind with
  | "if" =>
    let c ← sub scope
    let t ← sub scope
    if (← choose "gen.if.else" 2) == 0 then pure (L [S "if", c, t])
    else pure (L [S "if", c, t, ← sub scope])
  | "do" => pure (L [S "do", ← sub scope, ← sub scope])
  | "let" =>
    let n ← name "gen.let.name"
    let v ← sub scope
    pure (L [S "let*", V [S n, v], ← sub (n :: scope)])
  | "let-m" =>
    let n ← name "gen.let.name"
    let v ← sub scope
    pure (L [S "let", V [S n, v], ← sub (n :: scope)])
  | "let2" =>
    let n1 ← name "gen.let.name"
    let v1 ← sub scope
    let n2 ← name "gen.let.name2"
    let v2 ← sub (n1 :: scope)
    pure (L [S "let*", V [S n1, v1, S n2, v2], ← sub (n2 :: n1 :: scope)])
  | "loop" | "loop-m" =>
    let n ← name "gen.loop.name"
    let init ← sub scope
    let next ← sub (n :: scope)
    let body ← sub (n :: scope)
    pure (L [S (if kind == "loop" then "loop*" else "loop"), V [S n, init, S "k", I 0],
      L [S "if", L [S "=", S "k", I 1], body, L [S "recur", next, I 1]]])
  | "fn" | "fn-m" =>
    let named ← choose "gen.fn.named" 2
    let fname ← name "gen.fn.name"
    let p ← name "gen.fn.param"
    let inner := if named == 1 then p :: fname :: scope else p :: scope
    let body ← sub inner
    let next ← sub inner
    let arg ← sub scope
    let head := if kind == "fn" then "fn*" else "fn"
    let fnForm := L ((S head :: (if named == 1 then [S fname] else [])) ++
      [V [S p, S "k"], L [S "if", L [S "=", S "k", I 1], body, L [S "recur", next, I 1]]])
    pure (L [fnForm, arg, I 0])
  | "variadic" =>
    -- ((fn* name? [& p] body) arg): the rest parameter holds the argument list.
    let named ← choose "gen.fn.named" 2
    let fname ← name "gen.fn.name"
    let p ← name "gen.fn.param"
    let inner := if named == 1 then p :: fname :: scope else p :: scope
    let body ← sub inner
    let arg ← sub scope
    pure (L [L ((S "fn*" :: (if named == 1 then [S fname] else [])) ++ [V [S "&", S p], body]), arg])
  | "multi" =>
    -- ((fn* name? ([p] body1) ([p q] body2)) arg) or (… arg arg2): two arities, either called.
    let named ← choose "gen.fn.named" 2
    let fname ← name "gen.fn.name"
    let p ← name "gen.fn.param"
    let inner := if named == 1 then p :: fname :: scope else p :: scope
    let body1 ← sub inner
    let body2 ← sub ("q" :: inner)
    let arg ← sub scope
    let two ← choose "gen.multi.arity" 2
    let fnForm := L ((S "fn*" :: (if named == 1 then [S fname] else [])) ++
      [L [V [S p], body1], L [V [S p, S "q"], body2]])
    pure (L ([fnForm, arg] ++ (if two == 1 then [I 7] else [])))
  | "var" =>
    match ← choose "gen.var" 3 with
    | 0 => pure (L [S "var", S "inc"])
    -- (round 2's Spec checks privacy in `var`; Clojure's `lookupVar` does not (Compiler.java
    -- 7988), nor does jank: a private var is left out rather than judged by that inexact rule)
    | 1 => pure (L [S "var", S "when"])
    | _ =>
      let n ← name "gen.def.name"
      pure (L [S "do", L [S "def", S n, ← sub scope], L [S "var", S n]])
  | "letfn" =>
    -- (letfn* [f (fn* f [p] body)] (f arg))
    let fname ← name "gen.fn.name"
    let p ← name "gen.fn.param"
    let body ← sub (p :: fname :: scope)
    let arg ← sub (fname :: scope)
    pure (L [S "letfn*", V [S fname, L [S "fn*", S fname, V [S p], body]], L [S fname, arg]])
  | "macro" =>
    match ← choose "gen.macro" 6 with
    | 0 => pure (L [S "when", ← sub scope, ← sub scope])
    | 1 => pure (L [S "form-of", ← sub scope])
    | 2 => pure (L [S "env-count"])
    | 3 => pure (L [S "meta", L [S "mk-vec", ← sub scope]])
    | 4 => pure (L [S "mk-map", K "k", ← sub scope])
    | _ => pure (L [Obj.sym "other" "secret-of"])
  | "and" => pure (L [S "and", ← sub scope, ← sub scope])
  | "or" => pure (L [S "or", ← sub scope, ← sub scope])
  | "private" => pure (Obj.sym "other" "secret")
  | "call" =>
    match ← choose "gen.call" 5 with
    | 0 => pure (L [S "=", ← sub scope, ← sub scope])
    | 1 => pure (L [S "inc", ← sub scope])
    | 2 => pure (L [S "+", ← sub scope, ← sub scope])
    | 3 => pure (L [S "vector", ← sub scope, ← sub scope])
    | _ => pure (L [K "k", L [S "mk-map", K "k", ← sub scope]])
  | "call2" =>
    match ← choose "gen.call2" 9 with
    | 0 => pure (L [S "<", ← sub scope, ← sub scope])
    | 1 => pure (L [S "*", ← sub scope, ← sub scope])
    | 2 => pure (L [S "pos?", ← sub scope])
    | 3 => pure (L [S "nil?", ← sub scope])
    | 4 => pure (L [S "count", ← sub scope])
    | 5 => pure (L [S "first", ← sub scope])
    | 6 => pure (L [S "rest", ← sub scope])
    | 7 => pure (L [S "str", ← sub scope, ← sub scope])
    | _ => pure (L [S "list", ← sub scope, ← sub scope])
  | "vec" => pure (V [← sub scope, ← sub scope])
  | "map" => pure (.persistentArrayMap none [(K "k", ← sub scope)])
  | "set" => pure (.persistentHashSet none [← sub scope])
  | "try" => pure (L [S "try", ← sub scope])
  | "def" =>
    let n ← name "gen.def.name"
    let v ← sub scope
    pure (L [S "do", L [S "def", S n, v], S n])
  | "quote" => pure (L [S "quote", ← sub scope])
  | "case" =>
    let v ← match ← choose "gen.case.value" 4 with
      | 0 => pure (I 1) | 1 => pure (I 2) | 2 => pure (I 3)
      | _ => sub scope
    let e1 ← sub scope
    let dflt ← sub scope
    if (← choose "gen.case.clauses" 2) == 0 then pure (L [S "case", v, I 1, e1, dflt])
    else pure (L [S "case", v, I 1, e1, I 2, ← sub scope, dflt])
  | _ => leafGen g scope

/-- Every tag set aside in round 3: round 2's classes (R23–R36), by the analyzer path tags. -/
def knownTags : List (String × String) :=
  [("if-native-merge", "R23"), ("loop-native-recur", "R24"), ("int-arith", "R25"),
   ("case-branch-type", "R26"), ("recur-crosses-fn", "R27"), ("fn-name-shadowed", "R28"),
   ("macro-over-fn-name", "R29"), ("macro-form-env", "R30"), ("macro-meta-on-literal", "R31"),
   ("private-under-expansion", "R32"), ("bool-arith", "R33"), ("op-equal-object-builtin", "R36"),
   ("native-callee", "W3 (round 2's tag: a native literal local called)"),
   ("str-of-fn", "WA3 (a fn object's printed form, implementation-defined)"),
   ("case-def-order", "W4 (case analyzes its default before its clauses)"),
   ("local-macro-name", "W5 (macroexpand keeps expanding a local's name as a macro)")]

def known : List String := knownTags.map (·.1)

structure Prog where
  forms : List Obj
  taken : Array Taken

def genProgram (g : Grammar) : GM (List Obj) := do
  modify fun w => { w with budget := g.budget }
  pure [← gen g g.depth [] true]

/-- A string with every `#object[...]` (a fn object's printed identity, implementation-specific
on both sides) replaced by `#object`. -/
def stripObjects (s : String) : String := Id.run do
  let parts := s.splitOn "#object["
  let mut out := parts.headD ""
  for p in parts.drop 1 do
    out := out ++ "#object" ++ String.intercalate "]" ((p.splitOn "]").drop 1)
  return out

partial def normStrings : Obj → Obj
  | .persistentString t => .persistentString (stripObjects t)
  | .persistentVector m xs => .persistentVector m (xs.map normStrings)
  | .persistentList m xs => .persistentList m (xs.map normStrings)
  | .persistentHashSet m xs => .persistentHashSet m (xs.map normStrings)
  | .persistentArrayMap m kvs => .persistentArrayMap m (kvs.map fun (k, v) => (normStrings k, normStrings v))
  | .persistentHashMap m kvs => .persistentHashMap m (kvs.map fun (k, v) => (normStrings k, normStrings v))
  | o => o

/-- Every `(str …)` call made `(vector …)`: a program whose disagreement goes away is one whose
answer depends on how a fn object prints (implementation-defined on both sides: WA3). -/
partial def strToVector : Obj → Obj
  | .persistentList m (.symbol sm "" "str" :: xs) => .persistentList m (.symbol sm "" "vector" :: xs.map strToVector)
  | .persistentList m xs => .persistentList m (xs.map strToVector)
  | .persistentVector m xs => .persistentVector m (xs.map strToVector)
  | .persistentHashSet m xs => .persistentHashSet m (xs.map strToVector)
  | .persistentArrayMap m kvs => .persistentArrayMap m (kvs.map fun (k, v) => (strToVector k, strToVector v))
  | o => o

/-- Round 2's agreement, with printed fn identities ignored inside strings (`str` of a fn), and a
64-bit long overflow (Clojure throws, jank wraps) taken as jank's documented behavior (round 1's
A2: "signed integer overflow is well defined and will wrap"). -/
def agrees3 (j c : Outcome) : Bool :=
  match j, c with
  | .value a, .value b => (Outcome.value (normStrings a)).agrees (.value (normStrings b))
  | .value _, .thrown "integer overflow" => true
  | _, _ => j.agrees c

partial def hasStrCall : Obj → Bool
  | .persistentList _ (.symbol _ "" "str" :: _) => true
  | o => (o.elems.getD []).any hasStrCall ||
    (match o with
     | .persistentArrayMap _ kvs => kvs.any fun (k, v) => hasStrCall k || hasStrCall v
     | _ => false)

/-! ### Round 3's own classes, recognized so that searches continue past them -/

def isSymNamed (o : Obj) (n : String) : Bool :=
  match o with
  | .symbol _ "" m => m == n
  | _ => false

def evens {α : Type} : List α → List α
  | a :: _ :: rest => a :: evens rest
  | [a] => [a]
  | [] => []

/-- W4: a `case` form one of whose clauses or default holds a `def` (analysis order differs). -/
partial def caseWithDef : Obj → Bool
  | .persistentList _ (h :: v :: rest) =>
    let hasDef : Obj → Bool := fun e => (hasDefIn e)
    (isSymNamed h "case" && rest.any hasDef) || caseWithDef v || rest.any caseWithDef || caseWithDef h
  | o => (o.elems.getD []).any caseWithDef ||
    (match o with
     | .persistentArrayMap _ kvs => kvs.any fun (k, v) => caseWithDef k || caseWithDef v
     | _ => false)
where
  hasDefIn : Obj → Bool
    | .persistentList _ (h :: rest) => isSymNamed h "def" || hasDefIn h || rest.any hasDefIn
    | o => (o.elems.getD []).any hasDefIn ||
      (match o with
       | .persistentArrayMap _ kvs => kvs.any fun (k, v) => hasDefIn k || hasDefIn v
       | _ => false)

/-- Every LOCAL binding of `old` (let*/let/loop*/loop bindings, fn names and parameters, letfn
names) and the references that resolve to it, renamed `new`; var references stay. -/
partial def renameLocal (old new : String) (bound : Bool) : Obj → Obj
  | .symbol m "" n => if n == old && bound then .symbol m "" new else .symbol m "" n
  | .persistentList m (h :: rest) =>
    let rn := fun (b : Bool) (o : Obj) => renameLocal old new b o
    let headName := match h with | .symbol _ "" n => n | _ => ""
    if headName == "quote" || headName == "var" then .persistentList m (h :: rest)
    else if (headName == "let*" || headName == "let" || headName == "loop*" || headName == "loop") then
      match rest with
      | .persistentVector vm bs :: body =>
        -- sequential bindings
        let rec go (b : Bool) : List Obj → List Obj × Bool
          | n :: v :: more =>
            let v' := rn b v
            let b' := if isSymNamed n old then true else b
            let (more', bf) := go b' more
            ((if isSymNamed n old then .symbol none "" new else n) :: v' :: more', bf)
          | xs => (xs, b)
        let (bs', bodyBound) := go bound bs
        .persistentList m (h :: .persistentVector vm bs' :: body.map (rn bodyBound))
      | _ => .persistentList m (h :: rest.map (rn bound))
    else if headName == "fn*" || headName == "fn" then
      let (nameObj, arts) := match rest with
        | (s@(.symbol _ "" _)) :: more => (some s, more)
        | more => (none, more)
      let b0 := match nameObj with | some s => bound || isSymNamed s old | none => bound
      let nameObj' := nameObj.map fun s => if isSymNamed s old then .symbol none "" new else s
      let doArity := fun (params : List Obj) (body : List Obj) =>
        let b := b0 || params.any (isSymNamed · old)
        (params.map fun p => if isSymNamed p old then .symbol none "" new else p, body.map (rn b))
      let arts' := match arts with
        | .persistentVector vm ps :: body =>
          let (ps', body') := doArity ps body
          .persistentVector vm ps' :: body'
        | xs => xs.map fun a => match a with
          | .persistentList am (.persistentVector vm ps :: body) =>
            let (ps', body') := doArity ps body
            .persistentList am (.persistentVector vm ps' :: body')
          | o => o
      .persistentList m (h :: ((match nameObj' with | some s => [s] | none => []) ++ arts'))
    else if headName == "letfn*" then
      match rest with
      | .persistentVector vm bs :: body =>
        let names := evens bs
        let b := bound || names.any (isSymNamed · old)
        .persistentList m (h :: .persistentVector vm (bs.map (rn b)) :: body.map (rn b))
      | _ => .persistentList m (h :: rest.map (rn bound))
    else .persistentList m (rn bound h :: rest.map (rn bound))
  | .persistentVector m xs => .persistentVector m (xs.map (renameLocal old new bound))
  | .persistentHashSet m xs => .persistentHashSet m (xs.map (renameLocal old new bound))
  | .persistentArrayMap m kvs => .persistentArrayMap m (kvs.map fun (k, v) => (renameLocal old new bound k, renameLocal old new bound v))
  | o => o

/-- A run's tags: the analyzer paths it took, the macros it used, and `str-of-fn` when the
disagreement disappears with every `str` made `vector` (see `strToVector`). -/
def tagsOf (forms : List Obj) (j : JankRun) (c : Outcome) (oracle : Oracle) : List String :=
  let base := (j.tags ++ forms.flatMap formTags).eraseDups
  if !base.isEmpty || agrees3 j.outcome c then base
  else if forms.any caseWithDef then ["case-def-order"]
  else
    let fs := forms.map strToVector
    if forms.any hasStrCall && agrees3 (runJank fs oracle).outcome (runClojure fs) then ["str-of-fn"]
    else
      -- W5: locals named like a macro (`when`) renamed: the disagreement goes away.
      let rs := forms.map (renameLocal "when" "w__" false)
      if agrees3 (runJank rs oracle).outcome (runClojure rs) then ["local-macro-name"] else base

/-- One timeline: a program, both sides, compared; `skip` tags set aside. -/
def runOne (g : Grammar) (skip : List String) (oracle : Oracle := {}) (source : Source) : Ended :=
  match (genProgram g).run { decisions := { source } } with
  | .error (.violation p d) w => { taken := w.decisions.taken, violation := some (p, d) }
  | .error .limit w => { taken := w.decisions.taken, violation := none }
  | .error (.nodeDown _) w => { taken := w.decisions.taken, violation := none }
  | .ok forms w =>
    let j := runJank forms oracle
    let c := runClojure forms
    let tags := tagsOf forms j c oracle
    if !agrees3 j.outcome c && !(tags.any skip.contains) then
      { taken := w.decisions.taken,
        violation := some ("jank = Clojure",
          s!"{" ".intercalate (forms.map Obj.pr)} => jank {j.outcome.show}; Clojure {c.show}; tags {tags}") }
    else { taken := w.decisions.taken, violation := none }

/-- Every program, counted: agreeing, differing by tag set (with an example), out-of-model. -/
structure Tally where
  runs : Nat := 0
  agree : Nat := 0
  unsupported : Nat := 0
  differ : Nat := 0
  byTags : Array (List String × Nat × String) := #[]
  complete : Bool := false
  unsupportedEx : Array String := #[]
  unexplainedEx : Array String := #[]
  /-- Outside the models, by the model's message (jank side or Clojure side). -/
  unsupportedBy : Array (String × Nat) := #[]

def tallyUnder (g : Grammar) (prefix_ : Array Nat) (maxRuns : Nat) (oracle : Oracle := {}) : Tally := Id.run do
  let mut path := prefix_
  let mut t : Tally := {}
  for _ in [0:maxRuns] do
    match (genProgram g).run { decisions := { source := Source.path path } } with
    | .error _ _ => return t
    | .ok forms w =>
      let j := runJank forms oracle
      let c := runClojure forms
      let tags := tagsOf forms j c oracle
      t := { t with runs := t.runs + 1 }
      let unsup := match j.outcome, c with
        | .unsupported _, _ | _, .unsupported _ | .fuel, _ | _, .fuel => true
        | _, _ => false
      if unsup then
        let why := match j.outcome, c with
          | .unsupported m, _ => s!"jank: {(m.splitOn " ").headD m}"
          | _, .unsupported m => s!"Clojure: {(m.splitOn " ").headD m}"
          | .fuel, _ => "jank: fuel"
          | _, _ => "Clojure: fuel"
        let ub := match t.unsupportedBy.findIdx? (·.1 == why) with
          | some k => t.unsupportedBy.modify k fun (w, n) => (w, n + 1)
          | none => t.unsupportedBy.push (why, 1)
        t := { t with unsupported := t.unsupported + 1, unsupportedBy := ub }
        if t.unsupportedEx.size < 4 then
          t := { t with unsupportedEx := t.unsupportedEx.push s!"{" ".intercalate (forms.map Obj.pr)} => jank {j.outcome.show}; Clojure {c.show}" }
      if agrees3 j.outcome c then t := { t with agree := t.agree + 1 }
      else
        let ex := s!"{" ".intercalate (forms.map Obj.pr)} => jank {j.outcome.show}; Clojure {c.show}"
        if tags.isEmpty && t.unexplainedEx.size < 40 then t := { t with unexplainedEx := t.unexplainedEx.push ex }
        let byTags := match t.byTags.findIdx? (·.1 == tags) with
          | some k => t.byTags.modify k fun (ts, n, e) => (ts, n + 1, e)
          | none => t.byTags.push (tags, 1, ex)
        t := { t with differ := t.differ + 1, byTags }
      let taken := w.decisions.taken
      if taken.size < prefix_.size then return { t with complete := true }
      match nextPathUnder taken prefix_.size with
      | none => return { t with complete := true }
      | some p => path := p
  return t

/-- The same tally over random programs from `count` mixed seeds (from `first`). -/
def tallySeeds3 (g : Grammar) (count first : Nat) (oracle : Oracle := {}) : Tally := Id.run do
  let mut t : Tally := {}
  for i in [0:count] do
    match (genProgram g).run { decisions := { source := { gen := mkStdGen (mixSeed (first + i)) } } } with
    | .error _ _ => pure ()
    | .ok forms _ =>
      let j := runJank forms oracle
      let c := runClojure forms
      let tags := tagsOf forms j c oracle
      t := { t with runs := t.runs + 1 }
      let unsup := match j.outcome, c with
        | .unsupported _, _ | _, .unsupported _ | .fuel, _ | _, .fuel => true
        | _, _ => false
      if unsup then t := { t with unsupported := t.unsupported + 1 }
      if agrees3 j.outcome c then t := { t with agree := t.agree + 1 }
      else
        let ex := s!"{" ".intercalate (forms.map Obj.pr)} => jank {j.outcome.show}; Clojure {c.show}"
        if tags.isEmpty && t.unexplainedEx.size < 40 then t := { t with unexplainedEx := t.unexplainedEx.push ex }
        let byTags := match t.byTags.findIdx? (·.1 == tags) with
          | some k => t.byTags.modify k fun (ts, n, e) => (ts, n + 1, e)
          | none => t.byTags.push (tags, 1, ex)
        t := { t with differ := t.differ + 1, byTags }
  return { t with complete := false }

def printTally (label : String) (t : Tally) : IO Unit := do
  IO.println s!"== {label}: {t.runs} programs{if t.complete then " (complete)" else " (stopped)"}, {t.agree} agree, {t.differ} differ, {t.unsupported} outside the models"
  let untagged := (t.byTags.filter (·.1.isEmpty)).foldl (fun acc (_, n, _) => acc + n) 0
  IO.println s!"   differing with no tag (unexplained): {untagged}"
  IO.println s!"   outside the models, by cause: {t.unsupportedBy.toList}"
  for e in t.unsupportedEx do IO.println s!"   outside the models, e.g. {e}"
  for ex in t.unexplainedEx do
    IO.println s!"     unexplained, e.g. {ex}"
  let allTags := (t.byTags.toList.flatMap (·.1)).eraseDups
  for tg in allTags do
    let only := (t.byTags.filter (·.1 == [tg])).foldl (fun acc (_, n, _) => acc + n) 0
    let any := (t.byTags.filter (·.1.contains tg)).foldl (fun acc (_, n, _) => acc + n) 0
    let ex := match t.byTags.find? (·.1 == [tg]) with
      | some (_, _, e) => e
      | none => ""
    let r := (knownTags.lookup tg).getD "NEW"
    IO.println s!"   {tg} [{r}]: {any} take this path, {only} only this one; e.g. {ex}"

/-! ## Round 2's tiny depth-2 grammar, counted -/

/-- Round 2's `genExpr` program count at depth `d` with `k` locals in scope (the decision tree's
leaves), for `L` literals and `n` names, every feature on: the exact size of the world its
`exhaust` walked. -/
def r2Count (L n : Nat) : Nat → Nat → Nat
  | 0, k => 2 * L + k
  | d + 1, k =>
    let N := fun j => r2Count L n d j
    let leaf := 2 * L + k
    let ifs := N k * N k * (1 + N k)
    let dos := N k * N k
    let lets := n * N k * N (k + 1)
    let loops := n * N k * N (k + 1) * N (k + 1)
    let fns := n * n * (N (k + 1) * N (k + 1) * N k) + n * n * (N (k + 2) * N (k + 2) * N k)
    let macros := N k * N k + N k + 1 + N k + N k + 1
    let calls := N k * N k + N k + N k * N k + N k * N k + N k
    let quotes := N k
    let cases := (3 + N k) * N k * N k * (1 + N k)
    leaf + ifs + dos + lets + loops + fns + macros + 1 + calls + quotes + cases

/-- The same count split by the first decision (the top kind), at depth `d + 1` with no locals. -/
def r2KindCounts (L n d : Nat) : List (String × Nat) :=
  let N := fun j => r2Count L n d j
  let k := 0
  [("leaf", 2 * L + k), ("if", N k * N k * (1 + N k)), ("do", N k * N k),
   ("let", n * N k * N (k + 1)), ("loop", n * N k * N (k + 1) * N (k + 1)),
   ("fn", n * n * (N (k + 1) * N (k + 1) * N k) + n * n * (N (k + 2) * N (k + 2) * N k)),
   ("macro", N k * N k + N k + 1 + N k + N k + 1), ("private", 1),
   ("call", N k * N k + N k + N k * N k + N k * N k + N k), ("quote", N k),
   ("case", (3 + N k) * N k * N k * (1 + N k))]

/-- Round 2's tiny grammar (4 literals, 2 names): 14,523 programs at depth 1 (also counted by
`exhaust`), 44,589,295,635,161,858 at depth 2. -/
theorem r2_tiny_depth1 : r2Count 4 2 1 0 = 14523 := by decide
theorem r2_tiny_depth2 : r2Count 4 2 2 0 = 44589295635161858 := by decide
/-- Round 2's reduced grammar (6 literals, 3 names) at depth 1: 76,731, round 2's complete run. -/
theorem r2_reduced_depth1 : r2Count 6 3 1 0 = 76731 := by decide

end Jank.R3.Search.Analyzer
