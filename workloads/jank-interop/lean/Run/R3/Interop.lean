import Jank.R3.Interop.Theorems
import Jank.Analyzer.World

/-! Round 3 driver: Interop. CppInterOp 28b0830d replicated beside Clang's answers (llvmorg-23.1.0
where read, the C++20 standard elsewhere), round 2's interop worlds rerun on it, and the round-3
worlds (DSL members, templates, calls through pointers, class operators, member access,
unsafe-cast, branch types, native exceptions, AArch64 `char`) searched to completion. -/

open Determinismo
open Jank.Interop
open Jank.R3.Interop
open Jank.R3.Interop.Worlds
open Jank.Interop.Search (runW exploreMixed)

def describe (c : Counterexample) : String :=
  s!"{c.property} after {c.runs} timelines, {c.taken.size} decisions: {c.detail}"

def indent (s : String) : String := (s.splitOn "\n").map ("    " ++ ·) |> "\n".intercalate

/-- One world: mixed-seed `explore` (shrunk, with its tape), `exhaust`, the full table, and the
residual searches. -/
def world {α : Type} (name : String) (body : List String → EStateM Stop Jank.Interop.Search.W Unit) (seeds maxRuns : Nat)
    (cases : List α) (judge : α → Option (String × String)) (shown : Nat := 12) : IO Unit := do
  let t ← IO.monoMsNow
  IO.eprintln s!"[{t}] {name}"
  IO.println s!"== {name}"
  let run := runW (body [])
  match exploreMixed run seeds with
  | some c =>
    IO.println s!"  explore ({seeds} mixed seeds): {describe c}"
    let s := shrink run c
    IO.println s!"  shrunk to {s.taken.size} decisions: {s.detail}"
    IO.println s!"  tape:\n{indent (tape s.taken)}"
  | none => IO.println s!"  explore ({seeds} mixed seeds): nothing"
  let bad := cases.filterMap judge
  let classes := bad.foldl (fun acc (c, _) => if acc.contains c then acc else acc ++ [c]) []
  IO.println s!"  table: {bad.length} of {cases.length} cases deviate; classes: {classes.map fun c => s!"{c} ({(bad.filter (·.1 == c)).length})"}"
  for c in classes do
    for (_, d) in (bad.filter (·.1 == c)).take shown do IO.println s!"    [{c}] {d}"
  IO.println "  residual searches (exhaust, each found class set aside in turn):"
  for l in residual name body maxRuns do IO.println s!"    {l}"
  (← IO.getStdout).flush

def main : IO UInt32 := do
  let t0 ← IO.monoMsNow
  IO.println "jank3-interop: CppInterOp 28b0830d replicated (round 3) under jank 7135b7708's interop paths, against C++20 / the book / Clojure"
  -- 1. Census
  IO.println "== census: round 2's standard-modeled CppInterOp answers vs the CppInterOp replica"
  for r in Census.rows do
    IO.println s!"  {r.name}: {r.diffs.length} of {r.total} queries differ"
    for d in r.diffs.take 10 do IO.println s!"    {d}"
  (← IO.getStdout).flush
  -- 2. Round-2 entries re-checked
  IO.println "== round 2 re-checked on the replica"
  do
    let L := Jank.Analyzer.L
    let V := Jank.Analyzer.V
    let S := Jank.Analyzer.S
    let I := Jank.Analyzer.I
    let r36 := [L [S "loop*", V [S "x", .nil, S "n", I 0], L [S "if", L [S "=", S "n", I 1], S "x", L [S "recur", I 5, I 1]]]]
    let a := (Jank.Analyzer.runJank r36 {}).outcome.show
    let b := (Jank.Analyzer.runJank r36 { classBuiltinAssign := true }).outcome.show
    let c := (Jank.Analyzer.runClojure r36).show
    IO.println s!"  R36 (loop [x nil n 0] (if (= n 1) x (recur 5 1))): round 2 (no builtin = on objects) {a}; with CppInterOp's answer GetBuiltinOperatorType(=, object_ref, object_ref) = `{tshow (CppInterOp.getBuiltinOperatorType x86_64 x3 .equal [objectRef, objectRef])}`: {b}; Clojure {c}"
  let cstr : CType := .lref (.array (.cv true false (.b .char)) (some 4))
  let cptr : CType := .ptr (.cv true false (.b .char))
  IO.println s!"  R87 determine_implicit_conversion(`const char (&)[4]`, `const char *`): round 2 {reprStr (CppUtil.determineImplicitConversion x86_64 x3.w cstr cptr)}; replica {reprStr (Paths.determineImplicitConversion x86_64 x3 8 cstr cptr)} (GetPointeeType(`const char[4]`) = `{tshow (CppInterOp.getPointeeType (.array (.cv true false (.b .char)) (some 4)))}`)"
  -- world V decisions
  let castDiffs := Search.castTypes.flatMap fun s => Search.castTypes.filterMap fun d =>
    let r2 := CppUtil.isConstructible x86_64 x3.w d.type s.type || CppInterop.isImplicitlyConvertible x86_64 x3.w s.type d.type
    let r3 := Paths.isConstructible x86_64 x3 d.type s.type || CppInterOp.isImplicitlyConvertible x86_64 x3 s.type d.type
    if r2 == r3 then none else some s!"{s.text} → {d.text}: round 2 {r2}; replica {r3}"
  IO.println s!"  V (cpp/cast) acceptance (is_constructible || IsImplicitlyConvertible) over round 2's 196 pairs: {castDiffs.length} differ"
  for d in castDiffs.take 10 do IO.println s!"    {d}"
  -- world VIII recount
  for p in [x86_64, aarch64] do
    let bad := (round2Dsl p).filterMap dslJudge
    IO.println s!"  VIII (round 2's 147 chains) on the replica, {if p.charSigned then "x86-64" else "AArch64 Linux"}: {bad.length} of 147 deviate"
  let r2v8 := Search.allDsl.filterMap fun (ms, b) => Search.dslJudge ms b
  IO.println s!"  VIII as round 2 computed it (round 2's modifiers, x86-64): {r2v8.length} of 147"
  for (ms, b) in Search.allDsl do
    let old := (Search.dslJudge ms b).isSome
    let new := (dslJudge { p := x86_64, base := b, mods := ms }).isSome
    if old != new then
      IO.println s!"    changed: {(dslJudge { p := x86_64, base := b, mods := ms }).map (·.2) |>.getD ((Search.dslJudge ms b).getD "")} (round 2 {if old then "deviates" else "agrees"}; replica {if new then "deviates" else "agrees"})"
  -- world IX type pairs
  let ixTypes : List CType := [.b .int, .b .long, .b .double, .b .bool, typedRef "integer", typedRef "keyword", objectRef]
  let ixDiffs := ixTypes.flatMap fun a => ixTypes.filterMap fun b =>
    let u := CppInterop.getCommonType x86_64 x3.w a b
    let v := CppInterOp.getCommonType x86_64 x3 a b
    if u.canonical == v.canonical then none else some s!"({tshow a}, {tshow b}): round 2 {tshow u}; replica {tshow v}"
  IO.println s!"  IX GetCommonType over the IX branch types: {ixDiffs.length} pairs differ"
  for d in ixDiffs do IO.println s!"    {d}"
  -- III on AArch64
  let iii (p : Platform) := Search.allParams.filterMap fun c => (paramJudgeP p c).map (c.fn ++ "|" ++ c.v.text ++ "|" ++ toString c.lit ++ "|" ++ ·)
  let ix86 := iii x86_64
  let iarm := iii aarch64
  IO.println s!"  III (round 2's 312 parameter cases): x86-64 {ix86.length} deviate; AArch64 Linux {iarm.length} deviate"
  let key (s : String) := ((s.splitOn "|").take 3)
  for d in iarm.filter (fun s => !(ix86.any fun t => key t == key s)) do IO.println s!"    AArch64 only: {(d.splitOn "|").getLast!}"
  for d in ix86.filter (fun s => !(iarm.any fun t => key t == key s)) do IO.println s!"    x86-64 only: {(d.splitOn "|").getLast!}"
  (← IO.getStdout).flush
  -- 3. Round-3 worlds
  world "VIII'. DSL integer modifiers (CppInterOp Get*Type), 11 bases × chains ≤ 3 of signed/unsigned/short/long/const × 2 platforms"
    dslBody 3000 200000 (allDsl [x86_64, aarch64] dslBases 3) dslJudge 8
  world "X. DSL member forms :member / :member* / :&member, against the book and C++"
    memBody 3000 20000 allMem memJudge 6
  world "XI. calls through function pointers and pointers to members (build_indirect_cpp_call)"
    callBody 3000 20000 allCalls callJudge 6
  world "XII. function templates with explicit template arguments, called"
    tmplBody 3000 20000 allTmpl tmplJudge 6
  world "XIII. operators on class operands (GetOperator; no built-in candidates)"
    opBody 2000 20000 allOps opJudge 6
  world "XIV. data member access (cpp/.-name obj)"
    maBody 2000 20000 allMa (fun (o, n) => maJudge o n) 6
  world "XV. cpp/unsafe-cast (IsCStyleConvertible) against C-style casts"
    ucBody 3000 20000 allUc (fun (s, d) => ucJudge s d) 8
  world "XVI. if with native branches, references included (find_branch_common_type on GetCommonType)"
    brBody 2000 20000 allBr (fun (a, b) => brJudge a b) 8
  world "XVII. native exceptions: catch handler types"
    excBody 2000 20000 allExc (fun (h, e) => excJudge h e) 6
  -- 4. Theorems
  IO.println "== theorems (proved at build time; no sorry, no native_decide)"
  for n in ["applyMod_keeps_notLongLong", "dsl_never_long_long", "long_long_int_is_long",
            "signed_char_is_char_x86", "unsigned_char_is_char_aarch64", "signed_char_aarch64", "unsigned_char_x86",
            "short_long_bool", "isIntegral_enum", "isBuiltin_enum", "getPointeeType_array",
            "getScopeFromType_fnptr", "isImplicitlyConvertible_to_lref", "isImplicitlyConvertible_to_rref",
            "isCStyleConvertible_floating", "isCStyleConvertible_nullptr", "pm_const_pointee_dropped",
            "getCommonType_small_same", "getCommonType_ref_null"] do
    IO.println s!"  {n}"
  let t1 ← IO.monoMsNow
  IO.println s!"== done in {(t1 - t0) / 1000} s"
  return 0
