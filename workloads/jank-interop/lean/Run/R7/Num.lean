import Jank.R7.Num.Walk
import Jank.R7.Num.NaN
import Jank.R7.Num.DivSearch
import Jank.R7.Num.Theorems

/-! Round 7 driver: numbers (`jank7-num gen | cmp | div | brief | forms`). -/

open Jank.R3.Boost Jank.R3.Boost.Num Jank.R7.Num.Dec Jank.R7.Num.Walk

def walkDir : String := ".r7-scratch/num/walk"

def countBy {α : Type} (xs : Array α) (key : α → String) : List (String × Nat) :=
  let m := xs.foldl (fun (m : Std.HashMap String Nat) x => m.insert (key x) (m.getD (key x) 0 + 1)) {}
  m.toList.mergeSort (fun a b => a.1 ≤ b.1)

def gen : IO Unit := do
  IO.FS.createDirAll walkDir
  let qs := questions
  IO.FS.writeFile s!"{walkDir}/walk.clj" (cljProgram qs)
  IO.println s!"wrote {qs.size} questions over {vals.length} values ({decTexts.length} BigDecimals) to {walkDir}/walk.clj"

def vName : Verdict → String
  | .agree => "agree" | .text => "text" | .value => "value" | .kind => "kind"
  | .throws => "throws" | .other => "other"

/-- The class a jank disagreement belongs to (the earlier item it extends, or a new one). -/
def classify (q : Q) (j c : Out) (v : Verdict) : String :=
  let txt := match v with
    | .text => if isNotation j c then "text: notation (S5/R72)" else "text: scale (R72)"
    | v => vName v
  let isRatioNT := fun (x : Val) => match x.c with
    | .ratio _ d => (Java.terminating 1 d.toNat).isNone | _ => false
  let isDbl := fun (x : Val) => match x.c with | .dbl _ => true | _ => false
  let isRatio := fun (x : Val) => match x.c with | .ratio .. => true | _ => false
  match q with
  | .bin op a b _ =>
    if (isRatioNT a || isRatioNT b) && v == .throws then "S3: a non-terminating ratio converts (Clojure throws)"
    else if op == .div && isZeroC b.c && v == .throws then "N7-2: division by zero gives inf/nan"
    else if op == .div && v == .throws then "S3: a non-terminating quotient returns a value"
    else if v == .throws && (op == .rem || op == .quot) && isZeroC b.c then "zero divisor: both throw, jank a std::runtime_error"
    else if (isDbl a || isDbl b) && v == .kind then "S6: with a double, a BigDecimal"
    else if op == .quot && v == .other then "D4: quot is a long"
    else if op == .quot && v == .throws then "D4: quot through doubles (UB cast past i64)"
    else if op == .rem && (isRatio a || isRatio b) then s!"S8: rem with a ratio truncates the decimal ({txt})"
    else if op == .rem && v == .value then "S7: rem is a 128-digit fmod"
    else if op == .div && v == .value then "S2/S4: division by a Newton inverse in 128 digits"
    else if v == .value then "S4: 128 significant digits"
    else if (op == .max || op == .min) && v == .kind then "V57: max keeps its first operand on a tie"
    else s!"{op.name} {txt}"
  | .un op a =>
    if op == .hash then "N7-1: hash of a BigDecimal"
    else if op == .double then "double printing (round 2), not a BigDecimal difference"
    else if op == .bigdec && isRatioNT a then "S3: a non-terminating ratio converts (Clojure throws)"
    else if op == .long && v == .throws then "S12: long of a huge BigDecimal saturates"
    else if v == .value then "S4: 128 significant digits"
    else s!"{op.name} {txt}"

def cmp : IO Unit := do
  let qs := questions
  let txt ← IO.FS.readFile s!"{walkDir}/walk.out"
  let jvm := parseOut txt
  IO.println s!"== BigDecimal walk: {qs.size} questions (complete over {vals.length} values: {decTexts.length} BigDecimals, {otherTexts.length} others; {ops.length} binary operators × 2 paths on pairs with a BigDecimal, {uops.length} unary)"
  IO.println s!"   JVM answers read: {jvm.size}"
  -- 1. The model against the JVM.
  let mut modelBad : Array String := #[]
  let mut missing := 0
  let mut i := 0
  for q in qs do
    i := i + 1
    match jvm.get? (i - 1) with
    | none => missing := missing + 1
    | some a =>
      let m := q.clj.encS
      if m != a then modelBad := modelBad.push s!"  {q.form}: JVM {a} | model {m}"
  IO.println s!"== Java/Clojure model vs Clojure 1.12.3: {modelBad.size} differ, {missing} missing"
  for l in modelBad.toList.take 40 do IO.println l
  -- 2. jank today and with exact division, against the JVM-validated model.
  for (label, f) in [("jank today", Q.jank), ("jank with exact division (S2's fix only)", Q.jankFixed)] do
    let rows := qs.map (fun q => (q, f q, q.clj))
    let rows := rows.map (fun (q, j, c) => (q, j, c, verdict j c))
    IO.println s!"\n== {label}: verdicts"
    for (k, n) in countBy rows (fun (_, _, _, v) => vName v) do IO.println s!"  {k}: {n}"
    let bad := rows.filter (fun (_, _, _, v) => v != .agree)
    IO.println s!"-- by class"
    for (k, n) in countBy bad (fun (q, j, c, v) => classify q j c v) do IO.println s!"  {k}: {n}"
    IO.println s!"-- examples (3 per class)"
    let mut seen : Std.HashMap String Nat := {}
    for (q, j, c, v) in bad do
      let k := classify q j c v
      let n := seen.getD k 0
      if n < 3 then
        IO.println s!"  [{k}] {q.form} [{q.path}]: jank {j.show}; Clojure {c.show}"
        seen := seen.insert k (n + 1)

def div (args : List String) : IO Unit := do
  let bu1 := (args.getD 0 "20").toNat!
  let bu2 := (args.getD 1 "20").toNat!
  let t := Jank.R7.Num.DivSearch.search bu1 bu2 (-2) 3
  IO.println s!"== Exact division vs Clojure: complete over |u1| ≤ {bu1}, 1 ≤ |u2| ≤ {bu2}, scales -2..3 ({t.cases} pairs)"
  IO.println s!"  non-terminating (both throw with the fix): {t.nonTerminating}"
  IO.println s!"  texts agree: {t.agreeBoth}"
  IO.println s!"  texts differ: {t.textDiffers} (scale only {t.scaleOnly}, notation {t.notationN}, value {t.valueDiffers})"
  IO.println s!"  hypothesis H mispredicts: {t.hFails}"
  for e in t.examples do IO.println s!"    {e}"
  for e in t.failures do IO.println s!"    H fails: {e}"

def brief : IO Unit := do
  IO.println "== The brief's min/max NaN forms on round 6's model (Jank.R6.Num.MinMax.jMinMax)"
  for c in Jank.R7.Num.NaN.cases do
    IO.println s!"  {c.form} [{c.path}]: jank {c.jank}; Clojure {c.clj}"

/-- Single forms for the report and the tests (BigDecimal values read by both readers). -/
def forms : IO Unit := do
  let one := fun (op : Op) (a b : String) => do
    match mkVal a, mkVal b with
    | some x, some y =>
      IO.println s!"  ({op.name} {a} {b}): jank {(jrOut (jAnswer op x.j y.j)).show}; exact-division jank {(jrOut (jAnswerFixed op x.j y.j)).show}; Clojure {(crOut (cAnswer op x.c y.c true)).show}"
    | _, _ => IO.println s!"  ({op.name} {a} {b}): unreadable"
  let un := fun (op : UOp) (a : String) => do
    match mkVal a with
    | some x => IO.println s!"  ({op.name} {a}): jank {(jrOut (jUnary op x.j)).show}; Clojure {(crOut (cUnary op x.c)).show}"
    | none => IO.println s!"  ({op.name} {a}): unreadable"
  IO.println "== forms"
  one .div "6M" "3M"; one .div "6.0M" "3"; one .div "6.00M" "3"; one .div "1M" "4"; one .div "1.000M" "4"
  one .div "6M" "3.0M"; one .div "60M" "3.0M"; one .div "1M" "3"; one .div "1M" "0M"; one .div "0M" "0M"
  one .div "1M" "0"; one .div "1M" "1/3"; one .div "0M" "5.00M"; one .div "1M" "1024"
  one .div "1M" "1606938044258990275541962092341162602522202993782792835301376M"
  one .add "1.25M" "1.75M"; one .mul "0.5M" "0.2M"; one .sub "1.10M" "0.10M"; one .add "1M" "1"
  one .add "1.000M" "1/4"; one .quot "7.5M" "2"; one .quot "7M" "2"; one .quot "100M" "1.0M"
  one .quot "1E+130M" "3"; one .rem "7.50M" "2"; one .rem "1E+130M" "3"; one .rem "7M" "0M"
  one .max "1.0M" "1.00M"; one .min "1.0M" "1.00M"; one .max "1M" "1"; one .compare "1/3" "1M"
  one .mul "1.1M" "1.1M"; one .add "1E+130M" "1"; one .sub "1M" "1E-130M"
  un .str "1.50M"; un .str "1M"; un .str "100M"; un .str "1E+2M"; un .str "0.00M"; un .str "0.00001M"
  un .hash "1.5M"; un .hash "1M"; un .hash "0.1M"; un .hash "2.5M"; un .hash "100M"; un .hash "-1.5M"
  un .hash "12345.6789M"; un .hash "0M"
  un .bigdec "1"; un .bigdec "1e10"; un .bigdec "5N"; un .bigdec "1/4"; un .bigdec "1.0"
  un .inc "1.50M"; un .abs "-1.50M"; un .neg "1.50M"

def main (args : List String) : IO Unit := do
  match args with
  | ["gen"] => gen
  | ["cmp"] => cmp
  | "div" :: rest => div rest
  | ["brief"] => brief
  | ["forms"] => forms
  | _ => do brief; forms
