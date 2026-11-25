import Elle.Props2

/-!
# Round 3: round 2's properties, every one a timeline breaks

`checkAll2` is `Props2.checkHistory2` (the same properties, in the same order, with the same
details) without its early returns: it lists every property broken, so a fix's regression can't
hide behind an earlier, known incompleteness of the same timeline (round 2's library gap).
-/

namespace Elle.Props3

open Elle Elle.Spec Elle.SpecOpts Elle.Gen Elle.Props Elle.Props2 Determinismo

def checkAll2 (c : Config2) (h : History) (ord : Option (List (Nat × Int))) : List (String × String) := Id.run do
  let skip (k : String) := c.skip.contains k || c.skip.any fun s => k.startsWith (s ++ ":")
  let mut out : Array (String × String) := #[]
  if c.singleReads && !(h.toList.all fun o => o.value.all fun m =>
      m.f != .r || (o.value.filter fun m' => m'.f == .r && m'.k == m.k).length ≤ 1) then return []
  if c.noInfoReads && readsInfoWrite h then return []
  let opts := optsOf c ord
  let aN := analyze2 c opts h .none
  let aR := analyze2 c opts h .realtime
  let extras := dedup (c.models.map fun m => additionalGraphs { opts with models := some [m] })
  let memo : List (Extra × Except String Anomalies) := extras.map fun e => (e, analyze2 c opts h e)
  let an (e : Extra) : Except String Anomalies :=
    match memo.find? (·.1 == e) with | some (_, r) => r | none => analyze2 c opts h e
  let anM (m : String) : Except String Anomalies :=
    let o : Opts := { opts with models := some [m] }
    if c.fixD13 && !isLA c then analyze2 c o h (additionalGraphs o) else an (additionalGraphs o)
  if !skip "thrown" then
    if let .error e := aR then out := out.push ("thrown", s!"Elle throws: {e}")
  let is := if isLA c then interpsListAppend h else interpsRegister h
  let txs := txnViews h
  let asm := assumeOf c ord
  let isA := is.filter (asm.holds txs)
  -- 1. inference
  if !isLA c && !skip "inference" then
    for (src, vgs) in RwRegister.sources opts h do
      let a : Option Assume := match src with
        | "linearizable-keys" => some { lin := true }
        | "sequential-keys" => some { seq := true }
        | "transaction-order-keys" => some { order := ord }
        | "wfr-keys" => some { wfr := true }
        | "initial-state" => some {}
        | _ => none
      let some a := a | continue
      let scope := is.filter (a.holds txs)
      let mut done := false
      for (k, es) in vgs do
        for (v1, v2) in es do
          if done then continue
          if let some bad := scope.find? (fun i => !edgeHolds txs i k v1 v2) then
            out := out.push ("inference:" ++ src,
              s!"{src} infers {ednVal v1} < {ednVal v2} on key {k}; an interpretation where the assumption holds has the opposite: order {bad.order}, reads {bad.reads}")
            done := true
  -- 2. verdicts
  for m in c.models do
    let ev := verdictOf opts anM m
    let svAll := specVerdict is m
    let svA := specVerdict isA m
    match ev with
    | .ok .false_ =>
      if svA == .sat && !skip ("soundness:" ++ m) then
        out := out.push ("soundness:" ++ m, s!"Elle: {m} invalid; an interpretation satisfies {m} and the options' assumption")
    | .ok .true_ =>
      if svAll == .unsat && !skip ("completeness:" ++ m) then
        out := out.push ("completeness:" ++ m, s!"Elle: {m} valid; specification: {svAll.str}")
      let total := (c.lin && totalPerKey h rtBefore) || (c.seq && totalPerKey h procBefore)
      if total && svA == .unsat && !skip ("completeness-total:" ++ m) then
        out := out.push ("completeness-total:" ++ m,
          s!"Elle: {m} valid; the option's order fixes every key's versions, and every interpretation where its assumption holds violates {m}")
      if svAll != .unsat && svA == .unsat && !skip ("completeness-assumed:" ++ m) then
        out := out.push ("completeness-assumed:" ++ m,
          s!"Elle: {m} valid; every interpretation where the options' assumption holds violates {m} (some do hold it)")
    | _ => pure ()
  -- 2b. fixes against Elle as written
  if c.fixD3 || c.fixD13 then
    let base := { opts with fixD3 := false, fixD13 := false }
    let baseAnM (m : String) : Except String Anomalies :=
      let o : Opts := { base with models := some [m] }
      analyze2 c o h (additionalGraphs o)
    for m in c.models do
      match verdictOf base baseAnM m, verdictOf opts anM m with
      | .ok b, .ok f =>
        let sv := specVerdict isA m
        if b != .false_ && f == .false_ && sv == .sat && !skip "fix:new-false-positive" then
          out := out.push ("fix:new-false-positive", s!"{m}: Elle as written {b.str}, fixed invalid; an interpretation satisfies it")
        if b == .false_ && f != .false_ && sv == .unsat && !skip "fix:regression" then
          out := out.push ("fix:regression", s!"{m}: Elle as written invalid, fixed {f.str}; specification {sv.str}")
        if b == .false_ && f != .false_ && sv == .sat && !skip "fix:drops-false-positive" then
          out := out.push ("fix:drops-false-positive", s!"{m}: Elle as written invalid, fixed {f.str}; an interpretation satisfies it")
        if b != .false_ && f == .false_ && sv == .unsat && !skip "fix:caught" then
          out := out.push ("fix:caught", s!"{m}: Elle as written {b.str}, fixed invalid; every interpretation violates it")
      | .ok _, .error e => if !skip "fix:throws" then out := out.push ("fix:throws", s!"{m}: the fixed Elle throws {e}")
      | _, _ => pure ()
  -- 3. cyclic versions
  if !skip "claim" then
    if let .ok m := aN then
      if (m.lookup "cyclic-versions").isSome then
        if let some bad := isA.head? then
          out := out.push ("claim:cyclic-versions",
            s!"Elle reports cyclic-versions; an interpretation satisfies the options' assumption: order {bad.order}, reads {bad.reads}")
  -- distinct property names, first detail kept
  return out.toList.foldl (fun acc (p, d) => if acc.any (·.1 == p) then acc else acc ++ [(p, d)]) []

end Elle.Props3
