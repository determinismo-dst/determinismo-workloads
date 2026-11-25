import Elle
import Elle.Props
import Elle.Cases
import Elle.GenCP
import Elle.Monotonic
import Elle.Props2
import Elle.Folds
import Elle.Boundary
import Elle.ServiceProps
import Elle.CPSpec

/-!
# Searches

    lake exe elle-search exhaust la txns=3 keys=1 ... [runs=N] [out=results/NAME]
    lake exe elle-search explore rr seeds=N first=S ...

Every timeline is checked against every property; the first counterexample of each property is
kept, shrunk (determinismo's `shrink`), and written out with its tape and its history as EDN
(a case file real Elle's runner reads).
-/

open Elle Elle.Props Elle.Gen Determinismo

def parseBool (s : String) : Bool := s == "1" || s == "true"

def applyArg (c : Props.Config) (kv : String) : Props.Config :=
  match kv.splitOn "=" with
  | [k, v] =>
    let n := v.toNat?.getD 0
    let b := c.bounds
    match k with
    | "txns" => { c with bounds := { b with maxTxns := n } }
    | "mintxns" => { c with bounds := { b with minTxns := n } }
    | "mops" => { c with bounds := { b with maxMops := n } }
    | "keys" => { c with bounds := { b with keys := n } }
    | "threads" => { c with bounds := { b with threads := n } }
    | "maxread" => { c with bounds := { b with maxRead := n } }
    | "fail" => { c with bounds := { b with fail := parseBool v } }
    | "info" => { c with bounds := { b with info := parseBool v } }
    | "interleave" => { c with bounds := { b with interleave := parseBool v } }
    | "garbage" => { c with bounds := { b with garbage := parseBool v } }
    | "read" => { c with bounds := { b with readMode := if v == "cuts" then .cuts else .any } }
    | "skip" => { c with skip := c.skip ++ (v.splitOn ",").filter (· != "") }
    | "pairs" => { c with pairs := parseBool v }
    | "observed" => { c with observed := parseBool v }
    | "singlereads" => { c with singleReads := parseBool v }
    | "models" => { c with models := (v.splitOn ",").filter (· != "") }
    | _ => c
  | _ => c

def argNat (args : List String) (k : String) (d : Nat) : Nat :=
  (args.findSome? fun a => match a.splitOn "=" with
    | [k', v] => if k' == k then v.toNat? else none
    | _ => none).getD d

def argStr (args : List String) (k : String) (d : String) : String :=
  (args.findSome? fun a => match a.splitOn "=" with
    | [k', v] => if k' == k then some v else none
    | _ => none).getD d

structure Kept where
  property : String
  detail : String
  taken : Array Taken
  runs : Nat

def caseEdn (c : Props.Config) (id : Nat) (h : History) (models : List String) : String :=
  let wl := if c.bounds.workload == .listAppend then ":list-append" else ":rw-register"
  let ms := " ".intercalate (models.map (":" ++ ·))
  s!"\{:id {id} :workload {wl} :opts \{:consistency-models [{ms}]}\n :history {ednHistory h}}"

def modelsOf (property : String) : List String :=
  match property.splitOn ":" with
  | [_, m] => if Spec.specModels.contains m then [m] else ["strict-serializable"]
  | _ => ["strict-serializable"]

def applyArg2 (c : Props2.Config2) (kv : String) : Props2.Config2 :=
  match kv.splitOn "=" with
  | [k, v] =>
    let b := parseBool v
    match k with
    | "lin" => { c with lin := b }
    | "seq" => { c with seq := b }
    | "wfr" => { c with wfr := b }
    | "order" => { c with order := b }
    | "perkey" => { c with perKey := b }
    | "timeouts" => { c with timeouts := b }
    | "singlereads" => { c with singleReads := b }
    | "noinforeads" => { c with noInfoReads := b }
    | "ordernoinfo" => { c with orderNoInfo := b }
    | "fixd3" => { c with fixD3 := b }
    | "fixd13" => { c with fixD13 := b }
    | "skip" => { c with skip := c.skip ++ (v.splitOn ",").filter (· != "") }
    | "models" => { c with models := (v.splitOn ",").filter (· != "") }
    | _ =>
      let c1 := applyArg { bounds := c.bounds } kv
      { c with bounds := c1.bounds }
  | _ => c

def optsEdn (c : Props2.Config2) (ord : Option (List (Nat × Int))) (models : List String) : String :=
  let ms := " ".intercalate (models.map (":" ++ ·))
  let o := match ord with
    | some l => s!" :transaction-order \{{" ".intercalate (l.map fun ((i, n) : Nat × Int) => s!"{i} {n}")}}"
    | none => ""
  s!"\{:consistency-models [{ms}]{if c.lin then " :linearizable-keys? true" else ""}{if c.seq then " :sequential-keys? true" else ""}{if c.wfr then " :wfr-keys? true" else ""}{o}}"

def caseEdn2 (c : Props2.Config2) (id : Nat) (h : History) (ord : Option (List (Nat × Int))) (models : List String) : String :=
  let wl := if c.bounds.workload == .listAppend then ":list-append" else ":rw-register"
  let wl := if c.perKey then wl ++ " :per-key true" else wl
  s!"\{:id {id} :workload {wl} :opts {optsEdn c ord models}\n :history {ednHistory h}}"

def modelsOf2 (property : String) : List String :=
  match property.splitOn ":" with
  | [_, m] => if Spec.specModels.contains m then [m] else ["strict-serializable"]
  | _ => ["strict-serializable"]

/-- Round 2's differential test: replica results beside cases for real Elle, one per (seed, option
set, model). Option sets: each option alone and with `:wfr-keys?`. -/
def diff2 (wl : String) (args : List String) : IO UInt32 := do
  let base : Props2.Config2 := { bounds := { workload := if wl == "rr" then .register else .listAppend } }
  let c0 := args.foldl applyArg2 base
  let out := argStr args "out" s!"scratch/diff2-{wl}"
  let seeds := argNat args "seeds" 100
  let first := argNat args "first" 0
  let combos : List Props2.Config2 :=
    [{ c0 with lin := true }, { c0 with seq := true }, { c0 with order := true },
     { c0 with lin := true, wfr := true }, { c0 with seq := true, wfr := true },
     { c0 with order := true, wfr := true }, { c0 with lin := true, seq := true, order := true, wfr := true }]
  let combos := if argNat args "timeouts" 0 == 1 then [c0] else combos
  let models := ["strict-serializable", "serializable", "snapshot-isolation", "repeatable-read",
                 "read-committed", "read-uncommitted", "strong-session-serializable"]
  let mut cases : List String := []
  let mut mine : List String := []
  for i in List.range seeds do
    let mut j := 0
    for c in combos do
      let d : Decisions := { source := Source.seeded ((first + i) * 31 + j), limit := 400 }
      let gen : W (History × Option (List (Nat × Int))) := do
        let h ← genHistory c.bounds
        let ord ← if c.order then (do pure (some (← Props2.genOrder h))) else pure none
        pure (h, ord)
      match gen.run d with
      | .ok (h, ord) _ =>
        for m in models do
          let id := ((first + i) * 10 + j) * 10 + (models.findIdx? (· == m)).getD 0
          cases := cases ++ [caseEdn2 c id h ord [m]]
          let opts : Opts := { Props2.optsOf c ord with models := some [m] }
          let o := if c.bounds.workload == .listAppend then ListAppend.check opts h else RwRegister.check opts h
          let line := match o with
            | .result r => s!"\{:id {id} :valid? {r.valid.str} :anomaly-types [{" ".intercalate (r.anomalyTypes.map fun t => "\"" ++ t ++ "\"")}]}"
            | .thrown e => s!"\{:id {id} :error \"{e}\"}"
          mine := mine ++ [line]
      | .error _ _ => pure ()
      j := j + 1
  IO.FS.writeFile (out ++ ".cases.edn") ("[" ++ "\n".intercalate cases ++ "]\n")
  IO.FS.writeFile (out ++ ".replica.edn") ("\n".intercalate mine ++ "\n")
  IO.println s!"wrote {cases.length} cases"
  return 0

/-- Round 2: `exhaust2`/`explore2 rr|la key=value ...`. -/
def search2 (mode : String) (wl : String) (args : List String) : IO UInt32 := do
  let base : Props2.Config2 := { bounds := { workload := if wl == "rr" then .register else .listAppend } }
  let c := args.foldl applyArg2 base
  let out := argStr args "out" s!"results/{mode}-{wl}"
  let maxRuns := argNat args "runs" 1000000
  let seeds := argNat args "seeds" 1000
  let first := argNat args "first" 0
  let budgetMs := (argNat args "secs" 1700) * 1000
  let pre : Array Nat := ((argStr args "prefix" "").splitOn ".").filterMap (·.toNat?) |>.toArray
  let t0 ← IO.monoMsNow
  let mut kept : List Kept := []
  let mut stats : List (String × Nat) := []
  let mut runs := 0
  let mut checked := 0
  let mut complete := false
  let mut path : Array Nat := pre
  let mut go := true
  let mut i := 0
  while go && runs < maxRuns do
    if runs % 500 == 0 then
      let now ← IO.monoMsNow
      if now - t0 > budgetMs then go := false; break
      if runs % 20000 == 0 && runs > 0 then
        IO.println s!"  ... {runs} timelines, {(now - t0) / 1000}s"
        (← IO.getStdout).flush
    let src := if mode == "exhaust2" then Source.path path else Source.seeded (first + i)
    if mode != "exhaust2" && i ≥ seeds then go := false; break
    let (o, hx) := Props2.runOnce2 c src
    if hx.isSome then checked := checked + 1
    runs := runs + 1
    i := i + 1
    if let some (p, d) := o.violation then
      stats := amUpdate stats p 0 (· + 1)
      if !(kept.any (·.property == p)) then
        kept := kept ++ [{ property := p, detail := d, taken := o.taken, runs }]
        IO.println s!"[{runs}] {p}: {d}"
        (← IO.getStdout).flush
    if mode == "exhaust2" then
      match nextPath o.taken with
      | none => complete := true; go := false
      | some p =>
        if p.extract 0 pre.size != pre then complete := true; go := false
        else path := p
  let t1 ← IO.monoMsNow
  IO.println s!"{mode} {wl}: {runs} timelines{if complete then " (complete: every timeline within the bounds)" else ""}, {checked} histories, {kept.length} properties broken, {(t1 - t0) / 1000}s"
  for (p, n) in stats do IO.println s!"  {p}: {n} timelines"
  let mut report := s!"# {mode} {wl} {" ".intercalate args}\n{runs} timelines{if complete then " (complete)" else ""}, {checked} histories\n\n"
  let mut cases : List String := []
  let mut id := 0
  for k in kept do
    let cx : Counterexample := { taken := k.taken, property := k.property, detail := k.detail, runs := k.runs }
    let runP (src : Source) : Ended :=
      let e := Props2.run2 c src
      match e.violation with
      | some (p, _) => if p == k.property then e else { e with violation := none }
      | none => e
    let small := shrink runP cx 3000
    let (_, hx) := Props2.runOnce2 c (Source.path small.values)
    let (hs, ordS) := match hx with
      | some (h, ord) => (ednHistory h, match ord with | some l => s!"\ntransaction order: {l}" | none => "")
      | none => ("?", "")
    report := report ++ s!"## {k.property}\n{small.detail}\n\nhistory:\n{hs}{ordS}\n\ntape:\n{tape small.taken}\n\n"
    if let some (h, ord) := hx then
      cases := cases ++ [caseEdn2 c id h ord (modelsOf2 k.property)]
      id := id + 1
  IO.FS.writeFile (out ++ ".txt") report
  IO.FS.writeFile (out ++ ".cases.edn") ("[" ++ "\n".intercalate cases ++ "]\n")
  IO.println s!"wrote {out}.txt and {out}.cases.edn"
  return 0

def main (argv : List String) : IO UInt32 := do
  let mode := argv.headD "explore"
  let wl := (argv.drop 1).headD "la"
  let args := argv.drop 2
  if mode == "exhaust2" || mode == "explore2" then return ← search2 mode wl args
  if mode == "diff2" then return ← diff2 wl args
  if mode == "folds" then
    let base : Props2.Config2 := { bounds := { workload := if wl == "rr" then .register else .listAppend } }
    let c := args.foldl applyArg2 base
    let mal := argNat args "malform" 0 == 1
    let gen : W History := do
      let h ← genHistory c.bounds
      if mal then Folds.malform h else pure h
    let runF (src : Source) : Ended :=
      match gen.run { source := src, limit := 400 } with
      | .ok h d => { taken := d.taken, violation := Folds.check h (argNat args "chunkings" 512) }
      | .error _ d => { taken := d.taken, violation := none }
    let mut kept : List (String × Counterexample) := []
    let mut stats : List (String × Nat) := []
    let seeds := argNat args "seeds" 1000
    for i in List.range seeds do
      let e := runF (Source.seeded (argNat args "first" 0 + i))
      if let some (p, d) := e.violation then
        stats := amUpdate stats p 0 (· + 1)
        if (kept.lookup p).isNone then kept := kept ++ [(p, { taken := e.taken, property := p, detail := d, runs := i + 1 })]
    IO.println s!"folds {wl}: {seeds} histories{if mal then " (malformed)" else ""}, {kept.length} folds differ"
    for (p, n) in stats do IO.println s!"  {p}: {n}"
    for (p, cx) in kept do
      let runP (src : Source) : Ended :=
        let e := runF src
        match e.violation with
        | some (q, _) => if q == p then e else { e with violation := none }
        | none => e
      let small := shrink runP cx 2000
      match gen.run { source := Source.path small.values, limit := 400 } with
      | .ok h _ => IO.println s!"## {p}
{small.detail}
{ednHistory h}
"
      | .error _ _ => pure ()
    return 0
  if mode == "boundary" then
    let singles := dedup (Model.allAnomalyNames.map fun a => Model.anomaliesToImpossibleModels [a])
    IO.println s!"anomaly names: {Model.allAnomalyNames.length}; distinct singleton impossible sets: {singles.length}; models: {Model.allModelNames.length}"
    let (n, bad) := Boundary.checkAll
    IO.println s!"distinct impossible-model unions: {n}; failing a definition: {bad.length}"
    for (w, e) in bad.take 20 do IO.println s!"  {w}: {e}"
    return 0
  if mode == "svcdiff" then
    -- cases for the real service beside real Elle, and the replica's answers
    let seeds := argNat args "seeds" 50
    let first := argNat args "first" 0
    let out := argStr args "out" "scratch/r2/svc/sd"
    let mut cases : List String := []
    let mut mine : List String := []
    let ansLine (id : Nat) (a : Except String Service.Answer) : String :=
      match a with
      | .ok a => s!"\{:id {id} :valid {a.valid.str} :types [{" ".intercalate (a.types.map fun t => "\"" ++ t ++ "\"")}] :not [{" ".intercalate (a.not_.map fun t => "\"" ++ t ++ "\"")}]}"
      | .error e => s!"\{:id {id} :error \"{ServiceProps.ednEscape e}\"}"
    for i in List.range seeds do
      for kind in [0, 1, 2] do
        let d : Decisions := { source := Source.seeded ((first + i) * 7 + kind), limit := 400 }
        let bounds : Bounds := { workload := if kind == 0 then .listAppend else .register, maxTxns := 5,
                                 maxMops := 3, keys := 2, threads := 3, readMode := .cuts }
        let gen : W (History × List Op × List Op) := do
          if kind == 2 then
            let h ← GenCP.genHistory 4 4 2
            pure (h, h.toList, h.toList)
          else
            let h ← genHistory bounds
            let (opened, _) ← ServiceProps.genOpen h
            let dupd ← if kind == 0 then ServiceProps.genDup h.toList else pure h.toList
            pure (h, opened, dupd)
        let .ok (h, opened, dupd) _ := gen.run d | continue
        let model := match kind with | 0 => "list-append" | 1 => "rw-register" | _ => "closed-predicate"
        let sm : Service.Model := match kind with | 0 => .listAppend | 1 => .register | _ => .closedPredicate
        let edn (x : History) : String := if kind == 2 then GenCP.ednHistory x else ednHistory x
        let variants : List (String × Bool × List Op × Bool) :=
          (["strict-serializable", "serializable", "snapshot-isolation", "read-committed"].map fun m => (m, false, h.toList, true)) ++
          [("strict-serializable-per-key", false, h.toList, false), ("serializable", false, opened, false),
           ("strict-serializable", false, dupd, false)] ++
          (if kind == 1 then [("strict-serializable", true, h.toList, true), ("serializable", true, h.toList, true)] else [])
        let mut j := 0
        for (cons, lk, ops, withElle) in variants do
          let id := ((first + i) * 3 + kind) * 20 + j
          let body := "\n".intercalate (ops.map ServiceProps.jsonOp)
          let hist := if withElle then edn h else "nil"
          cases := cases ++ [s!"\{:id {id} :model \"{model}\" :consistency \"{cons}\" :lk {lk} :body \"{ServiceProps.ednEscape body}\"\n :history {hist}}"]
          mine := mine ++ [ansLine id (Service.check sm cons lk ops)]
          j := j + 1
    IO.FS.writeFile (out ++ ".cases.edn") ("[" ++ "\n".intercalate cases ++ "]\n")
    IO.FS.writeFile (out ++ ".replica.edn") ("\n".intercalate mine ++ "\n")
    IO.println s!"wrote {cases.length} cases"
    return 0
  if mode == "svcprops" then
    let base : Props2.Config2 := { bounds := { workload := if wl == "rr" then .register else .listAppend } }
    let c := args.foldl applyArg2 base
    let seeds := argNat args "seeds" 1000
    let mut kept : List (String × Counterexample) := []
    let mut stats : List (String × Nat) := []
    for i in List.range seeds do
      let (e, _) := ServiceProps.runOnce3 c (Source.seeded (argNat args "first" 0 + i))
      if let some (p, d) := e.violation then
        stats := amUpdate stats p 0 (· + 1)
        if (kept.lookup p).isNone then
          kept := kept ++ [(p, { taken := e.taken, property := p, detail := d, runs := i + 1 })]
          IO.println s!"[{i}] {p}: {d}"
          (← IO.getStdout).flush
    IO.println s!"svcprops {wl}: {seeds} histories, {kept.length} properties broken"
    for (p, n) in stats do IO.println s!"  {p}: {n}"
    let mut report := ""
    for (p, cx) in kept do
      let runP (src : Source) : Ended :=
        let e := (ServiceProps.runOnce3 c src).1
        match e.violation with
        | some (q, _) => if q == p then e else { e with violation := none }
        | none => e
      let small := shrink runP cx 2000
      match (ServiceProps.runOnce3 c (Source.path small.values)).2 with
      | some g =>
        report := report ++ s!"## {p}\n{small.detail}\n\nhistory:\n{ednHistory g.h}\nopened:\n{ednHistory g.opened.toArray}\nwith a duplicate:\n{ednHistory g.dupd.toArray}\n\n"
      | none => pure ()
    IO.FS.writeFile (argStr args "out" "scratch/r2/svcprops" ++ ".txt") report
    return 0
  if mode == "pkcase" then
    IO.println ServiceProps.perKeyReport
    IO.println (String.intercalate "\n" (ServiceProps.perKeyParts.map ServiceProps.jsonOp))
    return 0
  if mode == "cpfix" then
    let f : CPSpec.Fixes := { versionsAfter := argNat args "va" 0 == 1, versionLt := argNat args "vlt" 0 == 1,
                              write := argNat args "w" 0 == 1 }
    let models := ((argStr args "models" "").splitOn ",").filter (· != "")
    let models := if models.isEmpty then Spec.specModels else models
    let keys := argNat args "keys" 3
    let txns := argNat args "txns" 4
    let threads := argNat args "threads" 2
    -- misses: an :ok predicate read's rows emptied (a predicate read that missed what it must
    -- have seen: version-set's unborn fallback, closed_predicate.clj:393-403)
    let misses := argNat args "misses" 0 == 1
    let genM : W History := do
      let h ← GenCP.genHistory keys txns threads
      if !misses then return h
      let mut out : Array Op := #[]
      for o in h do
        if o.isOk && o.value.any (·.f == .rp) && (← decideRare (σ := Decisions) "rp.miss" 1 3) then
          out := out.push { o with value := o.value.map fun m => if m.f == .rp then { m with v := .kmap [] } else m }
        else out := out.push o
      return out
    let runF (src : Source) : Ended :=
      match genM.run { source := src, limit := 400 } with
      | .ok h d => { taken := d.taken, violation := CPSpec.check f h models }
      | .error _ d => { taken := d.taken, violation := none }
    let seeds := argNat args "seeds" 1000
    let mut kept : List (String × Counterexample) := []
    let mut stats : List (String × Nat) := []
    for i in List.range seeds do
      let e := runF (Source.seeded (argNat args "first" 0 + i))
      if let some (p, d) := e.violation then
        stats := amUpdate stats p 0 (· + 1)
        if (kept.lookup p).isNone then kept := kept ++ [(p, { taken := e.taken, property := p, detail := d, runs := i + 1 })]
    IO.println s!"cpfix va={f.versionsAfter} vlt={f.versionLt} w={f.write}: {seeds} histories, {kept.length} properties broken"
    for (p, n) in stats do IO.println s!"  {p}: {n}"
    for (p, cx) in kept do
      let runP (src : Source) : Ended :=
        let e := runF src
        match e.violation with
        | some (q, _) => if q == p then e else { e with violation := none }
        | none => e
      let small := shrink runP cx 2000
      match genM.run { source := Source.path small.values, limit := 400 } with
      | .ok h _ => IO.println s!"## {p}\n{small.detail}\n{GenCP.ednHistory h}\n"
      | .error _ _ => pure ()
    return 0
  if mode == "tstat" then
    let base : Props2.Config2 := { bounds := { workload := if wl == "rr" then .register else .listAppend } }
    let c := args.foldl applyArg2 base
    for (k, n) in Props2.timeoutStats c (argNat args "seeds" 100) (argNat args "first" 0) do
      IO.println s!"{k}: {n}"
    return 0
  let base : Props.Config := { bounds := { workload := if wl == "rr" then .register else .listAppend } }
  let c := args.foldl applyArg base
  let c := if mode == "exhaust" then { c with rankDecided := false } else c
  let out := argStr args "out" s!"results/{mode}-{wl}"
  let maxRuns := argNat args "runs" 1000000
  let seeds := argNat args "seeds" 1000
  let first := argNat args "first" 0
  if mode == "mono" then
    let mut cases : List String := []
    let mut mine : List String := []
    let mut disagree := 0
    let mut checked := 0
    for i in List.range seeds do
      let d : Decisions := { source := Source.seeded (first + i), limit := 400 }
      match (Elle.Monotonic.genHistory 5 2 3 2).run d with
      | .ok h _ =>
        for rt in [false, true] do
          let id := (first + i) * 10 + (if rt then 1 else 0)
          let r := Elle.Monotonic.check h rt
          let sp := Elle.Monotonic.spec h rt
          checked := checked + 1
          if r != sp then
            disagree := disagree + 1
            IO.println s!"disagreement (realtime {rt}): replica {r}, specification {sp}\n{" ".intercalate (h.toList.map Elle.Monotonic.ednOp)}"
          let wl := if rt then ":monotonic-realtime" else ":monotonic"
          cases := cases ++ [s!"\{:id {id} :workload {wl} :opts \{} :history [{"\n ".intercalate (h.toList.map Elle.Monotonic.ednOp)}]}"]
          mine := mine ++ [s!"\{:id {id} :valid? {r} :anomaly-types []}"]
      | .error _ _ => pure ()
    IO.FS.writeFile (out ++ ".cases.edn") ("[" ++ "\n".intercalate cases ++ "]\n")
    IO.FS.writeFile (out ++ ".replica.edn") ("\n".intercalate mine ++ "\n")
    IO.println s!"monotonic: {checked} checks against the specification, {disagree} disagreements; wrote {cases.length} cases"
    return 0
  if mode == "diffcp" then
    let sets : List (List String) := (Spec.specModels.map fun m => [m]) ++ [["strict-serializable"]]
    let mut cases : List String := []
    let mut mine : List String := []
    for i in List.range seeds do
      let d : Decisions := { source := Source.seeded (first + i), limit := 400 }
      match (Elle.GenCP.genHistory 4 4 2).run d with
      | .ok h _ =>
        let mut j := 0
        for ms in sets do
          let id := (first + i) * 100 + j
          let msE := " ".intercalate (ms.map (":" ++ ·))
          cases := cases ++ [s!"\{:id {id} :workload :closed-predicate :opts \{:consistency-models [{msE}]}\n :history {Elle.GenCP.ednHistory h}}"]
          let line := match ClosedPredicate.check { models := some ms } h with
            | .result r => s!"\{:id {id} :valid? {r.valid.str} :anomaly-types [{" ".intercalate (r.anomalyTypes.map fun t => "\"" ++ t ++ "\"")}]}"
            | .thrown e => s!"\{:id {id} :error \"{e}\"}"
          mine := mine ++ [line]
          j := j + 1
      | .error _ _ => pure ()
    IO.FS.writeFile (out ++ ".cases.edn") ("[" ++ "\n".intercalate cases ++ "]\n")
    IO.FS.writeFile (out ++ ".replica.edn") ("\n".intercalate mine ++ "\n")
    IO.println s!"wrote {cases.length} cases"
    return 0
  if mode == "cases" then
    let mut edn : List String := []
    let mut id := 0
    for cs in Elle.Cases.cases do
      let cfg : Props.Config := { bounds := { workload := cs.workload } }
      IO.println s!"## {cs.name}: {cs.note}"
      IO.println (ednHistory cs.h)
      let is := Props.interps cfg cs.h
      IO.println s!"  interpretations: {is.length}, clean: {(is.filter (·.clean)).length}"
      for ms in cs.models do
        let opts : Opts := { models := some ms }
        let o := if cs.workload == .listAppend then ListAppend.check opts cs.h else RwRegister.check opts cs.h
        let rep := match o with
          | .result r => s!"{r.valid.str} {r.anomalyTypes}"
          | .thrown e => s!"throws {e}"
        let sv := ms.map fun m => s!"{m}: {(Spec.verdict is m).str}"
        IO.println s!"  {ms}: replica {rep}; specification {sv}"
        edn := edn ++ [caseEdn cfg id cs.h ms]
        id := id + 1
    IO.FS.writeFile (out ++ ".cases.edn") ("[" ++ "\n".intercalate edn ++ "]\n")
    return 0
  if mode == "diff" then
    -- Replica results beside cases for real Elle: one case per (seed, model set).
    let sets : List (List String) := (Spec.specModels.map fun m => [m]) ++ [["strict-serializable"],
      ["strong-session-snapshot-isolation", "strong-read-uncommitted"],
      ["strong-session-serializable", "strong-read-uncommitted"]]
    let mut cases : List String := []
    let mut mine : List String := []
    for i in List.range seeds do
      let d : Decisions := { source := Source.seeded (first + i), limit := 400 }
      match (genHistory c.bounds).run d with
      | .ok h _ =>
        let mut j := 0
        for ms in sets do
          let id := (first + i) * 100 + j
          let e := caseEdn c id h ms
          let e := if argNat args "wfr" 0 == 1 then e.replace ":opts {" ":opts {:wfr-keys? true " else e
          cases := cases ++ [e]
          let opts : Opts := { models := some ms, wfrKeys := argNat args "wfr" 0 == 1 }
          let o := if c.bounds.workload == .listAppend then ListAppend.check opts h else RwRegister.check opts h
          let line := match o with
            | .result r => s!"\{:id {id} :valid? {r.valid.str} :anomaly-types [{" ".intercalate (r.anomalyTypes.map fun t => "\"" ++ t ++ "\"")}]}"
            | .thrown e => s!"\{:id {id} :error \"{e}\"}"
          mine := mine ++ [line]
          j := j + 1
      | .error _ _ => pure ()
    IO.FS.writeFile (out ++ ".cases.edn") ("[" ++ "\n".intercalate cases ++ "]\n")
    IO.FS.writeFile (out ++ ".replica.edn") ("\n".intercalate mine ++ "\n")
    IO.println s!"wrote {cases.length} cases"
    return 0
  let t0 ← IO.monoMsNow
  let mut kept : List Kept := []
  let mut runs := 0
  let mut complete := false
  let mut stats : List (String × Nat) := []
  let mut inScope := 0
  let budgetMs := (argNat args "secs" 1700) * 1000
  let dry := argNat args "dry" 0 == 1
  -- prefix=a.b.c: exhaust only the subtree under these first decisions
  let pre : Array Nat := ((argStr args "prefix" "").splitOn ".").filterMap (·.toNat?) |>.toArray
  if mode == "exhaust" then
    let mut path : Array Nat := pre
    let mut go := true
    while go && runs < maxRuns do
      if runs % 2000 == 0 then
        let now ← IO.monoMsNow
        if now - t0 > budgetMs then go := false; break
        if runs % 100000 == 0 && runs > 0 then
          IO.println s!"  ... {runs} timelines, {(now - t0) / 1000}s"
          (← IO.getStdout).flush
      let mut o : Ended := { taken := #[], violation := none }
      if dry then
        let d : Decisions := { source := Source.path path, limit := 400 }
        match (genHistory c.bounds).run d with
        | .ok _ d' => o := { taken := d'.taken, violation := none }
        | .error _ d' => o := { taken := d'.taken, violation := none }
      else
        let (e, h?) := runOnce c (Source.path path)
        if let some h := h? then
          if !c.observed || allObserved h then inScope := inScope + 1
        o := e
      runs := runs + 1
      if let some (p, d) := o.violation then
        stats := amUpdate stats p 0 (· + 1)
        if !(kept.any (·.property == p)) then
          kept := kept ++ [{ property := p, detail := d, taken := o.taken, runs }]
          IO.println s!"[{runs}] {p}: {d}"
      match nextPath o.taken with
      | none => complete := true; go := false
      | some p =>
        if p.extract 0 pre.size != pre then complete := true; go := false
        else path := p
  else
    for i in List.range seeds do
      let (o, h?) := runOnce c (Source.seeded (first + i))
      if let some h := h? then
        if !c.observed || allObserved h then inScope := inScope + 1
      runs := runs + 1
      if let some (p, d) := o.violation then
        stats := amUpdate stats p 0 (· + 1)
        if !(kept.any (·.property == p)) then
          kept := kept ++ [{ property := p, detail := d, taken := o.taken, runs }]
          IO.println s!"[seed {first + i}] {p}: {d}"
  let t1 ← IO.monoMsNow
  IO.println s!"{mode} {wl}: {runs} timelines{if complete then " (complete: every timeline within the bounds)" else ""}, {inScope} histories checked, {kept.length} properties broken, {(t1 - t0) / 1000}s"
  for (p, n) in stats do IO.println s!"  {p}: {n} timelines"
  -- shrink and write each
  let mut report := s!"# {mode} {wl} {" ".intercalate args}\n{runs} timelines{if complete then " (complete)" else ""}, {inScope} histories checked\n\n"
  let mut cases : List String := []
  let mut id := 0
  for k in kept do
    let cx : Counterexample := { taken := k.taken, property := k.property, detail := k.detail, runs := k.runs }
    let runP (src : Source) : Ended :=
      let e := run c src
      match e.violation with
      | some (p, d) => if p == k.property then e else { e with violation := none } |> fun e' => if p == k.property then e else e'
      | none => e
    let small := shrink runP cx 3000
    let (_, h?) := runOnce c (Source.path small.values)
    let hs := match h? with | some h => ednHistory h | none => "?"
    report := report ++ s!"## {k.property}\n{small.detail}\n\nhistory:\n{hs}\n\ntape:\n{tape small.taken}\n\n"
    if let some h := h? then
      cases := cases ++ [caseEdn c id h (modelsOf k.property)]
      id := id + 1
  IO.FS.writeFile (out ++ ".txt") report
  IO.FS.writeFile (out ++ ".cases.edn") ("[" ++ "\n".intercalate cases ++ "]\n")
  IO.println s!"wrote {out}.txt and {out}.cases.edn"
  return 0
