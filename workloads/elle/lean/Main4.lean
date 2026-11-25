import Elle
import Elle.Props
import Elle.Cases
import Elle.GenCP
import Elle.Props2
import Elle.ServiceProps
import Elle.CPSpec
import Elle.Props3
import Elle.Round3

/-!
# Round 3's searches

    elle-r4 exhaust3 la|rr key=value ... [prefix=a.b.c] [dry=1] [out=results/r3/NAME]
    elle-r4 explore3 la|rr seeds=N first=S ...

As round 2's `exhaust2`/`explore2` (the same configuration, properties and generator), with two
changes: every property a timeline breaks is counted, not only its first (`Props3.checkAll2`,
round 2's checks without their early returns; the cut-point checks of `timeouts=1` are not in
it), and `dry=1` counts the timelines under a
prefix without checking them (to split a space into segments under the job limit).
-/

open Elle Elle.Props Elle.Gen Determinismo

def parseBool (s : String) : Bool := s == "1" || s == "true"

def argNat (args : List String) (k : String) (d : Nat) : Nat :=
  (args.findSome? fun a => match a.splitOn "=" with
    | [k', v] => if k' == k then v.toNat? else none
    | _ => none).getD d

def argStr (args : List String) (k : String) (d : String) : String :=
  (args.findSome? fun a => match a.splitOn "=" with
    | [k', v] => if k' == k then some v else none
    | _ => none).getD d

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
    | _ => c
  | _ => c

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

/-- Every property `check` breaks: rerun with each one found skipped, until none is left. -/
partial def allFound (check : List String → Found) (skip : List String := [])
    (acc : List (String × String) := []) : List (String × String) :=
  match check skip with
  | none => acc
  | some (p, d) => if skip.contains p then acc else allFound check (skip ++ [p]) (acc ++ [(p, d)])

def optsEdn (c : Props2.Config2) (ord : Option (List (Nat × Int))) (models : List String) : String :=
  let ms := " ".intercalate (models.map (":" ++ ·))
  let o := match ord with
    | some l => s!" :transaction-order \{{" ".intercalate (l.map fun ((i, n) : Nat × Int) => s!"{i} {n}")}}"
    | none => ""
  s!"\{:consistency-models [{ms}]{if c.lin then " :linearizable-keys? true" else ""}{if c.seq then " :sequential-keys? true" else ""}{if c.wfr then " :wfr-keys? true" else ""}{o}}"

def caseEdn2 (c : Props2.Config2) (id : Nat) (h : History) (ord : Option (List (Nat × Int))) (models : List String) : String :=
  let wl := if c.bounds.workload == .listAppend then ":list-append" else ":rw-register"
  s!"\{:id {id} :workload {wl} :opts {optsEdn c ord models}\n :history {ednHistory h}}"

def modelsOf2 (property : String) : List String :=
  let ms := (property.splitOn ":").filter Spec.specModels.contains
  if ms.isEmpty then ["strict-serializable"] else ms.take 1

structure Kept where
  property : String
  detail : String
  taken : Array Taken
  runs : Nat

/-- Round 2's configuration, every property counted. -/
def search3 (mode : String) (wl : String) (args : List String) : IO UInt32 := do
  let base : Props2.Config2 := { bounds := { workload := if wl == "rr" then .register else .listAppend } }
  let c := args.foldl applyArg2 base
  let out := argStr args "out" s!"results/r3/{mode}-{wl}"
  let maxRuns := argNat args "runs" 1000000000
  let seeds := argNat args "seeds" 1000
  let first := argNat args "first" 0
  let budgetMs := (argNat args "secs" 1700) * 1000
  let dry := argNat args "dry" 0 == 1
  let pre : Array Nat := ((argStr args "prefix" "").splitOn ".").filterMap (·.toNat?) |>.toArray
  let gen : W (History × Option (List (Nat × Int))) := do
    let h ← genHistory c.bounds
    let ord ← if c.order then (do pure (some (← Props2.genOrder h c.orderNoInfo))) else pure none
    pure (h, ord)
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
    let src := if mode == "exhaust3" then Source.path path else Source.seeded (first + i)
    if mode != "exhaust3" && i ≥ seeds then go := false; break
    let d : Decisions := { source := src, limit := 400 }
    let (taken, found) := match gen.run d with
      | .ok (h, ord) d' =>
        (d'.taken, if dry then [] else Props3.checkAll2 c h ord)
      | .error _ d' => (d'.taken, [])
    if !dry then
      if let .ok _ _ := gen.run d then checked := checked + 1
    runs := runs + 1
    i := i + 1
    for (p, det) in found do
      stats := amUpdate stats p 0 (· + 1)
      if !(kept.any (·.property == p)) then
        kept := kept ++ [{ property := p, detail := det, taken, runs }]
        IO.println s!"[{runs}] {p}: {det}"
        (← IO.getStdout).flush
    if mode == "exhaust3" then
      match nextPath taken with
      | none => complete := true; go := false
      | some p =>
        if p.extract 0 pre.size != pre then complete := true; go := false
        else path := p
  let t1 ← IO.monoMsNow
  IO.println s!"{mode} {wl}: {runs} timelines{if complete then " (complete: every timeline within the bounds)" else ""}, {checked} histories, {kept.length} properties broken, {(t1 - t0) / 1000}s"
  for (p, n) in stats do IO.println s!"  {p}: {n} timelines"
  if dry then return 0
  let mut report := s!"# {mode} {wl} {" ".intercalate args}\n{runs} timelines{if complete then " (complete)" else ""}, {checked} histories\n\n"
  for (p, n) in stats do report := report ++ s!"- {p}: {n} timelines\n"
  report := report ++ "\n"
  let mut cases : List String := []
  let mut id := 0
  for k in kept do
    let cx : Counterexample := { taken := k.taken, property := k.property, detail := k.detail, runs := k.runs }
    let runP (src : Source) : Ended :=
      match gen.run { source := src, limit := 400 } with
      | .ok (h, ord) d' =>
        let fs := Props3.checkAll2 c h ord
        { taken := d'.taken, violation := fs.find? (·.1 == k.property) }
      | .error _ d' => { taken := d'.taken, violation := none }
    let small := shrink runP cx 1500
    match gen.run { source := Source.path small.values, limit := 400 } with
    | .ok (h, ord) _ =>
      let ordS := match ord with | some l => s!"\ntransaction order: {l}" | none => ""
      report := report ++ s!"## {k.property}\n{small.detail}\n\nhistory:\n{ednHistory h}{ordS}\n\ntape:\n{tape small.taken}\n\n"
      cases := cases ++ [caseEdn2 c id h ord (modelsOf2 k.property)]
      id := id + 1
    | .error _ _ => pure ()
  IO.FS.writeFile (out ++ ".txt") report
  IO.FS.writeFile (out ++ ".cases.edn") ("[" ++ "\n".intercalate cases ++ "]\n")
  IO.println s!"wrote {out}.txt and {out}.cases.edn"
  return 0

/-! ## Round 3's own searches: the deployed service, the fixes -/

def wlModel (wl : String) : Service.Model :=
  if wl == "rr" then .register else if wl == "cp" then .closedPredicate else .listAppend

def boundsOf (wl : String) (args : List String) : Bounds :=
  let c := args.foldl applyArg { bounds := { workload := if wl == "rr" then .register else .listAppend } }
  c.bounds

def ednOf (wl : String) (h : History) : String := if wl == "cp" then GenCP.ednHistory h else ednHistory h

/-- A history (with its service variants: some processes' last ops left open, and an `:info` in
place; an `:ok` read with a value twice) from decisions. -/
structure G3 where
  h : History
  opened : List Op := []
  infoed : List Op := []
  dupd : List Op := []

def genG3 (wl : String) (args : List String) (variants : Bool) : W G3 := do
  if wl == "cp" then
    let h ← GenCP.genHistory (argNat args "keys" 3) (argNat args "txns" 4) (argNat args "threads" 2)
    if argNat args "misses" 0 == 1 then
      let mut out : Array Op := #[]
      for o in h do
        if o.isOk && o.value.any (·.f == .rp) && (← decideRare (σ := Decisions) "rp.miss" 1 3) then
          out := out.push { o with value := o.value.map fun m => if m.f == .rp then { m with v := .kmap [] } else m }
        else out := out.push o
      return { h := out }
    return { h }
  let h ← genHistory (boundsOf wl args)
  if !variants then return { h }
  let (opened, infoed) ← ServiceProps.genOpen h
  let dupd ← if wl == "la" then ServiceProps.genDup h.toList else pure h.toList
  return { h, opened, infoed, dupd }

/-- Explore (seeds) or exhaust (every timeline under `prefix`) `check` over `gen`; every property
counted; each one's first counterexample shrunk and written out. -/
def search (name : String) (wl : String) (args : List String) (gen : W G3)
    (check : G3 → List (String × String)) : IO UInt32 := do
  let exhaustive := argNat args "exhaust" 0 == 1
  let out := argStr args "out" s!"results/r3/{name}"
  let seeds := argNat args "seeds" 1000
  let first := argNat args "first" 0
  let budgetMs := (argNat args "secs" 1700) * 1000
  let pre : Array Nat := ((argStr args "prefix" "").splitOn ".").filterMap (·.toNat?) |>.toArray
  let t0 ← IO.monoMsNow
  let mut kept : List Kept := []
  let mut stats : List (String × Nat) := []
  let mut runs := 0
  let mut complete := false
  let mut path : Array Nat := pre
  let mut go := true
  while go do
    if runs % 200 == 0 then
      let now ← IO.monoMsNow
      if now - t0 > budgetMs then go := false; break
      if runs % 5000 == 0 && runs > 0 then
        IO.println s!"  ... {runs} histories, {(now - t0) / 1000}s"
        (← IO.getStdout).flush
        -- the counts so far, in case the job's time limit ends it inside one history
        let mut partialTxt := s!"# {name} {wl} {" ".intercalate args}\n{runs} histories so far ({(now - t0) / 1000}s)\n\n"
        for (p, n) in stats do partialTxt := partialTxt ++ s!"- {p}: {n}\n"
        for k in kept do partialTxt := partialTxt ++ s!"\n## {k.property} (first at history {k.runs})\n{k.detail}\n"
        IO.FS.writeFile (out ++ ".partial.txt") partialTxt
    if !exhaustive && runs ≥ seeds then go := false; break
    let src := if exhaustive then Source.path path else Source.seeded (first + runs)
    let (taken, found) := match gen.run { source := src, limit := 400 } with
      | .ok g d' => (d'.taken, check g)
      | .error _ d' => (d'.taken, [])
    runs := runs + 1
    for (p, det) in found do
      stats := amUpdate stats p 0 (· + 1)
      if !(kept.any (·.property == p)) then
        kept := kept ++ [{ property := p, detail := det, taken, runs }]
        IO.println s!"[{runs}] {p}: {det}"
        (← IO.getStdout).flush
    if exhaustive then
      match nextPath taken with
      | none => complete := true; go := false
      | some p =>
        if p.extract 0 pre.size != pre then complete := true; go := false
        else path := p
  let t1 ← IO.monoMsNow
  IO.println s!"{name} {wl}: {runs} histories{if complete then " (complete: every timeline within the bounds)" else ""}, {kept.length} properties, {(t1 - t0) / 1000}s"
  for (p, n) in stats do IO.println s!"  {p}: {n}"
  let mut report := s!"# {name} {wl} {" ".intercalate args}\n{runs} histories{if complete then " (complete)" else ""}\n\n"
  for (p, n) in stats do report := report ++ s!"- {p}: {n}\n"
  report := report ++ "\n"
  let shrinkTries := argNat args "shrink" 600
  for k in kept do
    let cx : Counterexample := { taken := k.taken, property := k.property, detail := k.detail, runs := k.runs }
    let runP (src : Source) : Ended :=
      match gen.run { source := src, limit := 400 } with
      | .ok g d' => { taken := d'.taken, violation := (check g).find? (·.1 == k.property) }
      | .error _ d' => { taken := d'.taken, violation := none }
    let small := if shrinkTries == 0 then cx else shrink runP cx shrinkTries
    match gen.run { source := Source.path small.values, limit := 400 } with
    | .ok g _ =>
      let extra := (if g.opened.length != g.h.size && !g.opened.isEmpty then s!"\nopened:\n{ednHistory g.opened.toArray}" else "") ++
        (if !(Service.duplicates g.dupd).isEmpty then s!"\nwith a duplicate:\n{ednHistory g.dupd.toArray}" else "")
      report := report ++ s!"## {k.property}\n{small.detail}\n\nhistory:\n{ednOf wl g.h}{extra}\n\ntape:\n{tape small.taken}\n\n"
    | .error _ _ => pure ()
  IO.FS.writeFile (out ++ ".txt") report
  IO.println s!"wrote {out}.txt"
  return 0

def modelsArg (args : List String) : List String :=
  let ms := ((argStr args "models" "").splitOn ",").filter (· != "")
  if ms.isEmpty then Spec.specModels else ms

def answerEdn (id : Nat) (a : Except String Service.Answer) : String :=
  match a with
  | .ok a => s!"\{:id {id} :valid {a.valid.str} :types [{" ".intercalate (a.types.map fun t => "\"" ++ t ++ "\"")}] :not [{" ".intercalate (a.not_.map fun t => "\"" ++ t ++ "\"")}]}"
  | .error e => s!"\{:id {id} :error \"{ServiceProps.ednEscape e}\"}"

def outcomeEdn (id : Nat) (o : Outcome) : String :=
  match o with
  | .result r => s!"\{:id {id} :valid? {r.valid.str} :anomaly-types [{" ".intercalate (r.anomalyTypes.map fun t => "\"" ++ t ++ "\"")}]}"
  | .thrown e => s!"\{:id {id} :error \"{ServiceProps.ednEscape e}\"}"

def round3 (mode : String) (wl : String) (args : List String) : IO UInt32 := do
  let model := wlModel wl
  let models := modelsArg args
  if mode == "deployed" then
    let gen := genG3 wl args true
    return ← search s!"deployed-{wl}" wl args gen fun g =>
      Round3.deployedProps model g.h models ++
      (if model == .closedPredicate then [] else Round3.deployedServiceProps model g.h g.opened g.infoed g.dupd models) ++
      (if argNat args "perkey" 1 == 1 then Round3.perKeyProps model g.h else [])
  if mode == "fix" then
    let names := ((argStr args "fix" "").splitOn ",").filter (· != "")
    let gen := genG3 wl args false
    let sets := Round3.modelSets models (argNat args "pairs" 0 == 1)
    let rows := names.contains "d21" || names.contains "all"
    -- base=elle: Elle 0.2.8 as the base (the fix on the deployed Elle against Elle as written)
    let baseOf : Opts := if argStr args "base" "deployed" == "elle" then {} else Service.deployedOpts
    return ← search s!"fix-{"+".intercalate names}-{wl}" wl args gen fun g =>
      Round3.fixProps model (Round3.fixOf names) g.h sets rows baseOf
  if mode == "rename" then
    let names := ((argStr args "fix" "").splitOn ",").filter (· != "")
    let gen := genG3 wl args false
    return ← search s!"rename-{"+".intercalate names}-{wl}" wl args gen fun g =>
      Round3.renameProps (Round3.fixOf names) g.h models
  if mode == "svcdiff3" then
    -- cases for the real deployed service (JSON bodies) and the replica's answers
    let seeds := argNat args "seeds" 50
    let first := argNat args "first" 0
    let out := argStr args "out" "scratch/r3/svc/sd3"
    let mut cases : List String := []
    let mut mine : List String := []
    for i in List.range seeds do
      let gen := genG3 wl args true
      let .ok g _ := gen.run { source := Source.seeded (first + i), limit := 400 } | continue
      let variants : List (String × List Op) :=
        (["strict-serializable", "serializable", "snapshot-isolation", "repeatable-read", "read-committed",
          "read-uncommitted", "strong-session-serializable", "strong-read-uncommitted"].map fun m => (m, g.h.toList)) ++
        [("strict-serializable-per-key", g.h.toList)] ++
        (if g.opened.length != g.h.size && !g.opened.isEmpty then [("serializable", g.opened)] else []) ++
        (if wl == "la" && !(Service.duplicates g.dupd).isEmpty then [("strict-serializable", g.dupd), ("serializable", g.dupd)] else [])
      let mut j := 0
      for (cons, ops) in variants do
        let lks := if wl == "rr" && j < 2 then [false, true] else [false]
        for lk in lks do
          let id := (first + i) * 40 + j * 2 + (if lk then 1 else 0)
          let body := "\n".intercalate (ops.map ServiceProps.jsonOp)
          let model := if wl == "rr" then "rw-register" else if wl == "cp" then "closed-predicate" else "list-append"
          cases := cases ++ [s!"\{:id {id} :model \"{model}\" :consistency \"{cons}\" :lk {lk} :body \"{ServiceProps.ednEscape body}\" :history nil}"]
          mine := mine ++ [answerEdn id (Service.check (wlModel wl) cons lk ops true)]
        j := j + 1
    IO.FS.writeFile (out ++ ".cases.edn") ("[" ++ "\n".intercalate cases ++ "]\n")
    IO.FS.writeFile (out ++ ".replica.edn") ("\n".intercalate mine ++ "\n")
    IO.println s!"wrote {cases.length} cases"
    return 0
  if mode == "fixdiff" then
    -- cases for real Elle (the deployed namespaces and the fix's patch ahead) and the replica's
    -- results with the fix on the deployed Elle
    let names := ((argStr args "fix" "").splitOn ",").filter (· != "")
    let seeds := argNat args "seeds" 50
    let first := argNat args "first" 0
    let out := argStr args "out" s!"scratch/r3/fixdiff-{"+".intercalate names}-{wl}"
    let sets := Round3.modelSets models (argNat args "pairs" 0 == 1)
    let mut cases : List String := []
    let mut mine : List String := []
    for i in List.range seeds do
      let gen := genG3 wl args false
      let .ok g _ := gen.run { source := Source.seeded (first + i), limit := 400 } | continue
      let mut j := 0
      for ms in sets do
        let id := (first + i) * 1000 + j
        let wlk := if wl == "rr" then ":rw-register" else if wl == "cp" then ":closed-predicate" else ":list-append"
        let msE := " ".intercalate (ms.map (":" ++ ·))
        cases := cases ++ [s!"\{:id {id} :workload {wlk} :opts \{:consistency-models [{msE}]}\n :history {ednOf wl g.h}}"]
        let o := Round3.fixOf names { Service.deployedOpts with models := some ms }
        mine := mine ++ [outcomeEdn id (Service.judge model o g.h)]
        j := j + 1
    IO.FS.writeFile (out ++ ".cases.edn") ("[" ++ "\n".intercalate cases ++ "]\n")
    IO.FS.writeFile (out ++ ".replica.edn") ("\n".intercalate mine ++ "\n")
    IO.println s!"wrote {cases.length} cases"
    return 0
  if mode == "cases3" then
    -- each fix's minimal histories: real Elle's cases, and the replica's answers, deployed and fixed
    let cs : List (String × String × History × List (List String) × List String) :=
      let byName (n : String) : History := ((Cases.cases.find? (·.name == n)).map (·.h)).getD #[]
      [("d1-unobserved-appends", "la", byName "unobserved-appends-g-single",
          [["snapshot-isolation"], ["consistent-view"], ["repeatable-read"], ["serializable"]], ["d1"]),
       ("d1-register-initial-state", "rr", byName "register-initial-state-g-single",
          [["snapshot-isolation"], ["consistent-view"]], ["d1"]),
       ("d2-realtime-replaces-process", "la", byName "realtime-replaces-process",
          [["strong-session-snapshot-isolation"], ["strong-session-snapshot-isolation", "strong-read-uncommitted"],
           ["strong-session-serializable", "strong-read-uncommitted"]], ["d2"]),
       ("d4-failed-append-hides-ww", "la", byName "failed-append-hides-ww", [["read-uncommitted"]], ["d4"]),
       ("d5-info-may-have-aborted-2txn", "la", byName "info-may-have-aborted-2txn", [["read-uncommitted"]], ["d5"]),
       ("d5-info-write-may-have-aborted", "la", byName "info-write-may-have-aborted",
          [["read-uncommitted"], ["read-committed"]], ["d5"]),
       ("d6-fuzzy-read", "rr", byName "register-fuzzy-read",
          [["repeatable-read"], ["consistent-view"], ["snapshot-isolation"], ["read-committed"]], ["d6"]),
       ("d6-second-read-g1c", "rr", byName "register-second-read-g1c", [["read-committed"], ["serializable"]], ["d6"]),
       ("d7-future-read", "rr", byName "register-future-read", [["strict-serializable"], ["read-uncommitted"]], ["d7"]),
       ("d8-garbage-read", "la", byName "list-append-garbage-read", [["strict-serializable"], ["read-uncommitted"]], ["d8"]),
       ("d12-hash-order-a", "la", byName "value-hash-order-a", [["read-uncommitted"]], ["d12"]),
       ("d12-hash-order-b", "la", byName "value-hash-order-b", [["read-uncommitted"]], ["d12"]),
       ("d20-mixed-cycle", "cp", Theorems2.cpMixed, [["repeatable-read"], ["serializable"]], ["d20"]),
       ("d21-stale-true-read", "cp", Theorems2.cpStale, [["strict-serializable"], ["serializable"]], ["d21"]),
       ("d22-info-read", "cp", Theorems2.cpInfoRead true, [["consistent-view"], ["snapshot-isolation"]], ["d22"])]
    let out := argStr args "out" "scratch/r3/cases3"
    let mut cases : List String := []
    let mut mine : List String := []
    let mut id := 0
    for (name, w, h, sets, fx) in cs do
      let model := wlModel w
      let is := match model with
        | .listAppend => Spec.interpsListAppend h
        | .register => Spec.interpsRegister h
        | .closedPredicate => []
      IO.println s!"## {name}"
      for ms in sets do
        let wlk := if w == "rr" then ":rw-register" else if w == "cp" then ":closed-predicate" else ":list-append"
        let msE := " ".intercalate (ms.map (":" ++ ·))
        cases := cases ++ [s!"\{:id {id} :name \"{name}\" :workload {wlk} :opts \{:consistency-models [{msE}]}\n :history {ednOf w h}}"]
        let base : Opts := { Service.deployedOpts with models := some ms }
        let b := Service.judge model base h
        let f := Service.judge model (Round3.fixOf (fx ++ ["d21"].filter (fun _ => name.startsWith "d21")) base) h
        let sv : String := match model with
          | .closedPredicate => if ms.any (fun m => CPSpec.violates h m (name.startsWith "d21")) then "violated" else "satisfiable"
          | _ => if is.isEmpty then "no interpretation"
                 else if is.any (fun i => ms.all fun m => !(i.phen.any ((Spec.proscribed.lookup m).getD []).contains)) then "satisfiable"
                 else "violated in every interpretation"
        let showO (o : Outcome) : String := match o with
          | .result r => s!"{r.valid.str} {r.anomalyTypes}"
          | .thrown e => s!"throws {e}"
        IO.println s!"  {ms}: deployed {showO b}; fixed {showO f}; specification {sv}"
        let inner (x : String) : String := "{" ++ String.ofList ((x.toList.drop 1).dropLast) ++ "}"
        mine := mine ++ [s!"\{:id {id} :name \"{name}\" :deployed {inner (outcomeEdn id b)} :fixed {inner (outcomeEdn id f)}}"]
        id := id + 1
    IO.FS.writeFile (out ++ ".cases.edn") ("[" ++ "\n".intercalate cases ++ "]\n")
    IO.FS.writeFile (out ++ ".replica.edn") ("\n".intercalate mine ++ "\n")
    return 0
  if mode == "d15" then
    -- D15's fix over (malformed) histories, every chunking
    let mal := argNat args "malform" 1 == 1
    let gen : W G3 := do
      let h ← genHistory (boundsOf wl args)
      let h ← if mal then Folds.malform h else pure h
      return { h }
    return ← search s!"d15-{wl}" wl args gen fun g => Folds.checkD15 g.h (argNat args "chunkings" 512)
  if mode == "svccases3" then
    -- the fixes' minimal histories through the service: the deployed one and round 2's (b8f9cc9)
    let byName (n : String) : History := ((Cases.cases.find? (·.name == n)).map (·.h)).getD #[]
    let cpRead (r0 : Val) : List Op := Theorems2.cpOps [(0, 0), (1, 0)]
      [(1, [Theorems2.mw 1 1]), (2, [Theorems2.mr 1 1, { f := .r, k := 0, v := r0 }])]
    let cs : List (String × Service.Model × String × List Op × Valid) := [
      ("d3-process-skips-info", .listAppend, "strong-session-read-committed", (byName "process-skips-info-2txn").toList, .false_),
      ("d3-process-order-skips-info", .listAppend, "strong-session-serializable", (byName "process-order-skips-info").toList, .false_),
      ("d3-aborted-info-read", .listAppend, "strong-read-uncommitted", (byName "process-order-skips-info").toList, .true_),
      ("d3-aborted-info-read-session", .listAppend, "strong-session-read-uncommitted", (byName "process-order-skips-info").toList, .true_),
      ("d9-read-skew", .closedPredicate, "serializable", cpRead .nil, .false_),
      ("d9-read-skew-si", .closedPredicate, "snapshot-isolation", cpRead .nil, .false_),
      ("d9-consistent-read", .closedPredicate, "serializable", cpRead (.int 0), .true_),
      ("d10-versions-after", .closedPredicate, "snapshot-isolation",
        Theorems2.cpOps [(0, 0), (1, 0)] [(1, [Theorems2.mdel 1]), (2, [Theorems2.mrp (.eq 0) [], { f := .r, k := 1, v := .nil }])], .false_),
      ("d10-failure-to-observe", .closedPredicate, "strict-serializable", Theorems2.cpMiss.toList, .false_),
      ("d13-info-write-read-early", .register, "strict-serializable", (byName "register-info-write-read-early").toList, .false_),
      ("d16-duplicates-not", .listAppend, "serializable", Theorems2.dupRead, .false_),
      ("d17-duplicates-hide", .listAppend, "strict-serializable", Theorems2.dedupHides.toList, .false_),
      ("d19-per-key-predicate-read", .closedPredicate, "strict-serializable-per-key", Theorems2.cpStaleEq, .false_),
      ("d18-per-key-parts", .register, "strict-serializable-per-key", ServiceProps.perKeyParts, .false_),
      ("d18-per-key-parts-serializable", .register, "serializable", ServiceProps.perKeyParts, .true_)]
    let out := argStr args "out" "scratch/r3/svc/cases"
    let mut cases : List String := []
    let mut mine : List String := []
    let mut id := 0
    for (name, model, cons, ops, want) in cs do
      let d := Service.check model cons false ops true
      let r2 := Service.check model cons false ops false
      let e := Service.judge model { models := some [if cons == "strict-serializable-per-key" then "strict-serializable" else cons] } ops.toArray
      let showA (a : Except String Service.Answer) : String := match a with
        | .ok a => s!"{a.valid.str} {a.types} not {a.not_}" | .error e => s!"error {e}"
      let ok := match d with | .ok a => a.valid == want | .error _ => false
      IO.println s!"{name} ({cons}): deployed {showA d}; round 2's service {showA r2}; Elle 0.2.8 {match e with | .result r => s!"{r.valid.str} {r.anomalyTypes}" | .thrown t => t}; want {want.str}: {if ok then "ok" else "NO"}"
      let wlm := match model with | .register => "rw-register" | .closedPredicate => "closed-predicate" | _ => "list-append"
      let body := "\n".intercalate (ops.map ServiceProps.jsonOp)
      cases := cases ++ [s!"\{:id {id} :name \"{name}\" :model \"{wlm}\" :consistency \"{cons}\" :lk false :body \"{ServiceProps.ednEscape body}\" :history nil}"]
      mine := mine ++ [answerEdn id d]
      id := id + 1
    IO.FS.writeFile (out ++ ".cases.edn") ("[" ++ "\n".intercalate cases ++ "]\n")
    IO.FS.writeFile (out ++ ".replica.edn") ("\n".intercalate mine ++ "\n")
    return 0
  IO.eprintln s!"unknown mode {mode}"
  return 1

def main (argv : List String) : IO UInt32 := do
  let mode := argv.headD "explore3"
  let wl := (argv.drop 1).headD "la"
  let args := argv.drop 2
  if mode == "exhaust3" || mode == "explore3" then return ← search3 mode wl args
  round3 mode wl args
