import Elle.Round3
import Elle.Theorems2

/-!
# Round 3's theorems (`native_decide`: the compiled replica and specification evaluate them)

- The deployed service (service-5fc908e) catches round 1's and round 2's minimal histories that its
  patches and changes target, and keeps the aborted-read interpretation's verdict.
- Each round-3 fix catches its disagreement's minimal history, which the deployed Elle passes, and
  the specification's verdict is the fixed one.
-/

namespace Elle.Theorems3

open Elle Elle.Cases Elle.Theorems2

def byName (n : String) : History := ((Cases.cases.find? (·.name == n)).map (·.h)).getD #[]

def deployedValid (model : Service.Model) (cons : String) (ops : List Op) : Option Valid :=
  match Service.check model cons false ops true with
  | .ok a => some a.valid
  | .error _ => none

def round2Valid (model : Service.Model) (cons : String) (ops : List Op) : Option Valid :=
  match Service.check model cons false ops false with
  | .ok a => some a.valid
  | .error _ => none

/-- D3: the deployed service catches both session histories through an `:info` write; round 2's
service (Elle 0.2.8) passed them. The `[2 1]` history stays valid for strong read uncommitted (its
aborted interpretation), where Elle 0.2.8 rejected it. -/
theorem deployed_d3 :
    deployedValid .listAppend "strong-session-read-committed" (byName "process-skips-info-2txn").toList = some .false_ ∧
    round2Valid .listAppend "strong-session-read-committed" (byName "process-skips-info-2txn").toList = some .true_ ∧
    deployedValid .listAppend "strong-session-serializable" (byName "process-order-skips-info").toList = some .false_ ∧
    deployedValid .listAppend "strong-read-uncommitted" (byName "process-order-skips-info").toList = some .true_ ∧
    round2Valid .listAppend "strong-read-uncommitted" (byName "process-order-skips-info").toList = some .false_ := by
  native_decide

/-- D9 and D10: closed predicate's read skew through a write, and the predicate anti-dependency on a
key the init created. -/
theorem deployed_d9_d10 :
    let skew := cpOps [(0, 0), (1, 0)] [(1, [mw 1 1]), (2, [mr 1 1, { f := .r, k := 0, v := .nil }])]
    let unborn := cpOps [(0, 0), (1, 0)] [(1, [mdel 1]), (2, [mrp (.eq 0) [], { f := .r, k := 1, v := .nil }])]
    deployedValid .closedPredicate "serializable" skew = some .false_ ∧
    round2Valid .closedPredicate "serializable" skew = some .true_ ∧
    deployedValid .closedPredicate "snapshot-isolation" unborn = some .false_ ∧
    round2Valid .closedPredicate "snapshot-isolation" unborn = some .true_ := by native_decide

/-- D11: on D10's history the deployed explainer's predicate step is on key 0, from unborn. -/
theorem deployed_d11 :
    let unborn := (cpOps [(0, 0), (1, 0)] [(1, [mdel 1]), (2, [mrp (.eq 0) [], { f := .r, k := 1, v := .nil }])]).toArray
    (match ClosedPredicate.analyzeOpts { Service.deployedOpts with models := some ["snapshot-isolation"] } unborn .none with
     | .ok m => ((m.lookup "G-single").getD []).any fun c => match c with
        | .cycle _ steps => steps.any fun s => s.type == "rwp" && s.key == some 0
        | _ => false
     | .error _ => false) = true := by native_decide

/-- D13 (and D14 through the deployed rw-register with a transaction order). -/
theorem deployed_d13_d14 :
    deployedValid .register "strict-serializable" (byName "register-info-write-read-early").toList = some .false_ ∧
    round2Valid .register "strict-serializable" (byName "register-info-write-read-early").toList = some .true_ ∧
    validOf (RwRegister.check { Service.deployedOpts with models := some ["strict-serializable"], txnOrder := some ord14 } h14) =
      some .false_ := by native_decide

/-- D16, D17, D19: the service's own changes. -/
theorem deployed_d16_d17_d19 :
    (match Service.check .listAppend "serializable" false dupRead true with
     | .ok a => a.valid == .false_ && a.not_ == ["read-uncommitted"] | .error _ => false) = true ∧
    (match Service.check .listAppend "strict-serializable" false dedupHides.toList true with
     | .ok a => a.types.contains "G0-realtime" && a.types.contains "duplicate-elements" | .error _ => false) = true ∧
    deployedValid .closedPredicate "strict-serializable-per-key" cpStaleEq = some .false_ ∧
    round2Valid .closedPredicate "strict-serializable-per-key" cpStaleEq = some .true_ := by native_decide

/-- D18 with D19's fix: the deployed per-key graph's closure is real time between operations
sharing a key, on D19's and D18's histories; D18's history still fails per key. -/
theorem deployed_per_key_reading_b :
    Round3.perKeyExact cpStaleEq.toArray = none ∧
    Round3.perKeyExact ServiceProps.perKeyParts.toArray = none ∧
    deployedValid .register "strict-serializable-per-key" ServiceProps.perKeyParts = some .false_ := by native_decide

def fixed (names : List String) (model : Service.Model) (m : String) (h : History) : Option Valid :=
  validOf (Service.judge model (Round3.fixOf names { Service.deployedOpts with models := some [m] }) h)

def deployed (model : Service.Model) (m : String) (h : History) : Option Valid :=
  validOf (Service.judge model { Service.deployedOpts with models := some [m] } h)

def specLA (h : History) (m : String) : Spec.SpecVerdict := Spec.verdict (Spec.interpsListAppend h) m
def specRR (h : History) (m : String) : Spec.SpecVerdict := Spec.verdict (Spec.interpsRegister h) m

/-- D1: snapshot isolation and consistent view, valid as deployed, invalid with the fix; every
interpretation violates both. -/
theorem fix_d1 :
    let h := byName "unobserved-appends-g-single"
    deployed .listAppend "snapshot-isolation" h = some .true_ ∧ fixed ["d1"] .listAppend "snapshot-isolation" h = some .false_ ∧
    deployed .listAppend "consistent-view" h = some .true_ ∧ fixed ["d1"] .listAppend "consistent-view" h = some .false_ ∧
    specLA h "snapshot-isolation" = .unsat ∧ specLA h "consistent-view" = .unsat := by native_decide

/-- D2: strong session SI beside strong read uncommitted. -/
theorem fix_d2 :
    let h := byName "realtime-replaces-process"
    let ms := ["strong-session-snapshot-isolation", "strong-read-uncommitted"]
    validOf (Service.judge .listAppend { Service.deployedOpts with models := some ms } h) = some .true_ ∧
    validOf (Service.judge .listAppend (Round3.fixOf ["d2"] { Service.deployedOpts with models := some ms }) h) = some .false_ := by
  native_decide

/-- D4 and D5: read uncommitted with a failed append inside a read (caught), and with an `:info`
writer that may have aborted (no longer rejected). -/
theorem fix_d4_d5 :
    let h4 := byName "failed-append-hides-ww"
    let h5 := byName "info-may-have-aborted-2txn"
    deployed .listAppend "read-uncommitted" h4 = some .true_ ∧ fixed ["d4"] .listAppend "read-uncommitted" h4 = some .false_ ∧
    specLA h4 "read-uncommitted" = .unsat ∧
    deployed .listAppend "read-uncommitted" h5 = some .false_ ∧ fixed ["d5"] .listAppend "read-uncommitted" h5 = some .true_ ∧
    specLA h5 "read-uncommitted" = .sat := by native_decide

/-- D6 and D7: rw-register's fuzzy read and second-read G1c, and its future read. -/
theorem fix_d6_d7 :
    let fz := byName "register-fuzzy-read"
    let g1c := byName "register-second-read-g1c"
    let fut := byName "register-future-read"
    deployed .register "repeatable-read" fz = some .true_ ∧ fixed ["d6"] .register "repeatable-read" fz = some .false_ ∧
    specRR fz "repeatable-read" = .unsat ∧
    deployed .register "read-committed" g1c = some .true_ ∧ fixed ["d6"] .register "read-committed" g1c = some .false_ ∧
    specRR g1c "read-committed" = .unsat ∧
    deployed .register "strict-serializable" fut = some .true_ ∧ fixed ["d7"] .register "strict-serializable" fut = some .false_ ∧
    specRR fut "strict-serializable" = .none_ := by native_decide

/-- D8: the garbage read no longer throws, and is invalid. D12: renaming two values no longer
changes read uncommitted's verdict. -/
theorem fix_d8_d12 :
    let g := byName "list-append-garbage-read"
    deployed .listAppend "strict-serializable" g = none ∧ fixed ["d8"] .listAppend "strict-serializable" g = some .false_ ∧
    deployed .listAppend "read-uncommitted" (byName "value-hash-order-a") ≠
      deployed .listAppend "read-uncommitted" (byName "value-hash-order-b") ∧
    fixed ["d12"] .listAppend "read-uncommitted" (byName "value-hash-order-a") =
      fixed ["d12"] .listAppend "read-uncommitted" (byName "value-hash-order-b") := by native_decide

/-- D20, D21, D22: closed predicate's mixed cycle, stale `:true` read, and `:info` read. -/
theorem fix_d20_d21_d22 :
    deployed .closedPredicate "repeatable-read" cpMixed = some .true_ ∧
    fixed ["d20"] .closedPredicate "repeatable-read" cpMixed = some .false_ ∧
    deployed .closedPredicate "strict-serializable" cpStale = some .true_ ∧
    fixed ["d21"] .closedPredicate "strict-serializable" cpStale = some .false_ ∧
    deployed .closedPredicate "consistent-view" (cpInfoRead true) = some .true_ ∧
    fixed ["d22"] .closedPredicate "consistent-view" (cpInfoRead true) = some .false_ := by native_decide

/-- D15: the fixed pair-index fold rejects the double invocation in every chunking. -/
theorem fix_d15 :
    (Folds.chunkings doubleInvoke).all (fun ch => match Folds.pairIndexFoldFx.onChunks ch with
      | .error _ => true | .ok _ => false) = true ∧
    (Folds.chunkings doubleInvoke).any (fun ch => match Folds.pairIndexFold.onChunks ch with
      | .error _ => false | .ok _ => true) = true := by native_decide

/-- D1's register form: snapshot isolation passes the "nil before every value" G-single; with
the fix it doesn't. -/
theorem fix_d1_register :
    let h := byName "register-initial-state-g-single"
    deployed .register "snapshot-isolation" h = some .true_ ∧
    fixed ["d1"] .register "snapshot-isolation" h = some .false_ ∧
    specRR h "snapshot-isolation" = .unsat := by native_decide

/-- D23: one process reads [2] (the append of its own later transaction), then reads [3 4] (the
appends of its next, indeterminate, transaction) and appends 2. Every interpretation violates
strong read uncommitted (2 precedes 1, so T1 -ww-> T0 -rt-> T1); Elle 0.2.8 reported G0-realtime
through the `:info` transaction, the deployed Elle (D3's fix: no real time into `:info`
completions) passes it, and D5's fix (the version order without `:info` elements) catches it. -/
def h23 : History := serial [{ p := 0, status := .ok, mops := [r 0 [2], a 0 1] },
                             { p := 0, status := .ok, mops := [r 0 [3, 4], a 0 2] },
                             { p := 0, status := .info, mops := [a 0 3, a 0 4] }]

theorem d23 :
    validOf (Service.judge .listAppend { models := some ["strong-read-uncommitted"] } h23) = some .false_ ∧
    deployed .listAppend "strong-read-uncommitted" h23 = some .true_ ∧
    deployedValid .listAppend "strong-read-uncommitted" h23.toList = some .true_ ∧
    specLA h23 "strong-read-uncommitted" = .unsat ∧
    fixed ["d5"] .listAppend "strong-read-uncommitted" h23 = some .false_ ∧
    fixed ["d5"] .listAppend "strong-session-read-uncommitted" h23 = some .false_ := by native_decide

end Elle.Theorems3
