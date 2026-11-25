import Elle.Round3
import Elle.Cases
import Elle.Theorems3

/-!
# Round 4: the service as it will be deployed next, and D12's refinement

`service-9a914f9/src/elle/` is round 3's safe set, byte for byte: each of its six namespaces
equals `scratch/r3/fix-safe/elle/` (`diff -q`, 2026-11-25). Its `elle_service.clj` equals the
deployed one (`service-5fc908e/src/elle_service.clj`). So the replica's switch set for it is the
deployed one (D3, D9-D11, D13, the service's D16, D17, D19) plus round 3's safe fixes:

- `list_append.clj` (new there): D1 (`unread-pairs`, `unread-cycles`, 899-970; the merge,
  1146-1148), D4 (`committed-previous-element`, 566-586, used by `ww-mop-dep`, 595-599), D5
  (`preprocess`'s `g1a?`, 641-694), D8 (`dirty-update-cases`, 464-470; `garbage-read-cases`,
  505-515; reported, 1119-1120 and 1158-1159);
- `rw_register.clj`: D1 (register form), D6 (every external read, `:fuzzy-read`), D7
  (`:future-read`);
- `closed_predicate.clj`: D21 (rows as item reads), D22 (explainers read `:ok` ops only);
- `txn.clj`: D20 (mixed cycles);
- `consistency_model.clj` (new there): `:fuzzy-read` and `:garbage-read` in the lattice.

D4's step-over runs for every model there (`ww-mop-dep` always calls
`committed-previous-element`), as the replica's `fxOf` turns it on with D5.
-/

namespace Elle.Round4

open Elle Elle.Spec Elle.Service Elle.Round3

/-- The service as it will be deployed next (service-9a914f9): the deployed switches and round 3's
safe set (D1, D4 with D5, D6, D7, D8, D20, D21, D22). -/
def deployedNextOpts : Opts :=
  { Service.deployedOpts with
    fixD1 := true, fixD4 := true, fixD5 := true, fixD6 := true, fixD7 := true, fixD8 := true
    fixD20 := true, fixD21 := true, fixD22 := true }

/-- Round 3's fixes and round 4's D12 refinement, by name. -/
def fixes4 : List Fix := Round3.fixes ++ [⟨"d12b", fun o => { o with fixD12b := true }⟩,
  ⟨"next", fun o => { o with
    fixD1 := true, fixD4 := true, fixD5 := true, fixD6 := true, fixD7 := true, fixD8 := true
    fixD20 := true, fixD21 := true, fixD22 := true }⟩]

def fixOf4 (names : List String) : Opts → Opts :=
  fun o => names.foldl (fun o n => match fixes4.find? (·.name == n) with
    | some f => f.opts o
    | none => o) o

/-- D12's property: renaming values changes no verdict, over a given base. -/
def renameProps4 (fx : Opts → Opts) (base0 : Opts) (h : History) (models : List String) :
    List (String × String) :=
  let h' := renamed h
  models.flatMap fun m =>
    let base : Opts := { base0 with models := some [m] }
    let f1 := validOf (Service.judge .listAppend (fx base) h)
    let f2 := validOf (Service.judge .listAppend (fx base) h')
    let b1 := validOf (Service.judge .listAppend base h)
    let b2 := validOf (Service.judge .listAppend base h')
    (if f1 != f2 then [("rename:fixed:" ++ m, s!"{m}: {repr f1} renamed {repr f2}")] else []) ++
    (if b1 != b2 then [("rename:base:" ++ m, s!"{m}: {repr b1} renamed {repr b2}")] else [])

/-- The service's answer as it will be deployed next. -/
def checkNext (model : Service.Model) (consistency : String) (lk : Bool) (ops : List Op) :
    Except String Service.Answer :=
  Service.check model consistency lk ops true deployedNextOpts

end Elle.Round4

namespace Elle.Round4
open Elle Elle.Cases

/-- D12's one regression (round 3, `results/r3/X3-d12-la-any.txt`): key 0 is read as [1] (an
`:ok` append) and as [2] (a failed one). Strong read uncommitted is violated in every
interpretation; D12's first-read order picks [2] and passes it, its refinement picks [1]. -/
def d12Regression : History :=
  build [{ p := 1, status := .ok, mops := [r 0 [1], a 0 3] },
         { p := 2, status := .ok, mops := [a 1 2, r 0 [2]] },
         { p := 0, status := .ok, mops := [a 1 1, a 0 1] },
         { p := 0, status := .fail, mops := [a 0 2, rnil 0] }]
    [.inv 0, .inv 1, .done 0, .inv 2, .done 2, .done 1, .inv 3, .done 3]

end Elle.Round4
