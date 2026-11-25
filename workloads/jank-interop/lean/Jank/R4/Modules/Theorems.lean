import Jank.R4.Modules.Loader
import Jank.R4.Modules.Cli
import Jank.R4.Modules.Aot

/-!
# Round 4, modules: statements proved for every input

- `upsert_jank_last_wins`: registering the `.jank` slot of a module twice keeps the second file,
  whatever the index held before (register_entry's `res.first->second.jank = entry`): the later
  module-path element wins (F8).
- `firstHaving_first`: Clojure's lookup returns the first element that holds the resource.
- `checkFlag_prefix`: a short flag without a value matches every argument that starts with it
  (cli.cpp 34–51), so every argument starting with `-h` is `--help`.
- `aot_static_status_zero`: a program built with the static runtime exits 0 however its start-up
  or `-main` ends (c_api.cpp 1168 `return 0;`) (F3).
-/

namespace Jank.R4.Modules

theorem get_upsert_self (es : Entries) (k : String) (f : Entry → Entry) :
    (es.upsert k f).get? k = some (f ((es.get? k).getD {})) := by
  unfold Entries.upsert Entries.get?
  cases h : es.find? (·.1 == k) with
  | none => simp [List.find?_append, h]
  | some x =>
    have hx' := List.find?_some h
    have hx : (x.1 == k) = true := by simpa using hx'
    simp only [List.find?_map, Option.map_map]
    have hcomp : ((fun p : String × Entry => p.1 == k) ∘
        (fun (pe : String × Entry) => match pe with
          | (k', e) => if (k' == k) = true then (k', f e) else (k', e))) = (fun p => p.1 == k) := by
      funext ⟨k', e⟩
      by_cases hk : k' = k <;> simp [hk]
    rw [hcomp, h]
    rcases x with ⟨k0, e0⟩
    simp at hx
    simp [hx]

theorem upsert_jank_last_wins (es : Entries) (k : String) (e1 e2 : FileEntry) :
    (((es.upsert k fun x => { x with jank := some e1 }).upsert k fun x => { x with jank := some e2 }).get? k).bind (·.jank)
      = some e2 := by
  rw [get_upsert_self]; simp

theorem firstHaving_first (e : Elem) (path : List Elem) (res : String) (f : FileEntry)
    (h : elemHas e res = some f) : firstHaving (e :: path) res = some f := by
  simp [firstHaving, List.findSome?, h]

namespace Cli

theorem checkFlag_prefix (a short long : String) (rest : List String)
    (hs : short ≠ "") (hl : (a == long) = false) (hp : a.startsWith short = true) :
    checkFlag (a :: rest) short long false = .ok (some ("", rest)) := by
  simp [checkFlag, hl, hp, hs]

end Cli

namespace Aot

theorem aot_static_status_zero (p : Prog) (h : (aotRun p true).phase ≠ "compile") :
    (aotRun p true).status = 0 := by
  cases hc : compileProg p with
  | error e => simp [aotRun, hc] at h
  | ok lifted =>
    simp only [aotRun, hc]
    split
    · simp
    · split <;> simp

end Aot

end Jank.R4.Modules
