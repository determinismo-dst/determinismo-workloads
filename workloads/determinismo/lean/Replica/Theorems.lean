import Replica.Composer
import Replica.ComposerSearch
import Replica.Faults
import Replica.Verdicts
import Replica.Tape

/-!
# Theorems

For every input, not within bounds. Those marked "(by computation)" evaluate a concrete
counterexample (`native_decide`: they trust Lean's compiler as the searches do).
-/

namespace Replica.Theorems

open Determinismo

/-! ## Events are not properties (Verdicts) -/

def notEvent : Verdicts.AEvent → Bool
  | .event _ => false
  | _ => true

theorem foldlM_drops_events (l : List Verdicts.AEvent) (init : Array Verdicts.Property) :
    l.foldlM Verdicts.step init = (l.filter notEvent).foldlM Verdicts.step init := by
  induction l generalizing init with
  | nil => rfl
  | cons x xs ih =>
    cases x with
    | event n =>
      simp only [List.filter, notEvent, List.foldlM_cons, Verdicts.step]
      exact ih init
    | declare k m =>
      simp only [List.filter, notEvent, List.foldlM_cons]
      congr 1
      funext s
      exact ih s
    | eval k m c =>
      simp only [List.filter, notEvent, List.foldlM_cons]
      congr 1
      funext s
      exact ih s

/-- A timeline's property table is the same with its events left out: `sdk.event` makes no
property (SKILL.md: "an `sdk.event`, searchable and no property"). -/
theorem events_are_not_properties (t : Verdicts.Timeline) :
    Verdicts.timelineProps t = Verdicts.timelineProps { t with events := t.events.filter notEvent } := by
  unfold Verdicts.timelineProps
  exact foldlM_drops_events t.events #[]

/-! ## A tape's checkpoint passed over is never checked again (tape.zig:219-228) -/

/-- `check` at any other count than the next checkpoint's leaves the replay's cursor where it is. -/
theorem check_other_count (o : Tape.Overrides) (n : Nat) (h : UInt64)
    (hc : o.checkpointCursor < o.checkpoints.size)
    (hn : (o.checkpoints[o.checkpointCursor]!).1 ≠ n) :
    o.check n h = .ok o := by
  unfold Tape.Overrides.check
  have hne : (o.checkpointCursor == o.checkpoints.size) = false := by
    simp [Nat.ne_of_lt hc]
  have hn' : ((o.checkpoints[o.checkpointCursor]!).1 != n) = true := by
    simp [hn]
  simp [hne, hn']

/-- So once a replay's count passes the next checkpoint's without a guest event landing on it,
no later check compares anything: whatever the replay's history, it is never stopped. -/
theorem checks_never_stop (o : Tape.Overrides) (counts : List (Nat × UInt64))
    (hc : o.checkpointCursor < o.checkpoints.size)
    (hall : ∀ x ∈ counts, (o.checkpoints[o.checkpointCursor]!).1 ≠ x.1) :
    counts.foldlM (fun o (x : Nat × UInt64) => o.check x.1 x.2) o = .ok o := by
  induction counts with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.foldlM_cons]
    rw [check_other_count o x.1 x.2 hc (hall x (List.mem_cons_self))]
    exact ih (fun y hy => hall y (List.mem_cons_of_mem x hy))

/-! ## The swarm's rescue keeps a counted driver (composer.zig:261-270) -/

/-- The rescue's loop over the commands that count (`counts`), from `pick`: which it keeps.
`pick_index -|= 1` saturates: every counted command from the `pick`-th on is kept. -/
def rescue : List Bool → Nat → List Bool
  | [], _ => []
  | c :: cs, pick => if c then (pick == 0) :: rescue cs (pick - 1) else false :: rescue cs pick

theorem rescue_keeps_one (counts : List Bool) (pick : Nat) (h : pick < counts.count true) :
    (rescue counts pick).any id = true := by
  induction counts generalizing pick with
  | nil => simp at h
  | cons c cs ih =>
    cases c with
    | false =>
      simp only [rescue, Bool.false_eq_true, ite_false, List.any_cons, id, Bool.false_or]
      exact ih pick (by simpa using h)
    | true =>
      simp only [rescue, ite_true, List.any_cons, id]
      by_cases hp : pick = 0
      · simp [hp]
      · have : pick - 1 < cs.count true := by
          simp at h
          omega
        simp [ih (pick - 1) this]

/-- It keeps more than one (all from the pick on): "one of the workload's drivers at least",
not one alone (by computation). -/
theorem rescue_keeps_the_rest : rescue [true, true, true] 0 = [true, true, true] := by decide

/-- The rescue counts only parallel, serial and anytime commands (composer.zig:250-259): a
scenario whose marked commands are none of these needs none (by computation: the singleton
marked, two nemeses left out, the composer panics at composer.zig:718). -/
def singletonMarked : Composer.Scenario :=
  { commands := [{ name := "workload", kind := .singleton_driver, workload := true, runs := [1], exits := [.code 0] },
                 { name := "nemesis1", kind := .parallel_driver, runs := [1], exits := [.code 0] },
                 { name := "nemesis2", kind := .parallel_driver, runs := [1], exits := [.code 0] }] }

/-- The decisions: composer.singleton_eighths 0 (one eighth), composer.singleton 7 (not this
timeline), composer.swarm_p 0 (keep one eighth), composer.swarm nemesis1 7, nemesis2 7 (both
left out). -/
theorem singleton_marked_panics :
    (Composer.runTimeline singletonMarked {} Composer.Consts.tiny (Source.path #[0, 7, 0, 7, 7])).2 ==
      some (.violation "composer panics" "run_drivers: no driver kind kept (composer.zig:718: assert(kinds.len > 0))") := by
  native_decide

/-! ## The cap on nodes down (faults.zig:2090, 2134-2148) -/

/-- node_start's count (others under a takes-down fault or recovering) is at least the literal
count of others under a takes-down fault: admitted under it, the literal cap holds. -/
theorem literal_le_counted (nodes : List (Bool × Bool)) :
    (nodes.filter (·.1)).length ≤ (nodes.filter fun p => p.1 || p.2).length := by
  induction nodes with
  | nil => simp
  | cons x xs ih =>
    obtain ⟨a, r⟩ := x
    cases a <;> cases r <;> simp <;> omega

/-- The exclusion's hole (by computation): nodes a and b, b excluded, both allowing
partitions: the injector lists a partition of a and b, and a degradation whose node is b. -/
def excludedLater : Faults.Setup := { nodes := [{ name := "a" }, { name := "b" }], excluded := ["b"] }

theorem excluded_node_listed :
    ((Faults.faults_collect excludedLater).filter fun f => f.node == "b" || f.peer == "b").map Faults.Fault.label =
      ["partition a b", "degrade a b", "degrade b a"] := by
  native_decide

/-! ## Verdicts (by computation) -/

/-- An exit status, none for an error. -/
def code : Except String Nat → Option Nat
  | .ok n => some n
  | .error _ => none

/-- The same two timelines, ended in either order: one message evaluated as a `sometimes`
(true) in one and as an `always` (false) in the other. -/
def tSometimes : Verdicts.Timeline := { scenario := 0, events := [.eval .sometimes "m" true] }
def tAlways : Verdicts.Timeline := { scenario := 0, events := [.eval .always "m" false] }

theorem verdict_depends_on_order :
    code (Verdicts.explorerExit [[tSometimes, tAlways]] 1) = some 0 ∧
    code (Verdicts.explorerExit [[tAlways, tSometimes]] 1) = some 3 := by
  native_decide

/-- A `sometimes` true in scenario 1 and never true in scenario 0, both explored: the explorer
fails the run; judged as the documentation says (over all scenarios), it passes. -/
theorem sometimes_across_scenarios :
    code (Verdicts.explorerExit [[{ scenario := 0, events := [.eval .sometimes "m" false] }],
                           [{ scenario := 1, events := [.eval .sometimes "m" true] }]] 2) = some 3 ∧
    Verdicts.specFailing [{ scenario := 0, events := [.eval .sometimes "m" false] },
                          { scenario := 1, events := [.eval .sometimes "m" true] }] true = [] := by
  native_decide

/-- Two `sometimes` whose messages share their first 192 bytes: one true, the other never true.
The explorer passes; each is its own property in the documentation (and serve). -/
theorem long_messages_merge :
    code (Verdicts.explorerExit [[{ scenario := 0, events := [.eval .sometimes Verdicts.longA true,
                                                         .eval .sometimes Verdicts.longB false] }]] 1) = some 0 ∧
    (Verdicts.specFailing [{ scenario := 0, events := [.eval .sometimes Verdicts.longA true,
                                                        .eval .sometimes Verdicts.longB false] }] true).length = 1 := by
  native_decide

end Replica.Theorems

namespace Replica.Theorems

/-- A tape whose kept checkpoints all survive the thinning when the table is full makes the
replay's parse reach `assert(checkpoint_count < checkpoint_count_max)` (tape.zig:598): here a
table of two, a checkpoint every two events, checkpoints at events 4, 8 and 12 (the events at 2,
6 and 10 the VM's own: no checkpoint follows them) (by computation). -/
theorem thinning_can_overflow :
    (Tape.parse { interval := 2, checkpointMax := 2 }
      [.checkpoint 4 1, .checkpoint 8 2, .checkpoint 12 3]).toBool = false := by
  native_decide

/-- With a checkpoint at an odd position among them, it thins as documented: never refused. -/
theorem thinning_usual :
    (Tape.parse { interval := 2, checkpointMax := 2 }
      [.checkpoint 2 1, .checkpoint 4 2, .checkpoint 6 3, .checkpoint 8 4]).toBool = true := by
  native_decide

end Replica.Theorems

namespace Replica.Theorems

open Determinismo

/-! ## The composer's counterexamples, each a timeline of a small world (by computation) -/

/-- Whether `p` breaks in world `w`'s timeline of decisions `path` (ComposerSearch.worlds). -/
def violates (p : Composer.Prop') (w : Nat) (path : Array Nat) : Bool :=
  let wd := Composer.worlds[w]!
  (Composer.judge p wd.scenario wd.cmdline wd.consts (Source.path path)).violation.isSome

/-- A 60 ms length, parallelism 2: drive#1 runs 100 ms, drive#2 ends by a signal at 20 ms,
drive#3 runs 100 ms; the length's grace ends at 90 ms, both are killed, `interrupted` is reset
(composer.zig:519) and the finally runs. -/
theorem finally_after_a_signal : violates Composer.finallyAfterCompletion 4 #[1, 1, 0, 0, 1, 1, 0] = true := by
  native_decide

/-- A 60 ms length: the serial driver starts at 40 ms and runs 200 ms to completion
(composer.zig:820, 398-403): nothing bounds it. -/
theorem serial_past_the_length : violates Composer.lengthBound 5 #[0, 0, 0, 1, 1] = true := by
  native_decide

/-- A 30 ms limit, no length: two quiet stretches (10 ms each) carry the first start to 20 ms,
past half the limit (composer.zig:736-741). -/
theorem start_past_half_the_limit : violates Composer.noStartPastHalfLimit 12 #[0, 0, 0, 1, 1, 0, 0] = true := by
  native_decide

/-- A singleton timeline starts an anytime command beside the singleton (composer.zig:670-676). -/
theorem anytime_beside_the_singleton : violates Composer.singletonAloneStrict 7 #[0, 0] = true := by
  native_decide

/-- Five anytime commands, none marked: the swarm leaves all out and nothing rescues them
(composer.zig:257: unmarked, only parallel and serial drivers count); the composer panics. -/
theorem five_anytime_panics : violates Composer.noPanic 10 #[0, 7, 7, 7, 7, 6] = true := by
  native_decide

/-- min_drive 0, an eventually ending, no swarm: the fourth start exits 1 at 4 ms, during the
last pause, and is reaped by kill_all as killed (composer.zig:795, 390-396, 1200): no
"test commands exit successfully" fails in the timeline. -/
def hiddenFailure : Bool :=
  let wd := Composer.worlds[13]!
  let (w, stop) := Composer.runTimeline wd.scenario wd.cmdline wd.consts
    (Source.path #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1])
  stop.isNone &&
  (w.insts.any fun i => i.ownExit == some (.code 1) && !i.killedByComposer) &&
  !(w.log.any fun e => match e with
      | .assertion .always m false _ => m == "test commands exit successfully"
      | _ => false)

theorem failing_exit_hidden : hiddenFailure = true := by
  native_decide

end Replica.Theorems
