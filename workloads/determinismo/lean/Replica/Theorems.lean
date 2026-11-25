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

/-! ## A replay past a checkpoint's count is stopped (tape.zig:223-233 at 3939448; CE13 fixed) -/

/-- Below the next checkpoint's count, `check` compares nothing and moves nothing. -/
theorem check_below_waits (o : Tape.Overrides) (n : Nat) (h : UInt64)
    (hc : o.checkpointCursor < o.checkpoints.size)
    (hn : n < (o.checkpoints[o.checkpointCursor]!).1) :
    o.check n h = .ok o := by
  unfold Tape.Overrides.check
  have hne : (o.checkpointCursor == o.checkpoints.size) = false := by
    simp [Nat.ne_of_lt hc]
  simp [hne, hn]

/-- Past the next checkpoint's count (the tape's event there a guest line, the replay's not),
`check` stops the replay, whatever its hash: round 1's CE13 (the cursor waiting forever) is gone. -/
theorem check_past_stops (o : Tape.Overrides) (n : Nat) (h : UInt64)
    (hc : o.checkpointCursor < o.checkpoints.size)
    (hn : (o.checkpoints[o.checkpointCursor]!).1 < n) :
    (o.check n h).toBool = false := by
  unfold Tape.Overrides.check
  have hne : (o.checkpointCursor == o.checkpoints.size) = false := by
    simp [Nat.ne_of_lt hc]
  have hlt : ¬ n < (o.checkpoints[o.checkpointCursor]!).1 := by omega
  have hneq : ((o.checkpoints[o.checkpointCursor]!).1 != n) = true := by
    simp; omega
  simp [hne, hlt, hneq, Except.toBool]

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

/-- Round 1's CE3 (by computation): the singleton marked, two nemeses. At 3939448 a marked
singleton is no swarm command (composer.zig:223-235): the swarm weighs both nemeses and the
composer goes on (round 1's decisions, the rest first options). -/
def singletonMarked : Composer.Scenario :=
  { commands := [{ name := "workload", kind := .singleton_driver, workload := true, runs := [1], exits := [.code 0] },
                 { name := "nemesis1", kind := .parallel_driver, runs := [1], exits := [.code 0] },
                 { name := "nemesis2", kind := .parallel_driver, runs := [1], exits := [.code 0] }] }

/-- The decisions: composer.singleton_eighths 0 (one eighth), composer.singleton 7 (not this
timeline), composer.swarm_p 0 (keep one eighth), composer.swarm nemesis1 7, nemesis2 7 (both
left out). -/
def panics (stop : Option Stop) : Bool :=
  match stop with
  | some (.violation "composer panics" _) => true
  | _ => false

theorem singleton_marked_goes_on :
    panics (Composer.runTimeline singletonMarked {} Composer.Consts.tiny (Source.path #[0, 7, 0, 7, 7])).2 = false := by
  native_decide

/-- composer.zig:686-692 `rescue_counts`: a singleton, a first or an ending never counts, so the
rescue's pick is always among commands the drivers' phase can start. -/
theorem rescue_counts_only_swarm_commands (k : Composer.Kind) (w m : Bool) (d : Nat)
    (h : Composer.rescueCounts k w m d = true) : Composer.swarmable k = true := by
  unfold Composer.rescueCounts at h
  unfold Composer.swarmable
  cases k <;> simp +decide [Composer.isDriver] at h ⊢

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

/-- Round 1's CE6 (by computation): nodes a and b, b excluded. At 3939448 the injector lists
no fault naming b (faults.zig:1484-1489). -/
def excludedLater : Faults.Setup := { nodes := [{ name := "a" }, { name := "b" }], excluded := ["b"] }

theorem excluded_node_unlisted :
    ((Faults.faults_collect excludedLater).filter fun f => f.node == "b" || f.peer == "b").map Faults.Fault.label = [] := by
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

/-- Round 1's CE9, at 3939448: two properties (kinds apart), the false `always` fails in either
order. -/
theorem verdict_same_in_either_order :
    code (Verdicts.explorerExit [[tSometimes, tAlways]] 1) = some 3 ∧
    code (Verdicts.explorerExit [[tAlways, tSometimes]] 1) = some 3 := by
  native_decide

/-- Round 1's CE10, at 3939448: a `sometimes` true in scenario 1 and never true in scenario 0,
both explored: the explorer passes, as the documentation judges it. -/
theorem sometimes_across_scenarios_fixed :
    code (Verdicts.explorerExit [[{ scenario := 0, events := [.eval .sometimes "m" false] }],
                           [{ scenario := 1, events := [.eval .sometimes "m" true] }]] 2) = some 0 ∧
    Verdicts.specFailing [{ scenario := 0, events := [.eval .sometimes "m" false] },
                          { scenario := 1, events := [.eval .sometimes "m" true] }] true = [] := by
  native_decide

/-- Round 1's CE11, at 3939448: two `sometimes` whose messages share their first 192 bytes, one
true, the other never true: two properties (the hash), the explorer fails as documented. -/
theorem long_messages_apart :
    code (Verdicts.explorerExit [[{ scenario := 0, events := [.eval .sometimes Verdicts.longA true,
                                                         .eval .sometimes Verdicts.longB false] }]] 1) = some 3 ∧
    (Verdicts.specFailing [{ scenario := 0, events := [.eval .sometimes Verdicts.longA true,
                                                        .eval .sometimes Verdicts.longB false] }] true).length = 1 := by
  native_decide

end Replica.Theorems

namespace Replica.Theorems

/-- Round 1's CE14, at 3939448: a table of two, a checkpoint every two events, checkpoints at
events 4, 8 and 12: thinned twice, the parse succeeds (tape.zig:595) (by computation). -/
theorem thinning_no_longer_overflows :
    (Tape.parse { interval := 2, checkpointMax := 2 }
      [.checkpoint 4 1, .checkpoint 8 2, .checkpoint 12 3]).toBool = true := by
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

/-- Round 1's CE1 (round 1's decisions): a 60 ms length, parallelism 2: drive#1 runs 100 ms,
drive#2 ends by a signal at 20 ms, drive#3 runs 100 ms. At 3939448 the length's kills keep the
earlier interruption (composer.zig:534-539): the finally is skipped. -/
theorem finally_after_a_signal_fixed : violates Composer.finallyAfterCompletion 4 #[1, 1, 0, 0, 1, 1, 0] = false := by
  native_decide

/-- Round 1's CE4 (its decisions): a 60 ms length, a serial driver of 200 ms. At 3939448
`run_alone_until` bounds it (composer.zig:413-419, 881). -/
theorem serial_bounded_by_the_length : violates Composer.lengthBound 5 #[0, 0, 0, 1, 1] = false := by
  native_decide

/-- Round 1's CE5 (its decisions): a 30 ms limit, two quiet stretches. At 3939448 the stop is
checked after a quiet stretch (composer.zig:795-803). -/
theorem quiet_stretches_stop_at_half_the_limit : violates Composer.noStartPastHalfLimit 12 #[0, 0, 0, 1, 1, 0, 0] = false := by
  native_decide

/-- A singleton timeline starts an anytime command beside the singleton (composer.zig:670-676). -/
theorem anytime_beside_the_singleton : violates Composer.singletonAloneStrict 7 #[0, 0] = true := by
  native_decide

/-- Round 1's five anytime commands (its decisions): at 3939448 anytime commands alone count for
the rescue (composer.zig:692). -/
theorem five_anytime_go_on : violates Composer.noPanic 10 #[0, 7, 7, 7, 7, 6] = false := by
  native_decide

/-- Round 1's CE2 (its decisions): min_drive 0, the fourth start exits 1 at 4 ms and is reaped by
kill_all. At 3939448 an exit is the composer's kill only when SIGKILL ended it
(composer.zig:335-340): "test commands exit successfully" fails. -/
def hiddenFailure : Bool :=
  let wd := Composer.worlds[13]!
  let (w, stop) := Composer.runTimeline wd.scenario wd.cmdline wd.consts
    (Source.path #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1])
  stop.isNone &&
  (w.insts.any fun i => i.ownExit == some (.code 1) && !i.killedByComposer) &&
  !(w.log.any fun e => match e with
      | .assertion .always m false _ => m == "test commands exit successfully"
      | _ => false)

theorem failing_exit_judged : hiddenFailure = false := by
  native_decide

end Replica.Theorems
