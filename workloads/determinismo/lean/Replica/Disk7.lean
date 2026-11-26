import Replica.Disk5

/-!
# corrupt_reads at df8f08b: a reader that dies during its fault (round 7)

Round 6's list: the reader killed by the OOM killer, and pid reuse at the heal. The drain
(nodes.zig:2384-2420, unchanged from a7fe05d to df8f08b) waits for the reader through a pidfd
opened at the heal from the pid the reader wrote at its start. A reader that died during the
fault left its unread lines in the instance and no process at its pid: `pidfd_open` fails
(ESRCH), nothing is waited for, killed or said, and `rmdir` succeeds. If another process took the
pid meanwhile (pids wrap at `pid_max`), the pidfd is that process's: the heal waits 2 s for it,
says "drain" and SIGKILLs it.

The model is Disk5's with one more step, the reader's death (`Disk5.S.readerMayDie`).
-/

namespace Replica.Disk7

open Determinismo
open Replica.Disk5

def searchAll (exhaustRuns seeds : Nat) : IO Unit := do
  for (prop, src) in [(everyReadNamedOrSaid, "nodes.zig:2384-2420 (df8f08b: the drain; \"disk_reads_trace_failed\" when it is cut); schema.zig corrupt_reads (\"Every read it corrupts is named\")"),
                      (killsOnlyItsReader, "nodes.zig:2366-2391 (df8f08b: \"The tracer stopped (its pid read and killed, its instance removed)\")")] do
    say s!"== disk property: {prop}"
    say s!"   source: {src}"
    for steps in [4, 5, 6] do
      if let some f ← exhaustSaid s!"{prop} / df8f08b, the reader may die / {steps} steps" (judgeWith prop steps · .vdf8f08b false true) exhaustRuns then
        printFound f (storyD steps · .vdf8f08b false true)
      if let some f ← exploreSaid s!"{prop} / df8f08b, the reader may die / {steps} steps" (judgeWith prop steps · .vdf8f08b false true) seeds then
        printFound f (storyD steps · .vdf8f08b false true)
    -- The control: a reader that lives, at df8f08b.
    for steps in [4, 6] do
      if let some f ← exhaustSaid s!"{prop} / df8f08b, the reader lives / {steps} steps" (judgeWith prop steps · .vdf8f08b false false) exhaustRuns then
        printFound f (storyD steps · .vdf8f08b false false)

end Replica.Disk7
