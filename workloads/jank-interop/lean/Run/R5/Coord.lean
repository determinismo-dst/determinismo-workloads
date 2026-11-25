import Jank.R5.Coord.JankMath

/-! Round 5 driver: the coordinator's checks (`jank5-coord math`). -/

def main (args : List String) : IO Unit := do
  match args with
  | ["math"] => for l in Jank.R5.Coord.JankMath.report do IO.println l
  | _ => IO.println "usage: jank5-coord math"
