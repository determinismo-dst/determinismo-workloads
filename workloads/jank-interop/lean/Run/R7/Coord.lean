import Jank.R7.Coord.Case
import Jank.R7.Coord.Decimal

/-! Round 7, coordinator (`jank7-coord`): jank's `case` dispatch on the inputs of R44 and X1,
stock and corrected (`Jank.R7.Coord.Case`), beside Clojure's result. -/

open Jank.R7.Coord.Case

def showRow (form : String) (stock fixed clj : Nat) : IO Unit :=
  IO.println s!"{form}\n    stock jank {stock}; corrected {fixed}; Clojure {clj}"

def main : IO Unit := do
  IO.println ("jank hash of {} and #{}: " ++ toString emptyCollHash ++ s!"; of 4294967296: {hashInt 4294967296}; of 2147483648: {hashInt 2147483648}")
  showRow "(case {} {} :map #{} :set :none)   [:map=1 :set=2 :none=0]"
    (dispatch (stockBranches collide) 0 emptyMap) (dispatch (fixedBranches collide) 0 emptyMap)
    (clj collide 0 emptyMap)
  showRow "(case #{} {} :map #{} :set :none)"
    (dispatch (stockBranches collide) 0 emptySet) (dispatch (fixedBranches collide) 0 emptySet)
    (clj collide 0 emptySet)
  showRow "(case 987256456 {} :map #{} :set 4294967296 :big :none)   [:big=3]"
    (dispatch (stockBranches collideBig) 0 (.int 987256456))
    (dispatch (fixedBranches collideBig) 0 (.int 987256456)) (clj collideBig 0 (.int 987256456))
  showRow "(case 987256456 4294967296 :big :none)   control"
    (dispatch (stockBranches [(.int 4294967296, 3)]) 0 (.int 987256456))
    (dispatch (fixedBranches [(.int 4294967296, 3)]) 0 (.int 987256456))
    (clj [(.int 4294967296, 3)] 0 (.int 987256456))
  IO.println s!"(case 2147483648 2147483648 :hit :miss): stock key {keyStockInts 2147483648}, the value's integer {valueKey (.int 2147483648)}; corrected key {keyFixed [2147483648] 2147483648}"
