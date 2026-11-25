import Jank.R3.Immer.Champ

/-!
# Round 5, core: a value unequal to itself in a CHAMP (G11, extends R55)

jank's `=` is not reflexive on a string seq of non-ASCII text (R55: persistent_string_sequence.cpp
`equal` 34-37 compares its bytes with the other side's character objects). immer's `get` compares
the stored value with the query, and `do_add` compares the stored value with the new one, so such a
value is never found, and adding it twice stores it twice (`make_merged` down to a collision node,
since both copies have the same hash at every level). Shown here on the replica with an equality
that is false for that value (the hash is any fixed number).
-/

namespace Jank.R5.Core.ChampR55

open Jank.R3.Immer.Champ

/-- A set of naturals whose equality never holds for 5 (as R55's seq is never `=` to itself). -/
def selfUnequal : Cfg Nat Nat where
  hashT _ := 2654435769
  hashK _ := 2654435769
  eqTT a b := a == b && a != 5
  eqTK a b := a == b && a != 5

def twice : Champ Nat :=
  let (c1, s1) := (Champ.empty.add selfUnequal 5).run {}
  ((c1.add selfUnequal 5).run s1).1

/-- `(count (hash-set x x))` is 2. -/
theorem r55_stored_twice : twice.size = 2 := by decide +kernel

/-- `(contains? (hash-set x) x)` is false. -/
theorem r55_never_found : Champ.get selfUnequal ((Champ.empty.add selfUnequal 5).run {}).1 5 = none := by decide +kernel

/-- A value equal to itself is stored once (the control). -/
theorem control_stored_once :
    (((((Champ.empty.add selfUnequal 4).run {}).1).add selfUnequal 4).run {}).1.size = 1 := by decide +kernel

end Jank.R5.Core.ChampR55
