import Jank.R6.Num.MinMax

/-!
# Round 7, numbers: the brief's min/max NaN observation put to round 6's model

The real jank (main 7135b7708) gave, through a fn, `(max ##NaN 1)` = ##NaN (as Clojure) and
`(min ##NaN 1)` = 1. Round 6's `Jank.R6.Num.MinMax.jMinMax` (math.hpp `min` 738-865, `max`
865-992) is evaluated here on both forms, on every path: literals (native/native:
`std::min/max(static_cast<C>(l), static_cast<C>(r))`, C = double), a `let` (the same native types),
a fn value (object/object: `l < r ? l : r` and `l < r ? r : l`), and the two mixed paths (one
literal and one parameter: the same `l < r` choice with `make_box` of the native side).
-/

namespace Jank.R7.Num.NaN

open Jank.R6.Num.MinMax Jank.R3.Boost.Num

structure Case where
  form : String
  path : String
  isMax : Bool
  x : Arg
  y : Arg

def nanL (lit : Bool) : Arg := dbl nan "##NaN" lit
def oneL (lit : Bool) : Arg := lng 1 lit

/-- Both forms on every path (`let` binds literals: native, as literals). -/
def cases : List Case := Id.run do
  let mut out := []
  for isMax in [false, true] do
    let op := if isMax then "max" else "min"
    out := out ++
      [⟨s!"({op} ##NaN 1)", "literals", isMax, nanL true, oneL true⟩,
       ⟨s!"(let [a ##NaN b 1] ({op} a b))", "let", isMax, nanL true, oneL true⟩,
       ⟨s!"((fn [a b] ({op} a b)) ##NaN 1)", "fn", isMax, nanL false, oneL false⟩,
       ⟨s!"(apply {op} [##NaN 1])", "fn value", isMax, nanL false, oneL false⟩,
       ⟨s!"((fn [b] ({op} ##NaN b)) 1)", "literal + parameter", isMax, nanL true, oneL false⟩,
       ⟨s!"((fn [a] ({op} a 1)) ##NaN)", "parameter + literal", isMax, nanL false, oneL true⟩]
  return out

def Case.jank (c : Case) : String := showJ (jMinMax c.isMax c.x c.y)
def Case.clj (c : Case) : String := showC (cMinMax c.isMax c.x c.y)

end Jank.R7.Num.NaN
