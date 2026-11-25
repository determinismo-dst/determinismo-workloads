import Elle.Spec
import Elle.Txn
import Elle.R4.Dsg

/-!
# Round 4: from a cycle's class to the models it rules out

`lift_cycle` gives, in every (clean) interpretation, the phenomena of a cycle's class (`Claim`),
with Dsg's implications (G0 ⇒ G1c ⇒ G-nonadjacent; G-single ⇒ G2, G-nonadjacent; each phenomenon
⇒ its process and realtime variants). `classAlternatives` lists, per class, the sets of
phenomena one of which every interpretation shows. A model is ruled out when every alternative
holds a phenomenon the specification's model proscribes (`Spec.proscribed`).

Elle's own lattice (`prohibitedAnomalyTypes`) is a `while` loop over string graphs the kernel
can't evaluate, so the check that every class Elle prohibits for a model is ruled out for that
model is by evaluation (`elle-r5 lattice`), not by proof.
-/

namespace Elle.R4.Lattice

open Elle

def variants : List (String × Nat) := [("", 0), ("-process", 1), ("-realtime", 2)]

/-- Phenomena at variant `x` and above. -/
def up (ps : List String) (x : Nat) : List String :=
  (variants.filter (·.2 ≥ x)).flatMap fun (s, _) => ps.map (· ++ s)

def bases : List String :=
  ["G0", "G1c", "G-single-item", "G-single", "G-nonadjacent-item", "G-nonadjacent", "G2-item", "G2"]

/-- The alternatives `Claim` gives for a class (each alternative: phenomena that all hold). -/
def classAlternatives (base : String) (x : Nat) : List (List String) :=
  if base == "G0" then [up ["G0", "G1c", "G-nonadjacent"] x]
  else if base == "G1c" then [up ["G1c", "G-nonadjacent"] x]
  else if base == "G-single-item" || base == "G-single" then
    [up ["G-single", "G2", "G-nonadjacent"] x, up ["G1c", "G-nonadjacent"] x]
  else if base == "G2-item" || base == "G2" then [up ["G2"] x, up ["G1c", "G-nonadjacent"] x]
  else [up ["G-nonadjacent", "G2"] x, up ["G-nonadjacent", "G1c"] x]

/-- The class rules model `m` out: every alternative holds a phenomenon `m` proscribes. -/
def rulesOut (m base : String) (x : Nat) : Bool :=
  let pr := (Spec.proscribed.lookup m).getD []
  (classAlternatives base x).all fun alt => alt.any pr.contains

/-- D1's second search: a G-single (no variant) where an unread step took the other order. -/
def rulesOutUnread (m : String) : Bool :=
  let pr := (Spec.proscribed.lookup m).getD []
  (up ["G-single", "G2", "G-nonadjacent"] 0).any pr.contains

/-- Elle's cycle classes (base, variant) its lattice says model `m` prohibits, and those of them
the class doesn't rule out (should be none). -/
def table : List (String × List String × List String) :=
  Spec.specModels.map fun m =>
    let prohibited := prohibitedAnomalyTypes { models := some [m] }
    let classes := bases.flatMap fun b => variants.map fun (s, x) => (b, s, x)
    let elleBad := classes.filter fun (b, s, _) => prohibited.contains (b ++ s)
    (m, elleBad.map (fun (b, s, _) => b ++ s),
        (elleBad.filter fun (b, _, x) => !rulesOut m b x ||
          (b != "G0" && b != "G1c" && !rulesOutUnread m)).map fun (b, s, _) => b ++ s)

end Elle.R4.Lattice
