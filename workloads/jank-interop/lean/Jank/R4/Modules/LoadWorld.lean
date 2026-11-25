import Determinismo
import Jank.R4.Modules.Load

/-!
# Round 4, modules: the search world for `require`/`use`/`load`/`refer`/`alias`/`ns`

Two libraries `p.a` and `p.b` on the module path (`p.c` is missing). Each file is
`(ns <lib> <clause>?) (def v<x>) (println "<lib>") <extra>?`, its clause and extra form drawn
from small pools; then one or two top-level forms at the REPL in `user`. Both sides run the same
program (`Load.runTop`); every difference is classified by neutralizing one known feature at a
time (the classes below), and what no neutralization explains is `unexplained`.
-/

namespace Jank.R4.Modules.LoadWorld

open Determinismo Jank.R4.Modules.Load

def specPool : List Libspec :=
  [.sym "p.a", .sym "p.b", .vec "p.a" [.as "q"], .vec "p.b" [.as "q"],
   .vec "p.a" [.refer ["va"]], .vec "p.b" [.refer ["vb"]], .vec "p.c" [.asAlias "q"],
   .sym "p.c", .prefix "p" [.vec "a" [.as "q"]], .vec "p.a" [.referSet ["va"]]]

def flagPool : List (List Flag) := [[], [.reload], [.reloadAll], [.verbose]]

def topPool : List Form :=
  (specPool.flatMap fun sp => flagPool.map fun fl => Form.require [sp] fl) ++
  (specPool.map fun sp => Form.use [sp] []) ++
  [.refer "p.a" (some ["va"]) false, .refer "p.a" (some ["va"]) true, .alias "q" "p.a",
   .load "p.a", .load "/p/a", .removeNs "p.a", .printNs, .ref "q/va", .ref "va"]

def extraPool (self : String) : List (Option Form) :=
  [none, some (.require [.sym (if self == "p.a" then "p.b" else "p.a")] []), some .boom, some (.ref "va")]

structure W where
  decisions : Decisions

instance : Chaotic W where
  decisions w := w.decisions
  setDecisions w d := { w with decisions := d }

def drawFile (lib : String) : EStateM Stop W (List Form) := do
  let c ← decide s!"{lib}.clause" (specPool.length + 1)
  let clauses := if c == 0 then [] else [Clause.require [specPool[c - 1]!]]
  let e ← decide s!"{lib}.extra" (extraPool lib).length
  let v := if lib == "p.a" then "va" else "vb"
  let base := [Form.ns lib clauses, .defv v, .print lib]
  pure (match (extraPool lib)[e]! with | some f => base ++ [f] | none => base)

/-! ## Neutralizations (one known difference each) -/

def mapFlags (f : List Flag → List Flag) : Form → Form
  | .require s fl => .require s (f fl)
  | .use s fl => .use s (f fl)
  | x => x

def noVerbose (fs : List Form) : List Form := fs.map (mapFlags (·.filter (· != .verbose)))

def setToListOpt : Opt → Opt
  | .referSet xs => .refer xs
  | o => o

partial def setToListSpec : Libspec → Libspec
  | .vec l opts => .vec l (opts.map setToListOpt)
  | .prefix p items => .prefix p (items.map setToListSpec)
  | s => s

def setToListClause : Clause → Clause
  | .require s => .require (s.map setToListSpec)
  | .use s => .use (s.map setToListSpec)
  | c => c

def setToList : Form → Form
  | .require s fl => .require (s.map setToListSpec) fl
  | .use s fl => .use (s.map setToListSpec) fl
  | .refer l o _ => .refer l o false
  | .ns n cs => .ns n (cs.map setToListClause)
  | x => x

def hasForm (p : Form → Bool) (files : Files) (prog : List Form) : Bool :=
  prog.any p || files.any (fun (_, fs) => fs.any p)

def isLoad : Form → Bool | .load _ => true | _ => false

partial def specHasPrefix : Libspec → Bool | .prefix _ _ => true | _ => false

def hasPrefix : Form → Bool
  | .require s _ | .use s _ => s.any specHasPrefix
  | .ns _ cs => cs.any fun c => match c with | .require s | .use s => s.any specHasPrefix | _ => false
  | _ => false

/-- The known features, each with its neutralization of a program and its files. -/
def neutralizers : List (String × (Form → Form) × (List Form → List Form)) :=
  [("F7 :verbose prints nothing", id, noVerbose),
   ("F6 :only/:refer accepts a set", setToList, id)]

def neutral (subset : List Nat) (fs : List Form) : List Form :=
  subset.foldl (fun acc i => match neutralizers[i]? with
    | some (_, f, g) => g (acc.map f)
    | none => acc) fs

/-- The smallest set of known features whose neutralization makes the two sides agree, given an
equality of outcomes `eq`. -/
def explain (files : Files) (prog : List Form) (eq : Files → List Form → Bool) : Option (List String) :=
  let subsets : List (List Nat) := [[0], [1], [0, 1]]
  (subsets.find? fun sub => eq (files.map fun (l, fs) => (l, neutral sub fs)) (neutral sub prog)).map
    fun sub => sub.filterMap fun i => (neutralizers[i]?).map (·.1)

def classify (files : Files) (prog : List Form) (j c : Outcome) : String :=
  let both (fs : Files) (pr : List Form) := (runTop .jank fs pr).norm == (runTop .clj fs pr).norm
  if j.norm == c.norm then "agree"
  else if hasForm hasPrefix files prog then "documented: no prefix lists (book: no nested require)"
  else match explain files prog both with
  | some names => " + ".intercalate names
  | none =>
    if hasForm isLoad files prog then "F4 load takes a module name, not a resource path"
    else if j.results.any (· == some "refer-conflict") then "refer conflict: jank throws (as refer's docstring says); Clojure 1.12 keeps or replaces"
    else "unexplained"

def body (maxOps : Nat) : EStateM Stop W Unit := do
  let fa ← drawFile "p.a"
  let fb ← drawFile "p.b"
  let files : Files := [("p.a", fa), ("p.b", fb)]
  let n ← decide "ops" maxOps
  let mut prog : List Form := []
  for i in [0:n+1] do
    let k ← decide s!"op{i}" topPool.length
    prog := prog ++ [topPool[k]!]
  let j := runTop .jank files prog
  let c := runTop .clj files prog
  if j.norm != c.norm then
    let cls := classify files prog j c
    if cls != "agree" then
      violate cls s!"files {repr files}; program {repr prog}; jank {repr j}; Clojure {repr c}"

def run (maxOps : Nat) (source : Source) : Ended :=
  match (body maxOps).run { decisions := { source } } with
  | .ok _ w => { taken := w.decisions.taken, violation := none }
  | .error (.violation p d) w => { taken := w.decisions.taken, violation := some (p, d) }
  | .error .limit w => { taken := w.decisions.taken, violation := none }
  | .error (.nodeDown _) w => { taken := w.decisions.taken, violation := none }

/-! ## run-main: the main module loaded by the CLI -/

def mainPool : List (List Form) := [[.printNs], [.ref "va"], [.require [.sym "p.b"] []], []]

def rmBody : EStateM Stop W Unit := do
  let fa ← drawFile "p.a"
  let fb ← drawFile "p.b"
  let files : Files := [("p.a", fa), ("p.b", fb)]
  let m ← decide "main" mainPool.length
  let main := mainPool[m]!
  let j := runMain .jank files "p.a" main
  let c := runMain .clj files "p.a" main
  -- When start-up throws on both sides the process exits with status 1 on both: only what was
  -- printed before is observable (Clojure's require also removes the main namespace; jank's
  -- load_module does not, but nothing runs after).
  let bothFail := j.results != [none] && c.results != [none]
  let differ := if bothFail then j.out != c.out else j.norm != c.norm
  if differ then
    let dropNs (o : Outcome) : Outcome := { o.norm with cur := "", out := o.out.filter (!·.startsWith "*ns*") }
    let rmEq (fs : Files) (m : List Form) : Bool :=
      let j' := runMain .jank fs "p.a" m
      let c' := runMain .clj fs "p.a" m
      if j'.results != [none] && c'.results != [none] then
        j'.out.filter (!·.startsWith "*ns*") == c'.out.filter (!·.startsWith "*ns*")
      else dropNs j' == dropNs c'
    let cls :=
      if dropNs j == dropNs c then "F1 run-main calls -main with *ns* = clojure.core (clojure -m: user)"
      else if hasForm hasPrefix files main then "documented: no prefix lists (book: no nested require)"
      else if let some names := explain files main rmEq then "F1 + " ++ " + ".intercalate names
      else if j.evals.length > c.evals.length then
        let noEvals (o : Outcome) : Outcome := { dropNs o with evals := [] }
        if noEvals j == noEvals c then
          "run-main: the main module is not on *pending-paths*: a cycle back to it evaluates its file once more before the cycle error (nothing else differs)"
        else "F16 run-main: the main module is not on *pending-paths*: a cycle back to it evaluates it again, with visible effects"
      else "unexplained"
    violate cls s!"files {repr files}; -main {repr main}; jank {repr j}; Clojure {repr c}"

def rmRun (source : Source) : Ended :=
  match rmBody.run { decisions := { source } } with
  | .ok _ w => { taken := w.decisions.taken, violation := none }
  | .error (.violation p d) w => { taken := w.decisions.taken, violation := some (p, d) }
  | .error .limit w => { taken := w.decisions.taken, violation := none }
  | .error (.nodeDown _) w => { taken := w.decisions.taken, violation := none }

end Jank.R4.Modules.LoadWorld
