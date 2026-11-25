import Jank.R5.Errors.Model
import Jank.R3.Search.Common

/-!
# Round 5, errors: the program world

Each program is a small Clojure program that raises an error somewhere and then looks at it the
way a program can: which catch clause sees it, `ex-message`/`ex-data`/`ex-cause`, the root
cause's data, the namespaces, a var's metadata, how often a body ran, `*e`. Both sides run it
(the jank replica and the Clojure one of `Model.lean`) and the observations are compared.

A disagreement is classed by the mechanism that explains it; `unexplained` would be new. The
world is drawn by decisions and walked completely (`censusUnder`).
-/

namespace Jank.R5.Errors.World

open Determinismo Jank.R5.Errors

/-- Where the error comes from, as the caller runs it. -/
inductive Src where
  /-- `(read-string opts text)`; `opts` absent is the 1-arity. -/
  | readString (opt : EofOpt) (t : Text)
  /-- The form raised directly inside the caller's fn. -/
  | direct (i : Inner)
  /-- `(require lib)` of a lib missing from the module path. -/
  | requireMissing
  /-- `(require lib)` of a module whose top level raises after its `ns` form. -/
  | requireModule (i : Inner)
  /-- `(eval '(m))` with a macro `m` whose body raises. -/
  | macro (i : Inner)
  /-- `(eval '(def ^{:vb 1} x <raise>))`. -/
  | topDef (i : Inner)
  /-- `(deref (future <raise>))`. -/
  | future (i : Inner)
  deriving Repr, BEq, Inhabited

def Src.show : Src → String
  | .readString o t => s!"(read-string {o.show}{t.show})"
  | .direct i => i.show
  | .requireMissing => "(require 'missing)"
  | .requireModule i => s!"(require 'm) where m's top level runs {i.show}"
  | .macro i => s!"(eval '(m)) where macro m's body runs {i.show}"
  | .topDef i => s!"(eval '(def ^{"{"}:vb 1} x {i.show}))"
  | .future i => s!"@(future {i.show})"

def emptyNs : NsState := {}

def theModule (i : Inner) : Module := { lib := "jank-lean.r5-errors-fixture", raises := some i }

/-- jank: run the source in the caller (its result and the namespaces after). -/
def jSrc : Src → JRes × NsState
  | .readString o t => (jReadString o t, emptyNs)
  | .direct i => (.thrown (jInner i), emptyNs)
  | .requireMissing => (jRequireMissing, emptyNs)
  | .requireModule i => jLoadLib (theModule i) emptyNs
  | .macro i => (.thrown (jMacroConvert (jInner i)), emptyNs)
  | .topDef i => ((jTopDef ["vb"] false (some i)).1, emptyNs)
  | .future i => (jFuture (.thrown (jInner i)), emptyNs)

def cSrc : Src → CRes × NsState
  | .readString o t => (cReadString o t, emptyNs)
  | .direct i => (.thrown (cInner i), emptyNs)
  | .requireMissing => (cRequireMissing, emptyNs)
  | .requireModule i => cLoadLib (theModule i) emptyNs
  | .macro i => (.thrown (cMacroWrap i), emptyNs)
  | .topDef i => ((cTopDef ["vb"] false (some i)).1, emptyNs)
  | .future i => (cFuture (.thrown (cInner i)), emptyNs)

/-- Whether the source raises `Inner.exInfo` somewhere (so its data `{:k 1}` exists). -/
def Src.carriesData : Src → Bool
  | .direct .exInfo | .requireModule .exInfo | .macro .exInfo | .topDef .exInfo | .future .exInfo => true
  | _ => false

/-- What the program looks at. -/
inductive Look where
  /-- `(first (outcome f))`. -/
  | kind
  /-- The root data: `(let [[k e] (outcome f)] (when (= k :object) (data-with e :k)))`. -/
  | rootData
  /-- `(string? e)` of what the object catch got. -/
  | isString
  /-- `(find-ns lib)` after `(outcome f)`. -/
  | nsLeft
  deriving Repr, BEq, Inhabited, DecidableEq

def jRootData (r : JRes) : Option Data :=
  match r with
  | .thrown (.obj (.ex e)) => jDataWith e dataKey
  | _ => none

def cRootData (r : CRes) : Option Data :=
  match r with
  | .thrown e => cDataWith e dataKey
  | _ => none

def jIsString (r : JRes) : Bool :=
  match r with | .thrown (.obj (.str _)) => true | _ => false

def cIsString (_ : CRes) : Bool := false

/-- An observation, comparable across sides. -/
abbrev Obs := String

def jLook (s : Src) (l : Look) : Obs :=
  let (r, ns) := jSrc s
  match r with
  | .terminated w => s!"process ended: {w}"
  | _ =>
    match l with
    | .kind => (jOutcome r).show
    | .rootData => s!"{repr (jRootData r)}"
    | .isString => s!"{jIsString r}"
    | .nsLeft => s!"{ns.nss.contains "jank-lean.r5-errors-fixture"}"

def cLook (s : Src) (l : Look) : Obs :=
  let (r, ns) := cSrc s
  match l with
  | .kind => (cOutcome r).show
  | .rootData => s!"{repr (cRootData r)}"
  | .isString => s!"{cIsString r}"
  | .nsLeft => s!"{ns.nss.contains "jank-lean.r5-errors-fixture"}"

/-- The mechanism behind a disagreement of a `Src`/`Look` program. -/
def classify (s : Src) (l : Look) : String :=
  let (jr, _) := jSrc s
  match jr with
  | .terminated _ => "B6: a future whose body raises an error_ref ends the process"
  | _ =>
  match l, s with
  | .nsLeft, .requireModule _ => "B2: a failed require leaves the namespace it created"
  | .rootData, _ => "B3: an ex-info raised under the compiler or the loader loses its data"
  | .isString, .future _ => "B7: a failed future rethrows a native error as a string"
  | .kind, .readString _ .empty => "B11: read-string of a text without a form returns its eof value"
  | .kind, _ =>
    match jOutcome jr with
    | .error => "B1: an error_ref (read, analysis, load error) escapes the object catch"
    | .native => "known: a std::exception escapes the object catch (book native-exceptions.md; R26, U79)"
    | _ => "unexplained"
  | _, _ => "unexplained"

/-! ## Delays -/

/-- A delay program: `(let [d (delay body)] (outcome #(deref d)) (outcome #(deref d)))`, looking at
whether both derefs threw the same kind, and how often the body ran. -/
def delayBody (i : Option Inner) : JRes × CRes :=
  match i with
  | none => (.ok (.int 1), .ok (.int 1))
  | some i => (.thrown (jInner i), .thrown (cInner i))

def jDelayObs (i : Option Inner) : List Kind × Nat :=
  let (rs, d) := jDelayDerefs (delayBody i).1 2 {}
  (rs.map jOutcome, d.runs)

def cDelayObs (i : Option Inner) : List Kind × Nat :=
  let (rs, d) := cDelayDerefs (delayBody i).2 2 {}
  (rs.map cOutcome, d.runs)

/-- Every deref saw the same kind of exception. -/
def allSame : List Kind → Bool
  | [] => true
  | k :: ks => ks.all (· == k)

/-! ## Top-level def metadata, ex-info arguments, *e -/

def jDefMeta (i : Option Inner) : Obs := s!"{(jTopDef ["vb"] false i).2.metaKeys}"
def cDefMeta (i : Option Inner) : Obs := s!"{(cTopDef ["vb"] false i).2.metaKeys}"

/-- `(ex-message (ex-info msg {}))` -/
def jExInfoMsg (m : Option String) : Obs :=
  match jExInfo (match m with | some s => .str s | none => .nil) (.keys []) with
  | .ok v => match jExMessage v with
    | .ok (.str s) => s!"{some s}"
    | r => (jOutcome r).show
  | r => (jOutcome r).show

def cExInfoMsg (m : Option String) : Obs :=
  match cExInfo (match m with | some s => .str s | none => .nil) (.keys []) with
  | .ok v => s!"{cExMessage v}"
  | r => (cOutcome r).show

/-- `(ex-data (ex-info "m" data))` -/
def jExInfoData (d : Data) : Obs :=
  match jExInfo (.str "m") d with
  | .ok v => match jExData v with
    | .ok .nil => "nil"
    | .ok (.map d) => s!"{repr d}"
    | r => (jOutcome r).show
  | r => (jOutcome r).show

def cExInfoData (d : Data) : Obs :=
  match cExInfo (.str "m") d with
  | .ok v => match cExData v with
    | some d => s!"{repr d}"
    | none => "nil"
  | r => (cOutcome r).show

/-- At the nREPL after an eval that raised (jank's safe_eval; Clojure's `*e` is what was thrown):
`(ex-message *e)` empty or nil, `(ex-data *e)`, the root data through `ex-cause`. -/
def jStarEObs (s : Src) : Obs × Obs × Obs :=
  match (jSrc s).1 with
  | .thrown t =>
    let e := jStarE t
    (s!"{e.message != ""}", s!"{e.data != .nil}", s!"{jDataWith e dataKey |>.isSome}")
  | _ => ("-", "-", "-")

def cStarEObs (s : Src) : Obs × Obs × Obs :=
  match (cSrc s).1 with
  | .thrown e =>
    (s!"{(e.head?.bind (·.message)).isSome}", s!"{(e.head?.bind (·.data)).isSome}",
     s!"{(cDataWith e dataKey).isSome}")
  | _ => ("-", "-", "-")

/-! ## The world -/

structure W where
  decisions : Decisions := {}

instance : Chaotic W where
  decisions w := w.decisions
  setDecisions w d := { w with decisions := d }

abbrev WM := EStateM Stop W

def runW (body : WM Unit) (source : Source) : Ended :=
  match body.run { decisions := { source, limit := 1000 } } with
  | .ok _ w => { taken := w.decisions.taken, violation := none }
  | .error (.violation p d) w => { taken := w.decisions.taken, violation := some (p, d) }
  | .error .limit w => { taken := w.decisions.taken, violation := none }
  | .error (.nodeDown _) w => { taken := w.decisions.taken, violation := none }

def pickFrom {α : Type} [Inhabited α] (name : String) (xs : List α) : WM α := do
  let i ← decide (σ := W) name xs.length
  return xs.getD i default

def texts : List Text := [.form 7, .empty, .unterminated, .strayCloser]
def eofOpts : List EofOpt := [.absent, .eofthrow, .value 9]

def srcs : List Src :=
  (eofOpts.flatMap fun o => texts.map (Src.readString o)) ++
  Inner.all.map .direct ++ [.requireMissing] ++ Inner.all.map .requireModule ++
  Inner.all.map .macro ++ Inner.all.map .topDef ++ Inner.all.map .future

def looks : List Look := [.kind, .rootData, .isString, .nsLeft]

def check (j c : Obs) (cls : String) (detail : String) : WM Unit := do
  if j != c then violate (σ := W) cls s!"{detail}: Clojure {c}, jank {j}"

/-- One program of the world. -/
def program : WM Unit := do
  match ← decide (σ := W) "program.shape" 6 with
  | 0 =>
    let s ← pickFrom "src" srcs
    let l ← pickFrom "look" looks
    -- rootData only where the ex-info exists; nsLeft only after a require
    if l == .rootData && !s.carriesData then return
    if l == .nsLeft && !(match s with | .requireModule _ | .requireMissing => true | _ => false) then return
    if l == .isString && !(match s with | .future _ | .direct _ => true | _ => false) then return
    check (jLook s l) (cLook s l) (classify s l) s!"{s.show}, looking at {repr l}"
  | 1 =>
    let i ← pickFrom "delay.body" ([none] ++ Inner.all.map some)
    let (jk, jn) := jDelayObs i
    let (ck, cn) := cDelayObs i
    if allSame jk != allSame ck then
      violate (σ := W) "B4: a failed delay rethrows a native error as a string object"
        s!"(delay {(i.map Inner.show).getD "1"}) derefed twice, the kinds caught: Clojure {ck.map Kind.show}, jank {jk.map Kind.show}"
    if jn != cn then
      violate (σ := W) "B5: a delay whose body raises an error_ref runs it again"
        s!"(delay {(i.map Inner.show).getD "1"}) derefed twice, the body's runs: Clojure {cn}, jank {jn}"
  | 2 =>
    let i ← pickFrom "def.value" ([none] ++ Inner.all.map some)
    check (jDefMeta i) (cDefMeta i) "B8: a top-level def whose value raises keeps the def's metadata"
      s!"(def ^{"{"}:vb 1} x {(i.map Inner.show).getD "1"}), the var's metadata keys"
  | 3 =>
    let m ← pickFrom "exinfo.msg" [some "m", none]
    check (jExInfoMsg m) (cExInfoMsg m) "B9: ex-info rejects a nil message" s!"(ex-message (ex-info {(m.map (s!"\"{·}\"")).getD "nil"} {"{}"}))"
  | 4 =>
    let d ← pickFrom "exinfo.data" [Data.keys [], .keys ["k"], .nil]
    check (jExInfoData d) (cExInfoData d) "B10: (ex-info m nil) keeps nil data (Clojure 1.12: {})"
      s!"(ex-data (ex-info \"m\" {repr d}))"
  | _ =>
    let s ← pickFrom "nrepl.src" srcs
    let (jm, jd, jr) := jStarEObs s
    let (cm, cd, cr) := cStarEObs s
    -- what an exception without a message gives is a design of each side; compare the data
    -- *e carries and whether the root cause's data is reachable
    if (jSrc s).1 matches .terminated _ then return
    if jd == "-" && cd != "-" then
      violate (σ := W) "B11: read-string of a text without a form returns its eof value" s!"*e after {s.show}: Clojure sets it, jank evaluates without error"
    check jd cd "U44+: (ex-data *e) after a compile or load error is nil" s!"*e after {s.show}, (some? (ex-data *e))"
    check jr cr "U44+: *e loses the cause's data after a compile or load error" s!"*e after {s.show}, root data"
    let _ := (jm, cm)

def run : Source → Ended := runW program

end Jank.R5.Errors.World
