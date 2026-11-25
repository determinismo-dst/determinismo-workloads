import Jank.Analyzer.Spec

/-!
# The world the programs run in

The namespaces (`clojure.core`, `user`, `other`), the core vars with their metadata (`:macro`,
`:inline`, `:inline-arities`, `:private`) as core.jank defines them, a few user macros, and the
two runners: jank (each top-level form analyzed by a fresh `processor` in statement position,
`pass::optimize`d, then evaluated, as `context::eval_string` does, context_dynamic.cpp:49) and
Clojure (`Compiler.eval` of each form).
-/

namespace Jank.Analyzer

/-- A list form as the reader produces it: with `:jank/source` meta. -/
def L (xs : List Obj) : Obj := .persistentList (some sourceMeta) xs
def V (xs : List Obj) : Obj := .persistentVector none xs
def S (n : String) : Obj := Obj.s n
def I (i : Int) : Obj := Obj.ofInt i
def D (f : Float) : Obj := .smallReal f.toBits
def K (n : String) : Obj := kw n
def B (b : Bool) : Obj := .boolean b

/-- `when` (core.jank:855): `(list 'if condition (cons 'do body) nil)`. -/
def whenMacro : MacroFn
  | _ :: _ :: c :: body => .ok (.persistentList none [S "if", c, .persistentList none (S "do" :: body), .nil])
  | _ => .error "Wrong number of args passed to: when"

/-- `let` (core.jank:642): `` `(let* ~@decl) ``. -/
def letMacro : MacroFn
  | _ :: _ :: decl => .ok (.persistentList none (S "let*" :: decl))
  | _ => .error "Wrong number of args passed to: let"

/-- `loop` without destructuring (core.jank:3586, `(= db all-bindings)`): `` `(loop* ~@decl) ``. -/
def loopMacro : MacroFn
  | _ :: _ :: decl => .ok (.persistentList none (S "loop*" :: decl))
  | _ => .error "Wrong number of args passed to: loop"

/-- `fn` (core.jank:650): `` (with-meta `(fn* ~@decl) (meta &form)) ``. -/
def fnMacro : MacroFn
  | form :: _ :: decl => .ok ((Obj.persistentList none (S "fn*" :: decl)).setMeta form.getMeta)
  | _ => .error "Wrong number of args passed to: fn"

/-- `or` (core.jank:883): `(let [g x] (if g g (or more...)))`, `g` a gensym. -/
def orMacro : MacroFn
  | _ :: _ :: [] => .ok .nil
  | _ :: _ :: [x] => .ok x
  | _ :: _ :: x :: more => .ok (.persistentList none [Obj.sym "clojure.core" "let", V [S "or__g", x],
      .persistentList none [S "if", S "or__g", S "or__g", .persistentList none (Obj.sym "clojure.core" "or" :: more)]])
  | _ => .error "arity"

/-- `and` (core.jank:899): `(let [g x] (if g (and more...) g))`. -/
def andMacro : MacroFn
  | _ :: _ :: [] => .ok (.boolean true)
  | _ :: _ :: [x] => .ok x
  | _ :: _ :: x :: more => .ok (.persistentList none [Obj.sym "clojure.core" "let", V [S "and__g", x],
      .persistentList none [S "if", S "and__g", .persistentList none (Obj.sym "clojure.core" "and" :: more), S "and__g"]])
  | _ => .error "arity"

/-- The `case` clauses as (integer test, then) pairs and the default (or the `throw` jank's macro
uses without one). -/
def caseClauses (clauses : List Obj) (ge : Obj) : List (Obj × Obj) × Obj :=
  let rec pairs : List Obj → List (Obj × Obj)
    | t :: e :: rest => (t, e) :: pairs rest
    | _ => []
  let dflt := if clauses.length % 2 == 1 then clauses.getLastD .nil
    else .persistentList none [S "throw", .persistentList none [S "str", str "No matching clause: ", ge]]
  (pairs clauses, dflt)

/-- `case` (core.jank:4465 at 7135b7708) for integer tests that fit a table (`prep-ints`,
`fits-table?`): `(let [ge e] (case* ge 0 0 default imap))`, `imap` a sorted map from each test to
`(condp = ge test then default)` (`case-map-with-check`, core.jank:4332), which `condp`
(core.jank) expands to `(let [pred = expr ge] (if (pred test expr) then default))`. -/
def caseMacro : MacroFn
  | _ :: _ :: e :: clauses =>
    let ge := S "G__case"
    let (ps, dflt) := caseClauses clauses ge
    if clauses.length < 2 then .ok (.persistentList none [S "let*", V [ge, e], dflt])
    else
      let entries := ps.map fun (t, th) =>
        (t, .persistentList none [S "let*", V [S "pred__", S "=", S "expr__", ge],
              .persistentList none [S "if", .persistentList none [S "pred__", t, S "expr__"], th, dflt]])
      let key : Obj → Int := fun o => (match o with | .smallInteger v => v.toInt | .integer v => v.toInt | _ => 0)
      let sorted := entries.mergeSort fun a b => key a.1 ≤ key b.1
      .ok (.persistentList none [S "let*", V [ge, e],
        .persistentList none [S "case*", ge, I 0, I 0, dflt, .persistentSortedMap none sorted]])
  | _ => .error "Wrong number of args passed to: case"

/-- Clojure's `case` for integer tests, as its meaning: the first test equal to the value. -/
def cljCaseMacro : MacroFn
  | _ :: _ :: e :: clauses =>
    let ge := S "G__case"
    let (ps, dflt) := caseClauses clauses ge
    let body := ps.foldr (fun (t, th) acc =>
      .persistentList none [S "if", .persistentList none [S "=", ge, t], th, acc]) dflt
    .ok (.persistentList none [S "let*", V [ge, e], body])
  | _ => .error "Wrong number of args passed to: case"

/-- `(defmacro form-of [& _] (list 'quote &form))`. -/
def formOfMacro : MacroFn
  | form :: _ :: _ => .ok (.persistentList none [S "quote", form])
  | _ => .error "arity"

/-- `(defmacro env-count [] (count &env))`. -/
def envCountMacro : MacroFn
  | _ :: env :: _ => match env.elems with
    | some xs => .ok (Obj.long xs.length)
    | none => .error s!"count not supported on this type: {reprStr env.type}"
  | _ => .error "arity"

/-- `(defmacro mk-vec [& xs] (vec xs))`. -/
def mkVecMacro : MacroFn
  | _ :: _ :: xs => .ok (.persistentVector none xs)
  | _ => .error "arity"

/-- `(defmacro mk-map [k v] (hash-map k v))`. -/
def mkMapMacro : MacroFn
  | _ :: _ :: [k, v] => .ok (.persistentArrayMap none [(k, v)])
  | _ => .error "arity"

/-- `(defmacro secret-of [] 'other/secret)` defined in `other` (public macro, private var). -/
def secretOfMacro : MacroFn
  | _ :: _ :: _ => .ok (Obj.sym "other" "secret")
  | _ => .error "arity"

/-- `inc`'s `:inline` (core.jank:1646): `(list 'cpp/jank.runtime.inc x)`. -/
def incInline : MacroFn
  | [x] => .ok (.persistentList none [Obj.sym "cpp" "jank.runtime.inc", x])
  | _ => .error "inline arity"

/-- `+`'s `:inline` (core.jank:1372): `(list 'cpp/jank.runtime.add l r)`, arities `#{2}`. -/
def addInline : MacroFn
  | [l, r] => .ok (.persistentList none [Obj.sym "cpp" "jank.runtime.add", l, r])
  | _ => .error "inline arity"

/-- `*`'s `:inline` (core.jank:1405): `(list 'cpp/jank.runtime.mul l r)`, arities `#{2}`. -/
def mulInline : MacroFn
  | [l, r] => .ok (.persistentList none [Obj.sym "cpp" "jank.runtime.mul", l, r])
  | _ => .error "inline arity"

/-- `pos?`'s `:inline` (core.jank:1664): `(list 'cpp/jank.runtime.is_pos x)`. -/
def posInline : MacroFn
  | [x] => .ok (.persistentList none [Obj.sym "cpp" "jank.runtime.is_pos", x])
  | _ => .error "inline arity"

def coreVars : List VarCell :=
  [ { ns := "clojure.core", name := "=", bound := true },
    { ns := "clojure.core", name := "nil?", bound := true },
    { ns := "clojure.core", name := "meta", bound := true },
    { ns := "clojure.core", name := "vector", bound := true },
    { ns := "clojure.core", name := "list", bound := true },
    { ns := "clojure.core", name := "count", bound := true },
    { ns := "clojure.core", name := "first", bound := true },
    { ns := "clojure.core", name := "rest", bound := true },
    { ns := "clojure.core", name := "str", bound := true },
    { ns := "clojure.core", name := "inc", bound := true, inline := some incInline, inlineArities := some [1] },
    { ns := "clojure.core", name := "+", bound := true, inline := some addInline, inlineArities := some [2] },
    { ns := "clojure.core", name := "<", bound := true },
    { ns := "clojure.core", name := "*", bound := true, inline := some mulInline, inlineArities := some [2] },
    { ns := "clojure.core", name := "pos?", bound := true, inline := some posInline, inlineArities := some [1] },
    { ns := "clojure.core", name := "when", isMacro := true, macroFn := some whenMacro, bound := true },
    { ns := "clojure.core", name := "let", isMacro := true, macroFn := some letMacro, bound := true },
    { ns := "clojure.core", name := "loop", isMacro := true, macroFn := some loopMacro, bound := true },
    { ns := "clojure.core", name := "fn", isMacro := true, macroFn := some fnMacro, bound := true },
    { ns := "clojure.core", name := "or", isMacro := true, macroFn := some orMacro, bound := true },
    { ns := "clojure.core", name := "case", isMacro := true, macroFn := some caseMacro,
      cljMacroFn := some cljCaseMacro, bound := true },
    { ns := "clojure.core", name := "and", isMacro := true, macroFn := some andMacro, bound := true } ]

def userVars : List VarCell :=
  [ { ns := "user", name := "form-of", isMacro := true, macroFn := some formOfMacro, bound := true },
    { ns := "user", name := "env-count", isMacro := true, macroFn := some envCountMacro, bound := true },
    { ns := "user", name := "mk-vec", isMacro := true, macroFn := some mkVecMacro, bound := true },
    { ns := "user", name := "mk-map", isMacro := true, macroFn := some mkMapMacro, bound := true },
    { ns := "other", name := "secret", private_ := true, bound := true },
    { ns := "other", name := "secret-of", isMacro := true, macroFn := some secretOfMacro, bound := true } ]

/-- The runtime at the start of every program: `user` refers every `clojure.core` var. -/
def baseRuntime : Runtime :=
  let core := coreVars.map fun v => (v.name, v.ref)
  { namespaces := [
      { name := "clojure.core", mappings := core },
      { name := "user", mappings := core ++ (userVars.filter (·.ns == "user")).map fun v => (v.name, v.ref) },
      { name := "other", mappings := (userVars.filter (·.ns == "other")).map fun v => (v.name, v.ref) } ],
    vars := coreVars ++ userVars, currentNs := "user" }

def baseRoots : List (VarRef × VarRoot) :=
  (coreVars.filter (!·.isMacro)).map (fun v => (v.ref, VarRoot.builtin v.name))
  ++ [(⟨"other", "secret"⟩, .obj (Obj.long 42))]

/-- What a jank run leaves: its outcome and the model notes. -/
structure JankRun where
  outcome : Outcome
  notes : List String
  /-- Every top-level form's analysis state (for inspection). -/
  states : List AnState := []

/-- Runs forms through jank: per form, a fresh `processor` (new root frame) analyzes it in
statement position, `pass::optimize` runs, then the evaluation. The arena is kept across forms so
closures stay valid. -/
def runJank (forms : List Obj) (oracle : Oracle := {}) : JankRun := Id.run do
  let mut rt := baseRuntime
  let mut ar : Arena := {}
  let mut ev : EvState := { arena := {}, roots := baseRoots }
  let mut last : Outcome := .value .nil
  let mut notes : List String := []
  let mut states : List AnState := []
  for form in forms do
    let (ar', root) := ar.addFrame { type := .root }
    let s0 : AnState := { arena := ar', rt, rootFrame := root, oracle }
    let (r, s1) := runAnalysis (do let e ← analyzeTop form .statement; optimize e) s0
    states := states ++ [s1]
    notes := notes ++ s1.notes
    match r with
    | .error (.thrown e) => return { outcome := .compileError s!"{e.kind}: {e.message}", notes, states }
    | .error (.ub w) => return { outcome := .ub w, notes, states }
    | .error .fuel => return { outcome := .fuel, notes, states }
    | .ok (.error e) => return { outcome := .compileError s!"{e.kind}: {e.message}", notes, states }
    | .ok (.ok e) =>
      rt := s1.rt
      ar := s1.arena
      match (evalTop e).run { ev with arena := ar } with
      | .ok (v, ev') =>
        ev := ev'
        last := .value v
      | .error o => return { outcome := o, notes, states }
  return { outcome := last, notes, states }

/-- Runs forms through the Clojure spec (`Compiler.eval` per form). -/
def runClojure (forms : List Obj) : Outcome := Id.run do
  let mut st : CState := { rt := baseRuntime }
  let mut ev : CEvState := { roots := baseRoots }
  let mut last : Outcome := .value .nil
  for form in forms do
    match (cljAnalyze form {} .expr).run st with
    | .error o => return o
    | .ok (ce, st') =>
      st := st'
      match (cEvalV ce []).run ev with
      | .ok (v, ev') =>
        ev := ev'
        last := .value v
      | .error o => return o
  return last

end Jank.Analyzer
