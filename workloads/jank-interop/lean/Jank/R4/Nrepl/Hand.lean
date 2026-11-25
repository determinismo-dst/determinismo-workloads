import Jank.R4.Nrepl.JEval

/-!
# Round 3, nREPL: jank's handlers on the wired evaluator

- `safe_eval`'s bookkeeping (evaluate.cpp:733): after `eval_string` returned `v` (or none,
  `unwrap`ped: a zeroed `object_ref`, the double 0.0 in a release build, an abort in a debug one,
  REPORT-2 R132), `*3 ← *2`, `*2 ← *1`, `*1 ← v` with `var::set` (the thread's boxes); after an
  exception, `*e` ← the exception (an `ex_info` built from an `error_ref`'s or a non-`ex_info`
  object's text).
- `do-eval` (handler/eval.jank:22): `:no-code` for empty code, `:namespace-not-found` when the `ns`
  field names no namespace (`(-> ns symbol find-ns)`), else `with-capture` around
  `(binding [*ns* target-ns *file* file-path] [(safe-eval code line col) *ns*])`; the replies
  `[(out) (err) {:value (pr-str *1) :ns (str res-ns)} {:status [:done]}]`, or
  `[(out) (err) {:err (str *e)} {:ex (str *e) :status [:done :eval-error]}]`; `inspect`: `{:value
  (inspect-str *1) :status [:done]}`. `(pr-str *1)` runs after the capture ended, so what it
  prints (a lazy sequence's side effects) is not captured, and an exception it throws leaves
  `do-eval`: core.jank `handle-client`'s `catch` answers `{:status [:error :done] :err ...}`
  (REPORT-2 R126).
- `lookup`/`info` (handler/lookup.jank) and `completions` (handler/completions.jank) on the
  process's namespaces.

`replies` values are the handler's maps before `responses-for` (core.jank:39) adds `id` and
`session`.
-/

namespace Jank.R4.Nrepl
open Jank.R3.Nrepl

open Jank.Analyzer
open Jank.NreplServer (JVal kmap statusOf responsesFor strField coreModules specialForms)

/-! ## jank objects as bencode data (what `bencode/write` sees) -/

/-- The `JVal` of a jank object the handlers put in a reply (strings, keywords, symbols, numbers,
collections, nil, booleans). -/
partial def toJVal (h : Heap) : Obj → JVal
  | .nil => .nil
  | .boolean b => .bool b
  | .integer v => .int v.toInt
  | .smallInteger v => .int v.toInt
  | .persistentString s => JVal.s s
  | .keyword ns n => .kw (if ns.isEmpty then none else some (Jank.NreplServer.bytes ns)) (Jank.NreplServer.bytes n)
  | .symbol _ ns n => .sym (if ns.isEmpty then none else some (Jank.NreplServer.bytes ns)) (Jank.NreplServer.bytes n)
  | .persistentVector _ xs => .vec (xs.map (toJVal h))
  | .persistentList _ xs => .list (xs.map (toJVal h))
  | .persistentHashSet _ xs | .persistentSortedSet _ xs => .set (xs.map (toJVal h))
  | .persistentArrayMap _ kvs | .persistentHashMap _ kvs | .persistentSortedMap _ kvs =>
    .map (kvs.map fun (k, v) => (toJVal h k, toJVal h v))
  | .smallReal b | .real b => .real (Jank.Analyzer.fmtDouble (Float.ofBits b))
  | o => .str (Jank.NreplServer.bytes (prObj .jank h o))

/-! ## `safe_eval` -/

/-- The value `unwrap` gives for `jtl::none` in a release build: a zeroed `object_ref`, which
oref.hpp decodes as the double +0.0 (REPORT-2 R132). -/
def real0 : Obj := .smallReal 0

/-- `safe_eval`'s bookkeeping once `eval_string` returned or threw. `debug`: a debug build, where
`unwrap` of none aborts. -/
def finishSafeEval (s : ES) (r : Except Fail (Option Obj)) (debug : Bool) : ES × EvalEnd :=
  match r with
  | .ok v =>
    let value := match v with
      | some v => some v
      | none => if debug then none else some real0
    match value with
    | none => (s, .crash "jank_debug_assert(set) in option::unwrap: abort()")
    | some value =>
      let tb := s.tb
      let o1 := (tb.deref s.w.slots v1).getD .nil
      let o2 := (tb.deref s.w.slots v2).getD .nil
      -- var::set on the thread's boxes (always bound on a connection thread: connTB).
      let tb := (tb.set v3 o2).toOption.getD tb
      let tb := (tb.set v2 o1).toOption.getD tb
      let tb := (tb.set v1 value).toOption.getD tb
      ({ s with tb }, .ok value)
  | .error (.unsupported w) =>
    if w.startsWith "HANG" then (s, .hang w)
    else if w.startsWith "CRASH" then (s, .crash w)
    else (s, .unsupported w)
  | .error .fuel => (s, .unsupported "fuel")
  | .error (.ub w) => (s, .unsupported s!"UB {w}")
  | .error f =>
    let (s, e) := failObj s f
    let tb := (s.tb.set vE e).toOption.getD s.tb
    ({ s with tb }, .failed e)

/-- `eval_string` and `safe_eval` run to their end with no other thread (World S): the steps of
`EvRun`, output events collected in order. -/
def runSafeEval (s : ES) (code : List UInt8) (file : String) (debug : Bool) (maxSteps : Nat := 400) :
    ES × EvalEnd × List OutEv × List Obj := Id.run do
  let mut r := EvRun.start code
  let mut s := s
  let mut out : Array OutEv := #[]
  for _ in [0:maxSteps] do
    if r.isDone then break
    let (r', s', ev) := r.step s file
    r := r'
    s := s'
    if let some e := ev then out := out.push e
  match r.phase with
  | .done res =>
    let (s2, e) := finishSafeEval s res debug
    return (s2, e, out.toList, r.forms)
  | _ => return (s, .unsupported "step bound", out.toList, r.forms)

/-! ## `do-eval` -/

/-- An eval request's fields as `handle-message :eval` reads them (handler/eval.jank:66). -/
structure EvalReq where
  ns : Option String := none
  code : String
  file : String := "NO_SOURCE_PATH"
  inspect : Option Bool := none
  deriving Repr, Inhabited

/-- What `do-eval` decides before evaluating. -/
inductive Pre where
  | reply (r : JVal)
  | run (target : String)
  deriving Inhabited

/-- `do-eval`'s checks (lines 23–29): empty code; `(-> ns symbol find-ns)`. -/
def doEvalPre (w : JW) (q : EvalReq) : Pre :=
  if q.code.isEmpty then .reply (kmap [("status", statusOf ["no-code", "done"])])
  else
    let target := match q.ns with
      | some n => if (w.nss.find? (·.name == n)).isSome then some n else none
      | none => some "user"
    match target with
    | none => .reply (kmap [("status", statusOf ["namespace-not-found", "done"])])
    | some t => .run t

/-- `inspect-str` (inspect.jank:19), abstractly: its printed contents. -/
def inspectStr (h : Heap) (v : Obj) : String := s!"(\"--- Type\" ... (:value \"{prObj .jank h v}\") ...)"

/-- `(when-not (blank? stdout) {:out stdout})` (handler/eval.jank:41, 57). -/
def outReply (stdout : List UInt8) : JVal :=
  if Jank.NreplServer.blank (some stdout) then JVal.nil else kmap [("out", .str stdout)]

/-- `(when-not (blank? stderr) {:err stderr})` (handler/eval.jank:42, 58). -/
def errReply (stderr : List UInt8) : JVal :=
  if Jank.NreplServer.blank (some stderr) then JVal.nil else kmap [("err", .str stderr)]

/-- `doEvalReplies`, with what `(pr-str *1)` printed while realizing the value: written to the
process's stdout after the capture ended (it never reaches the client's `:out`). -/
def doEvalRepliesOut (s : ES) (success : Bool) (resNs : String) (stdout stderr : List UInt8)
    (inspect : Option Bool) : ES × Except String JVal × List OutEv :=
  let outR := outReply stdout
  let errR := errReply stderr
  let starE := (s.tb.deref s.w.slots vE).getD .nil
  let star1 := (s.tb.deref s.w.slots v1).getD .nil
  if !success then
    let es := strObj .jank s.w.heap starE
    (s, .ok (.vec [outR, errR, kmap [("err", JVal.s es)],
                   kmap [("ex", JVal.s es), ("status", statusOf ["done", "eval-error"])]]), [])
  else if inspect == some true then
    (s, .ok (kmap [("value", JVal.s (inspectStr s.w.heap star1)), ("status", statusOf ["done"])]), [])
  else
    -- `(pr-str *1)`: realizing a lazy value may throw (and print, uncaptured).
    match (prOf star1).run { s with out := #[] } with
    | .ok txt s' =>
      ({ s' with out := #[] }, .ok (.vec [outR, errR, kmap [("value", JVal.s txt), ("ns", JVal.s resNs)],
                                          kmap [("status", statusOf ["done"])]]), s'.out.toList)
    | .error f s' => ({ s' with out := #[] }, .error (f.show s'.w.heap), s'.out.toList)

/-- `do-eval`'s `cond` after the capture (lines 38–64): the replies, or the exception `pr-str`
threw (a lazy value's realization). `stdout`/`stderr` are what `readback` returned. -/
def doEvalReplies (s : ES) (success : Bool) (resNs : String) (stdout stderr : List UInt8)
    (inspect : Option Bool) : ES × Except String JVal :=
  let (s', r, _) := doEvalRepliesOut s success resNs stdout stderr inspect
  (s', r)


/-! ## lookup, info, completions -/

/-- `ns::find_var` (ns.cpp:117) with `qualify_symbol` (context.cpp:116) resolving the alias against
`current`, the calling thread's `*ns*` (REPORT-2 R111). -/
def jankNsResolve (w : JW) (current : String) (n : NsCell) (sym : Option String × String) : Option VarRef :=
  match sym with
  | (some q, name) =>
    let cur := (w.nss.find? (·.name == current))
    let qns := match cur.bind (·.aliases.lookup q) with
      | some a => a
      | none => q
    (w.nss.find? (·.name == qns)).bind fun t => t.mappings.lookup name
  | (none, name) => n.mappings.lookup name

/-- Clojure's `ns-resolve` (Compiler.maybeResolveIn → namespaceFor(n, sym)): the alias in `n`. -/
def cljNsResolve (nss : List NsCell) (n : NsCell) (sym : Option String × String) : Option VarRef :=
  match sym with
  | (some q, name) =>
    let target := (n.aliases.lookup q).getD q
    (nss.find? (·.name == target)).bind fun t => t.mappings.lookup name
  | (none, name) => n.mappings.lookup name

/-- handler/lookup.jank `lookup` (11): `(or (some-> ns symbol find-ns) default-ns)` — the
namespace a lookup searches. -/
def lookupTarget (w : JW) (ns : Option String) : Option NsCell :=
  match ns.bind fun n => w.nss.find? (·.name == n) with
  | some n => some n
  | none => w.nss.find? (·.name == "user")

/-- handler/lookup.jank `lookup` (5) and `handle` (18) on the process. -/
def lookupReply (w : JW) (current : String) (req : JVal) : JVal :=
  let ns := strField req "ns"
  let sym := match strField req "sym" with
    | some s => some s
    | none => strField req "symbol"
  let ns' := lookupTarget w ns
  let found := match ns', sym with
    | some n, some s => jankNsResolve w current n (Jank.NreplServer.splitSym s)
    | _, _ => none
  match found with
  | some r =>
    let m := (w.slots.get r).md
    let info := Jank.NreplServer.merge [
      kmap [("ns", toJVal w.heap ((metaGet m "jank/source").get (kw "module"))), ("name", (sym.map JVal.s).getD .nil)],
      (match metaGet m "doc" with
        | .nil => .nil
        | d => kmap [("doc", JVal.s (strObj .jank w.heap d))]),
      (match metaGet m "arglists" with
        | .nil => .nil
        | a => kmap [("arglists", toJVal w.heap a), ("arglists-str", JVal.s (strObj .jank w.heap a))])]
    let body := if strField req "op" == some "info" then info else kmap [("info", info)]
    Jank.NreplServer.merge [body, kmap [("status", statusOf ["done"])]]
  | none => kmap [("status", statusOf ["no-info", "done"])]

/-- handler/completions.jank `handle` (66): `vars-candidates` over `ns-map`, then the special
forms; `:ns` is the namespace searched (`(str ns)`). -/
def completionsReply (w : JW) (req : JVal) : JVal :=
  let pfx := match strField req "prefix" with
    | some p => some p
    | none => strField req "symbol"
  match (strField req "ns").bind (fun n => w.nss.find? (·.name == n)), pfx with
  | some n, some pfx =>
    let vars := n.mappings.filterMap fun (k, r) =>
      if k.startsWith pfx then
        let m := (w.slots.get r).md
        let ty := if (metaGet m "macro").truthy then "macro" else if (metaGet m "arglists").truthy then "function" else "var"
        some (kmap [("ns", JVal.s n.name), ("type", JVal.k ty), ("candidate", JVal.s k)])
      else none
    let specials := specialForms.filterMap fun k =>
      if k.startsWith pfx then some (kmap [("type", JVal.k "special-form"), ("candidate", JVal.s k)])
      else none
    kmap [("completions", .vec (vars ++ specials)), ("status", statusOf ["done"])]
  | _, _ => kmap [("status", statusOf ["done", "namespace-not-found"])]

end Jank.R4.Nrepl
