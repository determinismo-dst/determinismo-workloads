import Jank.Analyzer.World
import Jank.Read
import Jank.ReadClj
import Jank.Strings.Print
import Jank.PrintModel
import Jank.Nrepl.Server

/-!
# Round 3, nREPL: the process state an evaluation reads and writes

Shared by the jank replica (`JankEval`) and the Clojure spec (`CljEval`):

- the heap: exception objects (`ex-info`, and those `safe_eval` builds from an `error_ref`),
  namespace objects, atoms, unrealized lazy sequences (`map`'s), closures' environments;
- vars (`runtime::var`): root (none: unbound), metadata, the `dynamic` flag;
- thread bindings (context.cpp `push_thread_bindings` 706, `pop_thread_bindings` 750,
  `get_thread_binding` var.cpp 145, `var::set` var.cpp 114): frames of var → box, newest first,
  a pushed frame copying the previous one's boxes (so `set!` of a var not rebound reaches the box
  every frame shares);
- the forms the readers give, as the analyzer's `Obj`: jank's reader attaches
  `{:jank/source {...}}` to lists, vectors, maps, sets and symbols (parse.cpp 388, 415, 488, 506,
  1898 → core/meta.cpp `source_to_meta` 213: `:module` only when the current `*ns*`'s
  `to_code_string` names a core module, loader.cpp 256/284; `:file` only when `*file*` is not
  `NO_SOURCE_PATH`); Clojure's (LispReader) attaches `{:line :column}` to lists only (left out:
  nothing in the grammar reads it);
- printers: jank `to_code_string` / `to_string` (strings through util/escape.cpp `escape`, the
  `Jank.Strings.Print` replica), Clojure `pr-str` / `str` (strings through core_print
  `char-escape-string`, `Jank.Print.cljPrStr`). Printed forms other than strings that differ between
  the two printers (doubles, functions, exceptions, namespaces) are another area's (REPORT-2
  R68–R77): the grammar does not print them, and functions/exceptions print as `#fn` / `#error`
  on both sides.
-/

namespace Jank.R3.Nrepl

open Jank.Analyzer

/-! ## Heap -/

/-- An exception object (`obj::exception_info` in jank, `ExceptionInfo`/`Throwable` in Clojure). -/
structure ExObj where
  msg : String
  data : Obj := .nil
  /-- Where it came from, for stories: `throw`, `read`, `analyze`, `runtime`. -/
  origin : String := "throw"
  deriving Repr, Inhabited

/-- `(map f coll)` not yet realized: `f` and the elements. -/
structure LazyMap where
  f : Obj
  xs : List Obj
  deriving Repr, Inhabited

structure Heap where
  exs : Array ExObj := #[]
  /-- Namespace objects, by name (`.opaque .ns k`). -/
  nsObjs : Array String := #[]
  atoms : Array Obj := #[]
  lazies : Array LazyMap := #[]
  deriving Inhabited

def Heap.newEx (h : Heap) (e : ExObj) : Heap × Obj :=
  ({ h with exs := h.exs.push e }, .opaque .exceptionInfo h.exs.size)

def Heap.nsObj (h : Heap) (name : String) : Heap × Obj :=
  match h.nsObjs.toList.idxOf? name with
  | some k => (h, .opaque .ns k)
  | none => ({ h with nsObjs := h.nsObjs.push name }, .opaque .ns h.nsObjs.size)

def Heap.nsName? (h : Heap) : Obj → Option String
  | .opaque .ns k => h.nsObjs[k]?
  | _ => none

def Heap.newAtom (h : Heap) (v : Obj) : Heap × Obj :=
  ({ h with atoms := h.atoms.push v }, .opaque .atom h.atoms.size)

def Heap.newLazy (h : Heap) (l : LazyMap) : Heap × Obj :=
  ({ h with lazies := h.lazies.push l }, .opaque .lazySequence h.lazies.size)

/-! ## Vars -/

/-- A var's value cells (`runtime::var`: `root`, `meta` (here `md`), `dynamic`). -/
structure Slot where
  root : Option Obj := none
  md : Obj := .nil
  dynamic : Bool := false
  deriving Inhabited

abbrev Slots := List (VarRef × Slot)

def Slots.get (s : Slots) (r : VarRef) : Slot := (s.lookup r).getD {}
def Slots.set (s : Slots) (r : VarRef) (v : Slot) : Slots := (r, v) :: s.filter (·.1 != r)
def Slots.modify (s : Slots) (r : VarRef) (f : Slot → Slot) : Slots := s.set r (f (s.get r))

/-- Metadata lookup on a map object. -/
def metaGet (m : Obj) (k : String) : Obj := m.get (kw k)

/-! ## Thread bindings -/

/-- One thread's binding frames (`context::thread_binding_frames[thread_id]`). -/
structure TB where
  boxes : Array Obj := #[]
  /-- Frames, newest first: var → box index. -/
  frames : List (List (VarRef × Nat)) := []
  deriving Inhabited

/-- `push_thread_bindings(bindings)` (context.cpp:706): the new frame starts as a copy of the
current one; each var of `bindings` gets a new box. -/
def TB.push (tb : TB) (bindings : List (VarRef × Obj)) : TB := Id.run do
  let mut frame := tb.frames.headD []
  let mut boxes := tb.boxes
  for (v, o) in bindings do
    frame := (v, boxes.size) :: frame.filter (·.1 != v)
    boxes := boxes.push o
  return { boxes, frames := frame :: tb.frames }

/-- `pop_thread_bindings` (context.cpp:750). -/
def TB.pop (tb : TB) : TB := { tb with frames := tb.frames.drop 1 }

/-- `var::get_thread_binding` (var.cpp:145): the box of the newest frame. -/
def TB.binding? (tb : TB) (v : VarRef) : Option Nat := (tb.frames.headD []).lookup v

/-- `var::deref`: the thread binding, else the root. -/
def TB.deref (tb : TB) (slots : Slots) (v : VarRef) : Option Obj :=
  match tb.binding? v with
  | some b => tb.boxes[b]?
  | none => (slots.get v).root

/-- `var::set` (var.cpp:114): the box of the newest frame; an error when the var is not bound on
this thread. -/
def TB.set (tb : TB) (v : VarRef) (o : Obj) : Except String TB :=
  match tb.binding? v with
  | some b => .ok { tb with boxes := tb.boxes.set! b o }
  | none => .error s!"Cannot set non-thread-bound var: #'{v.ns}/{v.name}"

def coreRef (n : String) : VarRef := ⟨"clojure.core", n⟩
def vNs : VarRef := coreRef "*ns*"
def vFile : VarRef := coreRef "*file*"
def v1 : VarRef := coreRef "*1"
def v2 : VarRef := coreRef "*2"
def v3 : VarRef := coreRef "*3"
def vE : VarRef := coreRef "*e"

/-! ## Printers -/

def bytesStr (b : List UInt8) : String := String.fromUTF8! (ByteArray.mk b.toArray)

/-- A printed form that does not depend on the printer for what the grammar prints. -/
inductive PrSide where
  | jank
  | clj
  deriving BEq, Inhabited

/-- `to_code_string` (jank) / `pr-str` (Clojure) of a realized value, without lazy sequences.
Strings: jank escape.cpp `escape` (`Jank.Strings.stringToCodeString`), Clojure
`char-escape-string` (`Jank.Print.cljPrStr`). -/
partial def prObj (side : PrSide) (h : Heap) : Obj → String
  | .nil => "nil"
  | .boolean b => if b then "true" else "false"
  | .integer v => s!"{v.toInt}"
  | .smallInteger v => s!"{v.toInt}"
  | .smallReal b | .real b => Jank.Analyzer.fmtDouble (Float.ofBits b)
  | .persistentString s =>
    match side with
    | .jank => bytesStr (Jank.Strings.stringToCodeString s.toUTF8.toList)
    | .clj => bytesStr (Jank.Print.cljPrStr (s.toList.map Char.toNat))
  | .keyword ns n => if ns.isEmpty then s!":{n}" else s!":{ns}/{n}"
  | .symbol _ ns n => if ns.isEmpty then n else s!"{ns}/{n}"
  | .persistentVector _ xs => "[" ++ " ".intercalate (xs.map (prObj side h)) ++ "]"
  | .persistentArrayMap _ kvs | .persistentHashMap _ kvs | .persistentSortedMap _ kvs =>
    "{" ++ ", ".intercalate (kvs.map fun (k, v) => prObj side h k ++ " " ++ prObj side h v) ++ "}"
  | .persistentHashSet _ xs | .persistentSortedSet _ xs => "#{" ++ " ".intercalate (xs.map (prObj side h)) ++ "}"
  | .var ns n => s!"#'{ns}/{n}"
  | .opaque .exceptionInfo _ => "#error"
  | .opaque .ns k => match side with
    | .jank => (h.nsObjs[k]?).getD "?"
    | .clj => s!"#object[clojure.lang.Namespace 0x… \"{(h.nsObjs[k]?).getD "?"}\"]"
  | .opaque .jitClosure _ | .opaque .nativeFunctionWrapper _ | .opaque .jitFunction _ => "#fn"
  | .opaque .atom _ => "#atom"
  | .opaque t i => s!"#object[{reprStr t} {i}]"
  | o => "(" ++ " ".intercalate ((o.elems.getD []).map (prObj side h)) ++ ")"

/-- `to_string` (jank, `str`/`print`) / `str` (Clojure): a string's own text, a namespace's name,
nil as empty for `str` (the caller drops nil), else the printed form. -/
def strObj (side : PrSide) (h : Heap) : Obj → String
  | .persistentString s => s
  | .opaque .ns k => (h.nsObjs[k]?).getD "?"
  | o => prObj side h o

/-! ## Forms from the readers -/

/-- Code points to a Lean string. -/
def cps (xs : List Nat) : String := String.ofList (xs.map Char.ofNat)

/-- jank's `source_to_meta(start, end)` (core/meta.cpp:213) for a form read while `*ns*` is
`curNs` and `*file*` is `file`. Positions are left out (no property reads them). -/
def jankSourceMeta (curNs file : String) : Obj :=
  let src : List (Obj × Obj) :=
    (if Jank.NreplServer.coreModules.contains curNs then [(kw "module", str curNs)] else [])
    ++ (if file != "NO_SOURCE_PATH" then [(kw "file", str file)] else [])
  .persistentArrayMap none [(kw "jank/source", .persistentArrayMap none src)]

/-- A value from jank's reader (`Jank.Read`) as the analyzer's object: `make_box(i64)` for
integers (a tagged `small_integer` within i32, parse.cpp:1944), interned keywords, persistent
strings; lists, vectors, maps, sets and symbols with the reader's source metadata. Values the
grammar does not produce (doubles, ratios, regexes, ...) are `none`. -/
partial def jankForm (curNs file : String) : Jank.ReadValue.Val → Option Obj
  | .nil => some .nil
  | .bool b => some (.boolean b)
  | .long v => some (Obj.ofInt v)
  | .str s => some (.persistentString (cps s))
  | .kw ns n => some (.keyword (cps ns) (cps n))
  | .sym ns n => some (.symbol (some (jankSourceMeta curNs file)) (cps ns) (cps n))
  | .list xs => do pure (.persistentList (some (jankSourceMeta curNs file)) (← xs.mapM (jankForm curNs file)))
  | .vec xs => do pure (.persistentVector (some (jankSourceMeta curNs file)) (← xs.mapM (jankForm curNs file)))
  | .map kvs => do
    let es ← kvs.mapM fun (k, v) => do pure (← jankForm curNs file k, ← jankForm curNs file v)
    pure (.persistentArrayMap (some (jankSourceMeta curNs file)) es)
  | .set xs => do pure (.persistentHashSet (some (jankSourceMeta curNs file)) (← xs.mapM (jankForm curNs file)))
  | .withMeta m v => do
    let m' ← jankForm curNs file m
    let v' ← jankForm curNs file v
    let merged := match v'.getMeta, m' with
      | some (.persistentArrayMap _ a), .persistentArrayMap _ b => Obj.persistentArrayMap none (a ++ b)
      | _, b => b
    pure (v'.setMeta (some merged))
  | _ => none

/-- A value from Clojure's reader (`Jank.ReadClj`) as an object (no source metadata: only
`:line`/`:column` on lists, which nothing reads here). -/
partial def cljForm : Jank.ReadValue.Val → Option Obj
  | .nil => some .nil
  | .bool b => some (.boolean b)
  | .long v => some (Obj.long v)
  | .str s => some (.persistentString (cps s))
  | .kw ns n => some (.keyword (cps ns) (cps n))
  | .sym ns n => some (.symbol none (cps ns) (cps n))
  | .list xs => do pure (.persistentList none (← xs.mapM cljForm))
  | .vec xs => do pure (.persistentVector none (← xs.mapM cljForm))
  | .map kvs => do
    let es ← kvs.mapM fun (k, v) => do pure (← cljForm k, ← cljForm v)
    pure (.persistentArrayMap none es)
  | .set xs => do pure (.persistentHashSet none (← xs.mapM cljForm))
  | .withMeta m v => do
    let m' ← cljForm m
    let v' ← cljForm v
    pure (v'.setMeta (some m'))
  | _ => none

/-! ## Output events -/

/-- What an evaluation writes, in order: `fwrite`/`putc` on `FILE* stdout` (core.cpp `print1` 161,
`println` 169, `prn` 213), or on stderr. -/
inductive OutEv where
  | out (b : List UInt8)
  | err (b : List UInt8)
  deriving Repr, BEq, Inhabited

def OutEv.bytes : OutEv → List UInt8
  | .out b | .err b => b

def outBytes (evs : List OutEv) : List UInt8 := evs.flatMap fun e => match e with
  | .out b => b
  | .err _ => []

end Jank.R3.Nrepl
