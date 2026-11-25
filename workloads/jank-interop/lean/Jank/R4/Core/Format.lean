import Jank.R4.Core.Value

/-!
# Round 4: `format` and `printf`

**jank** (core.jank 6950–6958): `(defn format "Formats a string using std::format." [fmt & args]
(cpp/jank.runtime.format fmt args))`; `printf` prints `(apply format fmt args)`.
core.cpp `format` 237–369 scans the string itself:
- `{{` / `}}` at depth 0 are escapes (259–264);
- `{` opens a field (265): a digit after it is a manual index (271–297, the digits are dropped
  from the field text), otherwise an automatic one (301–316); mixing them throws;
- `}` closes it (318); at depth 0 the field text (e.g. `{}`, `{:x}`) goes to `std::vformat` with
  the next argument (325–359), index past the arguments → `std::format_error`;
- any other character is copied (361–371); an unbalanced brace throws (374–377).
detail/std_format.hpp `vformat_object_to`: an integer is formatted as `i64`, a real as `f64`,
anything else as its `to_string`. `%` is an ordinary character.

**Clojure**: `(format fmt & args)` is `String/format` (java.util.Formatter): `%s`, `%d`, `%a`,
`%%`, `%n`, …; braces are ordinary characters; a missing argument throws
MissingFormatArgumentException, a conversion that does not fit the argument throws
IllegalFormatConversionException, an unknown one UnknownFormatConversionException.

The replica covers the alphabet the search uses (`% s d a { }` and letters) on both sides; the
std::format field grammar is replicated for fields made of that alphabet: `{}` formats its
argument, `{` followed by anything but a digit, `:` or `}` is an invalid argument id
(`std::format_error`).
-/

namespace Jank.R4.Core.Format

open Jank.R4.Core

inductive Arg where
  | long (i : Int)
  | dbl (text : String) (hexA : String) (stdfmt : String)
  | str (s : String)
  deriving Repr, Inhabited

def Arg.code : Arg → String
  | .long i => toString i
  | .dbl t _ _ => t
  | .str s => "\"" ++ s ++ "\""

/-- A format result: the string, or a thrown error (only that something is thrown is compared). -/
inductive FR where
  | ok (s : String)
  | err (why : String)
  deriving Repr, Inhabited, BEq, DecidableEq

def FR.same : FR → FR → Bool
  | .ok a, .ok b => a == b
  | .err _, .err _ => true
  | _, _ => false

def FR.show : FR → String
  | .ok s => "\"" ++ s ++ "\""
  | .err w => s!"throws ({w})"

/-- std::format of one field `{…}` with its argument (`vformat_object_to`). -/
def stdFormatField (field : List Char) (a : Arg) : FR :=
  match field with
  | ['{', '}'] =>
    match a with
    | .long i => .ok (toString i)
    | .dbl _ _ s => .ok s
    | .str s => .ok s
  | _ => .err "std::format_error: invalid argument id or format spec"

/-- The scanner's state (core.cpp `format` 241–257). `digits` is set while a manual index is
being read (285–293 skip those digits; here they are consumed one per step); `skip` is set after
a `{{`/`}}` escape (259–264 advance past the second brace). -/
structure St where
  out : String := ""
  field : List Char := []
  depth : Int := 0
  /-- 0 unspecified, 1 automatic, 2 manual (`indexing_mode`). -/
  mode : Nat := 0
  idxs : List Nat := []
  auto : Nat := 0
  digits : Option Nat := none
  skip : Bool := false

/-- Close a top-level field (core.cpp 318–359). -/
def closeField (args : List Arg) (st : St) : Except String St :=
  match st.idxs with
  | [k] =>
    match args[k]? with
    | none => .error s!"The format argument index `{k}` is out of range."
    | some a =>
      match stdFormatField st.field a with
      | .ok s => .ok { st with out := st.out ++ s, field := [], idxs := [] }
      | .err e => .error e
  | k :: _ =>
    -- two or three fields (width/precision nesting): none parses in std::format for the
    -- search's alphabet, since the outer field has a non-digit, non-':' after '{'.
    match args[k]? with
    | none => .error s!"The format argument index `{k}` is out of range."
    | some _ => .error "std::format_error: nested field"
  | [] => .error "no field"

/-- One character outside a manual index (core.cpp 259–372). -/
def regular (args : List Arg) (c peek : Char) (st : St) : Except String St :=
  if st.depth == 0 && ((c == '{' && peek == '{') || (c == '}' && peek == '}')) then
    .ok { st with out := st.out.push c, skip := true }
  else if c == '{' then
    let st := { st with field := st.field ++ [c], depth := st.depth + 1 }
    if peek.isDigit then
      if st.mode == 1 then .error "Automatic and manual format indexes cannot be mixed"
      else .ok { st with mode := 2, digits := some 0 }
    else
      if st.mode == 2 then .error "Automatic and manual format indexes cannot be mixed"
      else .ok { st with mode := 1, idxs := st.idxs ++ [st.auto], auto := st.auto + 1 }
  else if c == '}' then
    let st := { st with field := st.field ++ [c], depth := st.depth - 1 }
    if st.depth == 0 then closeField args st else .ok st
  else
    if st.depth > 0 then .ok { st with field := st.field ++ [c] }
    else .ok { st with out := st.out.push c }

/-- core.cpp `format` 237–378, one character per step (structural, so the kernel can run it). -/
def scan (args : List Arg) : List Char → St → FR
  | [], st =>
    if st.digits.isSome || st.depth != 0 then .err "This format string has an unmatched brace."
    else .ok st.out
  | c :: rest, st =>
    if st.skip then scan args rest { st with skip := false }
    else
      let peek := rest.head?.getD '\x00'
      match st.digits with
      | some n =>
        if c.isDigit then scan args rest { st with digits := some (n * 10 + (c.toNat - '0'.toNat)) }
        else
          match regular args c peek { st with digits := none, idxs := st.idxs ++ [n] } with
          | .ok st' => scan args rest st'
          | .error e => .err e
      | none =>
        match regular args c peek st with
        | .ok st' => scan args rest st'
        | .error e => .err e

def jankFormat (fmt : String) (args : List Arg) : FR := scan args fmt.toList {}

/-- java.util.Formatter on the search's alphabet (no flags, width or precision). -/
def javaFormat (fmt : String) (args : List Arg) : FR := Id.run do
  let cs := fmt.toList.toArray
  let mut out : String := ""
  let mut ai := 0
  let mut i := 0
  -- Formatter.parse checks every specifier before formatting: an unknown conversion throws
  -- even after a missing argument; both are errors here, so the order does not matter.
  while i < cs.size do
    let c := cs[i]!
    if c != '%' then
      out := out.push c
      i := i + 1
    else
      if i + 1 ≥ cs.size then return .err "UnknownFormatConversionException '%'"
      let d := cs[i + 1]!
      i := i + 2
      if d == '%' then out := out.push '%'
      else if d == 'n' then out := out.push '\n'
      else if d == 's' || d == 'd' || d == 'a' then
        match args[ai]? with
        | none => return .err s!"MissingFormatArgumentException '%{d}'"
        | some a =>
          ai := ai + 1
          if d == 's' then
            out := out ++ (match a with | .long n => toString n | .dbl t _ _ => t | .str s => s)
          else if d == 'd' then
            match a with
            | .long n => out := out ++ toString n
            | _ => return .err "IllegalFormatConversionException d"
          else
            match a with
            | .dbl _ h _ => out := out ++ h
            | _ => return .err "IllegalFormatConversionException a"
      else return .err s!"UnknownFormatConversionException '{d}'"
  return .ok out

/-- jank copies `%` and every letter: a string without braces comes back unchanged, whatever
the arguments (for every string and argument list). -/
theorem scan_no_braces (args : List Arg) (cs : List Char) (st : St)
    (hd : st.depth = 0) (hg : st.digits = none) (hs : st.skip = false)
    (h : ∀ c ∈ cs, c ≠ '{' ∧ c ≠ '}') :
    scan args cs st = .ok (cs.foldl (fun s c => s.push c) st.out) := by
  induction cs generalizing st with
  | nil => simp [scan, hg, hd]
  | cons c rest ih =>
    have hc := h c (by simp)
    have hr : ∀ x ∈ rest, x ≠ '{' ∧ x ≠ '}' := fun x hx => h x (by simp [hx])
    have h1 : (c == '{') = false := by simp [hc.1]
    have h2 : (c == '}') = false := by simp [hc.2]
    have hreg : ∀ p, regular args c p st = .ok { st with out := st.out.push c } := by
      intro p
      simp [regular, h1, h2, hd]
    have step : scan args (c :: rest) st = scan args rest { st with out := st.out.push c } := by
      simp [scan, hs, hg, hreg]
    rw [step, List.foldl_cons]
    exact ih { st with out := st.out.push c } hd hg hs hr

theorem jank_format_percent_d : jankFormat "%d" [.long 5] = .ok "%d" := by decide

end Jank.R4.Core.Format
