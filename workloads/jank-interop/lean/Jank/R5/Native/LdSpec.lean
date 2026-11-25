import Jank.R5.Native.LdScript
import Determinismo

/-!
# Round 5, native loading: GNU ld's reading of the same scripts (the spec), and the census world

The spec is GNU ld 2.45's script grammar and lexer, restricted to what glibc-style `.so` scripts
use (`deps/binutils-ld/`, fetched from sourceware at tag binutils-2_45):

- ldgram.y 310–408: a script is a list of commands; `INPUT '(' input_list ')'`,
  `GROUP '(' input_list ')'`, `OUTPUT_FORMAT '(' NAME ')'`; `input_list1` is one or more of `NAME`,
  `LNAME` and `AS_NEEDED '(' input_list1 ')'`, each after the first optionally preceded by `,`.
- ldlex.l: `INPUT`, `GROUP`, `OUTPUT_FORMAT` are keywords only in the SCRIPT state (290–305);
  `AS_NEEDED` only in the INPUTLIST state (292); in INPUTLIST, `-l…` is an LNAME (409–412) and
  `=…` a sysroot-relative NAME (404–408); a double-quoted string is a NAME with no escapes
  (440–444); `/* … */` comments in both states (133–134), EOF inside one is fatal (685–717).
- ld.texi 4417–4474: every file named by INPUT or GROUP is in the link, AS_NEEDED shared
  libraries only when needed; a relative name is looked for in the script's directory, then the
  current directory, then the library search path; `-lfile` is searched like the `-l` option.

Scripts are drawn as sequences of tokens from an alphabet where ld's lexer is unambiguous (each
token separated by one space), rendered to text for jank's replica, and parsed as tokens by the
spec. The property: jank loads exactly the files ld would put in the link (the non-AS_NEEDED
entries), or both reject the script.
-/

namespace Jank.R5.Native.LdSpec

open Determinismo Jank.R5.Native.LdScript

inductive Tok where
  | group | input | asNeeded | lp | rp | comma
  | rel        -- libx.so.1
  | abs        -- /lib/liby.so.6
  | lname      -- -lz
  | quoted     -- "q r.so"
  | sysroot    -- =/usr/lib/libw.so
  | qparen     -- "p(.so"
  | comment    -- /* GROUP ( c ) */
  | outFmt     -- OUTPUT_FORMAT
  | openCmt    -- /* x   (no end)
  | qback      -- "a\b.so"
  deriving Repr, DecidableEq, Inhabited

def Tok.text : Tok → String
  | .group => "GROUP" | .input => "INPUT" | .asNeeded => "AS_NEEDED"
  | .lp => "(" | .rp => ")" | .comma => ","
  | .rel => "libx.so.1" | .abs => "/lib/liby.so.6" | .lname => "-lz"
  | .quoted => "\"q r.so\"" | .sysroot => "=/usr/lib/libw.so" | .qparen => "\"p(.so\""
  | .comment => "/* GROUP ( c ) */" | .outFmt => "OUTPUT_FORMAT" | .openCmt => "/* x"
  | .qback => "\"a\\b.so\""

def alphabet : List Tok :=
  [.group, .input, .asNeeded, .lp, .rp, .comma, .rel, .abs, .lname, .quoted, .sysroot, .qparen,
   .comment, .outFmt, .openCmt, .qback]

def render (ts : List Tok) : String := " ".intercalate (ts.map Tok.text)

/-- One file ld puts in the link (or considers, for AS_NEEDED). -/
structure Entry where
  name : String
  /-- `-lname` (searched like the `-l` option). -/
  lib : Bool := false
  asNeeded : Bool := false
  deriving Repr, DecidableEq

/-- A NAME inside an input list (INPUTLIST state): what the token denotes. Keywords of the SCRIPT
state are plain names there. -/
def listName : Tok → Option Entry
  | .rel => some { name := "libx.so.1" }
  | .abs => some { name := "/lib/liby.so.6" }
  | .lname => some { name := "z", lib := true }
  | .quoted => some { name := "q r.so" }
  | .sysroot => some { name := "=/usr/lib/libw.so" }
  | .qparen => some { name := "p(.so" }
  | .qback => some { name := "a\\b.so" }
  | .group => some { name := "GROUP" }
  | .input => some { name := "INPUT" }
  | .outFmt => some { name := "OUTPUT_FORMAT" }
  | _ => none

/-- A NAME in the SCRIPT state (OUTPUT_FORMAT's argument): `-lz` and `=…` are not single
tokens there, `AS_NEEDED` is a name. -/
def scriptName : Tok → Bool
  | .rel | .abs | .quoted | .qparen | .qback | .asNeeded => true
  | _ => false

/-- ld's lexer drops comments; an unterminated one is fatal (ldlex.l 711–714). -/
def dropComments : List Tok → Except String (List Tok)
  | [] => .ok []
  | .comment :: r => dropComments r
  | .openCmt :: _ => .error "EOF in comment"
  | t :: r => do pure (t :: (← dropComments r))

mutual
/-- `input_list1` (ldgram.y 375–408): one item, then items each optionally after `,`. -/
def inputList (an : Bool) : List Tok → Nat → Except String (List Entry × List Tok)
  | _, 0 => .error "fuel"
  | ts, f + 1 => do
    let (e1, r) ← item an ts f
    moreItems an r e1 f

def moreItems (an : Bool) : List Tok → List Entry → Nat → Except String (List Entry × List Tok)
  | _, _, 0 => .error "fuel"
  | ts, acc, f + 1 =>
    match ts with
    | .comma :: r =>
      match item an r f with
      | .ok (es, r') => moreItems an r' (acc ++ es) f
      | .error e => .error e
    | t :: _ =>
      if t == .rp then .ok (acc, ts)
      else match item an ts f with
        | .ok (es, r') => moreItems an r' (acc ++ es) f
        | .error e => .error e
    | [] => .ok (acc, [])

def item (an : Bool) : List Tok → Nat → Except String (List Entry × List Tok)
  | _, 0 => .error "fuel"
  | ts, f + 1 =>
    match ts with
    | .asNeeded :: .lp :: r => do
      let (es, r') ← inputList true r f
      match r' with
      | .rp :: r'' => pure (es, r'')
      | _ => .error "syntax error"
    | t :: r =>
      match listName t with
      | some e => .ok ([{ e with asNeeded := an }], r)
      | none => .error "syntax error"
    | [] => .error "syntax error"
end

/-- `ifile_list` (ldgram.y 304–368, the commands used here). -/
def commands : List Tok → Nat → Except String (List Entry)
  | _, 0 => .error "fuel"
  | ts, f + 1 =>
    match ts with
    | [] => .ok []
    | .group :: .lp :: r | .input :: .lp :: r => do
      let (es, r') ← inputList false r (2 * r.length + 2)
      match r' with
      | .rp :: r'' => pure (es ++ (← commands r'' f))
      | _ => .error "syntax error"
    | .outFmt :: .lp :: t :: .rp :: r =>
      if scriptName t then commands r f else .error "syntax error"
    | _ => .error "syntax error"

/-- What ld makes of a token script: the entries of every INPUT/GROUP, or an error. -/
def ldRead (ts : List Tok) : Except String (List Entry) := do
  let ts ← dropComments ts
  commands ts (ts.length + 1)

/-- What jank loads instead of the script (parse_ld_script on the rendered text). -/
def jankRead (ts : List Tok) : Option String := parseStr (render ts)

/-- The world: up to `maxLen` tokens. -/
structure LW where
  decisions : Decisions

instance : Chaotic LW where
  decisions w := w.decisions
  setDecisions w d := { w with decisions := d }

def classify (_ts : List Tok) (ld : Except String (List Entry)) (j : Option String) : Option String :=
  match ld with
  | .error _ =>
    match j with
    | none => none     -- both refuse (jank then hands the script to dlopen, which fails: Libs)
    | some _ => some "C3 ld rejects the script; jank reads a file from it"
  | .ok es =>
    let req := es.filter (!·.asNeeded)
    match j with
    | none =>
      if es.isEmpty then some "C4e a script naming no file: ld adds nothing; jank reads nothing (and dlopens the script)"
      else some "C4 ld reads files from the script; jank finds none"
    | some p =>
      match req with
      | [] =>
        match es with
        | e :: _ => if !e.lib && e.name == p then some "F fallback: jank loads the first AS_NEEDED file unconditionally (not a deviation)"
          else some "C5 jank loads another file than ld would"
        | [] => some "C5 jank loads a file the script does not name"
      | r :: rest =>
        if r.lib then some "C2 -lname: jank takes \"-lname\" as a path; ld searches lib<name>"
        else if r.name.startsWith "=" then some "C2s =path: jank takes the sysroot prefix as a directory"
        else if r.name != p then some "C5 jank loads another file than ld would"
        else if !rest.isEmpty then some "C1 several files: ld links every one; jank loads only the first"
        else none

def body (maxLen : Nat) : EStateM Stop LW Unit := do
  let n ← decide "len" (maxLen + 1)
  let mut ts : List Tok := []
  for i in [0:n] do
    let k ← decide s!"tok{i}" alphabet.length
    ts := ts ++ [alphabet[k]!]
  let ld := ldRead ts
  let j := jankRead ts
  if (match ld with | .error "fuel" => true | _ => false) then violate "spec fuel" (render ts)
  match classify ts ld j with
  | none => pure ()
  | some c =>
    unless c.startsWith "F " do
      violate c s!"script `{render ts}`: ld {repr (ld.toOption)}; jank loads {repr j}"

def run (maxLen : Nat) (source : Source) : Ended :=
  match (body maxLen).run { decisions := { source } } with
  | .ok _ w => { taken := w.decisions.taken, violation := none }
  | .error (.violation p d) w => { taken := w.decisions.taken, violation := some (p, d) }
  | .error .limit w => { taken := w.decisions.taken, violation := none }
  | .error (.nodeDown _) w => { taken := w.decisions.taken, violation := none }

/-- The control: the same world with the alphabet limited to what glibc's scripts use (GROUP,
AS_NEEDED, parentheses, absolute paths, comments, OUTPUT_FORMAT) and one required file. -/
def controlBody (maxLen : Nat) : EStateM Stop LW Unit := do
  let ctl : List Tok := [.group, .asNeeded, .lp, .rp, .abs, .comment, .outFmt]
  let n ← decide "len" (maxLen + 1)
  let mut ts : List Tok := []
  for i in [0:n] do
    let k ← decide s!"tok{i}" ctl.length
    ts := ts ++ [ctl[k]!]
  let ld := ldRead ts
  let j := jankRead ts
  match ld with
  | .ok es =>
    let req := es.filter (!·.asNeeded)
    if req.length ≤ 1 then
      match classify ts ld j with
      | none => pure ()
      | some c =>
        unless c.startsWith "F " || c.startsWith "C4e" do
          violate ("control: " ++ c) s!"script `{render ts}`: ld {repr es}; jank {repr j}"
  | .error _ => pure ()

def controlRun (maxLen : Nat) (source : Source) : Ended :=
  match (controlBody maxLen).run { decisions := { source } } with
  | .ok _ w => { taken := w.decisions.taken, violation := none }
  | .error (.violation p d) w => { taken := w.decisions.taken, violation := some (p, d) }
  | .error .limit w => { taken := w.decisions.taken, violation := none }
  | .error (.nodeDown _) w => { taken := w.decisions.taken, violation := none }

end Jank.R5.Native.LdSpec
