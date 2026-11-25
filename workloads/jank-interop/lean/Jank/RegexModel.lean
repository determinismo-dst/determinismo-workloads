import Determinismo
import Jank.StrModel

/-!
# Regexes: `re-find`, `re-seq`, `re-matches` on `std::regex` beside java.util.regex

jank's `re-pattern` (core.cpp `re_pattern`, 929) builds re_pattern.cpp `re_pattern(s)` (6):
`std::regex{ s.c_str(), std::regex_constants::ECMAScript }` over `char`, the UTF-8 **bytes**.
Its matchers (core.cpp):

- `re_matcher` (939): `match_input{ s.c_str() }`, a `std::string` built from the C string,
  so cut at the first NUL;
- `re_find(m)` (972): `std::regex_search(match_input, …)`, then `match_input =
  match_results.suffix().str()`: the next search runs on a **new string**, the rest after the
  match (its start is a new beginning for `^`; an empty match leaves it unchanged);
- `smatch_to_vector` (944): no match → nil; one sub-match → the string; else a vector of every
  sub-match's `str()`, `""` for a group that did not participate;
- `re_matches` (1002): `regex_search(search_str, …, match_continuous)` (the first match at 0
  in priority order, not a full match), then nil unless its suffix is empty.

`re-seq` (core.jank 6389) calls `re_find` on one matcher until it returns nil.

Clojure (core.clj): `re-find` = `Matcher.find()` + `re-groups` (nil for a group that did not
participate, a string when the pattern has no group); `re-seq` = successive `find()`s on one
matcher (after an empty match the next search starts one character later; `^` stays at the
input's start); `re-matches` = `Matcher.matches()` (the whole input, backtracking into
alternatives). java.util.regex matches code points; `.` excludes `\n \r \u0085    `;
`$` matches at the end and before a final line terminator.

Both engines are backtracking with the same priorities (leftmost, first alternative, greedy or
lazy quantifiers) for the syntax drawn here, so one engine is written once and given each
side's units, `.`, classes and `$` (C++ [re.grammar]: ECMAScript; `$` without `multiline` only
at the end).
-/

namespace Jank.Regex

open Determinismo

/-- A pattern as written in a program, over code points. -/
inductive Re where
  | lit (c : Nat)
  | any
  /-- `[…]` or `[^…]` with explicit members. -/
  | cls (neg : Bool) (members : List Nat)
  | cat (a b : Re)
  | alt (a b : Re)
  | star (r : Re) (lazy : Bool)
  | opt (r : Re)
  | group (r : Re)
  | bol
  | eol
  deriving Repr, BEq, Inhabited

def metas : List Nat := ".*?|()[]{}^$\\+".toList.map Char.toNat

def litSrc (c : Nat) : String :=
  if c == 0x0A then "\\n" else if metas.contains c then "\\" ++ String.singleton (Char.ofNat c)
  else String.singleton (Char.ofNat c)

mutual
def Re.src : Re → String
  | .lit c => litSrc c
  | .any => "."
  | .cls neg ms => "[" ++ (if neg then "^" else "") ++ String.join (ms.map litSrc) ++ "]"
  | .cat a b => Re.catSrc a ++ Re.catSrc b
  | .alt a b => Re.src a ++ "|" ++ Re.src b
  | .star r lazy => Re.atomSrc r ++ "*" ++ (if lazy then "?" else "")
  | .opt r => Re.atomSrc r ++ "?"
  | .group r => "(" ++ Re.src r ++ ")"
  | .bol => "^"
  | .eol => "$"
/-- A sub-pattern where a quantifier will follow: `(?:…)` unless already an atom. -/
def Re.atomSrc : Re → String
  | .lit c => litSrc c
  | .any => "."
  | .cls neg ms => Re.src (.cls neg ms)
  | .group r => Re.src (.group r)
  | r => "(?:" ++ Re.src r ++ ")"
/-- A sub-pattern inside a concatenation: an alternation needs `(?:…)`. -/
def Re.catSrc : Re → String
  | .alt a b => "(?:" ++ Re.src (.alt a b) ++ ")"
  | r => Re.src r
end

def Re.groups : Re → Nat
  | .cat a b | .alt a b => a.groups + b.groups
  | .star r _ | .opt r => r.groups
  | .group r => r.groups + 1
  | _ => 0

/-! ## One backtracking engine, two instruction sets -/

/-- A compiled pattern over units (code points for Java, bytes for jank). -/
inductive M where
  | atom (name : String) (ok : Nat → Bool)
  | seq (ms : List M)
  | alt (a b : M)
  | star (r : M) (lazy : Bool)
  | opt (r : M)
  | group (k : Nat) (r : M)
  | bol
  | eol
  deriving Inhabited

inductive Flavor where
  | java
  | ecma
  deriving BEq, Repr

def javaTerminator (u : Nat) : Bool := u == 0x0A || u == 0x0D || u == 0x85 || u == 0x2028 || u == 0x2029

/-- `$`: Java (no MULTILINE): at the end, or before a final line terminator (`\r\n` counted as
one); ECMAScript (no `multiline`): at the end only. -/
def eolOk (fl : Flavor) (inp : Array Nat) (i : Nat) : Bool :=
  let n := inp.size
  match fl with
  | .ecma => i == n
  | .java =>
    i == n ||
    (i + 1 == n && javaTerminator (inp.getD i 0) && !(inp.getD i 0 == 0x0A && i > 0 && inp.getD (i - 1) 0 == 0x0D)) ||
    (i + 2 == n && inp.getD i 0 == 0x0D && inp.getD (i + 1) 0 == 0x0A)

abbrev Caps := Array (Option (Nat × Nat))

/-- The engine: continuation passing, the first success in priority order. An iteration of `*`
that consumes nothing fails (ECMA-262 RepeatMatcher; Java's loops stop the same way here). -/
partial def go (fl : Flavor) (inp : Array Nat) (r : M) (i : Nat) (caps : Caps)
    (k : Nat → Caps → Option (Nat × Caps)) : Option (Nat × Caps) :=
  match r with
  | .atom _ ok => if h : i < inp.size then (if ok inp[i] then k (i + 1) caps else none) else none
  | .seq [] => k i caps
  | .seq (m :: ms) => go fl inp m i caps (fun j c => go fl inp (.seq ms) j c k)
  | .alt a b => match go fl inp a i caps k with
    | some r => some r
    | none => go fl inp b i caps k
  | .opt a => match go fl inp a i caps k with
    | some r => some r
    | none => k i caps
  | .star a lazy =>
    let iter : Unit → Option (Nat × Caps) := fun _ =>
      go fl inp a i caps (fun j c => if j == i then none else go fl inp (.star a lazy) j c k)
    if lazy then (match k i caps with | some r => some r | none => iter ())
    else (match iter () with | some r => some r | none => k i caps)
  | .group n a => go fl inp a i caps (fun j c => k j (c.set! n (some (i, j))))
  | .bol => if i == 0 then k i caps else none
  | .eol => if eolOk fl inp i then k i caps else none

/-- Numbering groups in the order their `(` appear. -/
partial def compileWith (litM : Nat → M) (anyM : M) (clsM : Bool → List Nat → M) (r : Re) (next : Nat) : M × Nat :=
  match r with
  | .lit c => (litM c, next)
  | .any => (anyM, next)
  | .cls neg ms => (clsM neg ms, next)
  | .cat a b =>
    let (ma, n1) := compileWith litM anyM clsM a next
    let (mb, n2) := compileWith litM anyM clsM b n1
    (.seq [ma, mb], n2)
  | .alt a b =>
    let (ma, n1) := compileWith litM anyM clsM a next
    let (mb, n2) := compileWith litM anyM clsM b n1
    (.alt ma mb, n2)
  | .star a lazy => let (m, n) := compileWith litM anyM clsM a next; (.star m lazy, n)
  | .opt a => let (m, n) := compileWith litM anyM clsM a next; (.opt m, n)
  | .group a => let (m, n) := compileWith litM anyM clsM a (next + 1); (.group next m, n)
  | .bol => (.bol, next)
  | .eol => (.eol, next)

/-- java.util.regex: code points. -/
def compileJava (r : Re) : M :=
  (compileWith (fun c => .atom "lit" (· == c))
    (.atom "." fun u => !javaTerminator u)
    (fun neg ms => .atom "class" fun u => ms.contains u != neg) r 1).1

/-- std::regex<char>: a literal is its UTF-8 bytes in a row; `.` and a class match one byte;
`.` excludes `\n` and `\r` (ECMAScript LineTerminators that fit a `char`); a class holds each
member's bytes. -/
def compileEcma (r : Re) : M :=
  (compileWith (fun c => .seq ((Jank.Str.utf8 c).map fun b => .atom "byte" (· == b.toNat)))
    (.atom "." fun b => b != 0x0A && b != 0x0D)
    (fun neg ms => let bs := (ms.flatMap Jank.Str.utf8).map (·.toNat)
                   .atom "byte class" fun b => bs.contains b != neg) r 1).1

/-- The leftmost match at or after `from`, in priority order. -/
def search (fl : Flavor) (m : M) (ngroups : Nat) (inp : Array Nat) (from_ : Nat) : Option (Nat × Nat × Caps) :=
  let init : Caps := Array.replicate (ngroups + 1) none
  ((List.range (inp.size + 1 - from_)).map (· + from_)).findSome? fun s =>
    (go fl inp m s init fun j c => some (j, c)).map fun (e, c) => (s, e, c)

/-! ## Results -/

inductive Grp where
  | str (b : List UInt8)
  | vec (xs : List (Option (List UInt8)))
  deriving DecidableEq, Inhabited

inductive G where
  | nil
  | one (g : Grp)
  | many (gs : List Grp)
  /-- An infinite seq: realizing it never ends. -/
  | infinite (prefix_ : List Grp)
  | err (w : String)
  deriving DecidableEq, Inhabited

def showOpt : Option (List UInt8) → String
  | none => "nil"
  | some b => Jank.Str.showBytes b

def Grp.show : Grp → String
  | .str b => Jank.Str.showBytes b
  | .vec xs => "[" ++ " ".intercalate (xs.map showOpt) ++ "]"

def G.show : G → String
  | .nil => "nil"
  | .one g => g.show
  | .many gs => "(" ++ " ".intercalate (gs.map Grp.show) ++ ")"
  | .infinite p => "(" ++ " ".intercalate (p.map Grp.show) ++ " …) an infinite seq: realizing it never ends"
  | .err w => s!"throws ({w})"

def G.agrees : G → G → Bool
  | .err _, .err _ => true
  | .infinite _, _ => false
  | a, b => a == b

/-! ## Clojure -/

def cpsBytes (inp : Array Nat) (s e : Nat) : List UInt8 :=
  ((inp.toList.drop s).take (e - s)).flatMap Jank.Str.utf8

/-- `re-groups`: the match when there is no group; else a vector, nil for a group that did not
participate. -/
def cljGroups (inp : Array Nat) (ngroups : Nat) (s e : Nat) (caps : Caps) : Grp :=
  if ngroups == 0 then .str (cpsBytes inp s e)
  else .vec (some (cpsBytes inp s e) :: ((List.range ngroups).map fun k =>
    (caps.getD (k + 1) none).map fun (a, b) => cpsBytes inp a b))

def cljFind (r : Re) (input : List Nat) : G :=
  let inp := input.toArray
  match search .java (compileJava r) r.groups inp 0 with
  | some (s, e, c) => .one (cljGroups inp r.groups s e c)
  | none => .nil

/-- Successive `Matcher.find()`s: after an empty match the next starts one later. -/
def cljSeq (r : Re) (input : List Nat) : G :=
  let inp := input.toArray
  let m := compileJava r
  let rec loop (fuel : Nat) (from_ : Nat) (acc : List Grp) : List Grp :=
    match fuel with
    | 0 => acc
    | f + 1 =>
      if from_ > inp.size then acc
      else match search .java m r.groups inp from_ with
        | none => acc
        | some (s, e, c) =>
          loop f (if e == s then e + 1 else e) (acc ++ [cljGroups inp r.groups s e c])
  match loop (inp.size + 2) 0 [] with
  | [] => .nil
  | gs => .many gs

/-- `Matcher.matches()`: the whole input. -/
def cljMatches (r : Re) (input : List Nat) : G :=
  let inp := input.toArray
  let init : Caps := Array.replicate (r.groups + 1) none
  match go .java inp (compileJava r) 0 init (fun j c => if j == inp.size then some (j, c) else none) with
  | some (e, c) => .one (cljGroups inp r.groups 0 e c)
  | none => .nil

/-! ## jank -/

/-- `std::string{ s.c_str() }`: the bytes before the first NUL. -/
def cString (bs : List UInt8) : List UInt8 := bs.takeWhile (· != 0)

def bytesOf (inp : Array Nat) (s e : Nat) : List UInt8 :=
  ((inp.toList.drop s).take (e - s)).map (·.toUInt8)

/-- core.cpp `smatch_to_vector` (944): one sub-match (no group) → the string; else every
sub-match's `str()`, `""` for one that did not participate. -/
def jankGroups (inp : Array Nat) (ngroups : Nat) (s e : Nat) (caps : Caps) : Grp :=
  if ngroups == 0 then .str (bytesOf inp s e)
  else .vec (some (bytesOf inp s e) :: ((List.range ngroups).map fun k =>
    some (match caps.getD (k + 1) none with
      | some (a, b) => bytesOf inp a b
      | none => [])))

def toUnits (bs : List UInt8) : Array Nat := (bs.map (·.toNat)).toArray

/-- `(re-find re s)` (core.jank 6379): `re_matcher` (939), `re_find` (972). -/
def jankFind (r : Re) (input : List Nat) : G :=
  let inp := toUnits (cString (Jank.Str.jstr input))
  match search .ecma (compileEcma r) r.groups inp 0 with
  | some (s, e, c) => .one (jankGroups inp r.groups s e c)
  | none => .nil

/-- `(re-seq re s)` (core.jank 6389): `re_find` again and again on one matcher; each search runs
on `match_results.suffix().str()`, a new string. An empty match at its start leaves the input
as it was: the same match again, forever. -/
def jankSeq (r : Re) (input : List Nat) : G :=
  let m := compileEcma r
  let rec loop (fuel : Nat) (cur : List UInt8) (acc : List Grp) : G :=
    match fuel with
    | 0 => .infinite acc
    | f + 1 =>
      let inp := toUnits cur
      match search .ecma m r.groups inp 0 with
      | none => if acc.isEmpty then .nil else .many acc
      | some (s, e, c) =>
        let g := jankGroups inp r.groups s e c
        let rest := cur.drop e
        if rest == cur then .infinite (acc ++ [g, g])
        else loop f rest (acc ++ [g])
  loop ((Jank.Str.jstr input).length + 2) (cString (Jank.Str.jstr input)) []

/-- `(re-matches re s)`: core.cpp `re_matches` (1002): the first match anchored at 0
(`match_continuous`), nil unless it reaches the end. -/
def jankMatches (r : Re) (input : List Nat) : G :=
  let inp := toUnits (cString (Jank.Str.jstr input))
  let init : Caps := Array.replicate (r.groups + 1) none
  match go .ecma inp (compileEcma r) 0 init (fun j c => some (j, c)) with
  | none => .nil
  | some (e, c) => if e == inp.size then .one (jankGroups inp r.groups 0 e c) else .nil

/-! ## Questions -/

inductive Api where
  | find
  | seq
  | matches
  deriving BEq, Repr, Inhabited

def Api.name : Api → String
  | .find => "re-find" | .seq => "re-seq" | .matches => "re-matches"

structure Case where
  api : Api
  re : Re
  input : List Nat
  deriving Inhabited

def Case.program (c : Case) : String :=
  s!"({c.api.name} #\"{c.re.src}\" {Jank.Str.lit c.input})"

def Case.eval (c : Case) : G × G :=
  match c.api with
  | .find => (jankFind c.re c.input, cljFind c.re c.input)
  | .seq => (jankSeq c.re c.input, cljSeq c.re c.input)
  | .matches => (jankMatches c.re c.input, cljMatches c.re c.input)

/-- Input code points: two letters, a newline, é (2 bytes), NUL. -/
def alphabet : List Nat := [0x61, 0x62, 0x0A, 0xE9, 0x00]

/-- Pattern atoms: letters, é, newline, `.`, `[é]`, `[^a]`, `^`, `$`. -/
def atoms : List Re :=
  [.lit 0x61, .lit 0x62, .lit 0xE9, .lit 0x0A, .any, .cls false [0xE9], .cls true [0x61], .bol, .eol]

def quantifiable : Re → Bool
  | .bol | .eol => false
  | _ => true

/-- Patterns of depth ≤ 1: atoms, a quantified or grouped atom, two atoms in a row or as
alternatives. -/
def patterns1 : List Re :=
  let q := atoms.filter quantifiable
  atoms ++ q.map (Re.star · false) ++ q.map (Re.star · true) ++ q.map Re.opt ++ atoms.map Re.group ++
  (atoms.flatMap fun a => atoms.map (Re.cat a)) ++ (atoms.flatMap fun a => atoms.map (Re.alt a))

/-- A few depth-2 shapes: groups around alternatives and quantified groups. -/
def patterns2 : List Re :=
  let small := [Re.lit 0x61, .lit 0x62, .any, .bol]
  (small.flatMap fun a => small.map fun b => Re.group (.alt a b)) ++
  (small.flatMap fun a => small.map fun b => Re.cat (.opt (.group a)) b) ++
  (small.flatMap fun a => small.map fun b => Re.alt a (.cat a b)) ++
  (small.filter quantifiable |>.map fun a => Re.star (.group a) false)

def inputs : Nat → List (List Nat)
  | 0 => [[]]
  | n + 1 => inputs n ++ ((inputs n).filter (·.length == n)).flatMap fun s => alphabet.map (s ++ [·])

def allCases : List Case :=
  (patterns1 ++ patterns2).flatMap fun re =>
    (inputs 3).flatMap fun input => [Api.find, .seq, .matches].map fun api => { api, re, input }

structure World where
  decisions : Decisions := {}

instance : Chaotic World where
  decisions w := w.decisions
  setDecisions w d := { w with decisions := d }

/-- A pattern drawn: an atom, or a combinator over smaller ones (depth ≤ `d`). -/
def drawRe : Nat → EStateM Stop World Re
  | 0 => do pure (atoms.getD (← decide (σ := World) "re.atom" atoms.length) .any)
  | d + 1 => do
    match ← decide (σ := World) "re.kind" 7 with
    | 0 => drawRe 0
    | 1 => pure (.cat (← drawRe d) (← drawRe d))
    | 2 => pure (.alt (← drawRe d) (← drawRe d))
    | 3 => do
      let r ← drawRe d
      pure (if quantifiable r then .star r false else r)
    | 4 => do
      let r ← drawRe d
      pure (if quantifiable r then .star r true else r)
    | 5 => do
      let r ← drawRe d
      pure (if quantifiable r then .opt r else r)
    | _ => pure (.group (← drawRe d))

def drawInput : EStateM Stop World (List Nat) := do
  let n ← decide (σ := World) "re.input.len" 4
  let mut out := []
  for k in List.range n do
    out := out ++ [alphabet.getD (← decide (σ := World) s!"re.input.char{k}" alphabet.length) 0]
  return out

def property : String := "jank's re-find, re-seq and re-matches agree with Clojure's"

def body : EStateM Stop World Unit := do
  let api := [Api.find, .seq, .matches].getD (← decide (σ := World) "re.api" 3) .find
  let re ← drawRe 2
  let input ← drawInput
  let c : Case := { api, re, input }
  let (j, cl) := c.eval
  unless j.agrees cl do
    violate (σ := World) property s!"{c.program}: Clojure {cl.show}, jank {j.show}"

def run (source : Source) : Ended :=
  match body.run { decisions := { source } } with
  | .ok _ w => { taken := w.decisions.taken, violation := none }
  | .error (.violation p d) w => { taken := w.decisions.taken, violation := some (p, d) }
  | .error .limit w => { taken := w.decisions.taken, violation := none }
  | .error (.nodeDown _) w => { taken := w.decisions.taken, violation := none }

/-! ## `$` replacement templates (`clojure.string/replace` with a pattern and a string)

jank: string_native.cpp `replace(s, re_pattern_ref, immutable_string)` (218) →
`std::regex_replace(s_str, regex, replacement_str)` with the default (ECMAScript) format rules
([re.results.form], ECMA-262 `GetSubstitution`): `$&` the match, `$n`/`$nn` a group (nothing
when out of range), `` $` ``/`$'`, `$$` a dollar, anything else literal. Clojure:
`Matcher.replaceAll` (appendReplacement): `$n` takes the most digits naming a group, `\x` is
`x`, `$` before anything else throws. Modeled on one match of a pattern with `groups` groups. -/

inductive Piece where
  | text (s : String)
  | group (k : Nat)
  deriving BEq, Repr

/-- ECMAScript `GetSubstitution` as libstdc++'s `format` does it, for a template. -/
def ecmaTemplate (groups : Nat) : List Char → List Piece
  | [] => []
  | '$' :: '$' :: r => .text "$" :: ecmaTemplate groups r
  | '$' :: '&' :: r => .group 0 :: ecmaTemplate groups r
  | '$' :: d1 :: d2 :: r =>
    if d1.isDigit && d2.isDigit then
      let n := (d1.toNat - 48) * 10 + (d2.toNat - 48)
      (if n ≤ groups then [.group n] else []) ++ ecmaTemplate groups r
    else if d1.isDigit then
      let n := d1.toNat - 48
      (if n ≤ groups then [.group n] else []) ++ ecmaTemplate groups (d2 :: r)
    else .text "$" :: ecmaTemplate groups (d1 :: d2 :: r)
  | '$' :: d1 :: r =>
    if d1.isDigit then
      let n := d1.toNat - 48
      (if n ≤ groups then [.group n] else []) ++ ecmaTemplate groups r
    else .text "$" :: ecmaTemplate groups (d1 :: r)
  | c :: r => .text (String.singleton c) :: ecmaTemplate groups r

def javaTemplateF (groups : Nat) : Nat → List Char → Except String (List Piece)
  | 0, _ => .ok []
  | _ + 1, [] => .ok []
  | f + 1, '\\' :: c :: r => do pure (.text (String.singleton c) :: (← javaTemplateF groups f r))
  | _ + 1, ['\\'] => .error "character to be escaped is missing"
  | f + 1, '$' :: r =>
    match r with
    | d :: r' =>
      if d.isDigit then
        let n := d.toNat - 48
        if n > groups then .error s!"No group {n}"
        else
          -- one more digit when it still names a group
          match r' with
          | d2 :: r'' =>
            if d2.isDigit && n * 10 + (d2.toNat - 48) ≤ groups then do
              pure (.group (n * 10 + (d2.toNat - 48)) :: (← javaTemplateF groups f r''))
            else do pure (.group n :: (← javaTemplateF groups f r'))
          | [] => do pure (.group n :: (← javaTemplateF groups f r'))
      else .error "Illegal group reference"
    | [] => .error "Illegal group reference: group index is missing"
  | f + 1, c :: r => do pure (.text (String.singleton c) :: (← javaTemplateF groups f r))

/-- Matcher.appendReplacement's template: `\c` → `c`; `$` + digits: the longest group number
that exists (at least one digit, else IllegalArgumentException); `$` before a non-digit (and not
`{`) throws. -/
def javaTemplate (groups : Nat) (t : List Char) : Except String (List Piece) :=
  javaTemplateF groups (t.length + 1) t

/-- The replacement text for one match whose groups print as `g0`, `g1`, …. -/
def expand (pieces : List Piece) : String :=
  String.join (pieces.map fun | .text s => s | .group k => s!"<g{k}>")


/-! ## Iterating matches: `clojure.string/split` and `replace` with a pattern

jank (7135b7708, string_native.cpp, unchanged since f3d82d654):
- `replace(s, re, replacement)` (218) → `std::regex_replace(s_str, regex, replacement_str)`, and
  `split(s, re, limit)` (393) → `std::cregex_iterator`. Both walk `std::regex_iterator`
  (C++ [re.regiter.incr], libstdc++ `regex_iterator::operator++`): after a match `m`, if `m` is
  empty (and not at the end) it first searches **at the same position** with
  `match_not_null | match_continuous`, and only when that fails from one position later;
  otherwise from `m`'s end (`match_prev_avail`: `^` stays at the input's start).
- `split` drops a leading empty match at 0, takes `limit - 1` matches when `limit > 0`, and
  with `limit == 0` drops trailing empty strings.

Clojure: `Matcher.replaceAll` and `Pattern.split` use successive `Matcher.find()`, which after
an empty match starts one character later and never retries a non-empty match there.
(`^` is left out of these patterns: in the first not-null retry, libstdc++ has not yet set
`match_prev_avail`, so `^` could match there; not modeled.) -/

/-- A search anchored at `from` (`match_continuous`); `notNull` refuses an empty match. -/
def searchAt (fl : Flavor) (m : M) (ngroups : Nat) (inp : Array Nat) (from_ : Nat) (notNull : Bool) :
    Option (Nat × Nat × Caps) :=
  let init : Caps := Array.replicate (ngroups + 1) none
  (go fl inp m from_ init fun j c => if notNull && j == from_ then none else some (j, c)).map
    fun (e, c) => (from_, e, c)

/-- `std::regex_iterator` over the whole input: every match it yields. -/
def ecmaIter (m : M) (ngroups : Nat) (inp : Array Nat) : List (Nat × Nat × Caps) :=
  let rec loop (fuel : Nat) (cur : Option (Nat × Nat × Caps)) (acc : List (Nat × Nat × Caps)) :=
    match fuel, cur with
    | 0, _ => acc
    | _, none => acc
    | f + 1, some (s, e, c) =>
      let acc := acc ++ [(s, e, c)]
      if s == e then
        if e == inp.size then acc
        else match searchAt .ecma m ngroups inp e true with
          | some x => loop f (some x) acc
          | none => loop f (search .ecma m ngroups inp (e + 1)) acc
      else loop f (search .ecma m ngroups inp e) acc
  loop (2 * inp.size + 4) (search .ecma m ngroups inp 0) []

/-- Successive `Matcher.find()`: one past an empty match. -/
def javaFinds (m : M) (ngroups : Nat) (inp : Array Nat) (fl : Flavor := .java) : List (Nat × Nat × Caps) :=
  let rec loop (fuel : Nat) (from_ : Nat) (acc : List (Nat × Nat × Caps)) :=
    match fuel with
    | 0 => acc
    | f + 1 =>
      if from_ > inp.size then acc
      else match search fl m ngroups inp from_ with
        | none => acc
        | some (s, e, c) => loop f (if e == s then e + 1 else e) (acc ++ [(s, e, c)])
  loop (inp.size + 2) 0 []

/-- The text of a template's pieces for one match (`$n` of a group that did not participate:
nothing, on both sides). -/
def expandWith (unitBytes : Array Nat → Nat → Nat → List UInt8) (inp : Array Nat)
    (s e : Nat) (caps : Caps) (pieces : List Piece) : List UInt8 :=
  pieces.flatMap fun
    | .text t => t.toUTF8.toList
    | .group 0 => unitBytes inp s e
    | .group k => match caps.getD k none with
      | some (a, b) => unitBytes inp a b
      | none => []

/-- jank `(clojure.string/replace s re template)`: string_native.cpp `replace` (218):
`std::regex_replace` over `s.c_str()`: every iterator match's prefix and formatted template, then
the last suffix. -/
def jankReplace (r : Re) (template : String) (input : List Nat) : G :=
  let inp := toUnits (cString (Jank.Str.jstr input))
  let ms := ecmaIter (compileEcma r) r.groups inp
  let pieces := ecmaTemplate r.groups template.toList
  let (out, last) := ms.foldl (fun (acc, prev) (s, e, c) =>
    (acc ++ bytesOf inp prev s ++ expandWith bytesOf inp s e c pieces, e)) ([], 0)
  .one (.str (out ++ bytesOf inp last inp.size))

/-- Clojure `(clojure.string/replace s re template)`: `Matcher.replaceAll`. -/
def cljReplace (r : Re) (template : String) (input : List Nat) : G :=
  let inp := input.toArray
  match javaTemplate r.groups template.toList with
  | .error w => .err w
  | .ok pieces =>
    let ms := javaFinds (compileJava r) r.groups inp
    let (out, last) := ms.foldl (fun (acc, prev) (s, e, c) =>
      (acc ++ cpsBytes inp prev s ++ expandWith cpsBytes inp s e c pieces, e)) ([], 0)
    .one (.str (out ++ cpsBytes inp last inp.size))

/-- jank `(clojure.string/split s re limit)`: string_native.cpp `split` (393). -/
def jankSplit (r : Re) (limit : Int) (input : List Nat) : G :=
  let bytes := Jank.Str.jstr input
  if bytes.isEmpty || limit == 1 then .many [.str bytes]
  else
    let inp := toUnits bytes
    let ms0 := ecmaIter (compileEcma r) r.groups inp
    -- "Ignore leading empty strings just like Java" (line 407).
    let ms := match ms0 with
      | (s, e, _) :: rest => if e == s && s == 0 then rest else ms0
      | [] => []
    let ms := if limit > 0 then ms.take (limit - 1).toNat else ms
    let (parts, prev) := ms.foldl (fun (acc, prev) (s, e, _) => (acc ++ [bytesOf inp prev s], e)) ([], 0)
    let parts := parts ++ [bytesOf inp prev inp.size]
    let parts := if limit == 0 then (parts.reverse.dropWhile (·.isEmpty)).reverse else parts
    .many (parts.map .str)

/-- Clojure `(clojure.string/split s re limit)`: `Pattern.split(input, limit)`. -/
def cljSplit (r : Re) (limit : Int) (input : List Nat) : G := Id.run do
  let inp := input.toArray
  let matchLimited := limit > 0
  let mut index := 0
  let mut list : List (List UInt8) := []
  for (s, e, _) in javaFinds (compileJava r) r.groups inp do
    if !matchLimited || (list.length : Int) < limit - 1 then
      if index == 0 && index == s && s == e then continue
      list := list ++ [cpsBytes inp index s]
      index := e
    else if (list.length : Int) == limit - 1 then
      list := list ++ [cpsBytes inp index inp.size]
      index := e
  if index == 0 then return .many [.str (cpsBytes inp 0 inp.size)]
  if !matchLimited || (list.length : Int) < limit then list := list ++ [cpsBytes inp index inp.size]
  if limit == 0 then list := (list.reverse.dropWhile (·.isEmpty)).reverse
  return .many (list.map .str)

def hasBol : Re → Bool
  | .bol => true
  | .cat a b | .alt a b => hasBol a || hasBol b
  | .star r _ | .opt r | .group r => hasBol r
  | _ => false

/-- Replace and split questions: patterns without `^`, inputs over `alphabetIter`. -/
inductive IterApi where
  | replace (template : String)
  | split (limit : Int)
  deriving BEq, Inhabited

structure IterCase where
  api : IterApi
  re : Re
  input : List Nat
  deriving Inhabited

def IterCase.program (c : IterCase) : String :=
  match c.api with
  | .replace t => s!"(clojure.string/replace {Jank.Str.lit c.input} #\"{c.re.src}\" {Jank.Str.lit (t.toList.map Char.toNat)})"
  | .split l => s!"(clojure.string/split {Jank.Str.lit c.input} #\"{c.re.src}\" {l})"

def IterCase.eval (c : IterCase) : G × G :=
  match c.api with
  | .replace t => (jankReplace c.re t c.input, cljReplace c.re t c.input)
  | .split l => (jankSplit c.re l c.input, cljSplit c.re l c.input)

/-- Inputs: two letters, newline, é (NUL left out: B29). -/
def alphabetIter : List Nat := [0x61, 0x62, 0x0A, 0xE9]

def inputsIter : Nat → List (List Nat)
  | 0 => [[]]
  | n + 1 => inputsIter n ++ ((inputsIter n).filter (·.length == n)).flatMap fun s => alphabetIter.map (s ++ [·])

def iterCases : List IterCase :=
  ((patterns1 ++ patterns2).filter (!hasBol ·)).flatMap fun re =>
    (inputsIter 3).flatMap fun input =>
      [IterApi.replace "-", .split 0, .split (-1), .split 2].map fun api => { api, re, input }

/-- Whether only the iteration rule can explain a deviation: ASCII letters only, no `$`. -/
def asciiOnly (c : IterCase) : Bool :=
  c.input.all (fun u => u == 0x61 || u == 0x62) &&
  (let rec ok : Re → Bool
    | .lit u => u == 0x61 || u == 0x62
    | .any => true
    | .cls _ ms => ms.all fun u => u == 0x61 || u == 0x62
    | .cat a b | .alt a b => ok a && ok b
    | .star r _ | .opt r | .group r => ok r
    | .bol | .eol => false
   ok c.re)

def iterProperty : String := "jank's clojure.string/replace and split with a pattern agree with Clojure's"

def iterBody : EStateM Stop World Unit := do
  let atomsNoBol := atoms.filter (· != .bol)
  let pickAtom : EStateM Stop World Re := do
    pure (atomsNoBol.getD (← decide (σ := World) "re.atom" atomsNoBol.length) .any)
  let kind ← decide (σ := World) "re.kind" 5
  let a ← pickAtom
  let re ← match kind with
    | 0 => pure a
    | 1 => pure (if quantifiable a then Re.star a false else a)
    | 2 => pure (if quantifiable a then Re.star a true else a)
    | 3 => pure (if quantifiable a then Re.opt a else a)
    | _ => do pure (Re.alt a (← pickAtom))
  let n ← decide (σ := World) "re.input.len" 4
  let mut input := []
  for k in List.range n do
    input := input ++ [alphabetIter.getD (← decide (σ := World) s!"re.input.char{k}" alphabetIter.length) 0]
  let api := [IterApi.replace "-", .split 0, .split (-1), .split 2].getD (← decide (σ := World) "re.iter.api" 4) (.split 0)
  let c : IterCase := { api, re, input }
  let (j, cl) := c.eval
  unless j.agrees cl do
    violate (σ := World) iterProperty s!"{c.program}: Clojure {cl.show}, jank {j.show}"

def iterRun (source : Source) : Ended :=
  match iterBody.run { decisions := { source } } with
  | .ok _ w => { taken := w.decisions.taken, violation := none }
  | .error (.violation p d) w => { taken := w.decisions.taken, violation := some (p, d) }
  | .error .limit w => { taken := w.decisions.taken, violation := none }
  | .error (.nodeDown _) w => { taken := w.decisions.taken, violation := none }

/-- With the iterator replaced by Java's `find()` rule (the fix), restricted to ASCII letters:
nothing left to explain. -/
def jankReplaceJavaIter (r : Re) (template : String) (input : List Nat) : G :=
  let inp := toUnits (cString (Jank.Str.jstr input))
  let ms := javaFinds (compileEcma r) r.groups inp .ecma
  let pieces := ecmaTemplate r.groups template.toList
  let (out, last) := ms.foldl (fun (acc, prev) (s, e, c) =>
    (acc ++ bytesOf inp prev s ++ expandWith bytesOf inp s e c pieces, e)) ([], 0)
  .one (.str (out ++ bytesOf inp last inp.size))

end Jank.Regex
