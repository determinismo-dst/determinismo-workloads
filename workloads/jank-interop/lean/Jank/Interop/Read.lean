import Jank.Interop.Eval

/-!
# A small reader for the searched programs

Turns the jank text of a program into the `Obj` forms the analyzer consumes, the way jank's reader
does for the subset used here: integers boxed by `make_box` (small when they fit i32), doubles,
strings, characters, keywords, symbols (`ns/name`), lists, vectors, `nil`/`true`/`false`, `##Inf`,
`##NaN`, and `#cpp x` as `(cpp/dsl x)` (parse.cpp:parse_tagged_cpp:981). It is a test helper, not
a replica of the reader.
-/

namespace Jank.Interop.Read

open Jank.Analyzer (Obj)

def isDelim (c : Char) : Bool := c.isWhitespace || c == '(' || c == ')' || c == '[' || c == ']' || c == ','

def parseNumber (s : String) : Option Obj :=
  let neg := s.startsWith "-"
  let body := if neg || s.startsWith "+" then (s.drop 1).toString else s
  if body.isEmpty || !(body.front.isDigit) then none
  else if body.all Char.isDigit then
    let n : Int := body.toNat!
    let v := if neg then -n else n
    if -2147483648 ≤ v ∧ v ≤ 2147483647 then some (.smallInteger (BitVec.ofInt 32 v))
    else if -(2 ^ 63) < v ∧ v < 2 ^ 63 then some (.integer (BitVec.ofInt 64 v))
    else some (.bigInteger v)
  else
    -- digits [. digits] [e [sign] digits]
    let parts := body.splitOn "e"
    let mant := parts.headD ""
    let expo : Int := match parts with
      | [_, e] => if e.startsWith "-" then -((e.drop 1).toString.toNat! : Int) else ((if e.startsWith "+" then (e.drop 1).toString else e).toNat! : Int)
      | _ => 0
    let ip := (mant.splitOn ".").headD ""
    let fp := (mant.splitOn ".").getD 1 ""
    let digits := (ip ++ fp).toNat!
    let e10 : Int := expo - fp.length
    let x := if e10 ≥ 0 then Float.ofScientific (digits * 10 ^ e10.toNat) false 0
             else Float.ofScientific digits true (-e10).toNat
    some (.smallReal (if neg then -x else x).toBits)

def atom (s : String) : Obj :=
  if s == "nil" then .nil
  else if s == "true" then .boolean true
  else if s == "false" then .boolean false
  else if s == "##Inf" then .smallReal (1.0 / 0.0 : Float).toBits
  else if s == "##-Inf" then .smallReal (-1.0 / 0.0 : Float).toBits
  else if s == "##NaN" then .smallReal 0x7FF8000000000000
  else if s.startsWith ":" then .keyword "" (s.drop 1).toString
  else if s.startsWith "\\" then .character (s.drop 1).toString
  else match parseNumber s with
    | some o => o
    | none =>
      match s.splitOn "/" with
      | [n] => .symbol none "" n
      | ns :: rest => if ns.isEmpty then .symbol none "" s else .symbol none ns ("/".intercalate rest)
      | [] => .symbol none "" s

partial def readForms (cs : List Char) (acc : List Obj) : Except String (List Obj × List Char) :=
  match cs with
  | [] => .ok (acc.reverse, [])
  | c :: rest =>
    if c.isWhitespace || c == ',' then readForms rest acc
    else if c == ')' || c == ']' then .ok (acc.reverse, cs)
    else match readOne cs with
      | .ok (o, rest') => readForms rest' (o :: acc)
      | .error e => .error e
where
  readOne (cs : List Char) : Except String (Obj × List Char) :=
    match cs with
    | '(' :: rest => do
      let (xs, rest') ← readForms rest []
      match rest' with
      | ')' :: r => .ok (.persistentList none xs, r)
      | _ => .error "unterminated list"
    | '[' :: rest => do
      let (xs, rest') ← readForms rest []
      match rest' with
      | ']' :: r => .ok (.persistentVector none xs, r)
      | _ => .error "unterminated vector"
    | '"' :: rest =>
      let s := rest.takeWhile (· != '"')
      .ok (.persistentString (String.mk s), rest.drop (s.length + 1))
    | '#' :: 'c' :: 'p' :: 'p' :: rest => do
      let (o, r) ← readOne (rest.dropWhile Char.isWhitespace)
      .ok (.persistentList none [.symbol none "cpp" "dsl", o], r)
    | _ =>
      let tok := cs.takeWhile (!isDelim ·)
      if tok.isEmpty then .error s!"unexpected {cs.headD ' '}"
      else .ok (atom (String.mk tok), cs.drop tok.length)

/-- The forms of a program text. -/
def read (s : String) : Except String (List Obj) := (readForms s.toList []).map (·.1)

/-- The single form of a text. -/
def read1 (s : String) : Obj := match read s with | .ok (o :: _) => o | _ => .nil

end Jank.Interop.Read
