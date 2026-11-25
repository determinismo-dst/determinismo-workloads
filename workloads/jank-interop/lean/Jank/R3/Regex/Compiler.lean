import Jank.R3.Regex.Scanner

/-!
# `std::__detail::_Compiler`, `_NFA`, `_StateSeq` and the matchers

libstdc++ 15.3.0 `regex_compiler.h`/`.tcc` and `regex_automaton.h`/`.tcc`, for ECMAScript without
`icase`/`collate`/`nosubs`/`multiline`/`__polynomial` (jank's only flags):

- `_Compiler` (compiler.tcc 66): `_M_disjunction` 87, `_M_alternative` 110, `_M_term` 125,
  `_M_assertion` 139, `_M_quantifier` 169, `_M_atom` 288, `_M_bracket_expression` 321,
  `_M_insert_*_matcher` 333–420, `_M_expression_term` 434, `_M_try_char` 538,
  `_M_match_token` 557, `_M_cur_int_value` 571;
- `_BracketMatcher` (compiler.h 410: `_M_add_*`, `_M_make_range`, `_M_ready`; compiler.tcc 583
  `_M_apply`), `_CharMatcher`, `_AnyMatcher<ECMA>` (compiler.h 366: not '\n', not '\r');
- `_NFA::_M_insert_*` (automaton.h 210–320), the 100000-state limit (`_M_insert_state`,
  automaton.h 322), `_M_insert_backref` (automaton.tcc 154), `_M_eliminate_dummy` (183),
  `_StateSeq::_M_clone` (199).

State ids are `Int` (`_StateIdT` is `long`; `_S_invalid_state_id` = -1). Every recursion is
structural on a fuel argument (the pattern's length bounds the tokens), so concrete patterns run in
the kernel.
-/

namespace Jank.R3.Regex

/-- automaton.h `_Opcode`. -/
inductive Op where
  | alternative | repeat_ | backref | lineBegin | lineEnd | wordBound | lookahead | subBegin
  | subEnd | dummy | match_ | accept
  deriving BEq, DecidableEq, Repr, Inhabited

/-- `_BracketMatcher`'s sets (translation and transform are the identity without icase/collate). -/
structure Bracket where
  chars : List Nat := []
  equivs : List (List Nat) := []
  /-- `_M_range_set`: pairs of signed `char` values. -/
  ranges : List (Int × Int) := []
  negClasses : List RMask := []
  classSet : RMask := RMask.zero
  nonMatching : Bool
  deriving BEq, Repr, Inhabited

/-- The `std::function<bool(char)>` of an `_S_opcode_match` state. -/
inductive Matcher where
  /-- `_AnyMatcher<_TraitsT, true, false, false>`. -/
  | any
  /-- `_CharMatcher`. -/
  | char (c : Nat)
  | bracket (b : Bracket)
  deriving BEq, Repr, Inhabited

/-- compiler.tcc `_BracketMatcher::_M_apply` (583), XOR `_M_is_non_matching`. -/
def Bracket.apply (loc : Loc) (b : Bracket) (ch : Nat) : Bool :=
  let hit :=
    b.chars.contains ch ||
    b.ranges.any (fun (lo, hi) => lo ≤ sval ch && sval ch ≤ hi) ||
    isctype loc ch b.classSet ||
    (!b.equivs.isEmpty && b.equivs.contains (transformPrimary loc [ch])) ||
    b.negClasses.any (fun m => !isctype loc ch m)
  hit != b.nonMatching

def Matcher.matches (loc : Loc) : Matcher → Nat → Bool
  | .any, c => c != 0x0A && c != 0x0D
  | .char c, d => c == d
  | .bracket b, d => b.apply loc d

/-- automaton.h `_State`. -/
structure St where
  op : Op
  next : Int := -1
  alt : Int := -1
  neg : Bool := false
  /-- `_M_subexpr` / `_M_backref_index`. -/
  idx : Nat := 0
  m : Matcher := .any
  deriving BEq, Repr, Inhabited

def St.hasAlt (s : St) : Bool :=
  s.op == .alternative || s.op == .repeat_ || s.op == .lookahead

def stateLimit : Nat := 100000

/-- A compiled `std::regex`: its NFA, `_M_subexpr_count` (group 0 included) and `_M_has_backref`. -/
structure NFA where
  states : Array St
  subCount : Nat
  hasBackref : Bool
  loc : Loc
  deriving Inhabited

/-- `_StateSeq`: start and end. -/
abbrev Seq := Int × Int

structure CState where
  nfa : Array St := #[]
  subCount : Nat := 0
  parenStack : Array Nat := #[]
  hasBackref : Bool := false
  /-- `_M_stack` (`std::stack<_StateSeq>`): the head is the top. -/
  stack : List Seq := []
  sc : Scanner
  value : List Nat := []

abbrev CM := StateT CState (Except RxErr)

def cthrow {α : Type} (e : RxErr) : CM α := fun _ => .error e

def loc : CM Loc := do return (← get).sc.loc

/-- automaton.h `_M_insert_state` (322). -/
def insertState (s : St) : CM Int := do
  let st ← get
  let nfa := st.nfa.push s
  set { st with nfa }
  if nfa.size > stateLimit then
    cthrow (rxErr .space "Number of NFA states exceeds limit. Please use shorter regex string, or use smaller brace expression, or make _GLIBCXX_REGEX_STATE_LIMIT larger.")
  else return (nfa.size - 1 : Nat)

def getSt (i : Int) : CM St := do return (← get).nfa.getD i.toNat default

def modSt (i : Int) (f : St → St) : CM Unit :=
  modify fun st => { st with nfa := st.nfa.modify i.toNat f }

/-- `_StateSeq::_M_append(_StateIdT)`. -/
def appendId (s : Seq) (id : Int) : CM Seq := do
  modSt s.2 (fun x => { x with next := id })
  return (s.1, id)

/-- `_StateSeq::_M_append(const _StateSeq&)`. -/
def appendSeq (s t : Seq) : CM Seq := do
  modSt s.2 (fun x => { x with next := t.1 })
  return (s.1, t.2)

def push (s : Seq) : CM Unit := modify fun st => { st with stack := s :: st.stack }

/-- `_M_pop()` (an empty `std::stack` cannot be popped here: every call follows a push). -/
def pop : CM Seq := do
  let st ← get
  match st.stack with
  | s :: rest => set { st with stack := rest }; return s
  | [] => return (-1, -1)

def insertDummy : CM Int := insertState { op := .dummy }
def insertAccept : CM Int := insertState { op := .accept }

def insertSubexprBegin : CM Int := do
  let st ← get
  let id := st.subCount
  set { st with subCount := id + 1, parenStack := st.parenStack.push id }
  insertState { op := .subBegin, idx := id }

def insertSubexprEnd : CM Int := do
  let st ← get
  let id := st.parenStack.back?.getD 0
  set { st with parenStack := st.parenStack.pop }
  insertState { op := .subEnd, idx := id }

def insertRepeat (next alt : Int) (neg : Bool) : CM Int :=
  insertState { op := .repeat_, next, alt, neg }

def insertAlt (next alt : Int) : CM Int := insertState { op := .alternative, next, alt }

/-- automaton.tcc `_M_insert_backref` (154). -/
def insertBackref (index : Nat) : CM Int := do
  let st ← get
  if index ≥ st.subCount then
    cthrow (rxErr .backref "Back-reference index exceeds current sub-expression count.")
  else if st.parenStack.contains index then
    cthrow (rxErr .backref "Back-reference referred to an opened sub-expression.")
  else
    set { st with hasBackref := true }
    insertState { op := .backref, idx := index }

/-- `_M_match_token` (compiler.tcc 557). -/
def matchToken (t : Tok) : CM Bool := do
  let st ← get
  if st.sc.token == t then
    match st.sc.advance with
    | .ok sc => set { st with value := st.sc.value, sc }; return true
    | .error e => cthrow e
  else return false

def intMin : Int := -2147483648
def intMax : Int := 2147483647

/-- `_M_cur_int_value` (compiler.tcc 571): `int` arithmetic with overflow checks; an overflow
throws `error_backref` ("invalid back reference"), whatever the use. -/
def curIntValue (radix : Nat) : CM Int := do
  let v := (← get).value
  let rec go : List Nat → Int → Option Int
    | [], acc => some acc
    | c :: cs, acc =>
      let m := acc * radix
      if m < intMin || m > intMax then none
      else
        let a := m + traitsValue c radix
        if a < intMin || a > intMax then none else go cs a
  match go v 0 with
  | some n => return n
  | none => cthrow (rxErr .backref "invalid back reference")

/-- `static_cast<char>(int)`: the low byte. -/
def toChar (i : Int) : Nat := (i % 256).toNat

/-- `_M_try_char` (compiler.tcc 538): an octal/hex number (as `char`) or an ordinary char. -/
def tryChar : CM Bool := do
  if ← matchToken .octNum then
    let v ← curIntValue 8
    modify fun st => { st with value := [toChar v] }
    return true
  else if ← matchToken .hexNum then
    let v ← curIntValue 16
    modify fun st => { st with value := [toChar v] }
    return true
  else matchToken .ordChar

def valueHead : CM Nat := do return (← get).value.headD 0

/-- `_StateSeq::_M_clone` (automaton.tcc 199): DFS with a `std::stack`, a `std::map` from old to
new ids (a node pushed twice before it is visited is inserted twice: the first copy is left
unreachable), then every copy's links rewritten through the map. -/
def cloneSeq (s : Seq) : CM Seq := do
  let rec walk : Nat → List Int → List (Int × Int) → CM (List (Int × Int))
    | 0, _, m => return m
    | _ + 1, [], m => return m
    | f + 1, u :: stk, m => do
      let dup ← getSt u
      let id ← insertState dup
      let m := (u, id) :: m.filter (·.1 != u)
      let stk := if dup.hasAlt && dup.alt != -1 && !(m.any (·.1 == dup.alt)) then dup.alt :: stk else stk
      if u == s.2 then walk f stk m
      else
        let stk := if dup.next != -1 && !(m.any (·.1 == dup.next)) then dup.next :: stk else stk
        walk f stk m
  let n := (← get).nfa.size
  let m ← walk (4 * n + 4) [s.1] []
  let find (k : Int) : Int := (m.find? (·.1 == k)).map (·.2) |>.getD (-1)
  for (_, v) in m do
    let r ← getSt v
    let next := if r.next != -1 then find r.next else r.next
    let alt := if r.hasAlt && r.alt != -1 then find r.alt else r.alt
    modSt v fun x => { x with next, alt }
  return (find s.1, find s.2)

/-- The `_BracketState` of `_M_insert_bracket_matcher`. -/
inductive BState where
  | none
  | char (c : Nat)
  | cls
  deriving BEq, Repr, Inhabited

/-- `_M_add_character_class` (compiler.h 456). -/
def addCharClass (b : Bracket) (name : List Nat) (neg : Bool) : CM Bracket := do
  let mask := lookupClassname (← loc) name false
  if mask == RMask.zero then cthrow (rxErr .collate "Invalid character class.")
  else if !neg then return { b with classSet := b.classSet.or mask }
  else return { b with negClasses := b.negClasses ++ [mask] }

/-- `_M_make_range` (compiler.h 470): signed `char` comparison. -/
def makeRange (b : Bracket) (l r : Nat) : CM Bracket := do
  if sval l > sval r then cthrow (rxErr .range "Invalid range in bracket expression.")
  else return { b with ranges := b.ranges ++ [(sval l, sval r)] }

/-- `_M_expression_term` (compiler.tcc 434): whether to go on, the cached last atom, the matcher. -/
def expressionTerm (last : BState) (b : Bracket) : CM (Bool × BState × Bracket) := do
  if ← matchToken .bracketEnd then return (false, last, b)
  -- `__push_char`: add any cached char, cache the new one.
  let pushChar (b : Bracket) (ch : Nat) : BState × Bracket :=
    match last with
    | .char c => (.char ch, { b with chars := b.chars ++ [c] })
    | _ => (.char ch, b)
  -- `__push_class`: add any cached char, record that a class came last.
  let pushClass (b : Bracket) : Bracket :=
    match last with
    | .char c => { b with chars := b.chars ++ [c] }
    | _ => b
  if ← matchToken .collsymbol then
    -- `_M_add_collate_element` (compiler.h 427) adds the element's first char itself
    let st := lookupCollatename (← get).value
    if st.isEmpty then cthrow (rxErr .collate "Invalid collate element.")
    else
      let b := { b with chars := b.chars ++ [st.headD 0] }
      if st.length == 1 then
        let (l, b) := pushChar b (st.headD 0)
        return (true, l, b)
      else return (true, .cls, pushClass b)
  else if ← matchToken .equivClassName then
    let b := pushClass b
    let st := lookupCollatename (← get).value
    if st.isEmpty then cthrow (rxErr .collate "Invalid equivalence class.")
    else return (true, .cls, { b with equivs := b.equivs ++ [transformPrimary (← loc) st] })
  else if ← matchToken .charClassName then
    let b ← addCharClass (pushClass b) (← get).value false
    return (true, .cls, b)
  else if ← tryChar then
    let (l, b) := pushChar b (← valueHead)
    return (true, l, b)
  else if ← matchToken .bracketDash then
    if ← matchToken .bracketEnd then
      -- "-]": the dash is a literal character, and the bracket ends
      let (l, b) := pushChar b 0x2D
      return (false, l, b)
    else match last with
      | .cls => cthrow (rxErr .range "Invalid start of '[x-x]' range in regular expression")
      | .char c =>
        if ← tryChar then
          let b ← makeRange b c (← valueHead)
          return (true, .none, b)
        else if ← matchToken .bracketDash then
          let b ← makeRange b c 0x2D
          return (true, .none, b)
        else cthrow (rxErr .range "Invalid end of '[x-x]' range in regular expression")
      | .none =>
        -- ECMAScript: a dash that is not part of a range is a literal
        let (l, b) := pushChar b 0x2D
        return (true, l, b)
  else if ← matchToken .quotedClass then
    let b := pushClass b
    let v := (← get).value
    let b ← addCharClass b v (ctypeIs (← loc) mUpper (v.headD 0))
    return (true, .cls, b)
  else cthrow (rxErr .brack "Unexpected character within '[...]' in regular expression")

/-- `while (_M_expression_term(__last_char, __matcher));` -/
def expressionTerms : Nat → BState → Bracket → CM (BState × Bracket)
  | 0, l, b => return (l, b)
  | f + 1, l, b => do
    let (go, l, b) ← expressionTerm l b
    if go then expressionTerms f l b else return (l, b)

/-- `_M_insert_bracket_matcher` (compiler.tcc 412). -/
def insertBracketMatcher (neg : Bool) : CM Unit := do
  let b : Bracket := { nonMatching := neg }
  let l ← (do
    if ← tryChar then return BState.char (← valueHead)
    else if ← matchToken .bracketDash then return BState.char 0x2D
    else return BState.none : CM BState)
  let (l, b) ← expressionTerms ((← get).sc.pat.size + 2) l b
  let b := match l with
    | .char c => { b with chars := b.chars ++ [c] }
    | _ => b
  let id ← insertState { op := .match_, m := .bracket b }
  push (id, id)

/-- `_M_insert_character_class_matcher` (compiler.tcc 396): `\d \D \s \S \w \W` outside a
bracket: a bracket matcher, non-matching when the letter is upper case. -/
def insertCharacterClassMatcher : CM Unit := do
  let v := (← get).value
  let b : Bracket := { nonMatching := ctypeIs (← loc) mUpper (v.headD 0) }
  let b ← addCharClass b v false
  let id ← insertState { op := .match_, m := .bracket b }
  push (id, id)

def insertMatcher (m : Matcher) : CM Unit := do
  let id ← insertState { op := .match_, m }
  push (id, id)

/-- `{n,m}` of `_M_quantifier` (compiler.tcc 214–282). -/
def intervalQuantifier (neg0 : Bool) : CM Unit := do
  if (← get).stack.isEmpty then cthrow (rxErr .badrepeat) else
  if !(← matchToken .dupCount) then cthrow (rxErr .badbrace) else
  let r ← pop
  let d ← insertDummy
  let mut e : Seq := (d, d)
  let minRep ← curIntValue 10
  let mut infi := false
  let mut n : Int := 0
  if ← matchToken .comma then
    if ← matchToken .dupCount then n := (← curIntValue 10) - minRep
    else infi := true
  if !(← matchToken .intervalEnd) then cthrow (rxErr .brace) else
  let neg := neg0 && (← matchToken .opt)
  -- `for (long __i = 0; __i < __min_rep; ++__i) __e._M_append(__r._M_clone());`
  let rec clones : Nat → Seq → CM Seq
    | 0, e => return e
    | k + 1, e => do
      let c ← cloneSeq r
      let e ← appendSeq e c
      clones k e
  e ← clones minRep.toNat e
  if infi then
    let tmp ← cloneSeq r
    let s ← insertRepeat (-1) tmp.1 neg
    let _ ← appendId tmp s
    e ← appendId e s
  else
    if n < 0 then cthrow (rxErr .badbrace) else
    let fin ← insertDummy
    let rec bounded : Nat → Seq → List Int → CM (Seq × List Int)
      | 0, e, stk => return (e, stk)
      | k + 1, e, stk => do
        let tmp ← cloneSeq r
        let alt ← insertRepeat tmp.1 fin neg
        let e ← appendSeq e (alt, tmp.2)
        bounded k e (alt :: stk)
    let (e', stk) ← bounded n.toNat e []
    e ← appendId e' fin
    -- swap `_M_next` and `_M_alt` of every repeat node created
    for a in stk do
      modSt a fun x => { x with next := x.alt, alt := x.next }
  push e

/-- `_M_quantifier` (compiler.tcc 169) for `*`, `+`, `?`; `{…}` in `intervalQuantifier`. -/
def quantifier : CM Bool := do
  let neg0 := true  -- ECMAScript
  let init : CM Bool := do
    if (← get).stack.isEmpty then cthrow (rxErr .badrepeat)
    else return (neg0 && (← matchToken .opt))
  if ← matchToken .closure0 then
    let neg ← init
    let e ← pop
    let rid ← insertRepeat (-1) e.1 neg
    let _ ← appendId e rid
    push (rid, rid)
    return true
  else if ← matchToken .closure1 then
    let neg ← init
    let e ← pop
    let rid ← insertRepeat (-1) e.1 neg
    let e ← appendId e rid
    push e
    return true
  else if ← matchToken .opt then
    let neg ← init
    let e ← pop
    let fin ← insertDummy
    let rid ← insertRepeat (-1) e.1 neg
    let _ ← appendId e fin
    let r ← appendId (rid, rid) fin
    push r
    return true
  else if ← matchToken .intervalBegin then
    intervalQuantifier neg0
    return true
  else return false

mutual
/-- `_M_disjunction` (compiler.tcc 87). -/
def disjunction : Nat → CM Unit
  | 0 => cthrow (rxErr .complexity "fuel")
  | f + 1 => do
    alternative f
    ors f
/-- `while (_M_match_token(_S_token_or)) { ... }` -/
def ors : Nat → CM Unit
  | 0 => return
  | f + 1 => do
    if ← matchToken .or_ then
      let alt1 ← pop
      alternative f
      let alt2 ← pop
      let e ← insertDummy
      let _ ← appendId alt1 e
      let _ ← appendId alt2 e
      -- __alt2 is state._M_next, __alt1 is state._M_alt
      let a ← insertAlt alt2.1 alt1.1
      push (a, e)
      ors f
    else return
/-- `_M_alternative` (compiler.tcc 110). -/
def alternative : Nat → CM Unit
  | 0 => cthrow (rxErr .complexity "fuel")
  | f + 1 => do
    if ← term f then
      let re ← pop
      alternative f
      let t ← pop
      let re ← appendSeq re t
      push re
    else
      let d ← insertDummy
      push (d, d)
/-- `_M_term` (compiler.tcc 125). -/
def term : Nat → CM Bool
  | 0 => cthrow (rxErr .complexity "fuel")
  | f + 1 => do
    if ← assertion f then return true
    if ← atom f then
      quantifiers f
      return true
    return false
/-- `while (this->_M_quantifier());` -/
def quantifiers : Nat → CM Unit
  | 0 => return
  | f + 1 => do if ← quantifier then quantifiers f else return
/-- `_M_assertion` (compiler.tcc 139). -/
def assertion : Nat → CM Bool
  | 0 => cthrow (rxErr .complexity "fuel")
  | f + 1 => do
    if ← matchToken .lineBegin then
      let id ← insertState { op := .lineBegin }
      push (id, id); return true
    else if ← matchToken .lineEnd then
      let id ← insertState { op := .lineEnd }
      push (id, id); return true
    else if ← matchToken .wordBound then
      let neg := (← get).value.headD 0 == 0x6E
      let id ← insertState { op := .wordBound, neg }
      push (id, id); return true
    else if ← matchToken .subexprLookaheadBegin then
      let neg := (← get).value.headD 0 == 0x6E
      disjunction f
      if !(← matchToken .subexprEnd) then cthrow (rxErr .paren) else
      let tmp ← pop
      let acc ← insertAccept
      let _ ← appendId tmp acc
      let id ← insertState { op := .lookahead, alt := tmp.1, neg }
      push (id, id); return true
    else return false
/-- `_M_atom` (compiler.tcc 288). -/
def atom : Nat → CM Bool
  | 0 => cthrow (rxErr .complexity "fuel")
  | f + 1 => do
    if ← matchToken .anychar then insertMatcher .any; return true
    else if ← tryChar then insertMatcher (.char (← valueHead)); return true
    else if ← matchToken .backref then
      let i ← curIntValue 10
      let id ← insertBackref i.toNat
      push (id, id); return true
    else if ← matchToken .quotedClass then insertCharacterClassMatcher; return true
    else if ← matchToken .subexprNoGroupBegin then
      let d ← insertDummy
      disjunction f
      if !(← matchToken .subexprEnd) then cthrow (rxErr .paren) else
      let t ← pop
      let r ← appendSeq (d, d) t
      push r; return true
    else if ← matchToken .subexprBegin then
      let b ← insertSubexprBegin
      disjunction f
      if !(← matchToken .subexprEnd) then cthrow (rxErr .paren) else
      let t ← pop
      let r ← appendSeq (b, b) t
      let e ← insertSubexprEnd
      let r ← appendId r e
      push r; return true
    else
      -- `_M_bracket_expression` (compiler.tcc 321)
      let neg ← matchToken .bracketNegBegin
      if !(neg || (← matchToken .bracketBegin)) then return false
      insertBracketMatcher neg
      return true
end

/-- automaton.tcc `_M_eliminate_dummy` (183). -/
def eliminateDummy (states : Array St) : Array St :=
  let skip (i : Int) : Int :=
    let rec go : Nat → Int → Int
      | 0, i => i
      | f + 1, i =>
        if i ≥ 0 && (states.getD i.toNat default).op == .dummy then go f (states.getD i.toNat default).next
        else i
    go (states.size + 1) i
  -- the result of following dummies is the same whether earlier states were rewritten or not
  states.map fun s => { s with next := skip s.next, alt := if s.hasAlt then skip s.alt else s.alt }

/-- `_Compiler(__b, __e, __loc, __flags)` (compiler.tcc 66) for `basic_regex(s.c_str(),
ECMAScript)`: the pattern is cut at its first NUL (`char_traits::length`). -/
def compile (loc : Loc) (pattern : List Nat) : Except RxErr NFA :=
  let pat := (pattern.takeWhile (· != 0)).toArray
  match Scanner.init pat loc with
  | .error e => .error e
  | .ok sc =>
    let body : CM Unit := do
      -- `_StateSeqT __r(*_M_nfa, _M_nfa->_M_start())` (state 0, inserted next)
      let b ← insertSubexprBegin
      let r ← appendId (0, 0) b
      disjunction (8 * pat.size + 16)
      if !(← matchToken .eof) then cthrow (rxErr .paren) else
      let t ← pop
      let r ← appendSeq r t
      let e ← insertSubexprEnd
      let r ← appendId r e
      let a ← insertAccept
      let _ ← appendId r a
      return
    match body.run { sc } with
    | .error e => .error e
    | .ok (_, st) => .ok { states := eliminateDummy st.nfa, subCount := st.subCount,
                           hasBackref := st.hasBackref, loc }

end Jank.R3.Regex
