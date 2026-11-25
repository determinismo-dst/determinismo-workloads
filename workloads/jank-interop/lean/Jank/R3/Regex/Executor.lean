import Jank.R3.Regex.Compiler

/-!
# `std::__detail::_Executor<…, __dfs_mode = true>`

libstdc++ 15.3.0 `regex_executor.h`/`.tcc`. `__regex_algo_impl` (regex.tcc 45) takes the BFS
executor only for `regex_constants::__polynomial` (or the test-only `_S_alternate` policy); jank
never passes it, so every search and match runs the recursive DFS executor:

- `_M_search` (executor.tcc 41), `_M_search_from_first`/`_M_match` (executor.h 90/97),
  `_M_main_dispatch(__dfs)` (executor.tcc 86);
- `_M_dfs` (executor.tcc 525) with every handler inlined: `_M_handle_repeat` (233) and
  `_M_rep_once_more` (206), `_M_handle_subexpr_begin`/`_end` (282/296), the assertions
  (310–344), `_M_handle_subexpr_lookahead` (348) and `_M_lookahead` (186, a sub-executor that
  starts at the current position with the current flags), `_M_handle_match` (358),
  `_M_handle_backref` (430), `_M_handle_accept` (461), `_M_handle_alternative` (507);
- `_M_at_begin`/`_M_at_end` (executor.h 154/180) without `multiline`, `_M_word_boundary`
  (executor.tcc 558), `_M_is_word` (executor.h 146).

The input is the whole buffer (`inp`) with the executor's `[begin, end)` inside it: with
`match_prev_avail` the character before `begin` is read. `depth` counts the `_M_dfs` frames on the
stack (a lookahead's sub-executor stacks its frames on the caller's); `maxDepth` is the deepest.
`fuel` bounds the depth and `budget` the number of `_M_dfs` calls (a search past either is
reported, not given a value).
-/

namespace Jank.R3.Regex

inductive Mode where
  | exact | prefix_
  deriving BEq, DecidableEq, Repr, Inhabited

/-- `regex_constants::match_flag_type` bits that the executor reads. -/
structure Flags where
  notBol : Bool := false
  notEol : Bool := false
  notBow : Bool := false
  notEow : Bool := false
  notNull : Bool := false
  continuous : Bool := false
  prevAvail : Bool := false
  deriving BEq, DecidableEq, Repr, Inhabited

/-- `sub_match<const char*>` as positions in the buffer. -/
structure Sub where
  first : Nat := 0
  second : Nat := 0
  matched : Bool := false
  deriving BEq, DecidableEq, Repr, Inhabited

structure ExSt where
  cur : Nat
  begin : Nat
  flags : Flags
  curRes : Array Sub
  res : Array Sub
  /-- `_M_rep_count`: per state, the position and the count. -/
  rep : Array (Nat × Nat)
  hasSol : Bool := false
  depth : Nat := 0
  maxDepth : Nat := 0
  /-- Frames left on the stack when every call in tail position is a sibling call. -/
  ntDepth : Nat := 0
  maxNT : Nat := 0
  steps : Nat := 0
  deriving Inhabited

/-- Set-aside toggles for the residual searches: each replaces one libstdc++ rule by Java's.
All off is the replica. -/
structure EFix where
  /-- `$` also before a final line terminator (Java's `Dollar`). -/
  javaDollar : Bool := false
  /-- A lookahead's sub-executor sees the characters before it (`match_prev_avail` whenever it
  does not start at the search's first position). -/
  lookPrevAvail : Bool := false
  /-- `match_not_null` is not passed into a lookahead's sub-executor. -/
  lookNoNotNull : Bool := false
  deriving BEq, Repr, Inhabited

structure Ctx where
  nfa : NFA
  inp : Array Nat
  end_ : Nat
  budget : Nat
  fix : EFix := {}

/-- Why a run was cut short: `depth` (more `_M_dfs` frames than the fuel) or `steps`. -/
inductive Abort where
  | depth | steps
  deriving BEq, DecidableEq, Repr, Inhabited

abbrev EM := StateT ExSt (Except Abort)

def ethrow {α : Type} (a : Abort) : EM α := fun _ => .error a

def Ctx.st (c : Ctx) (i : Int) : St := c.nfa.states.getD i.toNat default
def Ctx.at (c : Ctx) (i : Nat) : Nat := c.inp.getD i 0

/-- `_M_is_word`: `isctype(c, lookup_classname("w"))`. -/
def isWord (loc : Loc) (c : Nat) : Bool := isctype loc c (lookupClassname loc [0x77])

/-- `_M_at_begin` (executor.h 154), `multiline` off. -/
def atBegin (st : ExSt) : Bool :=
  if st.cur == st.begin then
    if st.flags.notBol then false
    else if st.flags.prevAvail then false
    else true
  else false

/-- `_M_at_end` (executor.h 180), `multiline` off. -/
def atEnd (c : Ctx) (st : ExSt) : Bool :=
  if st.cur == c.end_ then !st.flags.notEol
  else if c.fix.javaDollar then
    -- Java `Dollar(false)`: before a final \n, \r, \r\n (bytes 0x0A/0x0D)
    let n := c.end_
    (st.cur + 1 == n && (c.at st.cur == 0x0A && !(st.cur > 0 && c.at (st.cur - 1) == 0x0D) || c.at st.cur == 0x0D)) ||
    (st.cur + 2 == n && c.at st.cur == 0x0D && c.at (st.cur + 1) == 0x0A)
  else false

/-- `_M_word_boundary` (executor.tcc 558). -/
def wordBoundary (c : Ctx) (st : ExSt) : Bool :=
  if st.cur == st.begin && st.flags.notBow then false
  else if st.cur == c.end_ && st.flags.notEow then false
  else
    let left := (st.cur != st.begin || st.flags.prevAvail) && st.cur > 0 &&
      isWord c.nfa.loc (c.at (st.cur - 1))
    let right := st.cur != c.end_ && isWord c.nfa.loc (c.at st.cur)
    left != right

def setCurRes (k : Nat) (s : Sub) : EM Unit :=
  modify fun st => { st with curRes := st.curRes.set! k s }

/-- The sub-executor `_M_lookahead` (executor.tcc 186) builds: `_Executor(_M_current, _M_end,
__what, _M_re, _M_flags)` — its `_M_begin` is the current position, its flags the caller's
(the constructor drops not_bol/not_bow under prev_avail), its results a copy of the current ones,
fresh repeat counts. -/
def lookSub (c : Ctx) (outer : ExSt) : ExSt :=
  let fl := outer.flags
  let fl := if c.fix.lookPrevAvail && outer.cur != outer.begin then { fl with prevAvail := true } else fl
  let fl := if c.fix.lookNoNotNull then { fl with notNull := false } else fl
  let fl := if fl.prevAvail then { fl with notBol := false, notBow := false } else fl
  { cur := outer.cur, begin := outer.cur, flags := fl, curRes := outer.curRes,
    res := outer.curRes, rep := Array.replicate c.nfa.states.size (0, 0),
    hasSol := false, depth := outer.depth, maxDepth := outer.maxDepth,
    ntDepth := outer.ntDepth, maxNT := outer.maxNT, steps := outer.steps }

/-- `_M_dfs` (executor.tcc 525) and its handlers. `tail`: the C++ call is the caller's last
action (a sibling call at -O2 leaves no frame). -/
def dfs (c : Ctx) : Nat → Mode → Int → Bool → EM Unit
  | 0, _, _, _ => ethrow .depth
  | f + 1, mode, i, tail => do
    let st0 ← get
    if st0.steps ≥ c.budget then ethrow .steps
    let d := st0.depth + 1
    let nt := if tail then st0.ntDepth else st0.ntDepth + 1
    set { st0 with steps := st0.steps + 1, depth := d, maxDepth := max st0.maxDepth d,
                   ntDepth := nt, maxNT := max st0.maxNT nt }
    let s := c.st i
    -- `_M_rep_once_more` (executor.tcc 206)
    let repOnceMore : EM Unit := do
      let st ← get
      let k := i.toNat
      let rc := st.rep.getD k (0, 0)
      if rc.2 == 0 || rc.1 != st.cur then
        set { st with rep := st.rep.set! k (st.cur, 1) }
        dfs c f mode s.alt false
        modify fun st => { st with rep := st.rep.set! k rc }
      else if rc.2 < 2 then
        set { st with rep := st.rep.set! k (rc.1, rc.2 + 1) }
        dfs c f mode s.alt false
        modify fun st =>
          let r := st.rep.getD k (0, 0)
          { st with rep := st.rep.set! k (r.1, r.2 - 1) }
      else pure ()
    match s.op with
    | .repeat_ =>
      if !s.neg then
        repOnceMore
        -- "If it's DFS executor and already accepted, we're done."
        if !(← get).hasSol then dfs c f mode s.next true
      else
        dfs c f mode s.next false
        if !(← get).hasSol then repOnceMore
    | .subBegin =>
      let st ← get
      let r := st.curRes.getD s.idx {}
      setCurRes s.idx { r with first := st.cur }
      dfs c f mode s.next false
      let r' := (← get).curRes.getD s.idx {}
      setCurRes s.idx { r' with first := r.first }
    | .subEnd =>
      let st ← get
      let back := st.curRes.getD s.idx {}
      setCurRes s.idx { back with second := st.cur, matched := true }
      dfs c f mode s.next false
      setCurRes s.idx back
    | .lineBegin =>
      if atBegin (← get) then dfs c f mode s.next true
    | .lineEnd =>
      if atEnd c (← get) then dfs c f mode s.next true
    | .wordBound =>
      if wordBoundary c (← get) == !s.neg then dfs c f mode s.next true
    | .lookahead =>
      -- `_M_lookahead` (executor.tcc 186): a sub-executor over [current, end) with the
      -- current flags (its constructor drops not_bol/not_bow under prev_avail), a copy of the
      -- current results, fresh repeat counts, `_M_search_from_first` from the sub-NFA's start.
      let outer ← get
      set (lookSub c outer)
      dfs c f .prefix_ s.alt false
      let sub ← get
      let ok := sub.hasSol
      let merged :=
        if ok then
          (List.range sub.res.size).foldl (fun acc k =>
            let w := sub.res.getD k {}
            if w.matched then acc.set! k w else acc) outer.curRes
        else outer.curRes
      set { outer with curRes := merged, steps := sub.steps, maxDepth := sub.maxDepth, maxNT := sub.maxNT }
      if ok == !s.neg then dfs c f mode s.next true
    | .match_ =>
      let st ← get
      if st.cur == c.end_ then pure ()
      else if s.m.matches c.nfa.loc (c.at st.cur) then
        set { st with cur := st.cur + 1 }
        dfs c f mode s.next false
        modify fun st => { st with cur := st.cur - 1 }
      else pure ()
    | .backref =>
      let st ← get
      let sm := st.curRes.getD s.idx {}
      if !sm.matched then pure ()
      else
        let len := sm.second - sm.first
        let last := st.cur + min len (c.end_ - st.cur)
        let eq := (last - st.cur == len) &&
          (List.range len).all fun k => c.at (sm.first + k) == c.at (st.cur + k)
        if eq then
          if last != st.cur then
            let backup := st.cur
            set { st with cur := last }
            dfs c f mode s.next false
            modify fun st => { st with cur := backup }
          else dfs c f mode s.next true
    | .accept =>
      let st ← get
      let sol := if mode == .exact then st.cur == c.end_ else true
      let sol := if st.cur == st.begin && st.flags.notNull then false else sol
      if sol then set { st with hasSol := true, res := st.curRes }
      else set { st with hasSol := false }
    | .alternative =>
      -- ECMAScript: the left alternative; the right one only when the left found nothing
      dfs c f mode s.alt false
      if !(← get).hasSol then dfs c f mode s.next true
    | _ => pure ()
    modify fun st => { st with depth := st.depth - 1, ntDepth := st0.ntDepth }

/-- `_M_main_dispatch(__dfs)` (executor.tcc 86) after `_M_current = _M_begin`. -/
def searchFromFirst (c : Ctx) (fuel : Nat) (mode : Mode) : EM Bool := do
  modify fun st => { st with cur := st.begin, hasSol := false, curRes := st.res }
  dfs c fuel mode 0 false
  return (← get).hasSol

/-- `_M_search` (executor.tcc 41): from `begin`, then (unless `match_continuous`) with
`match_prev_avail` from each later position up to and including `end`. -/
def searchAll (c : Ctx) (fuel : Nat) : EM Bool := do
  if ← searchFromFirst c fuel .prefix_ then return true
  if (← get).flags.continuous then return false
  modify fun st => { st with flags := { st.flags with prevAvail := true } }
  let rec loop : Nat → EM Bool
    | 0 => return false
    | k + 1 => do
      let st ← get
      if st.begin == c.end_ then return false
      set { st with begin := st.begin + 1 }
      if ← searchFromFirst c fuel .prefix_ then return true
      loop k
  loop (c.end_ + 1)

/-- A finished `match_results<const char*>`: the visible sub-matches (none after a failed search),
prefix, suffix, the unmatched-sub sentinel and `_M_begin`. -/
structure MatchRes where
  subs : Array Sub
  pre : Sub
  suf : Sub
  unm : Sub
  mbegin : Nat
  deriving BEq, Repr, Inhabited

def MatchRes.empty (m : MatchRes) : Bool := m.subs.isEmpty
def MatchRes.size (m : MatchRes) : Nat := m.subs.size
/-- `operator[]`: past `size()`, the unmatched sentinel. -/
def MatchRes.get (m : MatchRes) (n : Nat) : Sub := if n < m.subs.size then m.subs.getD n {} else m.unm
def MatchRes.prefix (m : MatchRes) : Sub := if m.empty then m.unm else m.pre
def MatchRes.suffix (m : MatchRes) : Sub := if m.empty then m.unm else m.suf

/-- `sub_match::str()` over a buffer. -/
def Sub.str (inp : Array Nat) (s : Sub) : List Nat :=
  if s.matched then (inp.extract s.first s.second).toList else []

/-- Counters of one executor run. -/
structure Stats where
  steps : Nat := 0
  maxDepth : Nat := 0
  maxNT : Nat := 0
  deriving Repr, Inhabited, BEq

/-- `__regex_algo_impl` (regex.tcc 45) with the DFS executor: `regex_search` (match mode off) or
`regex_match` over `[s, e)` of `inp`. -/
def regexAlgo (nfa : NFA) (inp : Array Nat) (s e : Nat) (flags : Flags) (matchMode : Bool)
    (budget fuel : Nat) (fix : EFix := {}) : Except Abort (Bool × MatchRes × Stats) :=
  let c : Ctx := { nfa, inp, end_ := e, budget, fix }
  let init : Array Sub := Array.replicate nfa.subCount {}
  -- the `_Executor` constructor drops not_bol/not_bow under prev_avail
  let fl := if flags.prevAvail then { flags with notBol := false, notBow := false } else flags
  let st0 : ExSt := { cur := s, begin := s, flags := fl, curRes := init, res := init,
                      rep := Array.replicate nfa.states.size (0, 0) }
  let run : EM Bool := if matchMode then searchFromFirst c fuel .exact else searchAll c fuel
  match run.run st0 with
  | .error a => .error a
  | .ok (ok, st) =>
    let stats : Stats := { steps := st.steps, maxDepth := st.maxDepth, maxNT := st.maxNT }
    if ok then
      let subs := st.res.map fun r => if r.matched then r else { r with first := e, second := e }
      let m0 := subs.getD 0 {}
      let (pre, suf) :=
        if matchMode then (({ first := s, second := s, matched := false } : Sub),
                           ({ first := e, second := e, matched := false } : Sub))
        else (({ first := s, second := m0.first, matched := s != m0.first } : Sub),
              ({ first := m0.second, second := e, matched := m0.second != e } : Sub))
      .ok (true, { subs, pre, suf, unm := { first := e, second := e }, mbegin := s }, stats)
    else
      -- `_M_establish_failed_match(__e)`
      let u : Sub := { first := e, second := e, matched := false }
      .ok (false, { subs := #[], pre := u, suf := u, unm := u, mbegin := s }, stats)

end Jank.R3.Regex
