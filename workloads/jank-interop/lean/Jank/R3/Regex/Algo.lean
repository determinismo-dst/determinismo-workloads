import Jank.R3.Regex.Executor

/-!
# `regex_iterator`, `match_results::format`, `regex_replace`

libstdc++ 15.3.0 `regex.h`/`regex.tcc`:

- `regex_iterator(a, b, re, flags)` (regex.h 2782): `regex_search(a, b, …)`, else the end
  iterator; `operator++` (regex.tcc 509): after an empty match not at the end, first
  `regex_search(start, end, …, flags | match_not_null | match_continuous)` (without adding
  `match_prev_avail`), and only when that fails one position later; then
  `flags |= match_prev_avail` (kept from then on) and `regex_search(start, end, …)`. Every
  match's prefix starts at the previous match's end and `_M_begin` is reset to the iterator's
  begin.
- `match_results::format` (regex.tcc 380), ECMAScript rules (`format_default`): `$$`, `$&`,
  `` $` ``, `$'`, `$n`, `$nn` (two digits whenever two follow; nothing when the number is not a
  group), `$` before anything else is a literal `$`.
- `__regex_replace` (regex.tcc 466): each match's prefix then its formatted text, then the last
  suffix; `format_first_only` stops after the first.
-/

namespace Jank.R3.Regex

/-- Limits of one jank call (all executor runs share the `_M_dfs` call budget). -/
structure Lim where
  budget : Nat := 200000
  fuel : Nat := 4000
  /-- Matches an iterator or re-seq walk may produce before it is called infinite. -/
  iters : Nat := 64
  fix : EFix := {}
  deriving Inhabited, Repr

/-- `regex_search`/`regex_match` on `[s, e)` of `inp`, counting into `stats`. -/
def search (nfa : NFA) (inp : Array Nat) (s e : Nat) (flags : Flags) (lim : Lim)
    (stats : Stats) (matchMode : Bool := false) : Except Abort (Bool × MatchRes × Stats) :=
  match regexAlgo nfa inp s e flags matchMode (lim.budget - min lim.budget stats.steps) lim.fuel lim.fix with
  | .error a => .error a
  | .ok (ok, m, st) =>
    .ok (ok, m, { steps := stats.steps + st.steps, maxDepth := max stats.maxDepth st.maxDepth,
                  maxNT := max stats.maxNT st.maxNT })

/-- `regex_iterator<const char*>`: begin, end, flags, current match; `live` is
`_M_pregex != nullptr`. -/
structure RIter where
  begin : Nat
  end_ : Nat
  flags : Flags
  m : MatchRes
  live : Bool
  deriving Inhabited

/-- regex.h 2782. -/
def RIter.init (nfa : NFA) (inp : Array Nat) (a b : Nat) (flags : Flags) (lim : Lim)
    (stats : Stats) : Except Abort (RIter × Stats) := do
  let (ok, m, stats) ← search nfa inp a b flags lim stats
  return ({ begin := a, end_ := b, flags, m, live := ok }, stats)

/-- Prefix fix-up after a successful search in `operator++`. -/
def fixPrefix (m : MatchRes) (prefixFirst begin : Nat) : MatchRes :=
  let pre := { m.pre with first := prefixFirst, matched := prefixFirst != m.pre.second }
  { m with pre, mbegin := begin }

/-- `regex_iterator::operator++` (regex.tcc 509). -/
def RIter.next (it : RIter) (nfa : NFA) (inp : Array Nat) (lim : Lim) (stats : Stats) :
    Except Abort (RIter × Stats) := do
  let m0 := it.m.get 0
  if !m0.matched then return (it, stats)
  let start := m0.second
  let prefixFirst := m0.second
  let mut start := start
  let mut stats := stats
  if m0.first == m0.second then
    if start == it.end_ then return ({ it with live := false }, stats)
    let fl := { it.flags with notNull := true, continuous := true }
    let (ok, m, st) ← search nfa inp start it.end_ fl lim stats
    stats := st
    if ok then return ({ it with m := fixPrefix m prefixFirst it.begin }, stats)
    start := start + 1
  let flags := { it.flags with prevAvail := true }
  let (ok, m, st) ← search nfa inp start it.end_ flags lim stats
  if ok then return ({ it with flags, m := fixPrefix m prefixFirst it.begin }, st)
  else return ({ it with flags, m, live := false }, st)

/-- Every match an iterator yields from `[a, b)`, at most `lim.iters` (`none`: more than that). -/
def iterAll (nfa : NFA) (inp : Array Nat) (a b : Nat) (flags : Flags) (lim : Lim) :
    Except Abort (Option (List MatchRes) × Stats) := do
  let (it, stats) ← RIter.init nfa inp a b flags lim {}
  let rec go : Nat → RIter → List MatchRes → Stats → Except Abort (Option (List MatchRes) × Stats)
    | 0, _, _, st => .ok (none, st)
    | k + 1, it, acc, st =>
      if !it.live then .ok (some acc.reverse, st)
      else match it.next nfa inp lim st with
        | .error e => .error e
        | .ok (it', st') => go k it' (it.m :: acc) st'
  go (lim.iters + 1) it [] stats

def isDigitC (c : Nat) : Bool := 0x30 ≤ c && c ≤ 0x39

/-- `match_results::format` (regex.tcc 380), ECMAScript rules. -/
def format (m : MatchRes) (inp : Array Nat) (fmt : List Nat) : List Nat :=
  let output (idx : Nat) : List Nat := (m.get idx).str inp
  let copyIf (s : Sub) : List Nat := if s.matched then (inp.extract s.first s.second).toList else []
  let rec go : Nat → List Nat → List Nat
    | 0, rest => rest
    | f + 1, rest =>
      match rest.span (· != 0x24) with
      | (pre, []) => pre
      | (pre, _ :: after) =>
        -- `++__next == __fmt_last`
        match after with
        | [] => pre ++ [0x24]
        | c :: more =>
          if c == 0x24 then pre ++ [0x24] ++ go f more
          else if c == 0x26 then pre ++ output 0 ++ go f more
          else if c == 0x60 then pre ++ copyIf m.prefix ++ go f more
          else if c == 0x27 then pre ++ copyIf m.suffix ++ go f more
          else if isDigitC c then
            let (num, more) := match more with
              | d :: more' => if isDigitC d then ((c - 0x30) * 10 + (d - 0x30), more') else (c - 0x30, more)
              | [] => (c - 0x30, more)
            pre ++ (if num < m.size then output num else []) ++ go f more
          else pre ++ [0x24] ++ go f (c :: more)
  go (fmt.length + 1) fmt

/-- `__regex_replace` (regex.tcc 466) over `[a, b)`; `firstOnly` is `format_first_only`. -/
def regexReplace (nfa : NFA) (inp : Array Nat) (a b : Nat) (fmt : List Nat) (firstOnly : Bool)
    (lim : Lim) : Except Abort (Option (List Nat) × Stats) := do
  let (it, stats) ← RIter.init nfa inp a b {} lim {}
  if !it.live then return (some (inp.extract a b).toList, stats)
  let rec go : Nat → RIter → List Nat → Stats → Except Abort (Option (List Nat) × Stats)
    | 0, _, _, st => .ok (none, st)
    | k + 1, it, out, st =>
      let pre := it.m.prefix
      let out := out ++ (inp.extract pre.first pre.second).toList ++ format it.m inp fmt
      let suf := it.m.suffix
      if firstOnly then .ok (some (out ++ (inp.extract suf.first suf.second).toList), st)
      else match it.next nfa inp lim st with
        | .error e => .error e
        | .ok (it', st') =>
          if !it'.live then .ok (some (out ++ (inp.extract suf.first suf.second).toList), st')
          else go k it' out st'
  go (lim.iters + 1) it [] stats

end Jank.R3.Regex
