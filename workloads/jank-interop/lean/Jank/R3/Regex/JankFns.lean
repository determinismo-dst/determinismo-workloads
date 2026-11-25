import Jank.R3.Regex.Algo

/-!
# jank's regex functions on the replica (7135b7708)

- `re-pattern` (core.jank 6352 → core.cpp `re_pattern` 929 → re_pattern.cpp 6–10:
  `std::regex{ s.c_str(), ECMAScript }`); `#"…"` (parse.cpp `parse_regex` 888: the raw text
  between the quotes, `parse_string` does not unescape; a `std::exception` becomes a read
  error).
- `re-matcher` (core.cpp 938: `match_input{ s.c_str() }`, cut at the first NUL),
  `re-find` (core.jank 6378 → core.cpp `re_find` 972: `regex_search(match_input)`, groups
  through `smatch_to_vector` 945, then `match_input = suffix().str()`), `re-groups` (990),
  `re-seq` (core.jank 6388: `re_find` on one matcher until nil), `re-matches` (1002:
  `regex_search(s.c_str(), …, match_continuous)`, nil unless the suffix is empty).
- clojure.string (string.jank 19/99/166/175 → string_native.cpp): `replace` with a pattern and a
  string (218: `regex_replace(s.c_str(), re, replacement.c_str())`), with a function (226:
  `sregex_iterator` over `s.c_str()`; the function gets the match string; no match returns the
  original `s`), `replace-first` with a string (78: `regex_replace(s.c_str(), …,
  format_first_only)`, the result cut at NUL again) or a function (89: `regex_search` over
  `s.c_str()`, the function gets `smatch_to_vector`, the text around comes from the original
  `s`), `split` (393: `cregex_iterator` over all of `s`'s bytes, NULs included) and
  `split-lines` (`split s #"\r?\n" 0`).

Strings are their bytes (`List Nat`).
-/

namespace Jank.R3.Regex

/-- A value a call returns, compared across jank and Clojure. -/
inductive V where
  | nil
  | str (b : List Nat)
  /-- `re-groups` with groups: the match then each group (`none`: Clojure's nil). -/
  | vec (xs : List (Option (List Nat)))
  /-- A seq (re-seq) or a vector of strings (split). -/
  | list (xs : List V)
  /-- A seq that never ends: its first elements. -/
  | infinite (xs : List V)
  /-- An exception (its message). -/
  | err (what : String)
  /-- The model's limits were reached (`_M_dfs` calls or depth): no value claimed. -/
  | abort (why : String)
  deriving BEq, Repr, Inhabited

def cstr (s : List Nat) : List Nat := s.takeWhile (· != 0)

def abortV : Abort → V
  | .depth => .abort "depth"
  | .steps => .abort "steps"

/-- core.cpp `smatch_to_vector` (945): size 0 → nil, 1 → the match, else every sub-match's
`str()` (an unmatched one is ""). -/
def smatchToVector (inp : Array Nat) (m : MatchRes) : V :=
  if m.size == 0 then .nil
  else if m.size == 1 then .str ((m.get 0).str inp)
  else .vec (m.subs.toList.map fun s => some (s.str inp))

/-- `(re-pattern s)` / `#"s"`. -/
def jRePattern (loc : Loc) (s : List Nat) : Except RxErr NFA := compile loc s

/-- A `re_matcher`: the current `match_input` and `groups`. -/
structure JMatcher where
  input : List Nat
  groups : V := .nil

/-- core.cpp `re_find` (972). -/
def jReFindM (nfa : NFA) (m : JMatcher) (lim : Lim) : Except Abort (V × JMatcher × Stats) := do
  let inp := m.input.toArray
  let (_, mr, st) ← search nfa inp 0 inp.size {} lim {}
  let g := smatchToVector inp mr
  let input := if !mr.empty then mr.suffix.str inp else m.input
  return (g, { input, groups := g }, st)

/-- `(re-find re s)`. -/
def jReFind (nfa : NFA) (s : List Nat) (lim : Lim := {}) : V :=
  match jReFindM nfa { input := cstr s } lim with
  | .ok (v, _, _) => v
  | .error a => abortV a

/-- `(re-seq re s)`: `re_find` until nil. A match that leaves `match_input` as it was repeats
forever (the walk is deterministic). -/
def jReSeq (nfa : NFA) (s : List Nat) (lim : Lim := {}) : V :=
  let rec go : Nat → JMatcher → List V → V
    | 0, _, acc => .infinite acc.reverse
    | k + 1, m, acc =>
      match jReFindM nfa m lim with
      | .error a => abortV a
      | .ok (.nil, _, _) => if acc.isEmpty then .nil else .list acc.reverse
      | .ok (g, m', _) =>
        if m'.input == m.input then .infinite (g :: g :: acc).reverse
        else go k m' (g :: acc)
  go (lim.iters + 1) { input := cstr s } []

/-- `(re-matches re s)`: core.cpp `re_matches` (1002). -/
def jReMatches (nfa : NFA) (s : List Nat) (lim : Lim := {}) : V :=
  let inp := (cstr s).toArray
  match search nfa inp 0 inp.size { continuous := true } lim {} with
  | .error a => abortV a
  | .ok (_, mr, _) =>
    if !(mr.suffix.str inp).isEmpty then .nil else smatchToVector inp mr

/-- `(clojure.string/replace s re replacement-string)`: string_native.cpp 218. -/
def jReplaceStr (nfa : NFA) (s rep : List Nat) (lim : Lim := {}) : V :=
  let inp := (cstr s).toArray
  match regexReplace nfa inp 0 inp.size (cstr rep) false lim with
  | .error a => abortV a
  | .ok (none, _) => .abort "iterations"
  | .ok (some out, _) => .str out

/-- `(clojure.string/replace s re f)`: string_native.cpp 226; `f` gets the match string. -/
def jReplaceFn (nfa : NFA) (s : List Nat) (f : V → V) (lim : Lim := {}) : V :=
  let inp := (cstr s).toArray
  match iterAll nfa inp 0 inp.size {} lim with
  | .error a => abortV a
  | .ok (none, _) => .abort "iterations"
  | .ok (some [], _) => .str s
  | .ok (some ms, _) =>
    let rec go : List MatchRes → List Nat → V
      | [], out => .str out
      | m :: rest, out =>
        match f (.str ((m.get 0).str inp)) with
        | .str r =>
          let out := out ++ m.prefix.str inp ++ r
          if rest.isEmpty then .str (out ++ m.suffix.str inp) else go rest out
        | .err e => .err e
        | _ => .err "not a string"
    go ms []

/-- `(clojure.string/replace-first s re replacement-string)`: string_native.cpp 78. -/
def jReplaceFirstStr (nfa : NFA) (s rep : List Nat) (lim : Lim := {}) : V :=
  let inp := (cstr s).toArray
  match regexReplace nfa inp 0 inp.size (cstr rep) true lim with
  | .error a => abortV a
  | .ok (none, _) => .abort "iterations"
  | .ok (some out, _) => .str (cstr out)

/-- `(clojure.string/replace-first s re f)`: string_native.cpp 89; `f` gets
`smatch_to_vector`. -/
def jReplaceFirstFn (nfa : NFA) (s : List Nat) (f : V → V) (lim : Lim := {}) : V :=
  let inp := (cstr s).toArray
  match search nfa inp 0 inp.size {} lim {} with
  | .error a => abortV a
  | .ok (_, mr, _) =>
    if mr.empty then .str s
    else
      let i := (mr.get 0).first - mr.mbegin
      match f (smatchToVector inp mr) with
      | .str r =>
        let restI := i + ((mr.get 0).str inp).length
        .str (s.take i ++ r ++ (if restI < s.length then s.drop restI else []))
      | .err e => .err e
      | _ => .err "not a string"

/-- `(clojure.string/split s re limit)`: string_native.cpp `split` (393). -/
def jSplit (nfa : NFA) (s : List Nat) (limit : Int) (lim : Lim := {}) : V :=
  if s.isEmpty || limit == 1 then .list [.str s] else
  let inp := s.toArray
  match iterAll nfa inp 0 inp.size {} lim with
  | .error a => abortV a
  | .ok (none, _) => .abort "iterations"
  | .ok (some ms, _) =>
    -- "Ignore leading empty strings just like Java"
    let ms := match ms with
      | m :: rest => if (m.get 0).first == (m.get 0).second && (m.get 0).first == 0 then rest else ms
      | [] => []
    let ms := if limit > 0 then ms.take (limit - 1).toNat else ms
    let (parts, prev) := ms.foldl (fun (acc, prev) m =>
      (acc ++ [(inp.extract prev (m.get 0).first).toList], (m.get 0).second)) ([], 0)
    let parts := parts ++ [(inp.extract prev inp.size).toList]
    let parts := if limit == 0 then (parts.reverse.dropWhile (·.isEmpty)).reverse else parts
    .list (parts.map .str)

end Jank.R3.Regex
