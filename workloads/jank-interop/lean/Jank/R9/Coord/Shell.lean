/-!
# Round 9, coordinator: jank.shell's arguments (U88)

jank.shell's `sh` (upstream-r5/compiler+runtime/src/jank/jank/shell.jank 82-110) wraps each string
in double quotes with its own quotes backslashed (`shell-escape`, 82-83), joins them with spaces, and
hands the one string to `boost::process::v1::child`. boost splits it back with `build_args`
(deps/boost-process/include/boost/process/v1/detail/posix/basic_cmd.hpp 54-97): a `"` toggles a
quoted state (an escaped `\"` toggles it too), an unquoted space ends an entry, and each entry loses
one pair of outer quotes and has every `\"` replaced by `"` (`make_entry`). Clojure's `sh` gives the
strings to `Runtime.exec` as an argument array: each string is one argument, unchanged.

Proved here, for every list of arguments: when no argument contains `"`, boost's split gives the
arguments back exactly (`roundtrip_of_no_quote`). A `"` breaks it (`u88_echo`, the test's own
arguments). The fix U88 passes the strings as an argument vector, so the child's argv is the list
itself.
-/

namespace Jank.R9.Coord.Shell

/-- shell-escape: `(str "\"" (str/escape s {\" "\\\""}) "\"")`. -/
def escape (s : List Char) : List Char :=
  '"' :: (s.flatMap (fun c => if c = '"' then ['\\', '"'] else [c]) ++ ['"'])

/-- `(str/join " " xs)`. -/
def joinSp : List (List Char) → List Char
  | [] => []
  | [a] => a
  | a :: b :: rest => a ++ ' ' :: joinSp (b :: rest)

/-- `boost::replace_all(data, "\\\"", "\"")`: left to right, without overlaps. -/
def unescape : List Char → List Char
  | [] => []
  | [c] => [c]
  | c :: d :: rest => if c = '\\' ∧ d = '"' then '"' :: unescape rest else c :: unescape (d :: rest)
termination_by l => l.length

/-- `make_entry` (basic_cmd.hpp 61-71): one pair of outer quotes is stripped when the entry starts and
ends with `"` (an entry that is a lone `"` is undefined behaviour in C++, `assign(begin+1, end-1)`;
it is modelled as empty), then `replace_all`. -/
def makeEntry (d : List Char) : List Char :=
  if d.head? = some '"' ∧ d.getLast? = some '"' then unescape (d.drop 1).dropLast else unescape d

/-- The loop's state: the quote state, the previous character, the current entry (reversed) and the
entries so far (reversed). -/
structure St where
  inQ : Bool
  prev : Option Char
  part : List Char
  acc : List (List Char)
deriving DecidableEq, Repr

def St.init : St := ⟨false, none, [], []⟩

/-- One iteration of build_args' loop (basic_cmd.hpp 79-91). An unquoted space ends the entry; it is
pushed unless the space is the first character or follows a space. -/
def step (st : St) (c : Char) : St :=
  let inQ := if c = '"' then !st.inQ else st.inQ
  if inQ = false ∧ c = ' ' then
    let acc := if st.prev.isSome ∧ st.prev ≠ some ' ' then makeEntry st.part.reverse :: st.acc
      else st.acc
    ⟨inQ, some c, [], acc⟩
  else
    ⟨inQ, some c, c :: st.part, st.acc⟩

/-- build_args: the loop, then the last entry when it isn't empty (93-94). -/
def buildArgs (d : List Char) : List (List Char) :=
  let st := d.foldl step St.init
  (if st.part ≠ [] then makeEntry st.part.reverse :: st.acc else st.acc).reverse

/-- The child's argv on stock jank, from `(sh a b ...)`. -/
def stockArgv (args : List (List Char)) : List (List Char) :=
  buildArgs (joinSp (args.map escape))

/-! ## Lemmas -/

theorem flatMap_no_quote (s : List Char) (h : '"' ∉ s) :
    s.flatMap (fun c => if c = '"' then ['\\', '"'] else [c]) = s := by
  induction s with
  | nil => rfl
  | cons c t ih =>
    have hc : c ≠ '"' := fun e => h (e ▸ List.mem_cons_self ..)
    have ht : '"' ∉ t := fun m => h (List.mem_cons_of_mem _ m)
    simp [List.flatMap_cons, hc, ih ht]

theorem escape_no_quote (s : List Char) (h : '"' ∉ s) : escape s = '"' :: (s ++ ['"']) := by
  simp [escape, flatMap_no_quote s h]

theorem unescape_no_quote : ∀ (s : List Char), '"' ∉ s → unescape s = s
  | [], _ => by simp [unescape]
  | [c], _ => by simp [unescape]
  | c :: d :: rest, h => by
    have ht : '"' ∉ d :: rest := fun m => h (List.mem_cons_of_mem _ m)
    have hd : d ≠ '"' := fun e => ht (e ▸ List.mem_cons_self ..)
    rw [unescape]
    simp only [hd, and_false, ite_false]
    rw [unescape_no_quote (d :: rest) ht]
termination_by s => s.length

theorem makeEntry_escape (s : List Char) (h : '"' ∉ s) : makeEntry (escape s) = s := by
  rw [escape_no_quote s h, makeEntry]
  have hl : ('"' :: (s ++ ['"'])).getLast? = some '"' := by
    rw [← List.cons_append, List.getLast?_concat]
  simp only [List.head?_cons, hl, and_self, ite_true, List.drop_succ_cons, List.drop_zero]
  rw [List.dropLast_concat, unescape_no_quote s h]

/-- Inside quotes, characters other than `"` only accumulate. -/
theorem fold_quoted (s : List Char) (h : '"' ∉ s) (p : Option Char) (part : List Char)
    (acc : List (List Char)) :
    s.foldl step ⟨true, p, part, acc⟩ =
      ⟨true, (if s = [] then p else s.getLast?), s.reverse ++ part, acc⟩ := by
  induction s generalizing p part with
  | nil => simp
  | cons c t ih =>
    have hc : c ≠ '"' := fun e => h (e ▸ List.mem_cons_self ..)
    have ht : '"' ∉ t := fun m => h (List.mem_cons_of_mem _ m)
    have hs : step ⟨true, p, part, acc⟩ c = ⟨true, some c, c :: part, acc⟩ := by
      simp [step, hc]
    rw [List.foldl_cons, hs, ih ht]
    cases t with
    | nil => simp
    | cons d u => simp [List.getLast?_cons_cons]

/-- An escaped argument without quotes, read from an unquoted state with an empty entry. -/
theorem fold_escape (s : List Char) (h : '"' ∉ s) (p : Option Char) (acc : List (List Char)) :
    (escape s).foldl step ⟨false, p, [], acc⟩ = ⟨false, some '"', (escape s).reverse, acc⟩ := by
  rw [escape_no_quote s h, List.foldl_cons]
  have h1 : step ⟨false, p, [], acc⟩ '"' = ⟨true, some '"', ['"'], acc⟩ := by simp [step]
  rw [h1, List.foldl_append, fold_quoted s h]
  simp [step, List.reverse_append]

/-- The main loop over a joined list of escaped arguments. -/
theorem fold_join (args : List (List Char)) (h : ∀ a ∈ args, '"' ∉ a) (hne : args ≠ [])
    (p : Option Char) (acc : List (List Char)) :
    (joinSp (args.map escape)).foldl step ⟨false, p, [], acc⟩ =
      ⟨false, some '"', (escape (args.getLast hne)).reverse,
        ((args.dropLast).reverse ++ acc)⟩ := by
  induction args generalizing p acc with
  | nil => exact absurd rfl hne
  | cons a rest ih =>
    have ha : '"' ∉ a := h a (List.mem_cons_self ..)
    have hr : ∀ b ∈ rest, '"' ∉ b := fun b m => h b (List.mem_cons_of_mem _ m)
    cases rest with
    | nil =>
      simp only [List.map_cons, List.map_nil, joinSp]
      rw [fold_escape a ha]
      simp
    | cons b rest' =>
      simp only [List.map_cons, joinSp]
      rw [List.foldl_append, fold_escape a ha, List.foldl_cons]
      have hsp : step ⟨false, some '"', (escape a).reverse, acc⟩ ' ' =
          ⟨false, some ' ', [], a :: acc⟩ := by
        simp [step, List.reverse_reverse, makeEntry_escape a ha]
      rw [hsp]
      have := ih hr (List.cons_ne_nil _ _) (some ' ') (a :: acc)
      simp only [List.map_cons] at this
      rw [this]
      simp [List.dropLast_cons_of_ne_nil, List.getLast_cons]

/-- **U88, for every input.** When no argument contains `"`, boost's split gives the arguments back
exactly: stock jank's child gets Clojure's argv. -/
theorem roundtrip_of_no_quote (args : List (List Char)) (h : ∀ a ∈ args, '"' ∉ a) :
    stockArgv args = args := by
  by_cases hne : args = []
  · subst hne; simp [stockArgv, buildArgs, joinSp, St.init]
  · have hf := fold_join args h hne none []
    simp only [stockArgv, buildArgs, St.init, hf]
    have hlast : '"' ∉ args.getLast hne := h _ (List.getLast_mem hne)
    have hpart : (escape (args.getLast hne)).reverse ≠ [] := by simp [escape]
    simp only [ne_eq, hpart, not_false_eq_true, ite_true, List.reverse_reverse,
      makeEntry_escape _ hlast, List.append_nil, List.reverse_cons]
    exact List.dropLast_concat_getLast hne

/-- The real test's arguments: `(sh "echo" "a\" b")` gives echo the two arguments `a\` and `b"`,
so it prints `a\ b"` (the real jank's u88 output). -/
theorem u88_echo :
    stockArgv [['e', 'c', 'h', 'o'], ['a', '"', ' ', 'b']] =
      [['e', 'c', 'h', 'o'], ['a', '\\'], ['b', '"']] := by
  decide +kernel

/-- A `"` without a space survives (`a"b"c`); an odd number of `"` puts the next separator inside
quotes, so `a"` and `b` reach the child as one argument. -/
theorem quote_examples :
    stockArgv [['a', '"', 'b', '"', 'c']] = [['a', '"', 'b', '"', 'c']] ∧
    stockArgv [['a', '"'], ['b']] = [['a', '"', '"', ' ', '"', 'b']] := by
  decide +kernel

end Jank.R9.Coord.Shell
