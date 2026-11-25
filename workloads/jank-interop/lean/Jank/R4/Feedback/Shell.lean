/-!
# Round 4: `jank.shell/sh` (src/jank/jank/shell.jank) over boost.process v1

jank ships `jank.shell`, a port of `clojure.java.shell` (same header, authors and docstrings), whose
`sh` passes its strings to `boost::process::v1::child` (boost-process e4d0d405, jank's submodule;
`deps/boost-process/include/boost/process/v1/`). Two parts are replicated here.

**The command line.** shell.jank 98-103 joins the arguments with spaces after `shell-escape`
(shell.jank 78-79: wrap in `"`, each `"` becomes `\"` by `clojure.string/escape`), and
`child(std::string cmd, …)` is boost's *cmd style*: `exe_cmd_init::cmd` (detail/posix/basic_cmd.hpp
130-134) splits the string with `build_args` (55-100): a `"` toggles `in_quote` whether or not a
backslash precedes it, a space outside quotes ends an entry (an entry is pushed only when the
character before the space is not a space), and `make_entry` strips one pair of outer quotes and
replaces every `\"` by `"` (`boost::replace_all`). The executable is the first entry
(basic_cmd.hpp 115-121). Clojure's `sh` gives the strings to `Runtime.exec(String[])` unchanged
(clojure/java/shell.clj 113-116).

**The pipes.** shell.jank 52-73 writes `:in` to the child's stdin, closes it, then
`process.wait()`, and only then reads stdout and then stderr to their ends. boost closes the
parent's copies of the child's ends after the fork (detail/posix/pipe_out.hpp 51-54,
pipe_in.hpp 47-50). A pipe holds at most `cap` bytes (Linux: 65,536 by default); a writer blocks
while it is full. Clojure's `sh` (shell.clj 118-130) copies `:in` in a future, reads stderr in a
future and stdout on the calling thread, then `waitFor`s: nothing waits on a full pipe that nobody
drains.
-/

namespace Jank.R4.Feedback.Shell

/-! ## The command line -/

/-- shell.jank `shell-escape` (78-79): `(str "\"" (str/escape s {\" "\\\""}) "\"")`. -/
def shellEscape (s : List Char) : List Char :=
  '"' :: (s.flatMap fun c => if c = '"' then ['\\', '"'] else [c]) ++ ['"']

/-- `(str/join " " (map shell-escape cmd))` (shell.jank 99). -/
def joinCmd (args : List (List Char)) : List Char :=
  match args.map shellEscape with
  | [] => []
  | a :: rest => a ++ rest.flatMap (' ' :: ·)

/-- `boost::replace_all(data, "\\\"", "\"")`: every non-overlapping `\"`, left to right. -/
def replaceBsQuote : List Char → List Char
  | [] => []
  | [c] => [c]
  | c :: d :: r => if c = '\\' ∧ d = '"' then '"' :: replaceBsQuote r else c :: replaceBsQuote (d :: r)

/-- basic_cmd.hpp 62-73 `make_entry`: strip one pair of outer quotes, then `\"` → `"`. (A piece
that is a lone `"` makes `assign(begin+1, end-1)` an invalid range: flagged by `loneQuote`.) -/
def makeEntry (e : List Char) : List Char :=
  replaceBsQuote (match e with
    | '"' :: rest => if rest.getLast? = some '"' then rest.dropLast else e
    | _ => e)

/-- basic_cmd.hpp 55-100 `build_args`'s loop, iterator for iterator, collecting the raw pieces:
`part` the current piece (reversed), `q` `in_quote`, `prev` the character before. -/
def splitLoop : List Char → List Char → Bool → Option Char → List (List Char) → List (List Char)
  | [], part, _, _, st => if part.isEmpty then st.reverse else (part.reverse :: st).reverse
  | c :: rest, part, q, prev, st =>
    let q' := if c = '"' then !q else q
    if q' = false ∧ c = ' ' then
      let st' := if prev.isSome && prev != some ' ' then part.reverse :: st else st
      splitLoop rest [] q' (some c) st'
    else splitLoop rest (c :: part) q' (some c) st

def buildArgs (s : List Char) : List (List Char) := (splitLoop s [] false none []).map makeEntry

/-- The argv the child gets in jank. -/
def jankArgv (args : List (List Char)) : List (List Char) := buildArgs (joinCmd args)

/-- A piece that is a lone `"` (undefined behavior in `make_entry`). -/
def loneQuote (args : List (List Char)) : Bool := (splitLoop (joinCmd args) [] false none []).contains ['"']

/-- The argv the child gets in Clojure. -/
def cljArgv (args : List (List Char)) : List (List Char) := args

/-- `(sh "echo" "a\" b")`: the child gets `a\` and `b"` instead of `a" b`. -/
theorem quote_then_space_splits :
    jankArgv ["echo".toList, "a\" b".toList] = ["echo".toList, "a\\".toList, "b\"".toList] := by
  decide +kernel

/-- Balanced quotes come through: `(sh "echo" "fix \"x\" now")`. -/
theorem balanced_quotes_kept :
    jankArgv ["echo".toList, "fix \"x\" now".toList] = ["echo".toList, "fix \"x\" now".toList] := by
  decide +kernel

/-! ### For every argument list without `"`: the argv is the arguments -/

/-- The escaped form of an argument without `"`. -/
def wrap (a : List Char) : List Char := '"' :: (a ++ ['"'])

theorem flatMap_noquote (a : List Char) (h : '"' ∉ a) :
    (a.flatMap fun c => if c = '"' then ['\\', '"'] else [c]) = a := by
  induction a with
  | nil => rfl
  | cons x a ih =>
    have hx : x ≠ '"' := fun e => h (e ▸ List.mem_cons_self ..)
    have ha : '"' ∉ a := fun m => h (List.mem_cons_of_mem _ m)
    rw [List.flatMap_cons, if_neg hx, ih ha]; rfl

theorem shellEscape_noquote (a : List Char) (h : '"' ∉ a) : shellEscape a = wrap a := by
  simp only [shellEscape, wrap, flatMap_noquote a h, List.cons_append]

theorem replaceBsQuote_noquote (a : List Char) (h : '"' ∉ a) : replaceBsQuote a = a := by
  induction a with
  | nil => rfl
  | cons x a ih =>
    cases a with
    | nil => rfl
    | cons y b =>
      have hy : y ≠ '"' := fun e => h (e ▸ List.mem_cons_of_mem _ (List.mem_cons_self ..))
      have ha : '"' ∉ y :: b := fun m => h (List.mem_cons_of_mem _ m)
      have hn : ¬ (x = '\\' ∧ y = '"') := fun hh => hy hh.2
      simp only [replaceBsQuote, if_neg hn]
      rw [ih ha]

theorem makeEntry_wrap (a : List Char) (h : '"' ∉ a) : makeEntry (wrap a) = a := by
  have hl : (a ++ ['"']).getLast? = some '"' := by simp
  simp only [makeEntry, wrap, hl, if_true, List.dropLast_concat, replaceBsQuote_noquote a h]

/-- Inside quotes, a `"`-free run goes into the piece; the closing `"` ends the quote. -/
theorem loop_in_quote (a tail part : List Char) (prev : Option Char) (st : List (List Char))
    (h : '"' ∉ a) :
    splitLoop (a ++ '"' :: tail) part true prev st
      = splitLoop tail ('"' :: (a.reverse ++ part)) false (some '"') st := by
  induction a generalizing part prev with
  | nil => simp [splitLoop]
  | cons c a ih =>
    have hc : c ≠ '"' := fun e => h (e ▸ List.mem_cons_self ..)
    have ha : '"' ∉ a := fun m => h (List.mem_cons_of_mem _ m)
    rw [List.cons_append, splitLoop]
    simp only [if_neg hc, Bool.true_eq_false, false_and, if_false]
    rw [ih (c :: part) (some c) ha]
    simp

theorem reverse_piece (a : List Char) : ('"' :: (a.reverse ++ ['"'])).reverse = wrap a := by
  simp [wrap]

theorem loop_arg_sep (a tail : List Char) (prev : Option Char) (st : List (List Char))
    (h : '"' ∉ a) :
    splitLoop (wrap a ++ ' ' :: tail) [] false prev st
      = splitLoop tail [] false (some ' ') (wrap a :: st) := by
  have e : wrap a ++ ' ' :: tail = '"' :: (a ++ '"' :: ' ' :: tail) := by simp [wrap]
  rw [e, splitLoop]
  simp only [if_true, Bool.not_false, Bool.true_eq_false, false_and, if_false]
  rw [loop_in_quote a (' ' :: tail) ['"'] (some '"') st h, splitLoop]
  simp [reverse_piece, wrap]

theorem loop_last_arg (a : List Char) (prev : Option Char) (st : List (List Char))
    (h : '"' ∉ a) :
    splitLoop (wrap a) [] false prev st = (wrap a :: st).reverse := by
  have e : wrap a = '"' :: (a ++ '"' :: []) := by simp [wrap]
  rw [e, splitLoop]
  simp only [if_true, Bool.not_false, Bool.true_eq_false, false_and, if_false]
  rw [loop_in_quote a [] ['"'] (some '"') st h]
  simp [splitLoop, reverse_piece, wrap]

theorem loop_args (rest : List (List Char)) :
    ∀ (a : List Char) (prev : Option Char) (st : List (List Char)),
      '"' ∉ a → (∀ b ∈ rest, '"' ∉ b) →
      splitLoop (wrap a ++ rest.flatMap (fun b => ' ' :: wrap b)) [] false prev st
        = st.reverse ++ (a :: rest).map wrap := by
  induction rest with
  | nil => intro a prev st ha _; simp [loop_last_arg a prev st ha]
  | cons b rest ih =>
    intro a prev st ha hr
    have hb : '"' ∉ b := hr b (List.mem_cons_self ..)
    have hr' : ∀ c ∈ rest, '"' ∉ c := fun c m => hr c (List.mem_cons_of_mem _ m)
    rw [List.flatMap_cons, List.cons_append, loop_arg_sep a _ prev st ha,
      ih b (some ' ') (wrap a :: st) hb hr']
    simp

/-- ★ For every argument list in which no argument holds `"`, the child's argv is exactly the
arguments (as in Clojure), and no piece is a lone quote. -/
theorem jankArgv_noquote (args : List (List Char)) (h : ∀ a ∈ args, '"' ∉ a) :
    jankArgv args = args := by
  cases args with
  | nil => rfl
  | cons a rest =>
    have ha : '"' ∉ a := h a (List.mem_cons_self ..)
    have hr : ∀ b ∈ rest, '"' ∉ b := fun b m => h b (List.mem_cons_of_mem _ m)
    have hm : (rest.map shellEscape) = rest.map wrap := by
      apply List.map_congr_left; intro b m; exact shellEscape_noquote b (hr b m)
    have hj : joinCmd (a :: rest) = wrap a ++ rest.flatMap (fun b => ' ' :: wrap b) := by
      simp only [joinCmd, List.map_cons, shellEscape_noquote a ha, hm, List.flatMap_map]
    rw [jankArgv, buildArgs, hj, loop_args rest a none [] ha hr]
    simp only [List.reverse_nil, List.nil_append, List.map_map]
    rw [List.map_congr_left (g := id) (fun b m => by
      simp only [Function.comp, id]
      rcases List.mem_cons.mp m with e | m'
      · subst e; exact makeEntry_wrap _ ha
      · exact makeEntry_wrap _ (hr _ m'))]
    simp

/-! ## The pipes -/

/-- What the child does: `seq` writes `n` bytes to stdout and exits; `errOut` the same on stderr;
`cat` copies stdin to stdout byte by byte until stdin's end, then exits; `ignore` exits at once. -/
inductive Child where
  | seq (n : Nat)
  | errOut (n : Nat)
  | cat
  | ignore
  deriving Repr, BEq, DecidableEq, Hashable

/-- A pipe: bytes buffered, whether its write end is still open, whether its read end is open. -/
structure Pipe where
  buf : Nat := 0
  wOpen : Bool := true
  rOpen : Bool := true
  deriving Repr, BEq, DecidableEq, Hashable

/-- jank's parent (shell.jank 52-73): write `:in` (`left` bytes), close stdin, wait, read stdout
to its end, read stderr to its end. -/
inductive JPhase where
  | writeIn (left : Nat)
  | wait
  | readOut
  | readErr
  | done
  | sigpipe
  deriving Repr, BEq, DecidableEq, Hashable

structure St where
  inP : Pipe := {}
  outP : Pipe := {}
  errP : Pipe := {}
  /-- The child: bytes still to write (seq/errOut), or whether it is copying (cat); `none` exited. -/
  child : Option Child
  /-- Bytes the child has written so far (stdout + stderr) and the parent has read. -/
  written : Nat := 0
  readBack : Nat := 0
  deriving Repr, BEq, DecidableEq, Hashable

/-- A child's step, if it can make one: `none` when blocked or exited. A `cat` holding no byte
reads one (or exits at stdin's end); it then writes it (modeled as one step reading and writing,
blocked while stdout is full: `cat`'s buffer is the byte in hand). -/
def childStep (cap : Nat) (s : St) : Option St :=
  match s.child with
  | none => none
  | some (.seq 0) | some (.errOut 0) | some .ignore =>
    some { s with child := none, outP := { s.outP with wOpen := false }, errP := { s.errP with wOpen := false },
                  inP := { s.inP with rOpen := false } }
  | some (.seq (n+1)) =>
    if s.outP.buf < cap then some { s with child := some (.seq n), outP := { s.outP with buf := s.outP.buf + 1 }, written := s.written + 1 } else none
  | some (.errOut (n+1)) =>
    if s.errP.buf < cap then some { s with child := some (.errOut n), errP := { s.errP with buf := s.errP.buf + 1 }, written := s.written + 1 } else none
  | some .cat =>
    if s.inP.buf > 0 then
      if s.outP.buf < cap then
        some { s with inP := { s.inP with buf := s.inP.buf - 1 }, outP := { s.outP with buf := s.outP.buf + 1 }, written := s.written + 1 }
      else none
    else if !s.inP.wOpen then
      some { s with child := none, outP := { s.outP with wOpen := false }, errP := { s.errP with wOpen := false },
                    inP := { s.inP with rOpen := false } }
    else none

/-- jank's parent step. Writing to a pipe whose read end is closed raises SIGPIPE (`sigpipe`:
what happens next depends on the signal's disposition, which this model does not decide). -/
def jankStep (cap : Nat) : JPhase × St → Option (JPhase × St)
  | (.writeIn 0, s) => some (.wait, { s with inP := { s.inP with wOpen := false } })
  | (.writeIn (k+1), s) =>
    if !s.inP.rOpen then some (.sigpipe, s)
    else if s.inP.buf < cap then some (.writeIn k, { s with inP := { s.inP with buf := s.inP.buf + 1 } })
    else none
  | (.wait, s) => if s.child.isNone then some (.readOut, s) else none
  | (.readOut, s) =>
    if s.outP.buf > 0 then some (.readOut, { s with outP := { s.outP with buf := s.outP.buf - 1 }, readBack := s.readBack + 1 })
    else if !s.outP.wOpen then some (.readErr, s) else none
  | (.readErr, s) =>
    if s.errP.buf > 0 then some (.readErr, { s with errP := { s.errP with buf := s.errP.buf - 1 }, readBack := s.readBack + 1 })
    else if !s.errP.wOpen then some (.done, s) else none
  | (.done, _) | (.sigpipe, _) => none

/-- Every state jank's `sh` can reach (parent and child interleaved), breadth first, with a
bound on the number of states. -/
partial def jankReach (cap : Nat) (frontier : List (JPhase × St)) (seen : List (JPhase × St))
    (fuel : Nat) : List (JPhase × St) :=
  match fuel, frontier with
  | 0, _ => seen
  | _, [] => seen
  | f+1, x :: rest =>
    let nexts := ([jankStep cap x, (childStep cap x.2).map (x.1, ·)].filterMap id).filter (!seen.contains ·)
    jankReach cap (rest ++ nexts) (seen ++ nexts) f

/-- The outcomes of jank's `sh`: `done` with the bytes read back, `sigpipe`, or `hang` (a
reachable state where neither the parent nor the child can step and the parent is not done). -/
inductive Outcome where
  | done (bytes : Nat)
  | sigpipe
  | hang
  deriving Repr, BEq, DecidableEq

def jankOutcomes (cap : Nat) (c : Child) (inLen : Nat) : List Outcome :=
  let s0 : St := { child := some c }
  let all := jankReach cap [(.writeIn inLen, s0)] [(.writeIn inLen, s0)] 100000
  let ends := all.filter fun x => (jankStep cap x).isNone && (childStep cap x.2).isNone
  (ends.map fun (p, s) => match p with
    | .done => Outcome.done s.readBack
    | .sigpipe => .sigpipe
    | _ => .hang).eraseDups

/-- Clojure's `sh` (shell.clj 118-130): the stdin copy and the stderr read run in futures, stdout
is read on the calling thread, then `waitFor`: each of the four makes progress whenever its pipe
allows, so the only end is every pipe drained and the child exited. The outcome is the child's
total output (stdin bytes a child does not read are dropped: the future's IOException is never
dereferenced). -/
def cljOutcome (c : Child) (inLen : Nat) : Outcome :=
  match c with
  | .seq n | .errOut n => .done n
  | .cat => .done inLen
  | .ignore => .done 0

/-! ### For every pipe capacity: `seq` past it never returns in jank -/

/-- The states jank's `sh` reaches: the parent's and the child's steps, interleaved. -/
inductive Reach (cap : Nat) (x0 : JPhase × St) : JPhase × St → Prop where
  | base : Reach cap x0 x0
  | parent {x y} : Reach cap x0 x → jankStep cap x = some y → Reach cap x0 y
  | child {x s'} : Reach cap x0 x → childStep cap x.2 = some s' → Reach cap x0 (x.1, s')

def start (c : Child) (inLen : Nat) : JPhase × St := (.writeIn inLen, { child := some c })

/-- The invariant: the parent is at most waiting, nothing was read, and the child still owes
`m` bytes with `buf + m = n` and `buf ≤ cap`. -/
def SeqInv (cap n : Nat) (x : JPhase × St) : Prop :=
  (x.1 = .writeIn 0 ∨ x.1 = .wait) ∧ ∃ m, x.2.child = some (.seq m) ∧ x.2.outP.buf + m = n ∧ x.2.outP.buf ≤ cap

theorem seqInv_reach (cap n : Nat) (h : cap < n) :
    ∀ z, Reach cap (start (.seq n) 0) z → SeqInv cap n z := by
  intro z hr
  induction hr with
  | base => exact ⟨.inl rfl, n, rfl, by simp [start], by simp [start]⟩
  | @parent x y _ hs ih =>
    obtain ⟨hp, m, hc, hb, hcap⟩ := ih
    obtain ⟨p, s⟩ := x
    simp only at hp hc hb hcap
    rcases hp with hp | hp
    · subst hp; simp [jankStep] at hs; subst hs; exact ⟨.inr rfl, m, hc, hb, hcap⟩
    · subst hp; simp [jankStep, hc] at hs
  | @child x s' _ hs ih =>
    obtain ⟨hp, m, hc, hb, hcap⟩ := ih
    refine ⟨hp, ?_⟩
    cases m with
    | zero => omega
    | succ m =>
      simp only [childStep, hc] at hs
      split at hs
      · simp at hs; subst hs; exact ⟨m, rfl, by simp; omega, by simp; omega⟩
      · simp at hs

/-- For every capacity and every `n` past it, jank's `sh` with a child that prints `n` bytes and
reads nothing never returns: no reachable state has the parent done. -/
theorem seq_past_capacity_never_returns (cap n : Nat) (h : cap < n) :
    ∀ x, Reach cap (start (.seq n) 0) x → x.1 ≠ .done ∧ x.1 ≠ .sigpipe := by
  intro x hr
  obtain ⟨hp, _⟩ := seqInv_reach cap n h x hr
  rcases hp with hp | hp <;> simp [hp]

theorem childStep_seq_blocked (cap m : Nat) (s : St) (hc : s.child = some (.seq (m+1)))
    (hb : ¬ s.outP.buf < cap) : childStep cap s = none := by
  unfold childStep; rw [hc]; simp only []; simp [hb]

theorem childStep_seq_writes (cap m : Nat) (s : St) (hc : s.child = some (.seq (m+1)))
    (hb : s.outP.buf < cap) : childStep cap s =
      some { s with child := some (.seq m), outP := { s.outP with buf := s.outP.buf + 1 }, written := s.written + 1 } := by
  unfold childStep; rw [hc]; simp only []; simp [hb]

/-- …and it gets stuck: after `cap` bytes neither side can step. -/
theorem seq_past_capacity_stuck (cap n : Nat) (h : cap < n) :
    ∃ x, Reach cap (start (.seq n) 0) x ∧ jankStep cap x = none ∧ childStep cap x.2 = none := by
  have hw : Reach cap (start (.seq n) 0) (.wait, { inP := { wOpen := false }, child := some (.seq n) }) :=
    .parent .base (by simp [start, jankStep])
  have key : ∀ k, k ≤ cap → Reach cap (start (.seq n) 0)
      (.wait, { inP := { wOpen := false }, outP := { buf := k }, child := some (.seq (n - k)), written := k }) := by
    intro k
    induction k with
    | zero => intro _; simpa using hw
    | succ k ih =>
      intro hk
      have h1 := ih (by omega)
      have hn : n - k = (n - (k + 1)) + 1 := by omega
      let s0 : St := { inP := { wOpen := false }, outP := { buf := k }, child := some (.seq (n - k)), written := k }
      have hw := childStep_seq_writes cap (n - (k + 1)) s0 (by show some _ = some _; congr 2) (show k < cap by omega)
      have := Reach.child h1 hw
      simpa [s0] using this
  refine ⟨_, key cap (Nat.le_refl _), ?_, ?_⟩
  · simp [jankStep]
  · have hn : n - cap = (n - cap - 1) + 1 := by omega
    exact childStep_seq_blocked cap (n - cap - 1) _ (by show some _ = some _; congr 2) (by show ¬ cap < cap; omega)

end Jank.R4.Feedback.Shell
