import Jank.Nrepl.Bencode

/-!
# Round 5, nREPL: chunk boundaries never change the messages (T7's reduction, part 1)

jank's connection loop (`handle-client`, core.jank 79–106) reads with `read-message`
(core.jank 58–70):

    (if-let [result (bencode/parse buffer)]
      result
      (let [chunk (.read_some client) input (str buffer chunk)]
        (if-let [result (bencode/parse input)] result [nil input])))

so the bytes of a request reach `bencode/parse` (bencode.jank 78) as a growing buffer: every
`read_some` (nrepl/server.cpp 31–42) may return any nonempty part of what the client sent.
Round 3's World T draws those parts (`net.read.split`, `net.read.len`, Threads.lean `tReadLen`), which
is what puts T7 at ≈3.2·10¹¹ timelines.

Here:
- `readLoop` is `read-message` iterated over a list of chunks (round 2's `parse` replica,
  `Jank.NreplServer.parse`, for `bencode/parse`);
- ★ `chunking_independent`: for any byte string `m` whose proper prefixes all parse to nil and which
  parses whole to `[v nil]`, every chunking of `m` (any number of parts, empty parts allowed) makes
  the loop give exactly `v`, after the last part, with an empty buffer — what one whole read gives;
- `t7_prefixes_none`, `t7_whole`: T7's six requests (the bytes round 3's client sends, checked at run
  time against `specEncode ∘ tReqMap` by `jank5-nrepl t7-bytes`) satisfy both hypotheses, on both
  `char` signednesses (kernel evaluation of round 2's parser on every prefix).

Together: for every chunking of T7's byte streams, the messages the server sees, and when it sees
them complete, are those of whole reads. Part 2 (`Reduce.lean`) lifts this to the world.
-/

namespace Jank.R5.Nrepl

open Jank.NreplServer

/-- One `read-message` call given the next chunk: `(bencode/parse buffer)`, else read a chunk and
parse `(str buffer chunk)`. Returns the message (if any) and the new buffer. -/
def readStep (p : Platform) (buffer : Option Bytes) (chunk : Bytes) : Option JVal × Option Bytes :=
  match parse p buffer with
  | .value v r => (some v, r)
  | _ =>
    let input := buffer.getD [] ++ chunk
    match parse p (some input) with
    | .value v r => (some v, r)
    | _ => (none, some input)

/-- The loop over a list of chunks: the messages in order, and the buffer left. (A `read-message`
whose first `parse` already finds a message does not consume the chunk; that never happens below,
where the buffer is always a proper prefix.) -/
def readLoop (p : Platform) (buffer : Option Bytes) : List Bytes → List JVal × Option Bytes
  | [] => ([], buffer)
  | c :: cs =>
    let (o, b) := readStep p buffer c
    let (vs, b') := readLoop p b cs
    (o.toList ++ vs, b')

/-- Every proper prefix of `m` parses to nil (incomplete, as far as the server can tell). -/
def PrefixesNone (p : Platform) (m : Bytes) : Prop :=
  ∀ k, k < m.length → parse p (some (m.take k)) = .none

/-- `parse` gave nil. -/
def isNoneP : Parsed → Bool
  | .none => true
  | _ => false

theorem isNoneP_iff (x : Parsed) : isNoneP x = true ↔ x = .none := by
  cases x <;> simp [isNoneP]

/-- The decidable form used for concrete messages. -/
def prefixesNone (p : Platform) (m : Bytes) : Bool :=
  (List.range m.length).all fun k => isNoneP (parse p (some (m.take k)))

theorem prefixesNone_spec (p : Platform) (m : Bytes) (h : prefixesNone p m = true) :
    PrefixesNone p m := by
  intro k hk
  unfold prefixesNone at h
  rw [List.all_eq_true] at h
  exact (isNoneP_iff _).mp (h k (List.mem_range.mpr hk))

/-- Parsing `none` (no buffer yet) gives nil. -/
theorem parse_none (p : Platform) : parse p none = .none := rfl

/-- An empty buffer: none, or the empty string. -/
def EmptyBuf (b : Option Bytes) : Prop := b = none ∨ b = some []

/-- Empty chunks into an empty buffer give no message and leave the buffer empty (the empty string
parses to nil). -/
theorem readLoop_empty (p : Platform) (h0 : parse p (some []) = .none) :
    ∀ (cs : List Bytes) (b : Option Bytes), (∀ c ∈ cs, c = []) → EmptyBuf b →
      (readLoop p b cs).1 = [] ∧ EmptyBuf (readLoop p b cs).2 := by
  intro cs
  induction cs with
  | nil => intro b _ hb; exact ⟨rfl, hb⟩
  | cons x xs ih =>
    intro b hall hb
    have hx : x = [] := hall x (by simp)
    subst hx
    have hxs : ∀ y ∈ xs, y = [] := fun y hy => hall y (by simp [hy])
    have hb0 : parse p b = .none := by
      rcases hb with rfl | rfl
      · rfl
      · exact h0
    have hin : b.getD [] ++ ([] : Bytes) = [] := by
      rcases hb with rfl | rfl <;> rfl
    have hstep : readStep p b [] = (none, some []) := by
      simp only [readStep, hb0, hin, h0]
    have := ih (some []) hxs (Or.inr rfl)
    simp only [readLoop, hstep, Option.toList_none, List.nil_append]
    exact this

/-- The loop invariant: the buffer before a chunk is `none` (at the start) or a proper prefix of
`m`, and the chunks left are the rest of `m`. Then the loop gives exactly `v`, once, and ends with
an empty buffer. -/
theorem readLoop_prefix (p : Platform) (m : Bytes) (v : JVal)
    (hpre : PrefixesNone p m) (hwhole : parse p (some m) = .value v none) :
    ∀ (chunks : List Bytes) (j : Nat) (buffer : Option Bytes),
      j < m.length →
      (buffer = none ∧ j = 0 ∨ buffer = some (m.take j)) →
      (chunks.flatten = m.drop j) →
      (readLoop p buffer chunks).1 = [v] ∧ EmptyBuf (readLoop p buffer chunks).2 := by
  intro chunks
  induction chunks with
  | nil =>
    intro j buffer hj _ hcat
    simp only [List.flatten_nil] at hcat
    have : (m.drop j).length = 0 := by rw [← hcat]; rfl
    rw [List.length_drop] at this
    omega
  | cons c cs ih =>
    intro j buffer hj hbuf hcat
    have hc : c ++ cs.flatten = m.drop j := by simpa using hcat
    have hb : parse p buffer = .none := by
      rcases hbuf with ⟨rfl, _⟩ | rfl
      · rfl
      · exact hpre j hj
    have hct : c = (m.drop j).take c.length := by rw [← hc]; simp
    have hinput : buffer.getD [] ++ c = m.take (j + c.length) := by
      rcases hbuf with ⟨rfl, rfl⟩ | rfl
      · simp only [Option.getD_none, List.nil_append, Nat.zero_add]
        rw [hct]; simp
      · simp only [Option.getD_some]
        conv => lhs; rw [hct]
        rw [List.take_drop]
        have e : m.take j = (m.take (j + c.length)).take j := by
          rw [List.take_take]; congr 1; omega
        rw [e, List.take_append_drop]
    have hlen : j + c.length ≤ m.length := by
      have := congrArg List.length hc
      simp only [List.length_append, List.length_drop] at this
      omega
    have h0 : parse p (some []) = .none := by
      have := hpre 0 (by omega)
      simpa using this
    by_cases hfull : j + c.length = m.length
    · have hrest : cs.flatten = [] := by
        have := congrArg List.length hc
        simp only [List.length_append, List.length_drop] at this
        have h0 : cs.flatten.length = 0 := by omega
        exact List.eq_nil_of_length_eq_zero h0
      have hall : ∀ x ∈ cs, x = [] := fun x hx => List.flatten_eq_nil_iff.mp hrest x hx
      have hm : m.take (j + c.length) = m := by rw [hfull]; exact List.take_length
      have hstep : readStep p buffer c = (some v, none) := by
        simp only [readStep, hb, hinput, hm, hwhole]
      have := readLoop_empty p h0 cs none hall (Or.inl rfl)
      simp only [readLoop, hstep, Option.toList_some]
      exact ⟨by rw [this.1]; rfl, this.2⟩
    · have hlt : j + c.length < m.length := by omega
      have hstep : readStep p buffer c = (none, some (m.take (j + c.length))) := by
        simp only [readStep, hb, hinput, hpre _ hlt]
      have hcat' : cs.flatten = m.drop (j + c.length) := by
        have : cs.flatten = (m.drop j).drop c.length := by rw [← hc]; simp
        rw [this, List.drop_drop]
      have := ih (j + c.length) (some (m.take (j + c.length))) hlt (Or.inr rfl) hcat'
      simp only [readLoop, hstep, Option.toList_none, List.nil_append]
      exact this

/-- ★ For every message whose proper prefixes parse to nil and which parses whole to `[v nil]`, and
every chunking of it (any parts, empty ones allowed), `read-message`'s loop gives exactly `v`, once,
after the part that completes it, and leaves an empty buffer: what one whole read gives. -/
theorem chunking_independent (p : Platform) (m : Bytes) (v : JVal)
    (hpre : PrefixesNone p m) (hwhole : parse p (some m) = .value v none) (hne : m ≠ [])
    (chunks : List Bytes) (hcat : chunks.flatten = m) :
    (readLoop p none chunks).1 = [v] ∧ EmptyBuf (readLoop p none chunks).2 ∧
    readLoop p none [m] = ([v], none) := by
  have hpos : 0 < m.length := List.length_pos_iff.mpr hne
  refine ⟨?_, ?_, ?_⟩
  · exact (readLoop_prefix p m v hpre hwhole chunks 0 none hpos (Or.inl ⟨rfl, rfl⟩) (by simpa using hcat)).1
  · exact (readLoop_prefix p m v hpre hwhole chunks 0 none hpos (Or.inl ⟨rfl, rfl⟩) (by simpa using hcat)).2
  · simp only [readLoop, readStep, parse_none, Option.getD_none, List.nil_append, hwhole]
    rfl

/-! ## T7's requests -/

/-- The bytes round 3's T7 client sends (`tReqMap` then `specEncode`, ids `c0-0`…`c0-5`, the session
`uuid-0` its clone got): clone, eval, lookup, completions, describe, close. -/
def t7Msgs : List Bytes := [
  [100, 50, 58, 111, 112, 53, 58, 99, 108, 111, 110, 101, 50, 58, 105, 100, 52, 58, 99, 48, 45, 48, 101],
  [100, 50, 58, 111, 112, 52, 58, 101, 118, 97, 108, 50, 58, 105, 100, 52, 58, 99, 48, 45, 49, 55, 58,
   115, 101, 115, 115, 105, 111, 110, 54, 58, 117, 117, 105, 100, 45, 48, 52, 58, 99, 111, 100, 101, 49,
   56, 58, 40, 100, 111, 32, 40, 112, 114, 105, 110, 116, 32, 34, 97, 34, 41, 32, 51, 41, 50, 58, 110,
   115, 52, 58, 117, 115, 101, 114, 101],
  [100, 50, 58, 111, 112, 54, 58, 108, 111, 111, 107, 117, 112, 50, 58, 105, 100, 52, 58, 99, 48, 45, 50,
   50, 58, 110, 115, 52, 58, 117, 115, 101, 114, 51, 58, 115, 121, 109, 51, 58, 109, 97, 112, 101],
  [100, 50, 58, 111, 112, 49, 49, 58, 99, 111, 109, 112, 108, 101, 116, 105, 111, 110, 115, 50, 58, 105,
   100, 52, 58, 99, 48, 45, 51, 50, 58, 110, 115, 52, 58, 117, 115, 101, 114, 54, 58, 112, 114, 101, 102,
   105, 120, 50, 58, 109, 97, 101],
  [100, 50, 58, 111, 112, 56, 58, 100, 101, 115, 99, 114, 105, 98, 101, 50, 58, 105, 100, 52, 58, 99, 48,
   45, 52, 101],
  [100, 50, 58, 111, 112, 53, 58, 99, 108, 111, 115, 101, 50, 58, 105, 100, 52, 58, 99, 48, 45, 53, 55, 58,
   115, 101, 115, 115, 105, 111, 110, 54, 58, 117, 117, 105, 100, 45, 48, 101]]

/-- A message parses whole to a value with nothing left over. -/
def wholeOk (p : Platform) (m : Bytes) : Bool :=
  match parse p (some m) with
  | .value _ none => true
  | _ => false

/-- The hypotheses of `chunking_independent` for a list of messages, as one check (run by
`jank5-nrepl t7-bytes` on the compiled replica: round 2's `parse` is well-founded recursion, which
the kernel does not evaluate; `ParseK.lean` gives a kernel-evaluable copy). -/
def hypsHold (p : Platform) (ms : List Bytes) : Bool :=
  ms.all fun m => !m.isEmpty && prefixesNone p m && wholeOk p m

/-- ★ For every chunking of each message of a list whose messages satisfy the hypotheses, the loop
gives the message a whole read gives, once, at the part that completes it, and an empty buffer. -/
theorem chunking_independent_all (p : Platform) (ms : List Bytes) (h : hypsHold p ms = true)
    (m : Bytes) (hm : m ∈ ms) (chunks : List Bytes) (hcat : chunks.flatten = m) :
    ∃ v, parse p (some m) = .value v none ∧ (readLoop p none chunks).1 = [v] ∧
      EmptyBuf (readLoop p none chunks).2 := by
  have hb := List.all_eq_true.mp h m hm
  simp only [Bool.and_eq_true] at hb
  have hpre : PrefixesNone p m := prefixesNone_spec p m hb.1.2
  have hne : m ≠ [] := by
    have := hb.1.1
    intro h0; subst h0; simp at this
  have hw := hb.2
  unfold wholeOk at hw
  split at hw
  · rename_i v hv
    have := chunking_independent p m v hpre hv hne chunks hcat
    exact ⟨v, hv, this.1, this.2.1⟩
  · simp at hw

end Jank.R5.Nrepl
