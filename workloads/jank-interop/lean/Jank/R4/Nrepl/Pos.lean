/-!
# Round 4, nREPL: the `line`/`column` fields of an eval request

jank 7135b7708 (paths under `upstream-main/compiler+runtime/`):

- handler/eval.jank `:eval` (66–72): `(get msg "line" 1)`, `(get msg "column" 1)`; `:load-file`
  (74–80) the same → `do-eval` (22) → eval.jank `safe-eval` (4–16) builds
  `jank.read.source_position{0, line, col}` → evaluate.cpp `safe_eval` (733) →
  context_dynamic.cpp `eval_string(code, p)` (50–52): `read::lex::processor l_prc{ code, p }`.
- lex.cpp `processor(f, p)` (338–345): `pos.offset = p.offset; pos.line = p.line; pos.col =
  p.col`. `movable_position::operator++` (347–363): the byte at `offset` is `'\n'` → `col = 1`,
  `++line`; any other byte → `++col`. Positions count BYTES; only `'\n'` ends a line.
- A token's start position becomes the form's `source` (parse.cpp), and `source_to_meta`
  (core/meta.cpp 171–228) turns it into `{:jank/source {:file … :start {:offset :line :col} :end
  {…}}}`: the only place the request's line and column go. No `:line` or `:column` key is ever
  made (meta.cpp; processor.cpp and core.jank have none). The optimizer's `strip_source_meta`
  (analyze/pass/strip_source_meta.cpp 13–42) removes `:jank/source` from quoted literals, so
  `(meta '(a))` is nil; a `def`'s var keeps its name symbol's `{:jank/source …}` (evaluate.cpp
  333–337).

Clojure 1.12 (the spec; `clojure-ref/`), as nREPL's documented `eval` fields drive it ("line: the
line number in [file] at which [code] starts; column: the column number …"):

- the reader is a `LineNumberingPushbackReader` whose line is set to `line` and column to
  `column`. `read()` (LineNumberingPushbackReader.java 64–80): a line terminator (its
  `LineNumberReader` folds `"\r\n"`, `"\r"` and `"\n"` into one `'\n'`) sets the column to 1,
  anything else adds 1. Positions count UTF-16 code units.
- `ListReader` (LispReader.java 1236–1260) gives every non-empty list `{:line l :column c}`: the
  line, and the column of its `(`.
- `DefExpr.Parser` (Compiler.java 574) gives every `def`'d var `:line`, `:column` (the def form's)
  and `:file`.

This file replicates both counters, proves they agree on ASCII text without carriage returns,
and enumerates where they part.
-/

namespace Jank.R4.Nrepl.Pos

/-- A position: (line, column). -/
structure P where
  line : Nat
  col : Nat
  deriving Repr, BEq, DecidableEq, Inhabited

/-- `movable_position::operator++` (lex.cpp 347–363) on one byte. -/
def jankStep (p : P) (b : UInt8) : P :=
  if b == 10 then { line := p.line + 1, col := 1 } else { p with col := p.col + 1 }

/-- jank's position before each byte, from the request's (line, col). -/
def jankPos : P → List UInt8 → List P
  | _, [] => []
  | p, b :: bs => p :: jankPos (jankStep p b) bs

/-- Clojure's reader position before each character, the characters given as code points.
`LineNumberReader` folds `"\r\n"`, `"\r"` and `"\n"` into one terminator: a `'\n'` right after a
`'\r'` moves nothing. Every other character adds its UTF-16 length (2 above the BMP). -/
def cljPos : P → Bool → List Nat → List P
  | _, _, [] => []
  | p, prevCR, c :: cs =>
    p :: (if c == 10 && prevCR then cljPos p false cs
          else if c == 10 || c == 13 then cljPos { line := p.line + 1, col := 1 } (c == 13) cs
          else cljPos { p with col := p.col + (if c ≥ 0x10000 then 2 else 1) } false cs)

/-- Where each `(` of the code starts a list, as both sides number it: jank by byte offset,
Clojure by character. The census alphabet has no strings, comments or character literals, so every
`(` opens a list on both sides. -/
def listStarts (start : P) (code : String) : List (P × P) :=
  let cs := code.toList
  let cp := cljPos start false (cs.map Char.toNat)
  let offs := (cs.foldl (fun (acc : List Nat × Nat) c => (acc.1 ++ [acc.2], acc.2 + c.utf8Size)) ([], 0)).1
  let jp := jankPos start code.toUTF8.toList
  ((cs.zip (offs.zip cp)).filter (·.1 == '(')).map fun (_, (o, c)) => (jp.getD o default, c)

/-- What a program reads back for a list it quoted, `(meta '(…))`, by Clojure's keys
`[:line :column]`: jank nil (no such keys; the strip pass even removes `:jank/source`), Clojure
the list's position. -/
def jankLineMeta (_ : P) : Option P := none
def cljLineMeta (p : P) : Option P := some p

/-! ## Agreement on ASCII text without carriage returns -/

/-- For every start position and every byte string of ASCII bytes other than `'\r'`, jank's
position before each byte is Clojure's reader position before the same character. -/
theorem jankPos_eq_cljPos (p : P) (bs : List UInt8)
    (h : ∀ b ∈ bs, b.toNat < 128 ∧ b ≠ 13) :
    jankPos p bs = cljPos p false (bs.map UInt8.toNat) := by
  induction bs generalizing p with
  | nil => rfl
  | cons b bs ih =>
    have hb := h b (List.mem_cons_self ..)
    have ht : ∀ x ∈ bs, x.toNat < 128 ∧ x ≠ 13 := fun x hx => h x (List.mem_cons_of_mem _ hx)
    have hne : b.toNat ≠ 13 := by
      intro e; apply hb.2; exact UInt8.toNat_inj.mp (by simpa using e)
    simp only [jankPos, List.map, cljPos]
    congr 1
    by_cases h10 : b = 10
    · subst h10
      simp [jankStep, ih _ ht]
    · have hn : b.toNat ≠ 10 := by
        intro e; apply h10; exact UInt8.toNat_inj.mp (by simpa using e)
      have hlt : ¬ b.toNat ≥ 0x10000 := by omega
      simp [jankStep, h10, hn, hne, hlt, ih _ ht]

/-- Consequently a list's start agrees too (same text). Where they differ: a `'\r'` (a line on
Clojure, a column on jank) and a non-ASCII character before the `(` on the same line (bytes against
UTF-16 units). Neither is visible by Clojure's keys, since jank has no `:line`/`:column`. -/
theorem jank_has_no_line_meta (p : P) : jankLineMeta p ≠ cljLineMeta p := by
  simp [jankLineMeta, cljLineMeta]

end Jank.R4.Nrepl.Pos
