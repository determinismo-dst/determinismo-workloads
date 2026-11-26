import Jank.R9.Str.Units

/-! Round 9, area Str (W): W9u's index functions on canonical WTF-8, run on every text of at most
`n` atoms (default 3) over the harness's 14 atoms (ASCII, BMP letters, a combining mark,
U+E000/U+FFFF, three supplementary characters, lone surrogates). For each text it checks the
replica against Java's functions on the units: count, every nth, the hash loop, index-of and
last-index-of for 8 needles and every start, and every tail subs. The theorems of
`Jank.R9.Str.Units` prove these for every input; this run is their executable check. -/

open Jank.Str Jank.R9.Str

def atoms9 : List (List Nat) :=
  [[0x61], [0x2D], [0xE9], [0x20AC], [0x301], [0xFFFF], [0xE000], [0xD83D, 0xDE00],
   [0xD800, 0xDC00], [0xDBFF, 0xDFFF], [0xD83D], [0xDE00], [0xDBFF], [0xDC00]]

def needles9 : List (List Nat) :=
  [[], [0x61], [0xE9], [0xD83D], [0xDE00], [0xD83D, 0xDE00], [0x61, 0xE9], [0xDE00, 0x61]]

def main (args : List String) : IO Unit := do
  let n := (args.head? >>= String.toNat?).getD 3
  -- every sequence of at most n atoms (as units; duplicates of a shorter text removed)
  let mut texts : List (List Nat) := [[]]
  let mut layer : List (List Nat) := [[]]
  for _ in [0:n] do
    layer := layer.flatMap fun t => atoms9.map (t ++ ·)
    texts := texts ++ layer
  let mut cases := 0
  let mut bad := 0
  for us in texts do
    let b := wtf8 us
    cases := cases + 1
    if unitCount b != us.length then bad := bad + 1
    if hashUnits 0 b != javaHash us then bad := bad + 1
    for k in [0:us.length] do
      cases := cases + 1
      if nthUnit b k != us[k]? then bad := bad + 1
    for k in [0:us.length + 1] do
      cases := cases + 1
      if toUnits (subsTail b k) != us.drop k then bad := bad + 1
    for ns in needles9 do
      for f in [0:us.length + 4] do
        let fr : Int := (f : Int) - 2
        cases := cases + 2
        if indexOfFix b (wtf8 ns) fr != indexOfJ us ns fr then bad := bad + 1
        if lastIndexOfFix b (wtf8 ns) fr != lastIndexOfJ us ns fr then bad := bad + 1
  IO.println s!"Round 9, Str: {texts.length} texts of at most {n} atoms, {cases} checks, {bad} differ from Java's functions (complete {n})."
  -- the brief's examples, as W9u's jank computes them
  IO.println s!"(count \"é\") = {unitCount (wtf8 [0xE9])}; (count \"😀\") = {unitCount (wtf8 [0xD83D, 0xDE00])}"
  IO.println s!"(subs \"é-è\" 2) units = {toUnits (subsTail (wtf8 [0xE9, 0x2D, 0xE8]) 2)}"
  IO.println s!"(subs \"😀\" 1) bytes = {subsTail (wtf8 [0xD83D, 0xDE00]) 1} (the low surrogate's three-byte form)"
  IO.println s!"(nth \"😀\" 0) = {nthUnit (wtf8 [0xD83D, 0xDE00]) 0}; (index-of \"éa\" \"a\") = {indexOfFix (wtf8 [0xE9, 0x61]) (wtf8 [0x61]) 0}"
  IO.println s!"hash loop of \"é\" = {hashUnits 0 (wtf8 [0xE9])} (String.hashCode 233)"
