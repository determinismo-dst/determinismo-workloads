import Jank.R7.Champ.LawOne
import Jank.R7.Champ.Trans
import Jank.R7.Champ.Walk

/-!
Round 7 driver, CHAMP (`jank7-champ pairs | walk POOL set|map DEPTH MAXSTATES [FIXES]`).

- `pairs`: for every pool, each pair jank's `=` relates (either direction) whose jank hashes differ,
  or that jank's `=` relates in one direction only, or where jank's `=` and Clojure's differ, with
  how many low 5-bit chunks (CHAMP levels) their hashes share.
- `walk POOL set|map DEPTH MAXSTATES [FIXES]`: `Walk.bfs` over the pool with jank as it is (`none`),
  with every known cause fixed (`all`), or with every fix but the named one (`all-but-<name>`).
-/

open Jank.R3.Immer.Champ Jank.R7.Champ.Vals Jank.R7.Champ.Walk

def nan : W := dbl 0x7FF8000000000000 "##NaN"

def poolNum : Array W := #[dbl 0 "0.0", dbl 0x8000000000000000 "-0.0", dbl 0x4000000000000000 "2.0",
  dbl 0x3FF0000000000000 "1.0", nan, long 1, bigI 1, long 3, ratio 1 2, dec "1", dec "1.0",
  dec "1.0000000000000000001"]

def poolDec : Array W := #[dec "0", dec "0.00000000000000015", dec "0.0000000000000003", dec "1",
  dec "1.0000000000000000001", dec "1.0000000000000000002", dec "0.0", dec "2", long 0, dbl 0 "0.0"]

def eAcute : Char := Char.ofNat 233

def poolStr : Array W := #[.str "a", .char 'a', .strseq "a", .vec [.char 'a'], .list [.char 'a'],
  .lazy [.char 'a'], .strseq (String.singleton eAcute), .vec [.char eAcute], .list [.char eAcute],
  .str (String.singleton eAcute), .strseq "ab", .vec [.char 'a', .char 'b']]

def poolColl : Array W := #[.nil, .vec [], .list [], .lazy [], .map [], .set [], .str "",
  .map [(.kw "" "a", long 1)], .mapseq [(.kw "" "a", long 1)], .vec [.vec [.kw "" "a", long 1]],
  .list [.vec [.kw "" "a", long 1]], .set [long 1]]

def poolSym : Array W := #[.kw "" "a", .kw "x" "a", .kw "y" "a", .sym "" "a", .sym "x" "a", .sym "y" "a",
  .str "a", .str "x/a", .kw "x" "b", .sym "x" "b"]

def poolMix : Array W := #[dbl 0 "0.0", dbl 0x8000000000000000 "-0.0", dbl 0x4000000000000000 "2.0", nan,
  long 1, bigI 1, dec "1", dec "1.0000000000000000001", .strseq "a", .vec [.char 'a'],
  .strseq (String.singleton eAcute), .vec [.char eAcute], .list [], .lazy [], .mapseq [(.kw "" "a", long 1)],
  .vec [.vec [.kw "" "a", long 1]], .kw "x" "a", .sym "x" "a"]

def pools : List (String × Array W) :=
  [("num", poolNum), ("dec", poolDec), ("str", poolStr), ("coll", poolColl), ("sym", poolSym), ("mix", poolMix)]

/-- How many low 5-bit chunks two hashes share (0-7). -/
def sharedChunks (a b : Nat) : Nat := Id.run do
  let mut n := 0
  for i in List.range 7 do
    if (a >>> (5 * i)) % 32 == (b >>> (5 * i)) % 32 then n := n + 1 else return n
  return n

/-- A long whose jank hash shares at least `c` low chunks with `h` (a pusher), searched in `[2, 2^20)`. -/
def pusher (h c : Nat) : Option Int := Id.run do
  for n in List.range (1 <<< 20) do
    if n ≥ 2 then
      let hn := (jH Fix.none (long n)).toNat
      if sharedChunks hn h ≥ c then return some n
  return none

def pairsCmd : IO Unit := do
  for (name, pool) in pools do
    IO.println s!"== pool {name}: {pool.size} values: {(pool.map W.code).toList}"
    for i in List.range pool.size do
      for j in List.range pool.size do
        if i < j then
          let a := pool.getD i .nil
          let b := pool.getD j .nil
          let jab := jEq Fix.none a b
          let jba := jEq Fix.none b a
          let cab := cEq a b
          let ha := (jH Fix.none a).toNat
          let hb := (jH Fix.none b).toNat
          if jab != jba || jab != cab || ((jab || jba) && ha != hb) then
            IO.println s!"  {a.code} / {b.code}: jank (= a b) {jab}, (= b a) {jba}; Clojure {cab}; hashes {ha} {hb}, shared low chunks {sharedChunks ha hb}"
    for i in List.range pool.size do
      let a := pool.getD i .nil
      if !jEq Fix.none a a then IO.println s!"  {a.code}: jank (= x x) false (identity in Clojure's collections: true)"

def fixOf (s : String) : Fix :=
  match s with
  | "none" => Fix.none
  | "all" => Fix.all
  | "all-but-negzero" => { Fix.all with negzero := false }
  | "all-but-identity" => { Fix.all with identity := false }
  | "all-but-bigint" => { Fix.all with bigint := false }
  | "all-but-lazy" => { Fix.all with lazyEmpty := false }
  | "all-but-mapseq" => { Fix.all with mapseq := false }
  | "all-but-strseq" => { Fix.all with strseq := false }
  | "all-but-bigdec" => { Fix.all with bigdec := false }
  | "all-but-keepold" => { Fix.all with keepOld := false }
  | _ => Fix.none

/-- The pool with a pusher for every jank-equal pair with different hashes that share chunks. -/
def withPushers (pool : Array W) : Array W := Id.run do
  let mut extra : Array W := #[]
  for i in List.range pool.size do
    for j in List.range pool.size do
      if i < j then
        let a := pool.getD i .nil
        let b := pool.getD j .nil
        let ha := (jH Fix.none a).toNat
        let hb := (jH Fix.none b).toNat
        let c := sharedChunks ha hb
        if (jEq Fix.none a b || jEq Fix.none b a) && ha != hb && c ≥ 1 then
          match pusher ha c with
          | some n => if !(extra.any fun w => w.code == s!"{n}") then extra := extra.push (long n)
          | none => pure ()
  return pool ++ extra

def walkCmd (pname kind : String) (depth maxStates : Nat) (fixes : List String) : IO Unit := do
  let base := (pools.find? (·.1 == pname)).map (·.2) |>.getD #[]
  let pool := withPushers base
  IO.println s!"== walk pool {pname} ({kind}): {pool.size} values {(pool.map W.code).toList}; depth ≤ {depth}, ≤ {maxStates} states"
  for fx in fixes do
    let T := Tables.mk' pool (kind == "map") (fixOf fx)
    let t0 ← IO.monoMsNow
    IO.println s!"  fixes {fx}:"
    let r ← T.bfs depth maxStates
    let t1 ← IO.monoMsNow
    let t := r.tally
    IO.println s!"  fixes {fx}: {t.states} states, every sequence of length ≤ {r.completeDepth} covered; {if r.complete then "COMPLETE (no new state at the next depth: every length covered)" else s!"stopped in depth {r.depth} (frontier {r.frontier})"} ({(t1 - t0) / 1000} s)"
    IO.println s!"    disagreements: count {t.count}, count-vs-seq {t.countSeq}, contains? {t.contains}, get {t.getv}, representatives {t.repr}, set= {t.seteq}"
    let ps := t.pairs.toList.mergeSort (fun a b => a.2 ≥ b.2)
    for ((q, p), n) in ps.take 12 do
      IO.println s!"    contains?/get of {(pool.getD q .nil).code} (stored/expected {(pool.getD p .nil).code}): {n}"
    for f in t.firsts do IO.println s!"    e.g. {f}"
    (← IO.getStdout).flush

/-- vH1's programs on the replica: jank's hashes of the map seq, the vector and the first pusher. -/
def showCmd : IO Unit := do
  let e : W := .vec [.vec [.kw "" "a", long 1]]
  let ms : W := .mapseq [(.kw "" "a", long 1)]
  let pool0 : Array W := #[e, ms]
  let he := (jH Fix.none e).toNat
  let hm := (jH Fix.none ms).toNat
  let p : Nat := (List.range 100000).find? (fun (n : Nat) => n ≥ 2 && (jH Fix.none (long (n : Int))).toNat % 32 == he % 32) |>.getD 0
  let pool := pool0.push (long (p : Int))
  IO.println s!"jank hashes: [[:a 1]] {he} (chunks {he % 32}, {(he >>> 5) % 32}), (seq \{:a 1}) {hm} (chunks {hm % 32}, {(hm >>> 5) % 32}); first pusher {p}: hash {(jH Fix.none (long (p : Int))).toNat}"
  IO.println s!"(= [[:a 1]] (seq \{:a 1})) jank {jEq Fix.none e ms}, (= (seq \{:a 1}) [[:a 1]]) jank {jEq Fix.none ms e}; Clojure {cEq e ms}"
  for fx in [Fix.none, Fix.all] do
    let T := Tables.mk' pool false fx
    let s1 := ((Champ.empty.add T.cfg 0).run {}).1
    let s2 := ((s1.add T.cfg 2).run {}).1
    let M := Tables.mk' pool true fx
    -- (hash-map e :a p :b): elements 2·key + value
    let m := ((((Champ.empty.add M.cfg 0).run {}).1.add M.cfg (2 * 2 + 1)).run {}).1
    IO.println s!"fixes {if fx.mapseq then "all" else "none"}: (contains? (hash-set e) ms) {(s1.get T.cfg 1).isSome}; (contains? (conj (hash-set e) p) ms) {(s2.get T.cfg 1).isSome}; (get (hash-map e :a p :b) ms) {(m.get M.cfg 1).map fun x => if x % 2 == 0 then ":a" else ":b"}"

/-- BigDecimals jank calls = to 1M (within 2^-52), Clojure not, whose jank hash shares 1M's low chunks. -/
def decSearchCmd : IO Unit := do
  let one := dec "1"
  let h1 := (jH Fix.none one).toNat
  let mut found := 0
  for x in List.range 3000 do
    if found < 4 && x ≥ 1 then
      let digits := toString x
      let s := "1." ++ String.mk (List.replicate (19 - digits.length) '0') ++ digits
      let w := dec s
      let h := (jH Fix.none w).toNat
      if jEq Fix.none one w && !cEq one w && sharedChunks h h1 ≥ 1 then
        found := found + 1
        let T := Tables.mk' #[one, w] false Fix.none
        let s1 := ((Champ.empty.add T.cfg 0).run {}).1
        let s2 := ((s1.add T.cfg 1).run {}).1
        IO.println s!"{s}M: hash {h} (1M: {h1}), shared low chunks {sharedChunks h h1}; (contains? (hash-set 1M) x) jank {(s1.get T.cfg 1).isSome}; (count (hash-set 1M x)) jank {s2.size}; Clojure false, 2"

def main (args : List String) : IO Unit := do
  match args with
  | ["decsearch"] => decSearchCmd
  | ["show"] => showCmd
  | ["pairs"] => pairsCmd
  | ["walk", p, k, d, m] => walkCmd p k d.toNat! m.toNat! ["none", "all"]
  | "walk" :: p :: k :: d :: m :: fx => walkCmd p k d.toNat! m.toNat! fx
  | _ => IO.println "usage: jank7-champ pairs | walk POOL set|map DEPTH MAXSTATES [FIXES...]"
