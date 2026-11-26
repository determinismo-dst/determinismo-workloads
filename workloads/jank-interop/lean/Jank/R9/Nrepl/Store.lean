import Jank.R8.Nrepl.Exact

/-!
# Round 9, nREPL: the every-schedule search with a flat state store (T9u, T3u)

Round 8's `exactGraph` keeps each state's code as an `Array Nat` (about 120 bytes), a hash-map entry
for it (about 50) and its packed edges (about 36): T9u stopped at 22,000,971 states near 5 GB.
For deciding reachability (every reachable state's steps and final verdicts, deadlocks) the edges
are not needed. `flatSearch` keeps:

- the codes in one preallocated `ByteArray`, `W` little-endian `UInt32`s per state (`W` = 7 memory
  components + the most threads a scenario can have; an absent thread slot is `0xFFFFFFFF`): 48
  bytes per state for two clients;
- an open-addressing table of state ids (+1, `UInt32`, 0 = empty) over a power-of-two capacity,
  probed linearly; a slot is accepted only when the stored code equals the code byte for byte, so
  the table merges exactly the states with one code (round 8's ★ `same_code`: one code means one
  stored state component by component; injectivity with respect to `=` rests on nREPLA6-2 as
  before). No hash is trusted.

States are expanded in id order (breadth first), each live thread under every value of its own
decisions (round 8's `branchesOfP`, round 6's `branchesOf`), logs ordered by client (`canonKey`),
the judge at states with no live thread (`judgeEnd`, R125's properties set aside for the unlocked
scenarios), exactly as `EG.expand`; only the edges are dropped.
-/

namespace Jank.R9.Nrepl

open Determinismo Jank.R3.Nrepl Jank.R6.Nrepl Jank.R8.Nrepl Jank.NreplServer Jank.Analyzer

def absent : UInt32 := 0xFFFFFFFF

@[inline] def rd32 (b : ByteArray) (o : Nat) : UInt32 :=
  (b.get! o).toUInt32 ||| ((b.get! (o + 1)).toUInt32 <<< 8) ||| ((b.get! (o + 2)).toUInt32 <<< 16) ||| ((b.get! (o + 3)).toUInt32 <<< 24)

@[inline] def wr32 (b : ByteArray) (o : Nat) (v : UInt32) : ByteArray :=
  ((((b.set! o v.toUInt8).set! (o + 1) (v >>> 8).toUInt8).set! (o + 2) (v >>> 16).toUInt8).set! (o + 3) (v >>> 24).toUInt8)

@[inline] def push32 (b : ByteArray) (v : UInt32) : ByteArray :=
  (((b.push v.toUInt8).push (v >>> 8).toUInt8).push (v >>> 16).toUInt8).push (v >>> 24).toUInt8

/-- A code padded to `w` entries. -/
def padCode (w : Nat) (code : List Nat) : Array UInt32 :=
  let a := (code.map (·.toUInt32)).toArray
  a ++ Array.replicate (w - a.size) absent

def hashCode (c : Array UInt32) : UInt64 :=
  c.foldl (fun h x => (h ^^^ x.toUInt64) * 1099511628211) 14695981039346656037

/-- The code of state `i` (sentinels dropped). -/
def codeAt (codes : ByteArray) (w i : Nat) : List Nat := Id.run do
  let mut out := #[]
  for k in [0:w] do
    let v := rd32 codes ((i * w + k) * 4)
    if v != absent then out := out.push v.toNat
  return out.toList

def sameAt (codes : ByteArray) (w i : Nat) (c : Array UInt32) : Bool := Id.run do
  for k in [0:w] do
    if rd32 codes ((i * w + k) * 4) != c[k]! then return false
  return true

structure FlatOut where
  states : Nat := 0
  expanded : Nat := 0
  runs : Nat := 0
  finals : Nat := 0
  finalViol : Nat := 0
  stepViol : Nat := 0
  deadlocks : Nat := 0
  blockedMoves : Nat := 0
  progressSelf : Nat := 0
  maxThreads : Nat := 0
  examples : Array String := #[]
  complete : Bool := false
  overWidth : Nat := 0
  deriving Inhabited

/-- Finds code `c` (hash `h`) in the table, or the empty slot where it goes: (slot, id) with id 0 for
an empty slot, else the state id + 1. -/
def probe (codes slots : ByteArray) (w capMask : Nat) (c : Array UInt32) (h : UInt64) : Nat × Nat := Id.run do
  let mut s := (h.toNat) &&& capMask
  for _ in [0:capMask + 1] do
    let v := rd32 slots (s * 4)
    if v == 0 then return (s, 0)
    if sameAt codes w (v.toNat - 1) c then return (s, v.toNat)
    s := (s + 1) &&& capMask
  return (s, 0)

/-- Every state any schedule reaches, breadth first, with the flat store; stops past `maxStates`
states, past the deadline, or when the table's load passes one half. -/
def flatSearch (s : TScenario) (noOut : Bool) (w logCap maxStates deadlineMs : Nat) (step : StepFn)
    (progress : Nat → Nat → IO Unit) : IO FlatOut := do
  let t0 ← IO.monoMsNow
  let cap := 2 ^ logCap
  let capMask := cap - 1
  let mut slots : ByteArray := ByteArray.emptyWithCapacity (cap * 4)
  for _ in [0:cap * 4] do slots := slots.push 0
  let mut codes : ByteArray := ByteArray.emptyWithCapacity (maxStates * w * 4 + 4096)
  let mut T : Tabs := {}
  let mut o : FlatOut := {}
  -- the initial state
  let p0 := tInitial s.cfg s.scripts
  let k0 := canonKey (PKey.of p0)
  let (T1, code0) := T.encode k0
  T := T1
  let c0 := padCode w code0
  for x in c0 do codes := push32 codes x
  let (sl0, _) := probe codes slots w capMask c0 (hashCode c0)
  slots := wr32 slots (sl0 * 4) 1
  let mut n := 1
  let mut i := 0
  while i < n do
    if i % 1024 == 0 then
      if n > maxStates || n * 2 > cap || (← IO.monoMsNow) - t0 > deadlineMs then
        return { o with states := n, expanded := i }
      if i % 4194304 == 0 && i > 0 then progress i n
    let pcL := codeAt codes w i
    let some k := T.decode pcL | return { o with states := n, expanded := i, examples := o.examples.push s!"state {i} does not decode" }
    let pc := pcL.toArray
    let live := liveOf k
    o := { o with maxThreads := max o.maxThreads k.threads.size }
    if live.isEmpty then
      o := { o with finals := o.finals + 1 }
      if let some (p, d) := judgeEnd s k.mem noOut then
        o := { o with finalViol := o.finalViol + 1, examples := if o.examples.size < 5 then o.examples.push s!"final {i}: {p}: {d.take 300}" else o.examples }
      i := i + 1
      continue
    let mut moved := false
    for t in live do
      let some locals := k.threads.getD t none | continue
      for (_, res, q) in branchesOfP step k t locals do
        o := { o with runs := o.runs + 1 }
        match res with
        | .stop v =>
          moved := true
          if let some (p, d) := v then
            o := { o with stepViol := o.stepViol + 1, examples := if o.examples.size < 5 then o.examples.push s!"step at {i}: {p}: {d.take 300}" else o.examples }
        | _ =>
          let c := split (canonKey q)
          let h := hintsFor T pc c true
          let (T', code) := T.encodeC c h
          T := T'
          if code.length > w then
            o := { o with overWidth := o.overWidth + 1 }
            continue
          let ca := padCode w code
          let (sl, found) := probe codes slots w capMask ca (hashCode ca)
          let j ← if found == 0 then do
              for x in ca do codes := push32 codes x
              slots := wr32 slots (sl * 4) (n + 1).toUInt32
              n := n + 1
              pure (n - 1)
            else pure (found - 1)
          match res with
          | .blocked => if j != i then o := { o with blockedMoves := o.blockedMoves + 1 }
          | _ =>
            moved := true
            if j == i then o := { o with progressSelf := o.progressSelf + 1 }
    if !moved then o := { o with deadlocks := o.deadlocks + 1 }
    i := i + 1
  return { o with states := n, expanded := i, complete := true }

end Jank.R9.Nrepl
