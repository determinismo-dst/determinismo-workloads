import Elle.R4.Interp
import Elle.R4.GInterp
import Elle.Spec

/-!
# Round 4: the declarative model against round 1's executable specification

The proofs quantify over `Interp.Clean` interpretations and their `dsg`. For them to cover the
specification's, every clean interpretation `Spec.interpsListAppend` enumerates must satisfy
`Interp.Clean`, and each edge of `Interp.dsg` must be an edge of the specification's DSG with the
same relationship (`dsg` may have fewer: it omits committed `:info` transactions' reads). This
file checks both, executably, on any history (`elle-r5 validate`).
-/

namespace Elle.R4.Validate

open Elle Elle.R4 Elle.R4.LA

def ordOf (i : Spec.Interp) (k : Nat) : List Nat := (i.order.lookup k).getD []

def chainUpToB (h : History) (i : Spec.Interp) (k n : Nat) : List Int :=
  ((ordOf i k).take n).flatMap fun w => apps h w k

/-- `Interp.Clean`, decided on a concrete interpretation; the first failing clause, if any. -/
def cleanFails (h : History) (i : Spec.Interp) : List String := Id.run do
  let com (w : Nat) : Bool := i.dsg.verts.contains w
  let keys := dedup (h.toList.flatMap fun o => o.value.map (·.k))
  let mut out : List String := []
  for o in h.toList do
    if o.type == .ok && !com o.index then out := out ++ [s!"okCom {o.index}"]
  for w in i.dsg.verts do
    match h[w]? with
    | some o => if !(o.type == .ok || o.type == .info) then out := out ++ [s!"comPoss {w}"]
    | none => out := out ++ [s!"comPoss {w}"]
  for k in keys do
    let ord := ordOf i k
    if ord.length != (dedup ord).length then out := out ++ [s!"ordNodup {k}"]
    for o in h.toList do
      let w := o.index
      if ord.contains w != (com w && !(apps h w k).isEmpty) then out := out ++ [s!"ordMem {k} {w}"]
  for o in h.toList do
    if o.type != .ok then continue
    let t := o.index
    for j in List.range o.value.length do
      let m := o.value.getD j default
      if m.f != .r then continue
      let ord := ordOf i m.k
      let own := appsBefore o j m.k
      if own.isEmpty then
        let ok := (List.range (ord.length + 1)).any fun n =>
          toL m.v == chainUpToB h i m.k n && !(ord.take n).contains t
        if !ok then out := out ++ [s!"extRead {t} {j}"]
      else
        let ok := (List.range ord.length).any fun n =>
          ord[n]? == some t && toL m.v == chainUpToB h i m.k n ++ own
        if !ok then out := out ++ [s!"intRead {t} {j}"]
  return out

/-- `Interp.dsg`'s edges, computed: (a, b, relationship). -/
def dsgEdges (h : History) (i : Spec.Interp) : List (Nat × Nat × Rels) := Id.run do
  let com (w : Nat) : Bool := i.dsg.verts.contains w
  let keys := dedup (h.toList.flatMap fun o => o.value.map (·.k))
  let mut out : List (Nat × Nat × Rels) := []
  for k in keys do
    let ord := ordOf i k
    for (a, b) in ord.zip (ord.drop 1) do out := out ++ [(a, b, Rels.WW)]
  for o in h.toList do
    if o.type != .ok then continue
    let t := o.index
    for j in List.range o.value.length do
      let m := o.value.getD j default
      if m.f != .r || !(appsBefore o j m.k).isEmpty then continue
      let ord := ordOf i m.k
      for n in List.range (ord.length + 1) do
        if toL m.v == chainUpToB h i m.k n then
          if 0 < n then
            match ord[n - 1]? with
            | some a => if a != t then out := out ++ [(a, t, Rels.WR)]
            | none => pure ()
          match ord[n]? with
          | some b => if b != t then out := out ++ [(t, b, Rels.RW)]
          | none => pure ()
  for oa in h.toList do
    if oa.type != .ok then continue
    for ob in h.toList do
      let a := oa.index
      let b := ob.index
      if a != b && com b && a < invIdx h b then
        out := out ++ [(a, b, Rels.REALTIME)]
        if oa.process == ob.process then out := out ++ [(a, b, Rels.PROCESS)]
  return out

/-- Edges of `Interp.dsg` the specification's DSG lacks. -/
def extraEdges (h : History) (i : Spec.Interp) : List (Nat × Nat × Rels) :=
  (dsgEdges h i).filter fun (a, b, r) => Rels.inter (i.dsg.edge a b) r == 0

/-- On one history: each clean interpretation of the specification, against the declarative
model. -/
def check (h : History) : List (String × String) :=
  let is := Spec.interpsListAppend h
  let clean := is.filter (·.clean)
  (clean.filterMap fun i =>
    match cleanFails h i with
    | [] => none
    | f :: _ => some ("validate:clean-fails", s!"{f}; order {i.order}")) ++
  (clean.filterMap fun i =>
    match extraEdges h i with
    | [] => none
    | e :: _ => some ("validate:extra-edge", s!"{repr e}; order {i.order}")) ++
  (if clean.isEmpty then [] else [("validate:clean-interpretations", s!"{clean.length}")])


/-! ## The general model (dirty interpretations included) -/

/-- The bases the specification's interpretation gives each writer: the prefix of an `:ok` read
before the writer's first element, else the previous writer's installed version. -/
def gbaseOf (h : History) (i : Spec.Interp) (k : Nat) : List (Nat × List Int) := Id.run do
  let reads : List (List Int) := h.toList.filter (·.type == .ok) |>.flatMap fun o =>
    (o.value.filter fun m => m.f == .r && m.k == k).map fun m => toL m.v
  let mut out : List (Nat × List Int) := []
  let mut prev : List Int := []
  for w in ordOf i k do
    let a := apps h w k
    let pinned := reads.findSome? fun r => match a.head? with
      | some e0 => match r.findIdx? (· == e0) with
        | some q => some (r.take q)
        | none => none
      | none => none
    let b := pinned.getD prev
    out := out ++ [(w, b)]
    prev := b ++ a
  return out

/-- `GInterp.Valid`, decided on a concrete interpretation; failing clauses. -/
def gFails (h : History) (i : Spec.Interp) : List String := Id.run do
  let keys := dedup (h.toList.flatMap fun o => o.value.map (·.k))
  let base (k w : Nat) : List Int := ((gbaseOf h i k).lookup w).getD []
  let mut out : List String := []
  for k in keys do
    let ord := ordOf i k
    for a in List.range ord.length do
      for b in List.range ord.length do
        if a < b then
          let w := ord.getD a 0
          let w' := ord.getD b 0
          if !((base k w ++ apps h w k).isPrefixOf (base k w')) then out := out ++ [s!"chain {k} {w} {w'}"]
    for w in ord do
      if (apps h w k).any fun x => (base k w).contains x then out := out ++ [s!"own {k} {w}"]
  for o in h.toList do
    if o.type != .ok then continue
    for m in o.value do
      if m.f != .r then continue
      let v := toL m.v
      for w in ordOf i m.k do
        let a := apps h w m.k
        for n in List.range a.length do
          if v.contains (a.getD n 0) && !((base m.k w ++ a.take (n + 1)).isPrefixOf v) then
            out := out ++ [s!"pins {o.index} {w} {n}"]
      for x in v do
        if !(h.toList.any fun o' => o'.type != .invoke && (appsOf o' m.k).contains x) then
          out := out ++ [s!"appended {o.index} {x}"]
  return out

/-- Every interpretation of the specification (clean or not) against `GInterp.Valid`. -/
def checkG (h : History) : List (String × String) :=
  let is := Spec.interpsListAppend h
  (is.filterMap fun i =>
    match gFails h i with
    | [] => none
    | f :: _ => some ("validate:g-fails", s!"{f}; order {i.order}; clean {i.clean}")) ++
  (if is.any (!·.clean) then [("validate:dirty-interpretations", "")] else []) ++
  (if is.isEmpty then [] else [("validate:interpretations", "")])

end Elle.R4.Validate
