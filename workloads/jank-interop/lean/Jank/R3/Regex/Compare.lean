import Jank.R3.Regex.JankFns
import Jank.R3.Regex.Java

/-!
# One question, both sides, and the set-aside toggles

A question is a jank/Clojure call: `re-find`, `re-seq`, `re-matches`, `clojure.string/replace`
and `replace-first` (with a template or a function), `split`, on a pattern and an input given
as code points (jank gets their UTF-8 bytes; the pattern is the text of a `#"…"` literal).

`Fix` holds the toggles of the residual searches. Each replaces one jank/libstdc++ rule by
Java's; all off is the replica. A deviation's class is the first toggle (in `fixOrder`) that
makes it disappear; one no toggle removes is classified by its trigger (non-ASCII text, a
construct whose syntax differs) or reported as unexplained.
-/

namespace Jank.R3.Regex

/-- The function given to `replace`/`replace-first`: it shows its argument. -/
def renderArg : V → V
  | .str s => .str ([0x3C] ++ s ++ [0x3E])
  | .vec xs => .str ([0x3C] ++ ((xs.map (fun o => o.getD (bytesOf "nil"))).intersperse [0x7C]).flatten ++ [0x3E])
  | _ => .err "bad argument"

def renderArgC : J.CV → J.CV
  | .str s => .str ([0x3C] ++ s ++ [0x3E])
  | .vec xs => .str ([0x3C] ++ ((xs.map (fun o => o.getD (bytesOf "nil"))).intersperse [0x7C]).flatten ++ [0x3E])
  | _ => .err "bad argument"

inductive Api where
  | find | seq | matches
  | replace (t : List Nat)
  | replaceFn
  | replaceFirst (t : List Nat)
  | replaceFirstFn
  | split (limit : Int)
  deriving BEq, Repr, Inhabited

structure Q where
  api : Api
  pat : List Nat
  inp : List Nat
  deriving BEq, Repr, Inhabited

/-- The toggles. -/
structure Fix where
  /-- No cut at the first NUL (R83). -/
  noNulCut : Bool := false
  /-- A group that did not participate is nil (R80). -/
  nilGroups : Bool := false
  /-- `$` before a final line terminator (R79). -/
  javaDollar : Bool := false
  /-- `re-matches` with `regex_match` (R82). -/
  fullMatch : Bool := false
  /-- `re-seq` keeps one buffer and searches on with `match_prev_avail`, one past an empty match
  (R81). -/
  findIter : Bool := false
  /-- `replace`/`split` iterate as `Matcher.find()` instead of `regex_iterator` (R85). -/
  iterJava : Bool := false
  /-- Replacement templates by `appendReplacement`'s rules (R84). -/
  javaTemplate : Bool := false
  /-- A `replace` function gets `re-groups` (R84). -/
  fnGroups : Bool := false
  /-- A lookahead's sub-executor sees the text before it. -/
  lookPrevAvail : Bool := false
  /-- `match_not_null` not passed into a lookahead. -/
  lookNoNotNull : Bool := false
  deriving BEq, Repr, Inhabited

def fixOrder : List (String × (Fix → Fix)) := [
  ("nul-cut (R83)", fun f => { f with noNulCut := true }),
  ("unmatched-group-empty (R80)", fun f => { f with nilGroups := true }),
  ("dollar-final-newline (R79)", fun f => { f with javaDollar := true }),
  ("re-matches-first-match (R82)", fun f => { f with fullMatch := true }),
  ("re-seq-new-string (R81)", fun f => { f with findIter := true }),
  ("regex-iterator-retry (R85)", fun f => { f with iterJava := true }),
  ("ecmascript-template (R84)", fun f => { f with javaTemplate := true }),
  ("fn-gets-match-string (R84)", fun f => { f with fnGroups := true }),
  ("lookahead-at-start (RX)", fun f => { f with lookPrevAvail := true }),
  ("lookahead-not-null (RX)", fun f => { f with lookNoNotNull := true })]

def Fix.all : Fix := fixOrder.foldl (fun f (_, g) => g f) {}

def Fix.efix (fx : Fix) : EFix :=
  { javaDollar := fx.javaDollar, lookPrevAvail := fx.lookPrevAvail, lookNoNotNull := fx.lookNoNotNull }

def utf8s (cps : List Nat) : List Nat := (Jank.Str.jstr cps).map (·.toNat)

/-- `smatch_to_vector`, or with nil for an unmatched group. -/
def groupsV (fx : Fix) (inp : Array Nat) (m : MatchRes) : V :=
  if !fx.nilGroups then smatchToVector inp m
  else if m.size == 0 then .nil
  else if m.size == 1 then .str ((m.get 0).str inp)
  else .vec (m.subs.toList.map fun s => if s.matched then some (s.str inp) else none)

/-- Matches the way `Matcher.find()` walks, on the replica's executor (a fixed jank). -/
def javaWalk (nfa : NFA) (inp : Array Nat) (lim : Lim) : Except Abort (List MatchRes) :=
  let rec go : Nat → Nat → Stats → List MatchRes → Except Abort (List MatchRes)
    | 0, _, _, acc => .ok acc.reverse
    | k + 1, p, st, acc =>
      if p > inp.size then .ok acc.reverse
      else match search nfa inp p inp.size { prevAvail := p > 0 } lim st with
        | .error e => .error e
        | .ok (false, _, _) => .ok acc.reverse
        | .ok (true, m, st') =>
          let m0 := m.get 0
          go k (if m0.first == m0.second then m0.second + 1 else m0.second) st' (m :: acc)
  go (2 * inp.size + 4) 0 {} []

/-- `appendReplacement`'s template on a jank match (the fixed rule). -/
def javaExpand (inp : Array Nat) (m : MatchRes) (t : List Nat) : Except String (List Nat) :=
  let ng := m.size - 1
  let grp (n : Nat) : List Nat := (m.get n).str inp
  let rec go : Nat → List Nat → Except String (List Nat)
    | 0, _ => .ok []
    | _ + 1, [] => .ok []
    | f + 1, c :: rest =>
      if c == 0x5C then
        match rest with
        | [] => .error "character to be escaped is missing"
        | d :: r => do return [d] ++ (← go f r)
      else if c == 0x24 then
        match rest with
        | [] => .error "Illegal group reference: group index is missing"
        | d :: r =>
          if !isDigitC d then .error "Illegal group reference"
          else
            let rec num : Nat → Nat → List Nat → Nat × List Nat
              | 0, n, r => (n, r)
              | g + 1, n, r => match r with
                | x :: r' => if isDigitC x && n * 10 + (x - 0x30) ≤ ng then num g (n * 10 + (x - 0x30)) r' else (n, r)
                | [] => (n, r)
            let (n, r) := num 8 (d - 0x30) r
            if n > ng then .error s!"No group {n}"
            else do return grp n ++ (← go f r)
      else do return [c] ++ (← go f rest)
  go (t.length + 1) t

/-- jank's answer, with toggles. -/
def jankEval (loc : Loc) (fx : Fix) (q : Q) (lim : Lim := {}) : V :=
  let lim := { lim with fix := fx.efix }
  match compile loc (utf8s q.pat) with
  | .error e => .err e.what
  | .ok nfa =>
  let cut (s : List Nat) : List Nat := if fx.noNulCut then s else cstr s
  let input := utf8s q.inp
  let inpA := (cut input).toArray
  -- the matches replace/split walk
  let walk : Except Abort (Option (List MatchRes)) :=
    if fx.iterJava then (javaWalk nfa inpA lim).map some
    else (iterAll nfa inpA 0 inpA.size {} lim).map (·.1)
  let template (t : List Nat) (m : MatchRes) : Except String (List Nat) :=
    if fx.javaTemplate then javaExpand inpA m (cut (utf8s t)) else .ok (format m inpA (cut (utf8s t)))
  let replaceWith (first : Bool) (piece : MatchRes → Except String (List Nat)) (noMatch : V) : V :=
    match walk with
    | .error a => abortV a
    | .ok none => .abort "iterations"
    | .ok (some ms) =>
      let ms := if first then ms.take 1 else ms
      if ms.isEmpty then noMatch else
      let rec go : List MatchRes → Nat → List Nat → V
        | [], last, out => .str (out ++ (inpA.extract last inpA.size).toList)
        | m :: rest, last, out =>
          match piece m with
          | .error w => .err w
          | .ok r => go rest (m.get 0).second (out ++ (inpA.extract last (m.get 0).first).toList ++ r)
      go ms 0 []
  match q.api with
  | .find =>
    match search nfa inpA 0 inpA.size {} lim {} with
    | .error a => abortV a
    | .ok (_, m, _) => groupsV fx inpA m
  | .seq =>
    if !fx.findIter then
      -- `re_find` on one matcher until nil: each search on the previous suffix, a new string
      let rec seqLoop : Nat → List Nat → List V → V
        | 0, _, acc => .infinite acc.reverse
        | k + 1, cur, acc =>
          let a := cur.toArray
          match search nfa a 0 a.size {} lim {} with
          | .error e => abortV e
          | .ok (false, _, _) => if acc.isEmpty then .nil else .list acc.reverse
          | .ok (true, m, _) =>
            let g := groupsV fx a m
            let rest := m.suffix.str a
            if rest == cur then .infinite (g :: g :: acc).reverse else seqLoop k rest (g :: acc)
      seqLoop (lim.iters + 1) (cut input) []
    else
      match javaWalk nfa inpA lim with
      | .error a => abortV a
      | .ok [] => .nil
      | .ok ms => .list (ms.map (groupsV fx inpA))
  | .matches =>
    let flags : Flags := if fx.fullMatch then {} else { continuous := true }
    match search nfa inpA 0 inpA.size flags lim {} fx.fullMatch with
    | .error a => abortV a
    | .ok (_, m, _) =>
      if !fx.fullMatch && !(m.suffix.str inpA).isEmpty then .nil else groupsV fx inpA m
  | .replace t =>
    if !fx.iterJava && !fx.javaTemplate && !fx.noNulCut then jReplaceStr nfa input (utf8s t) lim
    else replaceWith false (template t) (.str (if fx.noNulCut then input else cut input))
  | .replaceFirst t =>
    if !fx.javaTemplate && !fx.noNulCut then jReplaceFirstStr nfa input (utf8s t) lim
    else replaceWith true (template t) (.str (cut input))
  | .replaceFn =>
    let arg (m : MatchRes) : V := if fx.fnGroups then groupsV fx inpA m else .str ((m.get 0).str inpA)
    replaceWith false (fun m => match renderArg (arg m) with
      | .str r => .ok r
      | _ => .error "not a string") (.str input)
  | .replaceFirstFn =>
    if !fx.nilGroups && !fx.noNulCut then jReplaceFirstFn nfa input renderArg lim
    else replaceWith true (fun m => match renderArg (groupsV fx inpA m) with
      | .str r => .ok r
      | _ => .error "not a string") (.str input)
  | .split limit =>
    if !fx.iterJava then jSplit nfa input limit lim
    else
      -- Pattern.split's loop over the fixed walk (fixed jank)
      if input.isEmpty || limit == 1 then .list [.str input] else
      let a := input.toArray
      match javaWalk nfa a lim with
      | .error e => abortV e
      | .ok ms => Id.run do
        let matchLimited := limit > 0
        let mut index := 0
        let mut list : List (List Nat) := []
        for m in ms do
          let st := (m.get 0).first
          let en := (m.get 0).second
          if !matchLimited || (list.length : Int) < limit - 1 then
            if index == 0 && index == st && st == en then continue
            list := list ++ [(a.extract index st).toList]
            index := en
          else if (list.length : Int) == limit - 1 then
            list := list ++ [(a.extract index a.size).toList]
            index := en
        if index == 0 then return .list [.str input]
        if !matchLimited || (list.length : Int) < limit then list := list ++ [(a.extract index a.size).toList]
        if limit == 0 then list := (list.reverse.dropWhile (·.isEmpty)).reverse
        return .list (list.map .str)

/-- Clojure's answer. -/
def cljEval (q : Q) (lim : J.Lim := {}) : J.CV :=
  match J.compile q.pat with
  | .error (.syntax e) => .err e
  | .ok p =>
    match p.node.unsupportedIn with
    | some w => .unknown w
    | none =>
    match q.api with
    | .find => J.reFind p q.inp lim
    | .seq => J.reSeq p q.inp lim
    | .matches => J.reMatches p q.inp lim
    | .replace t => J.replace p q.inp (.inl t) false lim
    | .replaceFirst t => J.replace p q.inp (.inl t) true lim
    | .replaceFn => J.replace p q.inp (.inr renderArgC) false lim
    | .replaceFirstFn => J.replace p q.inp (.inr renderArgC) true lim
    | .split l => J.split p q.inp l lim

/-- Whether Java accepts the pattern (compiles it). -/
def javaAccepts (pat : List Nat) : Bool :=
  match J.compile pat with
  | .ok _ => true
  | .error _ => false

def jankAccepts (loc : Loc) (pat : List Nat) : Bool :=
  match compile loc (utf8s pat) with
  | .ok _ => true
  | .error _ => false

partial def agreeV : V → J.CV → Bool
  | .nil, .nil => true
  | .str a, .str b => a == b
  | .vec xs, .vec ys => xs == ys
  | .list xs, .list ys => xs.length == ys.length && (xs.zip ys).all fun (a, b) => agreeV a b
  | .err _, .err _ => true
  | _, _ => false

inductive Verdict where
  | agree
  /-- Not compared: the spec model or the replica's limits do not decide it. -/
  | skip (why : String)
  /-- jank throws on a pattern Java compiles. -/
  | rejects (jankErr : String)
  /-- jank compiles a pattern Java rejects (counted, not a deviation). -/
  | acceptsInvalid (javaErr : String)
  | differ
  deriving BEq, Repr, Inhabited

/-- Whether Java's tree has a group inside a lookahead. -/
def lookGroups (pat : List Nat) : Bool :=
  match J.compile pat with
  | .ok p => p.node.groupInLook
  | .error _ => false

/-- Only the whole match of every result. -/
partial def whole : V → V
  | .vec xs => .str ((xs.headD none).getD [])
  | .list xs => .list (xs.map whole)
  | v => v

partial def wholeC : J.CV → J.CV
  | .vec xs => .str ((xs.headD none).getD [])
  | .list xs => .list (xs.map wholeC)
  | v => v

def verdict (loc : Loc) (fx : Fix) (q : Q) : Verdict × V × J.CV :=
  let c := cljEval q
  let ja := jankAccepts loc q.pat
  let ca := javaAccepts q.pat
  let j := jankEval loc fx q
  if !ja && ca then (.rejects (match j with | .err w => w | _ => "?"), j, c)
  else if ja && !ca then (.acceptsInvalid (match c with | .err w => w | _ => "?"), j, c)
  else match j, c with
    | .abort w, _ => (.skip s!"jank {w}", j, c)
    | _, .unknown w => (.skip s!"spec {w}", j, c)
    | _, _ =>
      if agreeV j c then (.agree, j, c)
      else if lookGroups q.pat && agreeV (whole j) (wholeC c) then
        (.skip "capture inside a lookahead (RXJ4)", j, c)
      else (.differ, j, c)

/-- The class of a deviation: the first toggle that removes it, else `none`. -/
def classify (loc : Loc) (q : Q) : Option String :=
  let rec go : List (String × (Fix → Fix)) → Fix → Option String
    | [], _ => none
    | (name, g) :: rest, fx =>
      let fx' := g fx
      match verdict loc fx' q with
      | (.agree, _, _) => some name
      | _ => go rest fx'
  go fixOrder {}

/-! ## Printing -/

def showB (b : List Nat) : String := Jank.Str.showBytes (b.map (·.toUInt8))

partial def V.show : V → String
  | .nil => "nil"
  | .str b => showB b
  | .vec xs => "[" ++ " ".intercalate (xs.map fun o => match o with | some b => showB b | none => "nil") ++ "]"
  | .list xs => "(" ++ " ".intercalate (xs.map V.show) ++ ")"
  | .infinite xs => "(" ++ " ".intercalate (xs.map V.show) ++ " …) infinite"
  | .err w => s!"throws ({w})"
  | .abort w => s!"<replica limit: {w}>"

partial def CV.show : J.CV → String
  | .nil => "nil"
  | .str b => showB b
  | .vec xs => "[" ++ " ".intercalate (xs.map fun o => match o with | some b => showB b | none => "nil") ++ "]"
  | .list xs => "(" ++ " ".intercalate (xs.map CV.show) ++ ")"
  | .err w => s!"throws ({w})"
  | .unknown w => s!"<spec: {w}>"

/-- A regex literal's text: the pattern as written (no escaping needed for the drawn
alphabets: no `"`). -/
def patLit (p : List Nat) : String :=
  "#\"" ++ String.join (p.map fun c =>
    if c == 0x0A then "\\n" else if c == 0x22 then "\\\"" else String.singleton (Char.ofNat c)) ++ "\""

def Q.program (q : Q) : String :=
  let s := Jank.Str.lit q.inp
  let r := patLit q.pat
  let t (x : List Nat) := Jank.Str.lit x
  match q.api with
  | .find => s!"(re-find {r} {s})"
  | .seq => s!"(re-seq {r} {s})"
  | .matches => s!"(re-matches {r} {s})"
  | .replace x => s!"(clojure.string/replace {s} {r} {t x})"
  | .replaceFirst x => s!"(clojure.string/replace-first {s} {r} {t x})"
  | .replaceFn => s!"(clojure.string/replace {s} {r} f)"
  | .replaceFirstFn => s!"(clojure.string/replace-first {s} {r} f)"
  | .split l => s!"(clojure.string/split {s} {r} {l})"

end Jank.R3.Regex
