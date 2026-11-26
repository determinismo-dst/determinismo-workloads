import Replica.Prelude
import Replica.Searching

/-!
# determinismo-ci's tests, replicated (platform 3939448)

How a test runner's JUnit report becomes assertions, and assertions a CI verdict:

- `guest/runtime/junit.zig:11-55` `cases`: each `<testcase` found from where the last one ended;
  its tag to the first `>`; its body to `</testcase>`; its `classname` and `name` by
  `attribute` (58-63: the text `" " ++ key ++ "=\""`, then up to the next `"`), a case without a
  name skipped; failed when its body contains the text `<failure` or else `<error`;
- `guest/runtime/assert_main.zig:36-52` `junit_assert`: each case an `always` named
  `"test passes: " ++ name`, true unless failed;
- `src/products/ci.zig:216-242`: a shard's run command, `{tests}` replaced by the shard's names
  through `awk ... | tr '\n' '\000' | xargs -0 sh -c '<run>' sh`, then `det-assert junit` over the
  report the run command wrote at `junit` (the file at that path once the command ended);
- `src/products/ci.zig:300-321` (shards' verdicts) and `438-480` `tests_judge` (tests').

The documentation's semantics (docs/CI.md "Verdicts per test", the `junit` field): each test of a
JUnit report is a property of its own in each timeline, failing when the test failed or errored
(skipped ones pass); each test gets its own verdict across its shard's timelines.

Not modeled: entities beyond those `unescape` knows (it is replicated), the messages' text,
Kaocha's name form (replicated, its cases not drawn).
-/

namespace Replica.Junit

open Determinismo

/-! ## Text search, as std.mem's -/

def findFrom (hay needle : Array Char) (start : Nat) : Option Nat := Id.run do
  if needle.size == 0 then return some start
  let mut i := start
  while i + needle.size ≤ hay.size do
    if (hay.extract i (i + needle.size)) == needle then return some i
    i := i + 1
  return none

def findChar (hay : Array Char) (c : Char) (start : Nat) : Option Nat := Id.run do
  let mut i := start
  while i < hay.size do
    if hay[i]! == c then return some i
    i := i + 1
  return none

def arr (s : String) : Array Char := s.toList.toArray
def str (a : Array Char) : String := String.ofList a.toList

/-- junit.zig:58-63 `attribute`. -/
def attr (tag : Array Char) (key : String) : Option (Array Char) := do
  let marker := arr (" " ++ key ++ "=\"")
  let start := (← findFrom tag marker 0) + marker.size
  let stop ← findChar tag '"' start
  return tag.extract start stop

/-- junit.zig:65-83 `unescape`. -/
def unescape (s : String) : String := Id.run do
  let entities := [("&amp;", "&"), ("&lt;", "<"), ("&gt;", ">"), ("&quot;", "\""), ("&apos;", "'")]
  let a := arr s
  let mut out : Array Char := #[]
  let mut i := 0
  while i < a.size do
    let mut matched := false
    if a[i]! == '&' then
      for (e, r) in entities do
        if !matched && (a.extract i (i + e.length)) == arr e then
          out := out ++ arr r
          i := i + e.length
          matched := true
    if !matched then
      out := out.push a[i]!
      i := i + 1
  return str out

structure Case where
  name : String
  failed : Bool
  deriving Repr, BEq, Inhabited

def startsAt (a : Array Char) (i : Nat) (prefix_ : String) : Bool :=
  a.extract i (i + prefix_.length) == arr prefix_

/-- junit.zig:58-87 (62e06e3) `element_index`: where a case's body opens `opening`, outside its
`<system-out>`/`<system-err>` (each skipped to the first `</system-out>`/`</system-err>` after its
tag, whatever lies between) and any CDATA section (skipped to its first `]]>`). -/
def elementIndex (body : Array Char) (opening : String) : Option Nat := Id.run do
  let mut at_ := 0
  for _ in [0:body.size + 1] do
    let some next := findChar body '<' at_ | return none
    if startsAt body next "<![CDATA[" then
      let some e := findFrom body (arr "]]>") next | return none
      at_ := e + 3
      continue
    let mut skipped := false
    for captured in ["system-out", "system-err"] do
      if !skipped && startsAt body next ("<" ++ captured) then
        let some tagEnd := findChar body '>' next | return none
        if tagEnd > 0 && body[tagEnd - 1]! == '/' then
          at_ := tagEnd + 1
        else
          let close := "</" ++ captured ++ ">"
          let some e := findFrom body (arr close) tagEnd | return none
          at_ := e + close.length
        skipped := true
    if skipped then continue
    if startsAt body next opening then return some next
    at_ := next + 1
  return none

/-- junit.zig:11-55 `cases` (names and verdicts; the message left out). At 3939448 a case failed
when its body held the text `<failure` or `<error` anywhere (CE16); at 62e06e3 by `elementIndex`. -/
def cases (report : String) (ver : Ver := .v62e06e3) : List Case := Id.run do
  let r := arr report
  let mut out : Array Case := #[]
  let mut pos := 0
  for _ in [0:r.size + 1] do
    let some opn := findFrom r (arr "<testcase") pos | break
    let some tagEnd := findChar r '>' opn | break
    let tag := r.extract opn tagEnd
    let closed := tag.size > 0 && tag[tag.size - 1]! == '/'
    let mut body : Array Char := #[]
    pos := tagEnd + 1
    if !closed then
      let close := (findFrom r (arr "</testcase>") pos).getD r.size
      body := r.extract pos close
      pos := close
    let cls := (attr tag "classname").getD #[]
    let some named := attr tag "name" | continue
    -- Kaocha's `ns/var` beside the classname `ns` (junit.zig:30-31).
    let name := if cls.size > 0 && named.size > cls.size + 1 && named.extract 0 cls.size == cls && named[cls.size]! == '/'
      then named.extract (cls.size + 1) named.size else named
    let full := if cls.size > 0 then str cls ++ "::" ++ str name else str name
    let failure := if ver == .v3939448 then
        (findFrom body (arr "<failure") 0).isSome || (findFrom body (arr "<error") 0).isSome
      else (elementIndex body "<failure").isSome || (elementIndex body "<error").isSome
    out := out.push { name := unescape full, failed := failure }
  return out.toList

/-- assert_main.zig:43-51: each case an `always` named "test passes: <name>", true unless failed. -/
def assertions (report : String) (ver : Ver := .v62e06e3) : List (String × Bool) :=
  (cases report ver).map fun c => ("test passes: " ++ c.name, !c.failed)

/-! ## A test runner's report, drawn: what each test did, then its XML -/

/-- A test case's child elements (what the runner reports). -/
inductive Child where
  | failure | error | skipped
  /-- Its captured output, as text the runner escaped. -/
  | outText (text : String)
  /-- Its captured output in a CDATA section (as Surefire, jest-junit and go-junit-report write it). -/
  | outCdata (text : String)
  /-- Its captured standard error in a CDATA section. -/
  | errCdata (text : String)
  deriving Repr, BEq, Inhabited

structure TestCase where
  cls : String
  name : String
  children : List Child
  /-- The whitespace before `name=`: a space, or a line break (XML allows any). -/
  newlineBeforeName : Bool := false
  deriving Repr, Inhabited

def escapeText (s : String) : String :=
  (s.replace "&" "&amp;").replace "<" "&lt;" |>.replace ">" "&gt;"

def Child.render : Child → String
  | .failure => "<failure message=\"assert 1 == 2\">x</failure>"
  | .error => "<error message=\"boom\">y</error>"
  | .skipped => "<skipped message=\"no\"/>"
  | .outText t => "<system-out>" ++ escapeText t ++ "</system-out>"
  | .outCdata t => "<system-out><![CDATA[" ++ t ++ "]]></system-out>"
  | .errCdata t => "<system-err><![CDATA[" ++ t ++ "]]></system-err>"

def TestCase.render (c : TestCase) : String :=
  let sep := if c.newlineBeforeName then "\n    " else " "
  let head := "<testcase classname=\"" ++ c.cls ++ "\"" ++ sep ++ "name=\"" ++ c.name ++ "\" time=\"0.1\""
  if c.children.isEmpty then head ++ " />"
  else head ++ ">" ++ String.join (c.children.map Child.render) ++ "</testcase>"

def render (cs : List TestCase) : String :=
  "<?xml version=\"1.0\" encoding=\"utf-8\"?><testsuites><testsuite name=\"suite\">\n" ++
  String.intercalate "\n" (cs.map TestCase.render) ++ "\n</testsuite></testsuites>"

/-- The documented verdict of a test case: failed when it holds a failure or an error element. -/
def TestCase.failedSpec (c : TestCase) : Bool := c.children.any fun | .failure | .error => true | _ => false

structure JS where
  decisions : Decisions := {}
  deriving Inhabited

instance : Chaotic JS where
  decisions s := s.decisions
  setDecisions _ d := { decisions := d }

structure JWorld where
  label : String
  cases : Nat := 2
  childMenu : List Child
  childrenMax : Nat := 2
  layouts : Bool := false

def drawReport (wd : JWorld) : EStateM Stop JS (List TestCase) := do
  let mut out := []
  for i in [0:wd.cases] do
    let n ← below "world.children" (wd.childrenMax + 1)
    let mut children := []
    for _ in [0:n] do children := children ++ [wd.childMenu[(← below "world.child" wd.childMenu.length)]!]
    let newline ← if wd.layouts then pure ((← below "world.layout" 2) == 1) else pure false
    out := out ++ [{ cls := "tests.test_app", name := s!"test_{i}", children, newlineBeforeName := newline }]
  return out

structure JProp where
  name : String
  source : String
  check : List TestCase → Option String

def verdictsAsReported : JProp :=
  { name := "a test fails exactly when its test case holds a failure or an error (skipped ones pass)"
    source := "guest/runtime/junit.zig:2-6: \"each `<testcase>`'s classname and name, whether it holds a `<failure>` or an `<error>` (skipped ones pass)\"; assert_main.zig:7-10; docs/CI.md (Verdicts per test; `junit`)"
    check := fun cs => Id.run do
      let said := cases (render cs)
      for c in cs do
        let full := c.cls ++ "::" ++ c.name
        match said.find? (·.name == full) with
        | some s =>
          if s.failed != c.failedSpec then
            return some s!"{full}: reported {if c.failedSpec then "failing" else "passing"} ({reprStr c.children}), judged {if s.failed then "failing" else "passing"}"
        | none => pure ()
      return none }

def everyCaseATest : JProp :=
  { name := "every test case of the report is a test of its own"
    source := "docs/CI.md (Verdicts per test): \"each test is a property of its own in each timeline (`det-assert junit`)\"; junit.zig:2: \"each `<testcase>`'s classname and name\""
    check := fun cs =>
      let said := (cases (render cs)).map (·.name)
      match cs.find? fun c => !said.contains (c.cls ++ "::" ++ c.name) with
      | some c => some s!"{c.cls}::{c.name} is in the report and no test ({if c.newlineBeforeName then "a line break before its name attribute" else "?"}); tests judged: {said}"
      | none => none }

def allJProps : List JProp := [verdictsAsReported, everyCaseATest]

def judgeJ (p : JProp) (wd : JWorld) (source : Source) : Ended :=
  match (drawReport wd).run { decisions := { source } } with
  | .ok cs s => { taken := s.decisions.taken, violation := (p.check cs).map fun d => (p.name, d) }
  | .error _ s => { taken := s.decisions.taken, violation := none }

def jstory (wd : JWorld) (source : Source) : List String :=
  match (drawReport wd).run { decisions := { source } } with
  | .ok cs _ => ["the report:"] ++ ((render cs).splitOn "\n") ++
      ["det-assert junit states:"] ++ ((assertions (render cs)).map fun (m, c) => s!"  always({c}) \"{m}\"")
  | .error _ _ => []

def jworlds : List JWorld :=
  [ { label := "two cases, failures, errors and skips",
      childMenu := [.failure, .error, .skipped] },
    { label := "two cases, failures, skips and captured output (escaped or CDATA) that mentions an error element",
      childMenu := [.failure, .skipped, .outText "<error code=\"503\"/>", .outCdata "<error code=\"503\"/>",
                    .outCdata "plain output"] },
    { label := "two cases, attribute layouts (a space or a line break before name)",
      childMenu := [.failure, .skipped], layouts := true },
    -- Round 5 (62e06e3's element_index): captured output in CDATA holding the closing tag of
    -- its own element (a test printing JUnit XML: a reporter's or a CI tool's own tests).
    { label := "two cases, failures, skips and captured output in CDATA that prints a closing system-out or system-err tag",
      childMenu := [.failure, .skipped, .outCdata "<error code=\"503\"/>",
                    .outCdata "</system-out><error code=\"503\"/>", .errCdata "</system-err><failure message=\"x\"/>"] } ]

/-! ## The shard's run command through xargs (ci.zig:226-233) -/

/-- GNU xargs's batches: as many arguments a batch as fit its command buffer (`-s`, 131,072
bytes by default), each argument counted with its terminating NUL, after the command's own
words (`sh -c '<run>' sh`). A batch is one run of the command. -/
def xargsBatches (buffer base : Nat) (names : List String) : List (List String) := Id.run do
  let mut batches : List (List String) := []
  let mut current : List String := []
  let mut used := base
  for n in names do
    if !current.isEmpty && used + n.length + 1 > buffer then
      batches := batches ++ [current]
      current := []
      used := base
    current := current ++ [n]
    used := used + n.length + 1
  if !current.isEmpty then batches := batches ++ [current]
  return batches

/-- What `det-assert junit` reads once the command ended: the report the last run of the runner
wrote at the `junit` path (each run writes it anew: pytest's `--junitxml`, jest-junit). -/
def testsJudged (buffer base : Nat) (shard : List String) : List String :=
  match (xargsBatches buffer base shard).getLast? with
  | some last => last
  | none => []

end Replica.Junit

namespace Replica.Junit

open Determinismo

/-- A shard's tests drawn: how many, each name's length (bytes). -/
structure XWorld where
  label : String
  testsMax : Nat := 4
  lengths : List Nat := [5, 12, 20]
  buffer : Nat := 48
  base : Nat := 16

def drawShard (wd : XWorld) : EStateM Stop JS (List String) := do
  let n := 1 + (← below "world.tests" wd.testsMax)
  let mut names := []
  for i in [0:n] do
    let len := wd.lengths[(← below "world.name_length" wd.lengths.length)]!
    let stem := s!"t{i}_"
    names := names ++ [stem ++ String.ofList (List.replicate (len - min len stem.length) 'x')]
  return names

def everyShardTestJudged : String := "every test of a shard is judged in the shard's timelines"
def everyShardTestJudgedSource : String :=
  "docs/CI.md (`junit`): \"each test gets its own verdict across its shard's timelines\"; (`run`): \"`{tests}` (the shard's names, as arguments: its part of the list ...)\""

def judgeX (wd : XWorld) (source : Source) : Ended :=
  match (drawShard wd).run { decisions := { source } } with
  | .ok names s =>
    let judged := testsJudged wd.buffer wd.base names
    let lost := names.filter (!judged.contains ·)
    { taken := s.decisions.taken,
      violation := if lost.isEmpty then none
        else some (everyShardTestJudged, s!"{names.length} tests in the shard, {(xargsBatches wd.buffer wd.base names).length} runs of the runner (xargs's buffer {wd.buffer} bytes): {lost.length} never judged: {lost}") }
  | .error _ s => { taken := s.decisions.taken, violation := none }

def xstory (wd : XWorld) (source : Source) : List String :=
  match (drawShard wd).run { decisions := { source } } with
  | .ok names _ =>
    let batches := xargsBatches wd.buffer wd.base names
    [s!"the shard's names: {names}"] ++
    (batches.zipIdx.map fun (b, i) => s!"run {i + 1} of the runner: {b} (its report written at the junit path)") ++
    [s!"det-assert junit reads the last: {testsJudged wd.buffer wd.base names}"]
  | .error _ _ => []

def searchAll (exhaustRuns : Nat) : IO (List Found) := do
  let mut found := []
  for p in allJProps do
    say s!"== junit property: {p.name}"
    say s!"   source: {p.source}"
    for wd in jworlds do
      if let some f ← exhaustSaid s!"{p.name} / {wd.label}" (judgeJ p wd) exhaustRuns then
        printFound f (jstory wd)
        found := found ++ [f]
  say s!"== ci property: {everyShardTestJudged}"
  say s!"   source: {everyShardTestJudgedSource}"
  let xw : XWorld := { label := "up to four tests, names of 5 to 20 bytes, an xargs buffer of 48 bytes" }
  if let some f ← exhaustSaid s!"{everyShardTestJudged} / {xw.label}" (judgeX xw) exhaustRuns then
    printFound f (xstory xw)
    found := found ++ [f]
  return found

end Replica.Junit

namespace Replica.Junit

/-- src/products/ci.zig:446-470 `tests_judge`'s count of timelines without their JUnit report, for
one run: `timelines -| reported`, `reported` the most timelines any test property was hit in,
over every shard's tests. `hits`: each test property's `timelines_hit`. -/
def unreportedTimelines (timelines : Nat) (hits : List Nat) : Nat :=
  timelines - hits.foldl max 0

end Replica.Junit
