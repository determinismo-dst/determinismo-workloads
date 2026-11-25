import Determinismo

/-!
# Round 4, CLI: `jank`'s argument parser against its documented options

jank 7135b7708: `util/cli.cpp` `check_flag` (13–53; a short flag matches any argument that
**starts with** it), `get_positional_arg` (64–77), `check_pending_flag` (79–92), `show_help`
(94–169, ends with `std::exit(1)`), `commit_scratchpad` (203–225), `parse_opts` (227–568), in
its order of tests; `include/cpp/jank/util/cli.hpp` (the defaults: `command::repl`,
`compilation_runtime::static_`, `output_filename "a.out"`, `target_dir "target"`,
`output_target unspecified`, `debug true`, `eagerness lazy`); `main.cpp` 199–301 (what runs
per command).

The spec is jank's own documentation: the `--help` text (cli.cpp 100–166), the book's
"Differences from Clojure / Command line" (`--` separates the program's arguments) and the
build-cache page (target `target`, build directory `target/_cache`).
-/

namespace Jank.R4.Modules.Cli

open Determinismo

inductive Cmd where
  | run | compile | compileModule | repl | cppRepl | runMain | checkHealth | printBinaryVersion
  | printCflags | help
  deriving Repr, BEq, Inhabited

def cmdOf : String → Option Cmd
  | "run" => some .run | "run-main" => some .runMain | "repl" => some .repl
  | "cpp-repl" => some .cppRepl | "compile" => some .compile | "compile-module" => some .compileModule
  | "check-health" => some .checkHealth | "print-binary-version" => some .printBinaryVersion
  | "print-cflags" => some .printCflags | "help" => some .help | _ => none

inductive Target where | unspecified | cpp | object
  deriving Repr, BEq, Inhabited

structure Opts where
  modulePath : String := ""
  profilerFile : String := "jank.profile"
  profiler : Bool := false
  perf : Bool := false
  gcIncremental : Bool := false
  includeDirs : List String := []
  libraryDirs : List String := []
  defineMacros : List String := []
  libs : List String := []
  frameworks : List String := []
  debug : Bool := true
  runtimeOpt : Nat := 0
  codegenOpt : Nat := 0
  hoistLiterals : Bool := false
  removeNops : Bool := false
  hoistVarDerefs : Bool := false
  directCall : Bool := false
  eager : Bool := false
  dynamicRuntime : Bool := false
  targetFile : String := ""
  targetModule : String := ""
  outputFilename : String := "a.out"
  targetDir : String := "target"
  buildDir : String := ""
  forcedBinaryVersion : String := ""
  outputModuleFilename : String := ""
  outputTarget : Target := .unspecified
  replPort : Nat := 0
  extraOpts : List String := []
  command : Cmd := .repl
  deriving Repr, BEq, Inhabited

/-- How a parse ended. `warned` lists the unused flags (cli.cpp 534–547). -/
inductive Parsed where
  | ok (o : Opts) (warned : List String)
  | err (msg : String)
  /-- `show_help` printed the help and called `std::exit(1)`. -/
  | help (status : Nat)
  deriving Repr, BEq, Inhabited

structure Scratch where
  runtimeOpt : Option Nat := none
  codegenOpt : Option Nat := none
  buildDir : Option String := none
  forcedBinaryVersion : Option String := none
  hoistLiterals : Option Bool := none
  removeNops : Option Bool := none
  hoistVarDerefs : Option Bool := none
  directCall : Option Bool := none
  deriving Inhabited

/-- `check_flag` (13–53): returns (matched, value, args consumed after the flag). -/
def checkFlag (args : List String) (short long : String) (needsValue : Bool) :
    Except String (Option (String × List String)) :=
  match args with
  | [] => .ok none
  | a :: rest =>
    if a == long then
      if needsValue then
        match rest with
        | [] => .error s!"The '{long}' flag requires an argument, but one was not provided."
        | v :: rest' => .ok (some (v, rest'))
      else .ok (some ("", rest))
    else if short != "" && a.startsWith short then
      if needsValue then
        let v := (a.drop short.length).toString
        if v == "" then
          match rest with
          | [] => .error s!"The '{short}' flag requires an argument, but one was not provided."
          | v' :: rest' => .ok (some (v', rest'))
        else .ok (some (v, rest))
      else .ok (some ("", rest))
    else .ok none

/-- `std::stoi` with `parsed_upto == size` (401–416): optional leading whitespace and sign,
then decimal digits, nothing after. -/
def stoiExact (s : String) : Option Int :=
  let cs := s.toList.dropWhile (· == ' ')
  let (neg, ds) := match cs with
    | '-' :: r => (true, r) | '+' :: r => (false, r) | r => (false, r)
  if ds.isEmpty || !ds.all Char.isDigit then none
  else
    let n := ds.foldl (fun acc c => acc * 10 + (c.toNat - '0'.toNat)) 0
    if n > 2147483647 + (if neg then 1 else 0) then none  -- stoi throws out_of_range
    else some (if neg then -(n : Int) else n)

/-- The optimization pass flags (194–200). -/
def passes : List String := ["hoist-literals", "remove-nops", "hoist-var-derefs", "direct-call"]

def setPass (s : Scratch) (p : String) (v : Bool) : Scratch :=
  match p with
  | "hoist-literals" => { s with hoistLiterals := some v }
  | "remove-nops" => { s with removeNops := some v }
  | "hoist-var-derefs" => { s with hoistVarDerefs := some v }
  | _ => { s with directCall := some v }

/-- `commit_scratchpad` (203–225). -/
def commit (o : Opts) (s : Scratch) : Opts :=
  let o := { o with runtimeOpt := s.runtimeOpt.getD 0, codegenOpt := s.codegenOpt.getD 0,
                    directCall := s.directCall.getD false,
                    buildDir := s.buildDir.getD (o.targetDir ++ "/_cache"),
                    forcedBinaryVersion := s.forcedBinaryVersion.getD "" }
  let o := if o.codegenOpt == 3 then { o with hoistVarDerefs := s.hoistVarDerefs.getD true } else o
  if o.codegenOpt ≥ 1 then { o with hoistLiterals := s.hoistLiterals.getD true, removeNops := s.removeNops.getD true } else o

/-- The parser's state between arguments. -/
structure PState where
  o : Opts := {}
  s : Scratch := {}
  pendingFlags : List (String × String) := []
  positional : List String := []
  command : String := ""
  deriving Inhabited

/-- The sentinel `show_help` raises (it prints and calls `std::exit(1)`). -/
def helpSentinel : String := "@help"

/-- The flag checks of one loop iteration (296–437), in the file's order. `none`: not a flag. -/
def tryFlags (args : List String) (st : PState) : Except String (Option (PState × List String)) := do
  let o := st.o
  let s := st.s
  let flagV (short long : String) := checkFlag args short long true
  let flag (short long : String) := checkFlag args short long false
  if let some _ ← flag "-h" "--help" then throw helpSentinel
  if let some (v, r) ← flagV "" "--module-path" then return some ({ st with o := { o with modulePath := v } }, r)
  if let some (_, r) ← flag "" "--profile" then return some ({ st with o := { o with profiler := true } }, r)
  if let some (v, r) ← flagV "" "--profile-output" then return some ({ st with o := { o with profilerFile := v } }, r)
  if let some (_, r) ← flag "" "--perf" then return some ({ st with o := { o with perf := true } }, r)
  if let some (_, r) ← flag "" "--no-debug" then return some ({ st with o := { o with debug := false } }, r)
  if let some (v, r) ← flagV "-O" "--optimization" then
    match v with
    | "0" => return some ({ st with s := { s with codegenOpt := some 0 } }, r)
    | "1" => return some ({ st with s := { s with codegenOpt := some 1 } }, r)
    | "2" => return some ({ st with s := { s with codegenOpt := some 2 } }, r)
    | "3" => return some ({ st with s := { s with codegenOpt := some 3 } }, r)
    | _ => throw s!"Invalid optimization level '{v}'."
  if let some (_, r) ← flag "" "--eager" then return some ({ st with o := { o with eager := true } }, r)
  if let some (_, r) ← flag "" "--lazy" then return some ({ st with o := { o with eager := false } }, r)
  if let some (v, r) ← flagV "" "--runtime" then
    if v == "static" then return some ({ st with o := { o with dynamicRuntime := false } }, r)
    else if v == "dynamic" then return some ({ st with o := { o with dynamicRuntime := true } }, r)
    else throw s!"Invalid runtime type '{v}'."
  if let some (v, r) ← flagV "-I" "--include-dir" then return some ({ st with o := { o with includeDirs := o.includeDirs ++ [v] } }, r)
  if let some (v, r) ← flagV "-D" "--define-macro" then return some ({ st with o := { o with defineMacros := o.defineMacros ++ [v] } }, r)
  if let some (v, r) ← flagV "-L" "--library-dir" then return some ({ st with o := { o with libraryDirs := o.libraryDirs ++ [v] } }, r)
  if let some (v, r) ← flagV "-l" "--link" then return some ({ st with o := { o with libs := o.libs ++ [v] } }, r)
  if let some (v, r) ← flagV "" "--framework" then return some ({ st with o := { o with frameworks := o.frameworks ++ [v] } }, r)
  if let some (v, r) ← flagV "" "--target-dir" then return some ({ st with o := { o with targetDir := v } }, r)
  if let some (v, r) ← flagV "" "--build-dir" then return some ({ st with s := { s with buildDir := some v } }, r)
  if let some (v, r) ← flagV "" "--force-binary-version" then return some ({ st with s := { s with forcedBinaryVersion := some v } }, r)
  if let some (v, r) ← flagV "-p" "--port" then
    match stoiExact v with
    | none => throw s!"Could not parse port: '{v}'."
    | some n =>
      if n > 65535 || n < 0 then throw s!"Port out of range [0...65,535]: '{v}'."
      else return some ({ st with o := { o with replPort := n.toNat } }, r)
  -- Command-specific flags, kept until the command is known (427–438); the map keeps one value.
  if let some (v, r) ← flagV "" "--name" then
    return some ({ st with pendingFlags := (st.pendingFlags.filter (·.1 != "--name")) ++ [("--name", v)] }, r)
  if let some (v, r) ← flagV "" "--output-target" then
    return some ({ st with pendingFlags := (st.pendingFlags.filter (·.1 != "--output-target")) ++ [("--output-target", v)] }, r)
  return none

/-- Take a pending flag (79–92). -/
def takePending (st : PState) (k : String) : Option String × PState :=
  match st.pendingFlags.lookup k with
  | some v => (some v, { st with pendingFlags := st.pendingFlags.filter (·.1 != k) })
  | none => (none, st)

/-- `get_positional_arg` (64–77). -/
def takePositional (st : PState) (command name : String) : Except String (String × PState) :=
  match st.positional with
  | [] => .error s!"Please provide the {command} command a {name}."
  | p :: ps => .ok (p, { st with positional := ps })

/-- The loop (263–453): returns the state after every argument, or an error / help. -/
def scan : List String → PState → Nat → Except String PState
  | [], st, _ => .ok st
  | _, st, 0 => .ok st
  | a :: tl, st, fuel + 1 =>
    if a == "--" then .ok { st with o := { st.o with extraOpts := st.o.extraOpts ++ tl } }
    else
      match passes.find? (fun p => a == s!"-O{p}" || a == s!"-Ono-{p}") with
      | some p => scan tl { st with s := setPass st.s p (a == s!"-O{p}") } fuel
      | none =>
        match tryFlags (a :: tl) st with
        | .error e => .error e
        | .ok (some (st', r)) => scan r st' fuel
        | .ok none =>
          if st.command == "" then
            match cmdOf a with
            | none => .error s!"Invalid command '{a}'."
            | some c => scan tl { st with command := a, o := { st.o with command := c } } fuel
          else scan tl { st with positional := st.positional ++ [a] } fuel

/-- `parse_opts` (227–568). -/
def parse (args : List String) : Parsed :=
  match scan args {} (args.length + 1) with
  | .error e => if e == helpSentinel then .help 1 else .err e
  | .ok st0 =>
    let st0 := if st0.command == "" then { st0 with command := "repl" } else st0
    let cmd := st0.command
    let r : Except String PState := do
      let mut st := st0
      if cmd == "run" then
        let (f, st') ← takePositional st cmd "file"
        st := { st' with o := { st'.o with targetFile := f } }
      else if cmd == "run-main" then
        let (m, st') ← takePositional st cmd "module"
        st := { st' with o := { st'.o with targetModule := m } }
      else if cmd == "repl" then
        if !st.positional.isEmpty then
          let (m, st') ← takePositional st cmd "module"
          st := { st' with o := { st'.o with targetModule := m } }
      else if cmd == "compile-module" || cmd == "compile" then
        let (m, st') ← takePositional st cmd "module"
        st := { st' with o := { st'.o with targetModule := m } }
        let (ot, st'') := takePending st "--output-target"
        st := st''
        if let some v := ot then
          if v == "cpp" then st := { st with o := { st.o with outputTarget := .cpp } }
          else if v == "object" then st := { st with o := { st.o with outputTarget := .object } }
          else throw s!"Invalid output type '{v}'."
        let (rt, st3) := takePending st "--runtime"
        st := st3
        if let some v := rt then st := { st with o := { st.o with targetFile := v } }
        if cmd == "compile" && st.o.outputTarget == .unspecified then
          st := { st with o := { st.o with outputTarget := .object } }
      else if cmd == "help" then
        throw helpSentinel
      let (nm, st4) := takePending st "--name"
      st := st4
      if let some v := nm then
        if (v.splitOn "/").length > 1 then throw "The argument to --name must be a file name, not a directory."
        if cmd == "compile-module" then st := { st with o := { st.o with outputModuleFilename := v } }
        else st := { st with o := { st.o with outputFilename := v } }
      if cmd == "run" || cmd == "run-main" || cmd == "repl" then
        st := { st with s := { st.s with runtimeOpt := st.s.codegenOpt } }
      if !st.pendingFlags.isEmpty then pure st   -- warned (534–547); positional args left unchecked
      else if !st.positional.isEmpty then throw s!"Extra positional args: {" ".intercalate st.positional}"
      else pure st
    match r with
    | .error e => if e == helpSentinel then .help 1 else .err e
    | .ok st => .ok (commit st.o st.s) (st.pendingFlags.map (·.1))

/-! ## The documented behavior (the spec)

From `--help` and the book: each documented option is accepted before or after the command;
an argument that starts with `-` and is not a documented option is an error; the first other
argument is the command; `run` takes a file, `run-main`, `compile` and `compile-module` a module,
`repl` an optional module, the others nothing; more positional arguments are an error; after `--`
everything goes to the program; `help`/`-h` print the help and exit successfully;
`--gc-incremental` enables incremental collection. Option values are compared where the
documentation names them. -/

structure Spec where
  command : Cmd := .repl
  file : String := ""
  module : String := ""
  gcIncremental : Bool := false
  codegenOpt : Nat := 0
  modulePath : String := ""
  extra : List String := []
  outputTarget : Target := .unspecified
  name : Option String := none
  dynamicRuntime : Bool := false
  deriving Repr, BEq, Inhabited

inductive SpecParsed where
  | ok (s : Spec)
  | err
  | help
  deriving Repr, BEq, Inhabited

/-- The documented options: (name, takes a value). Short forms take an attached value too. -/
def documented : List (String × Bool) :=
  [("-h", false), ("--help", false), ("--module-path", true), ("-p", true), ("--port", true),
   ("--profile", false), ("--profile-output", true), ("--perf", false), ("--gc-incremental", false),
   ("--no-debug", false), ("-O", true), ("--optimization", true), ("-Odirect-call", false),
   ("--eager", false), ("--lazy", false), ("--runtime", true), ("--target-dir", true),
   ("--build-dir", true), ("--force-binary-version", true), ("--name", true),
   ("--output-target", true), ("-I", true), ("--include-dir", true), ("-D", true),
   ("--define-macro", true), ("-L", true), ("--library-dir", true), ("-l", true),
   ("--framework", true)]

def shortWithValue : List String := ["-p", "-O", "-I", "-D", "-L", "-l"]

def specParse (args : List String) : SpecParsed := Id.run do
  let mut sp : Spec := {}
  let mut command : Option Cmd := none
  let mut pos : List String := []
  let mut rest := args
  let mut fuel := args.length + 1
  while fuel > 0 do
    fuel := fuel - 1
    match rest with
    | [] => fuel := 0
    | a :: tl =>
      if a == "--" then sp := { sp with extra := tl }; rest := []; fuel := 0
      else if a == "-h" || a == "--help" then return .help
      else if a.startsWith "-" && a.length > 1 then
        -- a documented long or short option, or an attached short value
        match documented.lookup a with
        | some true =>
          match tl with
          | [] => return .err
          | v :: tl' =>
            if a == "--module-path" then sp := { sp with modulePath := v }
            else if a == "-O" || a == "--optimization" then
              match v.toNat? with
              | some n => if n ≤ 3 && v.length == 1 then sp := { sp with codegenOpt := n } else return .err
              | none => return .err
            else if a == "--output-target" then
              if v == "cpp" then sp := { sp with outputTarget := .cpp }
              else if v == "object" then sp := { sp with outputTarget := .object } else return .err
            else if a == "--name" then
              if (v.splitOn "/").length > 1 then return .err
              sp := { sp with name := some v }
            else if a == "--runtime" then
              if v == "dynamic" then sp := { sp with dynamicRuntime := true }
              else if v != "static" then return .err
            else if a == "-p" || a == "--port" then
              match v.toNat? with
              | some n => if n > 65535 then return .err
              | none => return .err
            rest := tl'
        | some false =>
          if a == "--gc-incremental" then sp := { sp with gcIncremental := true }
          rest := tl
        | none =>
          match shortWithValue.find? (a.startsWith ·) with
          | some f =>
            let v := (a.drop f.length).toString
            if f == "-O" then
              match v.toNat? with
              | some n => if n ≤ 3 && v.length == 1 then sp := { sp with codegenOpt := n } else return .err
              | none => return .err
            else if f == "-p" then
              match v.toNat? with
              | some n => if n > 65535 then return .err
              | none => return .err
            rest := tl
          | none => return .err
      else
        match command with
        | none =>
          match cmdOf a with
          | none => return .err
          | some c => command := some c
        | some _ => pos := pos ++ [a]
        rest := tl
  let c := command.getD .repl
  if c == .help then return .help
  let need : Nat × Nat := match c with
    | .run | .runMain | .compile | .compileModule => (1, 1)
    | .repl => (0, 1)
    | _ => (0, 0)
  if pos.length < need.1 || pos.length > need.2 then return .err
  let sp1 := { sp with command := c }
  let sp2 := match c with
    | .run => { sp1 with file := pos.headD "" }
    | .runMain | .compile | .compileModule | .repl => { sp1 with module := pos.headD "" }
    | _ => sp1
  return .ok sp2

/-- Project jank's parse onto the documented fields. -/
def project : Parsed → SpecParsed
  | .err _ => .err
  | .help _ => .help
  | .ok o _ =>
    .ok { command := o.command, file := if o.command == .run then o.targetFile else "",
          module := match o.command with
            | .runMain | .compile | .compileModule | .repl => o.targetModule | _ => "",
          gcIncremental := o.gcIncremental, codegenOpt := o.codegenOpt, modulePath := o.modulePath,
          extra := o.extraOpts,
          outputTarget := if o.command == .compile || o.command == .compileModule then o.outputTarget else .unspecified,
          name := if o.outputModuleFilename != "" then some o.outputModuleFilename
                  else if o.outputFilename != "a.out" then some o.outputFilename else none,
          dynamicRuntime := o.dynamicRuntime }

/-- The spec projected the same way (`--output-target` only matters to the compile commands;
`--name a.out` is the default). -/
def specProject : SpecParsed → SpecParsed
  | .ok sp =>
    let ot : Target :=
      if sp.command == .compile || sp.command == .compileModule then
        (if sp.command == .compile && sp.outputTarget == .unspecified then .object else sp.outputTarget)
      else .unspecified
    let nm : Option String := if sp.name == some "a.out" then none else sp.name
    .ok { sp with outputTarget := ot, name := nm }
  | r => r

/-! ## The search world: argument lists over a token alphabet -/

def tokens : List (List String) :=
  [["run"], ["run-main"], ["compile"], ["compile-module"], ["repl"], ["help"], ["check-health"],
   ["f.jank"], ["app.core"], ["x"],
   ["--"], ["-h"], ["--gc-incremental"], ["-O2"], ["-O", "3"], ["-O9"], ["--module-path", "src"],
   ["--name", "out.cpp"], ["--output-target", "cpp"], ["--runtime", "dynamic"], ["-Isrc"],
   ["-Ono-hoist-literals"], ["--frob"], ["-hello"], ["-p", "80"]]

structure CW where
  decisions : Decisions

instance : Chaotic CW where
  decisions w := w.decisions
  setDecisions w d := { w with decisions := d }

/-- Drop a command flag and its value from an argument list. -/
def dropFlag (args : List String) (f : String) : List String :=
  match args with
  | [] => []
  | a :: v :: rest => if a == f then dropFlag rest f else a :: dropFlag (v :: rest) f
  | [a] => if a == f then [] else [a]

def classifyCli (args : List String) (j : SpecParsed) (sp : SpecParsed) : String :=
  let isErr (x : Parsed) := match x with | .err _ => true | _ => false
  if args.contains "--gc-incremental" then
    "F12 --gc-incremental (documented) is not parsed"
  else if args.any (fun a => a.startsWith "-h") && (match j with | .help => true | _ => false) then
    "help: jank exits 1 (and any argument starting with -h is -h)"
  else if args.any (fun a => a.startsWith "-Ono-" || a == "-Ohoist-literals") then
    "extension: undocumented -O<pass>/-Ono-<pass> flags accepted"
  else if args.contains "--frob" then
    "undocumented flag: jank takes it as a command or positional"
  else if (match sp, j with | .err, .ok _ => true | _, _ => false) &&
          (isErr (parse (dropFlag (dropFlag args "--name") "--output-target"))) then
    "F13 an unused command flag silences the extra-positional error"
  else "unexplained"

def cliBody (maxLen : Nat) : EStateM Stop CW Unit := do
  let n ← decide "len" (maxLen + 1)
  let mut args : List String := []
  for i in [0:n] do
    let t ← decide s!"tok{i}" tokens.length
    args := args ++ tokens[t]!
  let j := parse args
  let jp := project j
  let sp := specProject (specParse args)
  -- help: both print the help; jank's status is 1 (show_help's std::exit(1)).
  let agree := match jp, sp with
    | .help, .help => true
    | .err, .err => true
    | .ok a, .ok b => a == b
    | _, _ => false
  if !agree then
    violate (classifyCli args jp sp) s!"jank {args}: jank {repr j}; documented {repr sp}"

def cliRun (maxLen : Nat) (source : Source) : Ended :=
  match (cliBody maxLen).run { decisions := { source } } with
  | .ok _ w => { taken := w.decisions.taken, violation := none }
  | .error (.violation p d) w => { taken := w.decisions.taken, violation := some (p, d) }
  | .error .limit w => { taken := w.decisions.taken, violation := none }
  | .error (.nodeDown _) w => { taken := w.decisions.taken, violation := none }

end Jank.R4.Modules.Cli
