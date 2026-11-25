import Jank.Codegen.Processor

/-!
# Which optimizer runs on jank's emitted C++, and with which language rules

Replicas (jank 7135b7708, paths under `upstream-main/compiler+runtime/`):

- `util/cli.cpp` `parse_opts` 324-341 (`-O`/`--optimization` sets `codegen_optimization_level`),
  527-531 (`run`, `run-main`, `repl` copy it into `runtime_optimization_level`),
  `commit_scratchpad` 203-226 (both default to 0; the IR passes per codegen level);
- `CMakeLists.txt` 86-111 (`jank_aot_compiler_flags`, `jank_common_compiler_flags`), 140-147 (the
  build type's flags), 339-349 (`jank_jit_compiler_flags`: `-w -fwrapv -fno-stack-protector
  -fPIC ...`), 719-729 (`JANK_JIT_FLAGS` = common ++ jit ++ includes; `JANK_AOT_FLAGS` = the
  linker flags);
- `jit/processor_dynamic.cpp` 165-298 (the JIT's clang arguments: `-g`, includes,
  `JANK_JIT_FLAGS`, `-include-pch`, `-w -Wno-c++11-narrowing`, system flags, user `-I -L -D
  -framework`, then `-O<runtime level>`; `-g` removed without `--debug`);
- `aot/processor.cpp` `build_compiler_args` 167-319 (includes, `JANK_JIT_FLAGS`, `JANK_AOT_FLAGS`,
  `JANK_EXTRA_FLAGS`, user flags, `-g` or strip, `-std=c++20`, then `-O<codegen level>`) and
  `util/clang.cpp` `invoke_clang` 161-197 (system flags first, `JANK_EXTRA_FLAGS` once more last);
- `codegen/optimize.cpp` `optimize` 15-64 builds `buildPerModuleDefaultPipeline(level)` from the
  codegen level, but nothing calls it at 7135b7708 (`context.cpp:21` and `context_dynamic.cpp:27`
  include its header only): the LLVM pipeline that runs is clang's own for the `-O` it was given.
- `analyze/pass/optimize.cpp` 13-22: the only AST pass is `strip_source_meta`.

Clang (llvmorg-23.1.0, files under `deps/llvm-23.1.0-codegen/`): the last `-O` wins (`-Og` is
level 1); `-fwrapv` makes `+ - *` on signed integers wrap (no `nsw`), and nothing else defined;
C++11 and later functions get `mustprogress` and a `while(true){…}` loop with a non-empty body is
`llvm.loop.mustprogress` (`CGStmt.cpp` `checkIfLoopMustProgress` 1009-1048; only a trivially empty
body is exempt); the JIT (clang's `Interpreter`, `IncrementalAction` → `EmitLLVMOnlyAction`) runs
`BackendConsumer::HandleTranslationUnit` → `emitBackendOutput` → `RunOptimizationPipeline`
(`CodeGenAction.cpp` 322, `BackendUtil.cpp` 1364, 1138: `buildPerModuleDefaultPipeline(Level)`)
on every incremental module, so JIT code gets the same middle end as AOT code.
-/

namespace Jank.R3.Codegen

/-- A clang command-line argument, by the kinds that matter for the meaning of the code. -/
inductive Flag where
  | opt (n : Nat)
  /-- `-Og`: clang's optimization level 1. -/
  | optG
  | std (s : String)
  | fwrapv
  | noStrictOverflow
  | finiteLoops (on : Bool)
  | strictFloatCastOverflow (on : Bool)
  | strictAliasing (on : Bool)
  | warnNone
  | noNarrowingError
  | define (s : String)
  | include (s : String)
  | libDir (s : String)
  | debugInfo
  | other (s : String)
  deriving Repr, DecidableEq, Inhabited

/-- `CMAKE_BUILD_TYPE` (CMakeLists.txt 140-147). -/
inductive BuildType where
  | debug | release | relWithDebInfo | none
  deriving Repr, BEq, DecidableEq, Inhabited

/-- jank's commands (cli.cpp 226-236). -/
inductive Command where
  | run | runMain | repl | compile | compileModule | other
  deriving Repr, BEq, DecidableEq, Inhabited

/-- What the command line says (only what matters here). -/
structure Cli where
  command : Command := .run
  /-- `-O <n>`, if given (cli.cpp 324-341 accepts 0..3). -/
  opt : Option Nat := none
  debug : Bool := true
  defines : List String := []
  includes : List String := []
  libDirs : List String := []
  deriving Repr, Inhabited

/-- The two levels after `commit_scratchpad` (cli.cpp 203-206, 527-531). -/
structure Levels where
  runtime : Nat
  codegen : Nat
  deriving Repr, BEq, DecidableEq

def Cli.levels (c : Cli) : Levels :=
  let scratchCodegen := c.opt
  let scratchRuntime : Option Nat := match c.command with
    | .run | .runMain | .repl => scratchCodegen
    | _ => none
  { runtime := scratchRuntime.getD 0, codegen := scratchCodegen.getD 0 }

/-- The IR passes (cli.cpp 213-225: case 3 falls through to 2 and 1). -/
def Cli.irPasses (c : Cli) : Jank.Codegen.Passes := Jank.Codegen.Passes.ofLevel c.levels.codegen

/-- `jank_common_compiler_flags` (CMakeLists.txt 105-147, 274, 317-322) for a build type. -/
def commonFlags (bt : BuildType) : List Flag :=
  [.std "gnu++20", .define "JANK_VERSION", .define "JANK_CMAKE_BUILD_TYPE", .other "-femulated-tls",
   .define "GC_THREADS", .define "POINTER_MASK=0x0000FFFFFFFFFFFF", .define "IMMER_HAS_LIBGC=1",
   .define "IMMER_TAGGED_NODE=0", .define "HAVE_CXX14=1", .define "CPPINTEROP_USE_REPL",
   .define "FOLLY_HAVE_JEMALLOC=0", .define "FOLLY_HAVE_TCMALLOC=0",
   .define "FOLLY_ASSUME_NO_JEMALLOC=1", .define "FOLLY_ASSUME_NO_TCMALLOC=1"]
  ++ (match bt with
      | .debug => [.other "-Werror", .opt 0, .debugInfo]
      | .release => [.opt 2, .define "NDEBUG"]
      | .relWithDebInfo => [.optG, .debugInfo, .define "NDEBUG"]
      | .none => [])
  ++ [.define "LLVM_DEFINITIONS", .define "JANK_RESOURCE_DIR", .define "JANK_CLANG_PATH",
      .define "JANK_CLANG_MAJOR_VERSION", .define "JANK_CLANG_RESOURCE_DIR"]

/-- `jank_jit_compiler_flags` (CMakeLists.txt 339-349). -/
def jitCompilerFlags : List Flag :=
  [.warnNone, .fwrapv, .other "-fno-stack-protector", .other "-fPIC",
   .other "-Xclang", .other "-fno-validate-pch", .other "-Xclang", .other "-fno-pch-timestamp",
   .define "LLVM_DEFINITIONS", .include "clang system includes"]

/-- `JANK_JIT_FLAGS` (CMakeLists.txt 719-729). -/
def jankJitFlags (bt : BuildType) : List Flag :=
  commonFlags bt ++ jitCompilerFlags ++ [.include "jank lib includes"]

/-- `-O<n>` as `processor_dynamic.cpp` 282-297 and `aot/processor.cpp` 301-317 spell it (an out of
range level is `-O0` for the JIT, `-O2` for AOT; cli.cpp never produces one). -/
def optFlag (n : Nat) (dflt : Nat) : Flag := if n ≤ 3 then .opt n else .opt dflt

/-- The JIT's clang arguments (processor_dynamic.cpp 165-307) before the `-O` flag; without
`--debug` every `-g` is removed (293-301; the `-O` flag is not a `-g`, so filtering the prefix is
the same). -/
def jitArgsPrefix (bt : BuildType) (c : Cli) : List Flag :=
  let base : List Flag :=
    (if c.debug then [.debugInfo] else [])
    ++ [.include "clang ../include", .other "-resource-dir", .include "jank resource include",
        .libDir "jank resource lib"]
    ++ jankJitFlags bt
    ++ [.other "-include-pch", .warnNone, .noNarrowingError]
    ++ c.includes.map .include ++ c.libDirs.map .libDir ++ c.defines.map .define
  if c.debug then base else base.filter (· != .debugInfo)

def jitArgs (bt : BuildType) (c : Cli) : List Flag :=
  jitArgsPrefix bt c ++ [optFlag c.levels.runtime 0]

/-- The AOT compiler's arguments (`invoke_clang` of `build_compiler_args`, `JANK_EXTRA_FLAGS`
given as `extra`, which `invoke_clang` appends once more after everything). -/
def aotArgsPrefix (bt : BuildType) (c : Cli) (extra : List Flag) (dynamicRuntime : Bool) : List Flag :=
  [.include "clang ../include", .libDir "jank", .include "jank resource include",
   .libDir "jank resource lib"]
  ++ jankJitFlags bt ++ [.other "JANK_AOT_FLAGS (linker flags)"] ++ extra
  ++ c.libDirs.map .libDir ++ c.includes.map .include ++ c.defines.map .define
  ++ (if c.debug then [.debugInfo] else [.other "-Wl,--strip-all"])
  ++ [.std "c++20", .other "-Wno-c23-extensions"]
  ++ (if dynamicRuntime then [.other "-Wl,--export-dynamic", .other "-rdynamic"] else [])

def aotArgs (bt : BuildType) (c : Cli) (extra : List Flag) (dynamicRuntime : Bool) : List Flag :=
  aotArgsPrefix bt c extra dynamicRuntime ++ [optFlag c.levels.codegen 2] ++ extra

/-- Clang's optimization level: the last `-O<n>`/`-Og` (none: 0). -/
def effectiveOpt : List Flag → Nat
  | [] => 0
  | f :: rest =>
    let later := rest.any fun g => match g with | .opt _ | .optG => true | _ => false
    if later then effectiveOpt rest
    else match f with
      | .opt n => n
      | .optG => 1
      | _ => effectiveOpt rest

/-- Signed `+ - *` overflow wraps (`-fwrapv`, or `-fno-strict-overflow` which implies it). -/
def wrapsSignedOverflow (fs : List Flag) : Bool := fs.contains .fwrapv || fs.contains .noStrictOverflow

/-- The C++ standard of the last `-std=`. -/
def effectiveStd (fs : List Flag) : String :=
  (fs.filterMap fun f => match f with | .std s => some s | _ => none).getLast?.getD "gnu++17"

/-- `getLangOpts().CPlusPlus11` for the standards jank passes. -/
def isCxx11OrLater (s : String) : Bool :=
  s == "c++11" || s == "gnu++11" || s == "c++14" || s == "gnu++14" || s == "c++17" || s == "gnu++17"
  || s == "c++20" || s == "gnu++20" || s == "c++23" || s == "gnu++23" || s == "c++26" || s == "gnu++26"

/-- `-ffinite-loops`/`-fno-finite-loops` (`FiniteLoopsKind`): the last one, else the language default. -/
def finiteLoopsKind (fs : List Flag) : Option Bool :=
  (fs.filterMap fun f => match f with | .finiteLoops b => some b | _ => none).getLast?

/-- `CodeGenFunction::checkIfLoopMustProgress` (CGStmt.cpp 1009-1048) for a `while` whose
condition is the constant `true` (jank's `while(true){…}`, cpp_processor.cpp 1013). -/
def loopMustProgress (fs : List Flag) (hasEmptyBody : Bool) : Bool :=
  match finiteLoopsKind fs with
  | some false => false
  | some true => !hasEmptyBody
  | none => if isCxx11OrLater (effectiveStd fs) then !hasEmptyBody else false

/-- `checkIfFunctionMustProgress` (CodeGenFunction.h): every C++11 function, unless
`-fno-finite-loops`. -/
def functionMustProgress (fs : List Flag) : Bool :=
  match finiteLoopsKind fs with
  | some false => false
  | _ => isCxx11OrLater (effectiveStd fs)

/-- `fptosi` of an out-of-range value is poison unless `-fno-strict-float-cast-overflow`. -/
def floatCastOverflowIsPoison (fs : List Flag) : Bool :=
  match (fs.filterMap fun f => match f with | .strictFloatCastOverflow b => some b | _ => none).getLast? with
  | some b => b
  | none => true

/-- What the optimizer may assume of the code jank emits in one mode. -/
structure Semantics where
  level : Nat
  wraps : Bool
  loopsMustProgress : Bool
  functionsMustProgress : Bool
  fptosiPoison : Bool
  deriving Repr, BEq, DecidableEq

def semanticsOf (fs : List Flag) : Semantics :=
  { level := effectiveOpt fs, wraps := wrapsSignedOverflow fs,
    loopsMustProgress := loopMustProgress fs false, functionsMustProgress := functionMustProgress fs,
    fptosiPoison := floatCastOverflowIsPoison fs }

/-! ## For every build type and command line -/

theorem effectiveOpt_append_opt (xs : List Flag) (n : Nat) : effectiveOpt (xs ++ [.opt n]) = n := by
  induction xs with
  | nil => simp [effectiveOpt]
  | cons f rest ih =>
    simp only [List.cons_append, effectiveOpt]
    have : (rest ++ [Flag.opt n]).any (fun g => match g with | .opt _ | .optG => true | _ => false) = true := by
      simp
    simp [this, ih]

theorem optFlag_le (n d : Nat) (h : n ≤ 3) : optFlag n d = .opt n := by simp [optFlag, h]

/-- The JIT always gets `-fwrapv` (CMakeLists.txt 342 through `JANK_JIT_FLAGS`). -/
theorem jit_has_fwrapv (bt : BuildType) (c : Cli) : Flag.fwrapv ∈ jitArgs bt c := by
  unfold jitArgs jitArgsPrefix
  split
  · simp [jankJitFlags, jitCompilerFlags]
  · simp only [List.mem_append, List.mem_filter]
    left
    refine ⟨by simp [jankJitFlags, jitCompilerFlags], ?_⟩
    decide

/-- AOT compilation always gets `-fwrapv` (`build_compiler_args` adds `JANK_JIT_FLAGS`). -/
theorem aot_has_fwrapv (bt : BuildType) (c : Cli) (extra : List Flag) (dyn : Bool) :
    Flag.fwrapv ∈ aotArgs bt c extra dyn := by
  simp [aotArgs, aotArgsPrefix, jankJitFlags, jitCompilerFlags]

/-- The JIT's clang level is the runtime level, whatever the build type (Release's `-O2` from
`JANK_JIT_FLAGS` is overridden): the last flag is `-O<runtime>`. -/
theorem jit_level (bt : BuildType) (c : Cli) (h : c.levels.runtime ≤ 3) :
    effectiveOpt (jitArgs bt c) = c.levels.runtime := by
  unfold jitArgs
  rw [optFlag_le _ _ h, effectiveOpt_append_opt]

/-- `run`, `run-main` and `repl`: the JIT runs at the `-O` given (default 0). -/
theorem run_levels (c : Cli) (h : c.command = .run ∨ c.command = .runMain ∨ c.command = .repl) :
    c.levels.runtime = c.levels.codegen := by
  rcases h with h | h | h <;> simp [Cli.levels, h]

/-- `compile`/`compile-module`: macros and top-level forms run in the JIT at -O0 whatever `-O`. -/
theorem compile_jit_at_O0 (c : Cli) (h : c.command = .compile ∨ c.command = .compileModule) :
    c.levels.runtime = 0 := by
  rcases h with h | h <;> simp [Cli.levels, h]

/-- AOT without `JANK_EXTRA_FLAGS`: clang's level is the codegen level. -/
theorem aot_level (bt : BuildType) (c : Cli) (dyn : Bool) (h : c.levels.codegen ≤ 3) :
    effectiveOpt (aotArgs bt c [] dyn) = c.levels.codegen := by
  unfold aotArgs
  rw [optFlag_le _ _ h, List.append_nil, effectiveOpt_append_opt]

/-- No mode passes `-ffinite-loops`/`-fno-finite-loops` or `-fno-strict-float-cast-overflow`. -/
def noLoopOrCastFlags (fs : List Flag) : Bool :=
  fs.all fun f => match f with | .finiteLoops _ | .strictFloatCastOverflow _ => false | _ => true

end Jank.R3.Codegen
