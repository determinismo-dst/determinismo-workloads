import Jank.R5.Native.LdScript
import Jank.R5.Native.LdSpec
import Determinismo

/-!
# Round 5, native loading: which libraries jank loads for `-l`, under the JIT and in an AOT link

jank 94d32623, `upstream-r5/compiler+runtime/src/cpp/jank/`:

- `jit/processor_dynamic.cpp`
  - `shared_lib_name` 51–64 (`lib{}.so` on Linux), `static_lib_name` 66–75 (`lib{}.a`),
    `is_static_lib` 77–80 (ends with `.a`);
  - `build_library_dirs` 99–143: the `-L` dirs (made absolute), then Clang's default dirs, then
    `-L` flags in JANK_JIT_FLAGS/JANK_EXTRA_FLAGS;
  - `find_lib` 737–785: an absolute path as is (if a regular file); `./x` from the current
    directory; else the first `dir/x` that is a regular file;
  - `resolve_libs` 787–871: the literal name first; `:x` forces a static library; otherwise
    `lib<x>.so` in **every** directory, and only then `lib<x>.a` in every directory;
  - `load_libs` 873–895 (from the JIT's constructor, 432–436);
  - `load_dynamic_library_impl` 897–949: on Linux a file that is not ELF is read as a GNU ld
    script (`parse_ld_script`), its one path resolved against the script's directory,
    normalized, rejected if it is the script itself, followed to depth 8; anything else goes to
    `clang::Interpreter::LoadDynamicLibrary` under `llvm::cantFail`;
  - `load_static_library` 956–961 (`linkStaticLibraryInto` under `cantFail`).
- `aot/processor.cpp` 246–249, 356–394: the AOT link gets `-L` for the user's dirs, Clang's
  default dirs, and for each `-l`: a static resolution as its path, a dynamic one as
  `-l<the user's string>` (the comment at 357–359: "so the same libs are found as during JIT").
- `llvm::cantFail` (llvm/Support/Error.h 769–781 at llvmorg-23.1.0, `deps/llvm-23.1.0-native/`):
  `llvm_unreachable` on failure — undefined behavior in a release (NDEBUG) build, an abort with
  a message in a debug build. `OrcIncrementalExecutor::LoadDynamicLibrary` (108–120) returns the
  failure of `EPCDynamicLibrarySearchGenerator::Load`, i.e. of `dlopen`.

The spec for an AOT link is GNU ld's `-l` (ld.texi 724–738: per directory, `lib<x>.so` before
`lib<x>.a`; `:file` names a file) and its reading of a `.so` that is a script (`LdSpec`). The
spec for the JIT is jank's own: the CLI help (util/cli.cpp 157–161: "-l <lib> Library
identifiers, absolute or relative paths") and aot/processor.cpp's comment that the AOT link finds
the same libraries as the JIT.
-/

namespace Jank.R5.Native.Libs

open Determinismo

/-- What a file holds, as the loaders see it. -/
inductive Kind where
  /-- An ELF shared object `dlopen` accepts. -/
  | elfDyn
  /-- ELF magic, but `dlopen` refuses it (truncated, another machine, `ET_REL`). -/
  | elfBad
  /-- A GNU ld script (drawn as LdSpec tokens: ld reads the tokens, jank the rendered text). -/
  | script (ts : List Jank.R5.Native.LdSpec.Tok)
  /-- Other text. -/
  | text (s : String)
  /-- An `ar` archive. -/
  | archive
  deriving Repr, DecidableEq, Inhabited

abbrev FS := List (String × Kind)


/-- `std::filesystem::path::lexically_normal` on the paths this world uses ('/'-separated,
`.` and `..` components). -/
def normalize (p : String) : String :=
  let absP := p.startsWith "/"
  let parts := (p.splitOn "/").filter (fun c => c != "" && c != ".")
  let st := parts.foldl (fun (acc : List String) c =>
    if c == ".." then (match acc with
      | [] => if absP then [] else [".."]
      | ".." :: _ => ".." :: acc
      | _ :: r => r)
    else c :: acc) []
  let body := "/".intercalate st.reverse
  if absP then "/" ++ body else (if body == "" then "." else body)

/-- The file at a path (the operating system resolves `.` and `..`). -/
def FS.get (fs : FS) (p : String) : Option Kind :=
  (fs.find? (fun e => normalize e.1 == normalize p)).map (·.2)

def parent (p : String) : String :=
  match (p.splitOn "/").dropLast with
  | [] => "."
  | [""] => "/"
  | cs => "/".intercalate cs

def isAbs (p : String) : Bool := p.startsWith "/"

/-- `is_elf_file` (parse_ld_script.cpp 211–222): the first 4 bytes are `\x7fELF`. -/
def isElf (fs : FS) (p : String) : Bool :=
  match fs.get p with
  | some .elfDyn | some .elfBad => true
  | _ => false

/-- The setting: `-L` dirs (absolute), Clang's default dirs, the current directory. -/
structure Setting where
  userDirs : List String := ["/u1", "/u2"]
  sysDirs : List String := ["/sys"]
  cwd : String := "/cwd"
  deriving Repr

def Setting.dirs (st : Setting) : List String := st.userDirs ++ st.sysDirs

/-- `find_lib` (737–785) on Linux. -/
def findLib (fs : FS) (st : Setting) (lib : String) : Option String :=
  if isAbs lib then (if (fs.get lib).isSome then some lib else none)
  else if lib.startsWith "./" then
    let p := st.cwd ++ "/" ++ lib
    if (fs.get p).isSome then some p else none
  else (st.dirs.map (· ++ "/" ++ lib)).find? (fun p => (fs.get p).isSome)

def isStaticLib (p : String) : Bool := p.endsWith ".a"

/-- One resolved `-l`: the path and whether it is static. -/
structure Resolved where
  lib : String
  isStatic : Bool
  deriving Repr, DecidableEq

/-- `resolve_libs` (787–871) for one `-l` value. -/
def resolve (fs : FS) (st : Setting) (lib : String) : Except String Resolved :=
  match findLib fs st lib with
  | some p => .ok { lib := p, isStatic := isStaticLib p }
  | none =>
    if lib.startsWith ":" then
      let l := String.ofList (lib.toList.drop 1)
      match findLib fs st l with
      | some p => if isStaticLib p then .ok { lib := p, isStatic := true }
        else .error s!"Failed to find static library '{l}'. This library is not static."
      | none =>
        match findLib fs st s!"lib{l}.a" with
        | none => .error s!"Failed to find static library '{l}'."
        | some p => if isStaticLib p then .ok { lib := p, isStatic := true }
          else .error s!"Failed to find static library '{l}'. This library is not static."
    else
      match findLib fs st s!"lib{lib}.so" with
      | some p => .ok { lib := p, isStatic := false }
      | none =>
        match findLib fs st s!"lib{lib}.a" with
        | none => .error s!"Failed to find library '{lib}'."
        | some p => .ok { lib := p, isStatic := true }

/-- How the JIT's start-up ends for one `-l`. -/
inductive JitOut where
  /-- These files are mapped into the process (dlopen / the static library linked in). -/
  | loaded (files : List String)
  /-- jank reports an error and exits (a `std::runtime_error` from the JIT's constructor). -/
  | reported (msg : String)
  /-- `llvm::cantFail` on a failure: undefined behavior (release) or an abort (debug). -/
  | cantFail (what : String)
  deriving Repr, DecidableEq

/-- `load_dynamic_library_impl` (905–948), on Linux. `dlopen` succeeds exactly on `elfDyn`. -/
def loadDynamic (fs : FS) : String → Nat → Nat → JitOut
  | _, _, 0 => .reported "fuel"
  | path, depth, f + 1 =>
    let viaDlopen : JitOut :=
      match fs.get path with
      | some .elfDyn => .loaded [path]
      | some .elfBad => .cantFail s!"dlopen refuses ELF file {path}"
      | some (.text _) | some (.script _) => .cantFail s!"dlopen of the text file {path}"
      | some .archive => .cantFail s!"dlopen of the archive {path}"
      | none => .cantFail s!"dlopen of the missing file {path}"
    if isElf fs path then viaDlopen
    else
      let text := match fs.get path with
        | some (.text s) => some s
        | some (.script ts) => some (Jank.R5.Native.LdSpec.render ts)
        | some .archive => some "!<arch>\n"
        | _ => none   -- read_file fails: parse_ld_script returns none
      match text.bind Jank.R5.Native.LdScript.parseStr with
      | none => viaDlopen
      | some r =>
        if depth ≥ 8 then .reported s!"Exceeded the maximum GNU ld script nesting depth while loading `{path}`."
        else
          let rp := normalize (if isAbs r then r else parent path ++ "/" ++ r)
          if rp == normalize path then .reported s!"This GNU ld script `{path}` refers to itself."
          else loadDynamic fs rp (depth + 1) f

/-- `load_static_library` (956–961): `linkStaticLibraryInto` accepts an archive. -/
def loadStatic (fs : FS) (p : String) : JitOut :=
  match fs.get p with
  | some .archive => .loaded [p]
  | _ => .cantFail s!"linkStaticLibraryInto of a non-archive {p}"

/-- The JIT's start-up with `-l lib` (processor ctor 432–436 → load_libs → resolve_libs). -/
def jit (fs : FS) (st : Setting) (lib : String) : JitOut :=
  match resolve fs st lib with
  | .error e => .reported e
  | .ok r => if r.isStatic then loadStatic fs r.lib else loadDynamic fs r.lib 0 12

/-! ## GNU ld (the AOT link) -/

/-- How the link ends. -/
inductive LinkOut where
  /-- The files in the link: shared objects (all needed ones) and archives. -/
  | linked (files : List String)
  | error (msg : String)
  deriving Repr, DecidableEq

/-- ld's `-l<x>` search (ld.texi 724–738): `:file` exactly; else per directory `lib<x>.so`
then `lib<x>.a`. -/
def ldSearch (fs : FS) (st : Setting) (x : String) : Option String :=
  if x.startsWith ":" then
    (st.dirs.map (· ++ "/" ++ String.ofList (x.toList.drop 1))).find? (fun p => (fs.get p).isSome)
  else
    st.dirs.foldl (fun acc d => match acc with
      | some p => some p
      | none =>
        let so := s!"{d}/lib{x}.so"
        let a := s!"{d}/lib{x}.a"
        if (fs.get so).isSome then some so else if (fs.get a).isSome then some a else none) none

/-- A relative name in a script (ld.texi 4441–4445): the script's directory, the current
directory, the library search path. -/
def ldScriptName (fs : FS) (st : Setting) (scriptDir : String) (n : String) : Option String :=
  if isAbs n then (if (fs.get n).isSome then some n else none)
  else if n.startsWith "=" then
    let p := String.ofList (n.toList.drop 1)
    if (fs.get p).isSome then some p else none   -- no sysroot: `=` is dropped (ldfile.c)
  else
    ([scriptDir, st.cwd] ++ st.dirs).map (· ++ "/" ++ n) |>.find? (fun p => (fs.get p).isSome)

/-- ld's treatment of one input file (a shared object, an archive, or a script), with depth. -/
def ldInput (fs : FS) (st : Setting) : String → Nat → LinkOut
  | _, 0 => .error "fuel"
  | p, f + 1 =>
    match fs.get p with
    | none => .error s!"cannot find {p}"
    | some .elfDyn => .linked [p]
    | some .archive => .linked [p]
    | some .elfBad => .error s!"{p}: file format not recognized"
    | some (.text s) => if s.all Char.isWhitespace then .linked [] else .error s!"{p}: syntax error"
    | some (.script ts) =>
      match Jank.R5.Native.LdSpec.ldRead ts with
      | .error e => .error s!"{p}: {e}"
      | .ok es =>
        es.foldl (fun acc (e : Jank.R5.Native.LdSpec.Entry) =>
          match acc with
          | .error m => .error m
          | .linked fsAcc =>
            if e.asNeeded then .linked fsAcc   -- added only when needed
            else
              let found := if e.lib then ldSearch fs st e.name else ldScriptName fs st (parent p) e.name
              match found with
              | none => .error s!"cannot find {if e.lib then "-l" ++ e.name else e.name}"
              | some q =>
                match ldInput fs st q f with
                | .error m => .error m
                | .linked more => .linked (fsAcc ++ more)) (.linked [])

/-- The AOT link for one `-l` (aot/processor.cpp 375–394): a static resolution passed as its
path, a dynamic one as `-l<the user's string>`; jank's own resolution errors first. -/
def aot (fs : FS) (st : Setting) (lib : String) : LinkOut :=
  match resolve fs st lib with
  | .error e => .error e
  | .ok r =>
    if r.isStatic then ldInput fs st r.lib 12
    else match ldSearch fs st lib with
      | none => .error s!"cannot find -l{lib}"
      | some p => ldInput fs st p 12

/-- The ld link of `-l<lib>` alone (the spec for what the library flag means). -/
def ldOnly (fs : FS) (st : Setting) (lib : String) : LinkOut :=
  match ldSearch fs st lib with
  | none => .error s!"cannot find -l{lib}"
  | some p => ldInput fs st p 12

end Jank.R5.Native.Libs
