import Jank.R5.Native.Libs

/-!
# Round 5, native loading: the `-l` world

A file system of three library directories (`-L /u1 -L /u2`, Clang's default `/sys`) and fixed
targets the scripts name (`/sys/libx.so.1`, `/lib/liby.so.6`, `/sys/libz.so`, `/usr/lib/libw.so`,
each a loadable ELF shared object). Each directory's `libfoo.so` is drawn from: absent, a loadable
ELF, an ELF `dlopen` refuses, one of eight GNU ld scripts, plain text; its `libfoo.a` is absent or
an archive. The `-l` value is drawn from `foo`, `:foo`, `:libfoo.so`, `libfoo.so`, `/u2/libfoo.so`,
`./libfoo.so` (with `/cwd/libfoo.so` a loadable ELF).

Properties, each with its source:
- J1 (util/cli.cpp 160–161, "-l <lib> Library identifiers, absolute or relative paths"; and
  aot/processor.cpp 357–359): when the JIT starts with a `-l`, the AOT link of the same flags
  finds it too.
- J2 (aot/processor.cpp 357–359, "so the same libs are found as during JIT"): the JIT maps the
  same library files that the AOT link puts in.
- J3 (ld.texi 4417–4474 and 724–738): the JIT maps every file ld would link for the flag.
- J4: the JIT either starts or reports an error; it never reaches `llvm::cantFail` with a failure.
-/

namespace Jank.R5.Native.LibsWorld

open Determinismo Jank.R5.Native.Libs Jank.R5.Native.LdSpec

def scripts : List (List Tok) :=
  [ [.group, .lp, .rel, .rp],                                   -- s1 relative name
    [.group, .lp, .abs, .rel, .rp],                             -- s2 two files
    [.input, .lp, .lname, .rp],                                 -- s3 -lz
    [.group, .lp, .asNeeded, .lp, .rel, .rp, .abs, .rp],        -- s4 AS_NEEDED then a file
    [.comment],                                                 -- s5 no command
    [.group, .lp, .abs],                                        -- s6 unbalanced
    [.group, .lp, .sysroot, .rp],                               -- s7 =/path
    [.group, .lp, .abs, .rp] ]                                  -- s8 one absolute file (glibc's shape)

def soChoices : List (Option Kind) :=
  [none, some .elfDyn, some .elfBad] ++ scripts.map (some ∘ .script) ++ [some (.text "hello")]

def fixed : FS :=
  [("/sys/libx.so.1", .elfDyn), ("/lib/liby.so.6", .elfDyn), ("/sys/libz.so", .elfDyn),
   ("/usr/lib/libw.so", .elfDyn), ("/cwd/libfoo.so", .elfDyn)]

def libArgs : List String := ["foo", ":foo", ":libfoo.so", "libfoo.so", "/u2/libfoo.so", "./libfoo.so"]

structure W where
  decisions : Decisions

instance : Chaotic W where
  decisions w := w.decisions
  setDecisions w d := { w with decisions := d }

def jitFiles : JitOut → Option (List String)
  | .loaded fs => some fs
  | _ => none

def classify (lib : String) (j : JitOut) (a : LinkOut) (l : LinkOut) : Option String :=
  match j with
  | .cantFail w =>
    if (w.splitOn "missing").length > 1 then some "J4m the JIT reaches cantFail: a script's file is missing where jank looks (the script's directory)"
    else if (w.splitOn "text file").length > 1 then some "J4t the JIT reaches cantFail: dlopen of a text file (not an INPUT/GROUP script)"
    else some "J4e the JIT reaches cantFail: dlopen refuses a file (bad ELF)"
  | .reported _ =>
    match a with
    | .linked _ => some "J1r the JIT reports an error; the AOT link succeeds"
    | .error _ => none
  | .loaded jfs =>
    match a with
    | .error _ =>
      if lib.startsWith "/" || lib.startsWith "./" || lib.startsWith "lib" then
        some "J1 the AOT link rejects a -l (a path or file name, as the CLI help allows) the JIT loads"
      else some "J1o the AOT link fails where the JIT loads"
    | .linked afs =>
      if jfs != afs then
        if afs.length > jfs.length && afs.take jfs.length == jfs then
          some "J2s the AOT link has files the JIT never maps (a script naming several)"
        else some "J2 the JIT and the AOT link use different library files"
      else
        match l with
        | .linked lfs => if lfs != jfs && !lib.startsWith ":" then some "J3 the JIT maps other files than ld's -l would" else none
        | .error _ => none

def body : EStateM Stop W Unit := do
  let mut fs : FS := fixed
  for d in ["/u1", "/u2", "/sys"] do
    let k ← decide s!"{d}/libfoo.so" soChoices.length
    if let some kind := soChoices[k]! then fs := fs ++ [(s!"{d}/libfoo.so", kind)]
    let a ← decide s!"{d}/libfoo.a" 2
    if a == 1 then fs := fs ++ [(s!"{d}/libfoo.a", .archive)]
  let li ← decide "lib" libArgs.length
  let lib := libArgs[li]!
  let st : Setting := {}
  let j := jit fs st lib
  let a := aot fs st lib
  let l := ldOnly fs st lib
  match classify lib j a l with
  | none => pure ()
  | some c => violate c s!"-l{lib} with {repr (fs.drop fixed.length)}: JIT {repr j}; AOT link {repr a}; ld -l {repr l}"

def run (source : Source) : Ended :=
  match body.run { decisions := { source } } with
  | .ok _ w => { taken := w.decisions.taken, violation := none }
  | .error (.violation p d) w => { taken := w.decisions.taken, violation := some (p, d) }
  | .error .limit w => { taken := w.decisions.taken, violation := none }
  | .error (.nodeDown _) w => { taken := w.decisions.taken, violation := none }

end Jank.R5.Native.LibsWorld
