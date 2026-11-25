/-!
# Arity dispatch: fixed and variadic fns, calls with more than 10 arguments, `apply`

Replicas (jank 7135b7708):

- analyze/processor.cpp `analyze_fn_arity` 1748-1871: `&` is skipped, the rest symbol is a
  parameter, more than `max_params` (10, core/call.hpp:18) parameters is an error;
  `analyze_fn` 2032-2101: one variadic arity, no fixed arity with `params.size() >=` the variadic
  arity's, no two arities with the same size and variadic-ness;
- ir/processor.cpp `arity_flags` 339-369 with core/call.hpp `build_arity_flags`,
  `mask_variadic_arity`, `extract_variadic_arity_mask` (`flags & 0b10001111`),
  `is_variadic_ambiguous`; `gen(function)` 371-405: slot `arity_<params.size()>`; codegen
  `_jank_fn`/`_jank_vfn` (cpp_processor.cpp 709-736, api.cpp);
- analyze/processor.cpp `analyze_call` 3612-3663: arguments past the 10th packed into one list
  expression, passed as an 11th argument `more`;
- runtime/obj/jit_function.cpp `call` 0..10 (`arity_n` or `invalid_arity<n>`), object.cpp 175-188
  (the 11-argument `call` throws `invalid_arity<11>`);
- runtime/obj/jit_variadic_function.cpp (and jit_variadic_closure.cpp, identical switches) `call`
  for 0..10 arguments and for 10 + `more` (`concat*` of the packed tail);
- evaluate.cpp 376-399 (a top-level call: `apply_to(…, already_packed = true)`) and
  core/call.cpp `apply_to` 13-150 (`sequence_length(s, 11)`, then `call` with up to 10 arguments
  or 10 and the rest of the seq); core.jank `apply` 1047-1058.

Spec: Clojure 1.12 Compiler.java `FnExpr.parse` 4550-4572 (one variadic overload, no two
overloads with the same arity, no fixed arity above the variadic one's required count),
`FnMethod.parse` 5968 (at most 20 required parameters), `RestFn`/`AFunction` dispatch and
`applyTo` (a fixed arity for exactly its count, else the variadic one with the rest as a seq or
nil, else `ArityException` with the number of arguments).
-/

namespace Jank.R3.Codegen.Variadic

/-- One arity: its required parameters and whether it has `& rest`. -/
structure Ar where
  fixed : Nat
  variadic : Bool
  deriving Repr, BEq, DecidableEq, Inhabited

/-- jank's `params.size()`: the rest symbol counts. -/
def Ar.size (a : Ar) : Nat := a.fixed + (if a.variadic then 1 else 0)

/-- A bound parameter value: argument `i` (1-based), nil, or a seq of arguments. -/
inductive PV where
  | arg (i : Nat)
  | nil
  | seq (xs : List Nat)
  deriving Repr, BEq, DecidableEq, Inhabited

/-- What a call did: the arity that ran (its index in the fn) and its parameters, or an arity
exception (with the count it reports), or the fn did not compile. -/
inductive Disp where
  | ran (arity : Nat) (bound : List PV)
  | arityError (reported : Nat)
  | compileError (msg : String)
  deriving Repr, BEq, DecidableEq, Inhabited

/-! ## jank -/

def maxParams : Nat := 10

/-- `analyze_fn_arity` and `analyze_fn`'s checks. -/
def jankCheck (ars : List Ar) : Option String :=
  if ars.any (·.size > maxParams) then some "This function has too many parameters. The max is 10."
  else
    let vs := ars.filter (·.variadic)
    if vs.length > 1 then some "A function may only have one variadic arity."
    else
      let vSize := (vs.head?.map (·.size)).getD 0
      if !vs.isEmpty && ars.any (fun a => !a.variadic && a.size ≥ vSize) then
        some "The variadic arity of this function has fewer parameters than one of its fixed arities"
      else if (ars.zipIdx.any fun (a, i) => ars.zipIdx.any fun (b, j) => i < j && a.size == b.size && a.variadic == b.variadic) then
        some "There are multiple arities with the same number of parameters."
      else none

/-- `arity_flags` (ir/processor.cpp 339-369) as the `u8` it is. -/
def arityFlags (ars : List Ar) : Nat :=
  let variadic := ars.foldl (fun acc a => if a.variadic then some a else acc) none
  let highest := ars.foldl (fun acc a => if a.variadic then acc else match acc with
    | none => some a
    | some h => if h.size < a.size then some a else some h) none
  match variadic with
  | some v =>
    let amb := match highest with | some h => h.size == v.size - 1 | none => false
    ((1 <<< 7) ||| ((if amb then 1 else 0) <<< 6) ||| (v.size - 1)) % 256
  | none => (highest.map (·.size)).getD 0 % 256

def isAmbiguous (flags : Nat) : Bool := (flags &&& 0x40) != 0
def variadicMask (flags : Nat) : Nat := flags &&& 0x8F
def maskVariadicArity (k : Nat) : Nat := 0x80 ||| k

/-- `arities[arity.params.size()] = name`: the slot's arity (the last one written). -/
def slot (ars : List Ar) (s : Nat) : Option Nat :=
  (ars.zipIdx.filter (fun (a, _) => a.size == s)).getLast?.map (·.2)

/-- `do_call(arity_s, this, values...)`: the arity in slot `s`, or `invalid_arity<count>`. -/
def doCall (ars : List Ar) (s : Nat) (values : List PV) : Disp :=
  match slot ars s with
  | some i => .ran i values
  | none => .arityError values.length

def args (lo hi : Nat) : List Nat := (List.range (hi + 1)).filter (fun i => lo ≤ i)

/-- `jit_function::call` with `n` arguments (n > 10: the 11-argument overload). -/
def fnCall (ars : List Ar) (n : Nat) : Disp :=
  if n ≤ 10 then doCall ars n ((args 1 n).map .arg) else .arityError 11

/-- `jit_variadic_function::call` with `n` arguments; for n > 10 the analyzer passed 10 and a list
of the others (`more`), which `concat*` appends. -/
def vfnCall (ars : List Ar) (n : Nat) : Disp :=
  let flags := arityFlags ars
  let mask := variadicMask flags
  let amb := isAmbiguous flags
  if n == 0 then
    if flags == maskVariadicArity 0 then doCall ars 1 [.nil] else doCall ars 0 []
  else if n ≤ 10 then
    match (List.range n).find? (fun k => mask == maskVariadicArity k) with
    | some k => doCall ars (k + 1) ((args 1 k).map .arg ++ [.seq (args (k + 1) n)])
    | none =>
      if mask == maskVariadicArity n && !amb then
        if n ≤ 9 then doCall ars (n + 1) ((args 1 n).map .arg ++ [.nil])
        else doCall ars 10 ((args 1 9).map .arg ++ [.seq (args 10 10)])
      else doCall ars n ((args 1 n).map .arg)
  else
    match (List.range 10).find? (fun k => mask == maskVariadicArity k) with
    | some k => doCall ars (k + 1) ((args 1 k).map .arg ++ [.seq (args (k + 1) n)])
    | none => doCall ars 10 ((args 1 9).map .arg ++ [.seq (args 10 n)])

/-- A call of the fn with `n` arguments: compiled call, top-level `evaluate::eval` (`apply_to`
with the packed list) or `apply` (`apply_to` of a seq of `n`) all reach the same `call`
overload: at most 10 arguments, else 10 and the rest. -/
def jankCall (ars : List Ar) (n : Nat) : Disp :=
  match jankCheck ars with
  | some m => .compileError m
  | none => if ars.any (·.variadic) then vfnCall ars n else fnCall ars n

/-! ## Clojure -/

def cljCheck (ars : List Ar) : Option String :=
  if ars.any (·.fixed > 20) then some "Can't specify more than 20 params"
  else
    let vs := ars.filter (·.variadic)
    if vs.length > 1 then some "Can't have more than 1 variadic overload"
    else if (ars.zipIdx.any fun (a, i) => ars.zipIdx.any fun (b, j) =>
        i < j && !a.variadic && !b.variadic && a.fixed == b.fixed) then
      some "Can't have 2 overloads with same arity"
    else match vs.head? with
      | some v => if ars.any (fun a => !a.variadic && a.fixed > v.fixed) then
          some "Can't have fixed arity function with more params than variadic function" else none
      | none => none

def cljCall (ars : List Ar) (n : Nat) : Disp :=
  match cljCheck ars with
  | some m => .compileError m
  | none =>
    match ars.zipIdx.find? (fun (a, _) => !a.variadic && a.fixed == n) with
    | some (_, i) => .ran i ((args 1 n).map .arg)
    | none =>
      match ars.zipIdx.find? (fun (a, _) => a.variadic && a.fixed ≤ n) with
      | some (a, i) => .ran i ((args 1 a.fixed).map .arg ++ [if n == a.fixed then .nil else .seq (args (a.fixed + 1) n)])
      | none => .arityError n

/-- The class of a disagreement. -/
def classOf (ars : List Ar) (c j : Disp) : String :=
  match c, j with
  | .compileError _, .compileError _ => "agree"
  | _, .compileError _ =>
    if ars.any (·.size > maxParams) then "CG4 more than 10 parameters rejected" else "jank rejects"
  | .compileError _, _ => "jank accepts what Clojure rejects"
  | .arityError a, .arityError b => if a == b then "agree" else "arity exception reports 11 arguments"
  | _, _ => if c == j then "agree" else "dispatch differs"

/-! ## For every input (bounded domains) -/

/-- A fn with only `[a1 .. ar & rest]` (r ≤ 9): jank binds what Clojure binds, for every call of
0 to 14 arguments. -/
theorem only_variadic_agrees :
    ∀ r : Fin 10, ∀ n : Fin 15, jankCall [⟨r.val, true⟩] n.val = cljCall [⟨r.val, true⟩] n.val := by
  decide

/-- `([a1 .. ar] …) ([a1 .. ar & rest] …)` (the ambiguous flag): jank agrees for 0 to 14
arguments. -/
theorem ambiguous_agrees :
    ∀ r : Fin 10, ∀ n : Fin 15,
      jankCall [⟨r.val, false⟩, ⟨r.val, true⟩] n.val = cljCall [⟨r.val, false⟩, ⟨r.val, true⟩] n.val := by
  decide

/-- A fixed arity of 11 to 20 parameters: Clojure compiles it, jank rejects it. -/
theorem eleven_to_twenty_fixed (p : Nat) (h1 : 10 < p) (h2 : p ≤ 20) :
    jankCheck [⟨p, false⟩] ≠ none ∧ cljCheck [⟨p, false⟩] = none := by
  constructor
  · simp [jankCheck, Ar.size, maxParams]; omega
  · simp [cljCheck]; omega

/-- `[a1 .. a10 & rest]`: Clojure compiles it, jank rejects it (the rest symbol is counted). -/
theorem ten_and_rest :
    jankCheck [⟨10, true⟩] ≠ none ∧ cljCheck [⟨10, true⟩] = none := by decide

end Jank.R3.Codegen.Variadic
