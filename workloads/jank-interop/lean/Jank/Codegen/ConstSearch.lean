import Jank.Codegen.Pipeline
import Determinismo

/-!
# Searching the literals: every constant jank emits as C++ text must denote the same value

Module (AOT) target: each lifted constant is initialized by `new (&ns::c) auto(<gen_constant>)`
(cpp_processor.cpp:2175-2180). Its meaning is the C++ meaning of that text (`Exec`: literal
types, string literal decoding, overload resolution of `ratio::create`, `char const *`
parameters read up to the first NUL) and the runtime functions it calls (codegen/api.cpp). The
spec: the value is the constant itself (same type, same value, same metadata; a `NaN` is a `NaN`).

Doubles also reach the eval target as text (`small_real_ref{ <double> }`, cpp_processor.cpp:195),
through the same printer: `searchDoubles` checks it over drawn bit patterns.
-/

namespace Jank.Codegen.ConstSearch

open Jank.Codegen Jank.Analyzer Jank.Codegen.Exec Determinismo

/-- The C++ meaning of a constant's text (bytes): parse it as an expression and evaluate it. -/
def meaning (bytes : List UInt8) (dynamicRuntime : Bool) : Except String JV := do
  let text := String.ofList (bytes.map fun b => Char.ofNat b.toNat)
  let toks ← match CppAst.tokenize text with
    | .ok t => pure t
    | .error e => throw s!"compile error: {e}"
  let e ← match CppAst.parseExpr.run { toks } with
    | .ok (e, st) =>
      if st.pos != toks.size then throw "compile error: trailing tokens"
      pure e
    | .error e => throw s!"compile error: {e}"
  if !(CppAst.checkExpr [] [] e |>.toBool) then throw "compile error: undeclared"
  let m0 : M := { prog := {}, latin1 := true, dynamicRuntime }
  match (evalE { dynamic := dynamicRuntime } [[]] e).run m0 with
  | .ok v _ => match v with
    | .obj o => pure o
    | _ => throw "not an object"
  | .error (.err m) _ =>
    if m.startsWith "integer literal is too large" || m.startsWith "unknown escape"
       || m.startsWith "hex escape" then throw s!"compile error: {m}"
    throw s!"model gap: {m}"
  | .error (.thrown _) _ => throw "throws at load"
  | .error (.ub m) _ => throw s!"undefined behaviour: {m}"
  | .error _ _ => throw "model gap"

/-- In the dynamic runtime, metadata read back from a code string is evaluated
(`_jank_eval_str`, api_dynamic.cpp); in the static runtime it is only read. -/
partial def evalMetas (dyn : Bool) : JV → JV
  | .vec xs m => .vec (xs.map (evalMetas dyn)) (m.map (evalMeta dyn))
  | .list xs m => .list (xs.map (evalMetas dyn)) (m.map (evalMeta dyn))
  | .sym ns n m => .sym ns n (m.map (evalMeta dyn))
  | .set xs => .set (xs.map (evalMetas dyn))
  | .map kvs => .map (kvs.map fun (k, v) => (evalMetas dyn k, evalMetas dyn v))
  | x => x
where
  evalMeta (dyn : Bool) (m : JV) : JV :=
    if !dyn then m
    else match evalForm (fun q => (userPrims.find? (fun p => "user/" ++ p.1 == q)).map (fun p => JV.prim p.2)) [] m with
      | .ok (v, _) => v
      | .error e => .other s!"meta evaluation throws: {e}"

/-- One constant: what jank's AOT code makes of it. -/
def check (o : Obj) (dynamicRuntime : Bool) : Option String :=
  match genConstant o true with
  | .error e => some s!"code generation fails: {e}"
  | .ok bytes =>
    let expected := JV.ofObj o
    match meaning bytes dynamicRuntime with
    | .error e => if e.startsWith "model gap" then none else some s!"{e} (text: {textOf bytes})"
    | .ok v =>
      let v := evalMetas dynamicRuntime v
      if v.same expected then none
      else some s!"denotes {v.show}, not {expected.show} (text: {textOf bytes})"

/-! ## Drawing constants -/

structure W where
  decisions : Decisions := {}

instance : Chaotic W where
  decisions w := w.decisions
  setDecisions w d := { w with decisions := d }

def interestingInts : List Int :=
  [0, 1, -1, 7, 2147483647, -2147483648, 2147483648, -2147483649, 4294967296,
   9223372036854775807, -9223372036854775808]

def interestingBigs : List Int :=
  [0, 1, -1, 9223372036854775807, -9223372036854775808, 9223372036854775808,
   -9223372036854775809, 18446744073709551615, 18446744073709551616, -18446744073709551616,
   36893488147419103232]

def interestingReals : List UInt64 :=
  [0x0000000000000000, 0x8000000000000000, 0x3FF0000000000000, 0xBFF8000000000000,
   0x7FF0000000000000, 0xFFF0000000000000, 0x7FF8000000000000, 0x0000000000000001,
   0x000FFFFFFFFFFFFF, 0x0010000000000000, 0x7FEFFFFFFFFFFFFF, 0x4415AF1D78B58C40,
   0x3FB999999999999A, 0x4340000000000001, 0x4480F0CF064DD592, 0x44B52D02C7E14AF6]

/-- Characters for strings, characters, symbol and keyword names. -/
def interestingChars : List Char :=
  ['a', 'b', '\x00', '"', '\\', '?', '=', '\n', '\t', '\x01', '\x7f', 'é', '€', '😀', 'x', '0', '/']

def drawChar (name : String) : EStateM Stop W Char := do
  pure ((← pick (σ := W) name interestingChars).getD 'a')

def drawStr (name : String) : EStateM Stop W String := do
  let n ← decide (σ := W) s!"{name}.length" 4
  let mut cs : List Char := []
  for k in List.range n do cs := cs ++ [← drawChar s!"{name}.char{k}"]
  pure (String.ofList cs)

/-- Names the reader can produce (lex.cpp `is_symbol_char`): no quote, backslash, whitespace or
control character. The others reach a constant only through macros (the table shows them). -/
def drawName (name : String) : EStateM Stop W String := do
  let n ← decide (σ := W) s!"{name}.length" 3
  let mut cs : List Char := []
  for k in List.range (n + 1) do
    cs := cs ++ [(← pick (σ := W) s!"{name}.char{k}" ['a', 'b', '-', '?', '!', 'é', '€', '😀', '_']).getD 'a']
  pure (String.ofList cs)

def drawRatio (name : String) : EStateM Stop W Obj := do
  let n := (← pick (σ := W) s!"{name}.num" (interestingBigs.filter (· != 0))).getD 1
  let d := (← pick (σ := W) s!"{name}.den" ((interestingBigs.filter (· > 1)) ++ [2, 3])).getD 2
  let g : Int := Int.gcd n d
  let (n, d) := (n / g, d / g)
  if d == 1 then pure (.bigInteger n) else pure (.ratio n d)

mutual
partial def drawAtom (name : String) : EStateM Stop W Obj := do
  match ← decide (σ := W) s!"{name}.kind" 9 with
  | 0 => pure (Obj.ofInt ((← pick (σ := W) s!"{name}.int" interestingInts).getD 0))
  | 1 => pure (.bigInteger ((← pick (σ := W) s!"{name}.big" interestingBigs).getD 0))
  | 2 => drawRatio name
  | 3 => pure (.smallReal ((← pick (σ := W) s!"{name}.real" interestingReals).getD 0))
  | 4 => pure (.persistentString (← drawStr s!"{name}.str"))
  | 5 => pure (.character (String.singleton (← drawChar s!"{name}.char")))
  | 6 => pure (.keyword "" (← drawName s!"{name}.kw"))
  | 7 => pure (.symbol none "" (← drawName s!"{name}.sym"))
  | _ => pure (if (← decide (σ := W) s!"{name}.bool" 2) == 0 then .nil else .boolean true)

partial def drawConst (name : String) (depth : Nat) : EStateM Stop W Obj := do
  if depth == 0 then return ← drawAtom name
  match ← decide (σ := W) s!"{name}.shape" 6 with
  | 0 | 1 => drawAtom name
  | k =>
    let n ← decide (σ := W) s!"{name}.count" 3
    let mut xs : List Obj := []
    for i in List.range n do xs := xs ++ [← drawConst s!"{name}.{i}" (depth - 1)]
    let mta : Option Obj ← if (← decide (σ := W) s!"{name}.meta" 3) == 0 then
        -- metadata values: no doubles (their code string, `##Inf` etc., is not modeled)
        let mv ← drawAtom s!"{name}.metaval"
        let mv := match mv with | .smallReal _ | .real _ => Obj.ofInt 0 | x => x
        pure (some (.persistentArrayMap none [(.keyword "" "k", mv)]))
      else pure none
    match k with
    | 2 => pure (.persistentVector mta xs)
    | 3 => pure (.persistentList mta xs)
    | 4 => pure (.persistentHashSet none (xs.foldl (fun acc x =>
        if acc.any (fun y => (JV.ofObj y).equiv (JV.ofObj x)) then acc else acc ++ [x]) []))
    | _ => pure (.cons none (xs.headD .nil) (.persistentList none (xs.drop 1)))
end

/-- The first part (depth first) of a constant that is wrong on its own, and its kind. -/
partial def culprit (o : Obj) (dyn : Bool) : Option (String × Obj) :=
  let kids : List Obj := match o with
    | .persistentVector _ xs | .persistentList _ xs | .persistentHashSet _ xs => xs
    | .cons _ f r => [f, r]
    | _ => []
  match kids.findSome? (culprit · dyn) with
  | some r => some r
  | none =>
    if (check o dyn).isNone then none
    else some ((match o with
      | .ratio .. => "ratio" | .persistentString .. => "string" | .character .. => "character"
      | .symbol .. => "symbol" | .keyword .. => "keyword" | .bigInteger .. => "big integer"
      | .smallReal .. | .real .. => "double" | .smallInteger .. | .integer .. => "integer"
      | .persistentVector .. => "vector" | .persistentList .. => "list" | .cons .. => "cons"
      | .persistentHashSet .. => "set" | _ => "other"), o)

def body (dyn : Bool) : EStateM Stop W Unit := do
  let o ← drawConst "const" 2
  match check o dyn with
  | some d =>
    let (k, part) := match culprit o dyn with
      | some (k, part) => (k, (JV.ofObj part).show)
      | none => ("whole", "")
    violate (σ := W) s!"an AOT constant denotes itself [{k}]" s!"[{k}: {part}] {(JV.ofObj o).show}: {d}"
  | none => pure ()

def run (dyn : Bool) (source : Source) : Ended :=
  match (body dyn).run { decisions := { source } } with
  | .ok _ w => { taken := w.decisions.taken, violation := none }
  | .error (.violation p d) w => { taken := w.decisions.taken, violation := some (p, d) }
  | .error .limit w => { taken := w.decisions.taken, violation := none }
  | .error (.nodeDown _) w => { taken := w.decisions.taken, violation := none }

/-- Every atom kind on its own, and some by hand, for the table of results. -/
def table (dyn : Bool) : List (String × Option String) :=
  let atoms : List Obj :=
    (interestingInts.map Obj.ofInt) ++ (interestingBigs.map Obj.bigInteger)
    ++ [.ratio 1 9223372036854775808, .ratio 9223372036854775809 2, .ratio (-9223372036854775809) 2,
        .ratio 1 36893488147419103232, .ratio 1 3, .ratio (-9223372036854775808) 3]
    ++ (interestingReals.map Obj.smallReal)
    ++ [.persistentString "a\x00b", .persistentString "\x00", .persistentString "??=",
        .persistentString "a\"b\\c\n", .persistentString "é€😀\x01\x7f",
        .character "\x00", .character "\"", .character "\\", .character "😀",
        .keyword "" "a\"b", .keyword "" "a\\b", .keyword "" "ok", .symbol none "" "a\"b",
        .symbol none "" "a\nb", .symbol none "" "ok",
        .persistentSortedMap none [(Obj.ofInt 1, Obj.ofInt 2)], .persistentSortedSet none [Obj.ofInt 1],
        .opaque .inst 0,
        .persistentVector (some (.persistentArrayMap none [(.keyword "" "k", .persistentList none [.symbol none "" "add", Obj.ofInt 1, Obj.ofInt 2])])) [Obj.ofInt 1],
        .symbol (some (.persistentArrayMap none [(.keyword "" "tag", .symbol none "" "String")])) "" "x"]
  atoms.map fun o => ((JV.ofObj o).show, check o dyn)

/-! ## Doubles: printed (`string_builder::operator()(double)`), read back as C++ -/

def doubleCheck (b : UInt64) : Option String :=
  let t := Float.sbF64 b
  match Float.cppMeaning t with
  | some r => if Float.sameDouble r b then none else some s!"{b} prints as {t}, read back as {r}"
  | none => some s!"{b} prints as {t}, not a C++ floating literal"

def doubleBody : EStateM Stop W Unit := do
  -- a sign, an exponent field (biased to the edges), a mantissa
  let s ← decide (σ := W) "real.sign" 2
  let ek ← decide (σ := W) "real.exp_kind" 4
  let e : Nat ← match ek with
    | 0 => decide (σ := W) "real.exp_low" 4
    | 1 => do pure (2046 - (← decide (σ := W) "real.exp_high" 4))
    | 2 => do pure (1023 + (← decide (σ := W) "real.exp_mid" 80) - 40)
    | _ => decide (σ := W) "real.exp" 2048
  let mk ← decide (σ := W) "real.mant_kind" 3
  let m : Nat ← match mk with
    | 0 => decide (σ := W) "real.mant_small" 8
    | 1 => do pure (2^52 - 1 - (← decide (σ := W) "real.mant_top" 8))
    | _ => do
      let mut x := 0
      for k in List.range 4 do x := x * 8192 + (← decide (σ := W) s!"real.mant{k}" 8192)
      pure (x % 2^52)
  let b : UInt64 := UInt64.ofNat ((s * 2^63) + e * 2^52 + m)
  if let some d := doubleCheck b then violate (σ := W) "a double prints as a C++ literal of itself" d

def runDoubles (source : Source) : Ended :=
  match doubleBody.run { decisions := { source } } with
  | .ok _ w => { taken := w.decisions.taken, violation := none }
  | .error (.violation p d) w => { taken := w.decisions.taken, violation := some (p, d) }
  | .error .limit w => { taken := w.decisions.taken, violation := none }
  | .error (.nodeDown _) w => { taken := w.decisions.taken, violation := none }

end Jank.Codegen.ConstSearch
