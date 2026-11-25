import Jank.Interop.Value

/-!
# jank's conversion trait and boxing, replicated

`include/cpp/jank/runtime/convert/builtin.hpp` (every `convert<T>` specialization: `into_object`
and each `from_object` overload), `convert/function.hpp` (`convert_function`),
`core/make_box.hpp` (every `make_box` overload the trait uses), `obj/opaque_box`, and
`c_api.cpp: jank_unbox*` (what `cpp/box` / `cpp/unbox` emit calls to). Paths are under
`upstream/compiler+runtime/`.

Values: a jank object is an `Obj` (Jank/Analyzer/Expr.lean); a native value a `CVal`. A thrown
C++ exception is `Fault.thrown` (`try_object`'s "invalid object type").
-/

namespace Jank.Interop

open Jank.Analyzer (Obj ObjectType)

/-- `obj::X::obj_type` names, for `try_object` diagnostics. -/
def objTypeName (o : Obj) : String := reprStr o.type

/-- `runtime::try_object<T>(o)` (rtti.hpp): the object when `o.get_type() == T::obj_type`, else
throws. -/
def tryObject (want : ObjectType) (o : Obj) : CRes Obj :=
  if o.type == want then .ok o
  else .error (.thrown s!"invalid object type (expected {reprStr want} found {objTypeName o})")

/-! ## make_box (core/make_box.hpp) -/

/-- `make_box(std::nullptr_t)` (make_box.hpp:16). -/
def makeBoxNullptr : Obj := .nil
/-- `make_box(bool)` (make_box.hpp:22). -/
def makeBoxBool (b : Bool) : Obj := .boolean b
/-- `make_box(char)` (make_box.hpp:40): `make_box<obj::character>(i)`, `character(char)`
(character.cpp) stores the one byte as its `data`. -/
def makeBoxChar (byte : Nat) : Obj := .character (charDataOfByte (byte % 256))
/-- `make_box(char const *)` (make_box.hpp:57): asserts non-null, copies. -/
def makeBoxCStr (s : String) : Obj := .persistentString s
/-- `make_box(immutable_string_view)` / `std::string` (make_box.hpp:51). -/
def makeBoxString (s : String) : Obj := .persistentString s
/-- `make_box<T>(T d)` for floating `T` (make_box.hpp:80): `static_cast<f64>(d)`, a small real. -/
def makeBoxReal (x : Float) : Obj := .smallReal x.toBits

/-- `make_box<T>(T i)` for integral `T` (make_box.hpp:88):
`if(detail::min_small_integer <= i && i <= detail::max_small_integer)` with `-Wsign-compare`
silenced: the comparisons are C++ comparisons between an `i32` and a `T`, under the usual
arithmetic conversions. Then a tagged `i32`, else `make_box<obj::integer>(static_cast<i64>(i))`. -/
def makeBoxIntegral (p : Platform) (w : World) (k : Builtin) (i : Int) : Obj :=
  let lo := Cxx.evalBinop p w .lessEqual (.b .int) (.b k) (.int .int (-2147483648)) (.int k i)
  let hi := Cxx.evalBinop p w .lessEqual (.b k) (.b .int) (.int k i) (.int .int 2147483647)
  match lo, hi with
  | .ok (.bool true), .ok (.bool true) => .smallInteger (BitVec.ofInt 32 i)
  | _, _ => .integer (BitVec.ofInt 64 (Cxx.wrapTo p .long i))

/-- `make_box(i64)`. -/
def makeBoxI64 (i : Int) : Obj :=
  if -2147483648 ≤ i ∧ i ≤ 2147483647 then .smallInteger (BitVec.ofInt 32 i)
  else .integer (BitVec.ofInt 64 i)

/-! ## The conversion trait (convert/builtin.hpp) -/

/-- Which specialization of `convert<T>` a (canonical, unqualified, non-reference) type selects:
the `requires` clauses of builtin.hpp, in its order. `none`: no specialization, `convert<T>` is
incomplete. -/
inductive Spec where
  | objectRef            -- convert<object_ref> (builtin.hpp:16)
  | objectPtr            -- convert<object *>, convert<object const *> (builtin.hpp:31)
  | typed (v : String)   -- typed_object_ref<T> (builtin.hpp:57)
  | smallInteger         -- convert<obj::small_integer_ref> (builtin.hpp:76)
  | smallReal            -- convert<obj::small_real_ref> (builtin.hpp:93)
  | void_                -- convert<void> (builtin.hpp:128)
  | nullptr_             -- convert<jtl::nullptr_t> (builtin.hpp:141)
  | bool_                -- convert<bool> (builtin.hpp:155)
  | char_                -- convert<char> (builtin.hpp:174)
  | enum_ (name : String) -- std::is_enum_v<T> (builtin.hpp:194)
  | integral (k : Builtin) -- integral, not bool/char/char8_t/char16_t/char32_t/wchar_t (builtin.hpp:225)
  | floating (k : Builtin) -- std::is_floating_point_v<T> (builtin.hpp:275)
  | cString (signedChar : Bool) -- decay_t<T> in {char *, char const *, signed char *, signed char const *} (builtin.hpp:301)
  | string_              -- jtl::immutable_string, immutable_string_view, std::string (builtin.hpp:326)
  | vector (elem : CType) -- native_vector<T> / std::vector<T> of convertible T (builtin.hpp:348)
  deriving Repr, BEq, Inhabited

/-- The specialization `convert<T>` selects (`T` taken canonical, cv-free, non-reference, as
`cpp_util::is_trait_convertible` and the codegen pass it). -/
partial def convertSpec (w : World) (t : CType) : Option Spec :=
  match (Cxx.nonRef t).canonical.unqual with
  | .record n =>
    if n == objectRefName then some .objectRef
    else if n == orefName "small_integer" then some .smallInteger
    else if n == orefName "small_real" then some .smallReal
    else if n == "std::basic_string<char>" then some .string_
    else if n == "std::vector<int>" then some (.vector (.b .int))
    else match w.findClass n with
      | some c => c.orefOf.map Spec.typed
      | none => none
  | .ptr u =>
    match u.canonical with
    | .record "jank::runtime::object" | .cv true false (.record "jank::runtime::object") => some .objectPtr
    | .b .char | .cv true false (.b .char) => some (.cString false)
    | .b .schar | .cv true false (.b .schar) => some (.cString true)
    | _ => none
  | .array e _ =>
    match e.canonical with
    | .b .char | .cv true false (.b .char) => some (.cString false)
    | .b .schar | .cv true false (.b .schar) => some (.cString true)
    | _ => none
  | .b k =>
    match k with
    | .void => some .void_
    | .nullptr => some .nullptr_
    | .bool => some .bool_
    | .char => some .char_
    | .char8 | .char16 | .char32 | .wchar => none
    | k => if k.isIntegerKind then some (.integral k) else if k.isFloating then some (.floating k) else none
  | .enum n => some (.enum_ n)
  | _ => none

/-- `convert<T>::into_object(t)` for the specialization `s`. -/
partial def intoObject (p : Platform) (w : World) (s : Spec) (v : CVal) : CRes Obj :=
  match s, v with
  -- builtin.hpp:18 / 33 / 60: identity
  | .objectRef, .obj o | .objectPtr, .obj o | .typed _, .obj o => .ok o
  -- builtin.hpp:78: `make_box<obj::integer>(o.data)`: a heap integer, even for a small value
  | .smallInteger, .obj (.smallInteger i) => .ok (.integer (i.signExtend 64))
  -- builtin.hpp:96: `make_box<obj::real>(o.data)`
  | .smallReal, .obj (.smallReal b) => .ok (.real b)
  -- builtin.hpp:130 / 143
  | .void_, _ => .ok .nil
  | .nullptr_, _ => .ok .nil
  -- builtin.hpp:157
  | .bool_, .bool b => .ok (makeBoxBool b)
  -- builtin.hpp:176: `make_box(char)`
  | .char_, .int _ c => .ok (makeBoxChar (Cxx.wrapTo p .uchar c).toNat)
  -- builtin.hpp:196: `make_box(static_cast<i64>(o))`
  | .enum_ _, .enumv _ x => .ok (makeBoxI64 (Cxx.wrapTo p .long x))
  -- builtin.hpp:227: `make_box(static_cast<i64>(o))`
  | .integral _, .int _ x => .ok (makeBoxI64 (Cxx.wrapTo p .long x))
  | .integral _, .bool b => .ok (makeBoxI64 (if b then 1 else 0))
  -- builtin.hpp:277: `make_box(static_cast<f64>(o))`
  | .floating _, v =>
    match Cxx.toNum v with
    | some n => do
      let .flt _ x ← Cxx.convertNum p .double n | .error (.unmodeled "floating")
      .ok (makeBoxReal x)
    | none => .error (.unmodeled "floating into_object")
  -- builtin.hpp:303: null → nil, else `make_box(o)`
  | .cString _, .cstr none => .ok .nil
  | .cString _, .cstr (some s) => .ok (makeBoxCStr s)
  -- builtin.hpp:328
  | .string_, .str s => .ok (makeBoxString s)
  | .vector e, .vec xs => do
    let some es := convertSpec w e | .error (.unmodeled "element")
    let os ← xs.mapM (intoObject p w es)
    .ok (.persistentVector none os)
  | _, _ => .error (.unmodeled s!"into_object {reprStr s} of {reprStr v}")

/-- `detail::is_tagged_small_int` on an object (oref.hpp:119). -/
def isTaggedSmallInt : Obj → Bool | .smallInteger _ => true | _ => false
/-- `detail::is_tagged_small_real` (oref.hpp:113). -/
def isTaggedSmallReal : Obj → Bool | .smallReal _ => true | _ => false

/-- `object_ref::to_integer()` (oref.hpp:958): a tagged integer's value; a tagged real's
`static_cast<i64>` (NaN gives 0; out of range is undefined); else the object's virtual
`to_integer` (number.cpp: `integer` its data, `real` as a tagged real, `boolean` 0 or 1;
character.cpp:104 `mbrtowc` of its bytes, the code point under jank's UTF-8 locale (IA19);
big_integer.cpp:210 / ratio.cpp:123 `to_i64`, which throws out of range); `object::to_integer`
(object.cpp:263) throws `unsupported behavior: number_like` for the rest. -/
def objectToInteger (p : Platform) (o : Obj) : CRes Int :=
  let ofReal (x : Float) : CRes Int :=
    if x.isNaN then .ok 0
    else match Cxx.convertNum p .long (.f x) with
      | .ok (.int _ v) => .ok v
      | .ok _ => .error (.unmodeled "to_integer")
      | .error f => .error f
  let toI64 (v : Int) : CRes Int :=
    if Builtin.long.fits p v then .ok v
    else .error (.thrown s!"The value `{v}` is out of range for `i64` conversion.")
  match o with
  | .smallInteger v => .ok v.toInt
  | .integer v => .ok v.toInt
  | .smallReal b | .real b => ofReal (Float.ofBits b)
  | .boolean b => .ok (if b then 1 else 0)
  | .character d =>
    match d.toList with
    | [c] => if 0xF780 ≤ c.toNat && c.toNat ≤ 0xF7FF then .ok 0 else .ok c.toNat
    | c :: _ => .ok c.toNat
    | [] => .ok 0
  | .bigInteger v => toI64 v
  | .ratio n d => toI64 (n.tdiv d)
  | o => .error (.thrown s!"unsupported behavior: number_like on {objTypeName o}")

/-- `object_ref::to_real()` (oref.hpp:977): a tagged integer as `f64`, a tagged real itself, else
the object's virtual `to_real` (`integer` and `boolean` converted, big_integer.cpp:233 `to_f64`
(infinite on overflow), ratio.cpp:118 numerator over denominator as doubles); characters,
nil and the rest throw `unsupported behavior: number_like` (object.cpp:270). -/
def objectToReal (o : Obj) : CRes Float :=
  match o with
  | .smallInteger v => .ok (Float.ofInt v.toInt)
  | .integer v => .ok (Float.ofInt v.toInt)
  | .smallReal b | .real b => .ok (Float.ofBits b)
  | .boolean b => .ok (if b then 1.0 else 0.0)
  | .bigInteger v => .ok (Float.ofInt v)
  | .ratio n d => .ok (Float.ofInt n / Float.ofInt d)
  | o => .error (.thrown s!"unsupported behavior: number_like on {objTypeName o}")

/-- `convert<T>::from_object(object_ref)` for the specialization `s` (the overload the emitted
code calls on an untyped `object_ref`). -/
def fromObject (p : Platform) (w : World) (s : Spec) (o : Obj) : CRes CVal :=
  match s with
  | .objectRef | .objectPtr => .ok (.obj o)
  -- builtin.hpp:63: `try_object<typename T::value_type>(t)`
  | .typed v =>
    let want : Option ObjectType := match v with
      | "nil" => some .nil | "boolean" => some .boolean | "integer" => some .integer
      | "real" => some .real | "persistent_string" => some .persistentString
      | "character" => some .character | "keyword" => some .keyword | "big_integer" => some .bigInteger
      | "ratio" => some .ratio | "persistent_vector" => some .persistentVector
      | "opaque_box" => some .opaqueBox
      | _ => none
    match want with
    | some t => do let o ← tryObject t o; .ok (.obj o)
    | none => .error (.unmodeled s!"typed {v}")
  -- builtin.hpp:83: tagged → `as_integer`, else `try_object<obj::integer>(o)->data` returned as a
  -- `small_integer_ref`, whose `oref(i64)` constructor (oref.hpp:1886) does `static_cast<i32>`
  | .smallInteger =>
    match o with
    | .smallInteger i => .ok (.obj (.smallInteger i))
    | _ => do
      let .integer i ← tryObject .integer o | .error (.unmodeled "")
      .ok (.obj (.smallInteger (i.truncate 32)))
  | .smallReal =>
    match o with
    | .smallReal b => .ok (.obj (.smallReal b))
    | _ => do
      let .real b ← tryObject .real o | .error (.unmodeled "")
      .ok (.obj (.smallReal b))
  | .void_ => .ok .void
  -- builtin.hpp:146: whatever the object
  | .nullptr_ => .ok .nullptr
  -- builtin.hpp:162: `try_object<obj::boolean>(o)->data`
  | .bool_ => do
    let .boolean b ← tryObject .boolean o | .error (.unmodeled "")
    .ok (.bool b)
  -- builtin.hpp:181: `try_object<obj::character>(o)->data[0]`: the first byte of the UTF-8
  | .char_ => do
    let .character d ← tryObject .character o | .error (.unmodeled "")
    let b := (charDataBytes d).headD 0
    .ok (.int .char (Cxx.wrapTo p .char b.toNat))
  -- builtin.hpp:201: tagged → `static_cast<T>(as_integer)`, else `static_cast<T>(try_object<obj::integer>(o)->data)`
  | .enum_ n =>
    let u := (w.findEnum n).map (·.underlying) |>.getD .int
    match o with
    | .smallInteger i => .ok (.enumv n (Cxx.wrapTo p u i.toInt))
    | _ => do
      let .integer i ← tryObject .integer o | .error (.unmodeled "")
      .ok (.enumv n (Cxx.wrapTo p u i.toInt))
  -- builtin.hpp:232 (7135b7708): tagged → `static_cast<T>(as_integer)`, else
  -- `static_cast<T>(o.to_integer())` (it was `try_object<obj::integer>(o)->data` at f3d82d654)
  | .integral k =>
    match o with
    | .smallInteger i => .ok (.int k (Cxx.wrapTo p k i.toInt))
    | _ => do
      let i ← objectToInteger p o
      .ok (.int k (Cxx.wrapTo p k i))
  -- builtin.hpp:282 (7135b7708): tagged small real → `static_cast<T>(as_real)`, else
  -- `static_cast<T>(o.to_real())` (it was `try_object<obj::real>(o)->data` at f3d82d654)
  | .floating k =>
    match o with
    | .smallReal b => Cxx.convertNum p k (.f (Float.ofBits b))
    | _ => do
      let x ← objectToReal o
      Cxx.convertNum p k (.f x)
  -- builtin.hpp:312: `try_object<obj::persistent_string>(o)->data.c_str()` (a `char const *`)
  | .cString _ => do
    let .persistentString s ← tryObject .persistentString o | .error (.unmodeled "")
    .ok (.cstr (some s))
  -- builtin.hpp:333
  | .string_ => do
    let .persistentString s ← tryObject .persistentString o | .error (.unmodeled "")
    .ok (.str s)
  -- builtin.hpp:360
  | .vector e => do
    let .persistentVector _ xs ← tryObject .persistentVector o | .error (.unmodeled "")
    let some es := convertSpec w e | .error (.unmodeled "element")
    let vs ← xs.mapM (fromObjectElem p w es)
    .ok (.vec vs)
where
  /-- Elements of a vector: the integral/floating/string cases only. -/
  fromObjectElem (p : Platform) (w : World) (s : Spec) (o : Obj) : CRes CVal :=
    match s, o with
    | .integral k, .smallInteger i => .ok (.int k (Cxx.wrapTo p k i.toInt))
    | .integral k, o => do let i ← objectToInteger p o; .ok (.int k (Cxx.wrapTo p k i))
    | _, _ => .error (.unmodeled "vector element")

/-- The C++ type `convert<T>::from_object(object_ref)` returns (builtin.hpp): `T`, except the
C-string specialization, which returns `char const *` whatever `T` is (builtin.hpp:312). -/
def fromObjectReturnType (s : Spec) (t : CType) : CType :=
  match s with
  | .cString _ => .ptr (.const (.b .char))
  | _ => (Cxx.nonRef t).canonical.unqual

/-- `convert_function` (convert/function.hpp:13): wraps a native function pointer as a function
on `object_ref`s. When `R` and every `Args` are already `object_ref`, it is the pointer itself;
otherwise the lambda converts each argument with `convert<decay_t<Args>>::into_object` (not
`from_object`) before calling `fn` with it. Modeled as which conversion it applies to argument
`i`; it is used nowhere in the analyzer or codegen. -/
def convertFunctionArgConversion : String := "into_object"

/-! ## Opaque boxes (obj/opaque_box.hpp, c_api.cpp) -/

/-- `make_box<obj::opaque_box>(ptr, "<type>")` as `cpp/box` emits it (cpp_processor.cpp:1831):
the pointer (`jtl::ptr<void>`, const dropped by its `void const *` constructor) and the name. -/
structure OpaqueBox where
  addr : Nat
  canonicalType : String
  deriving Repr, BEq, Inhabited

/-- `jank_unbox_with_source(type, o, source)` (c_api.cpp:570): the box's pointer when its
recorded type is empty or equal to `type` (a string comparison), else throws
`runtime/invalid-unbox`. -/
def jankUnboxWithSource (type : String) (box : OpaqueBox) : CRes Nat :=
  if !box.canonicalType.isEmpty && box.canonicalType != type then
    .error (.thrown s!"This opaque box holds a `{box.canonicalType}`, but it was unboxed as a `{type}`.")
  else .ok box.addr

/-- `jank_unbox` (c_api.cpp:554): the same check, without source. -/
def jankUnbox := jankUnboxWithSource

/-- `jank_unbox_with_source_c` (c_api.cpp:590): the same check, source as a string. -/
def jankUnboxWithSourceC := jankUnboxWithSource

end Jank.Interop
