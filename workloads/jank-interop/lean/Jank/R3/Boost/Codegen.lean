import Jank.R3.Boost.Num

/-!
# Round 3, Boost: number constants through the code generator

codegen/cpp_processor.cpp:

- JIT (`compilation_target::eval`): `lift_constant` (131-213) refers to a boxed constant by its
  address (`{type}{ _jank_codegen{ }, (void*)0x… }`): the literal's own object, no text.
- AOT (`compilation_target::module`): the module header declares each lifted constant (2072-2077)
  and the load function rebuilds it (`new (&ns::name) auto(` `gen_constant(v, buffer, true)`
  `);`, 2176-2180). `gen_constant` (253-488) writes
  - a big integer as `jank::runtime::make_box<jank::runtime::obj::big_integer>("{to_string()}")`
    (305-310): at load, `big_integer(immutable_string)` (the only viable constructor for a
    `char const[N]`: boost's string constructor of `number` is explicit) → `init` → boost
    `assign` (decimal text: exact);
  - a big decimal as `jank::runtime::make_box<jank::runtime::obj::big_decimal>("{to_string()}")`
    (311-316): at load, `big_decimal(immutable_string)` → `rd_string(c_str())`, where
    `to_string()` is boost's `str()` plus `.0` when there is no `.` (string_builder.cpp:240-249);
  - a ratio as `jank::runtime::obj::ratio::create({n}, {d})` (317-323; round 2's R50).
-/

namespace Jank.R3.Boost.Codegen

open Jank.R3.Boost Jank.R3.Boost.Dec Jank.R3.Boost.Num

/-- The C++ expression `gen_constant` writes for a boxed number constant. -/
def genConstant : JV → String
  | .big v => s!"jank::runtime::make_box<jank::runtime::obj::big_integer>(\"{CppInt.str v}\")"
  | .dec d => s!"jank::runtime::make_box<jank::runtime::obj::big_decimal>(\"{decStr d}\")"
  | .ratio n d => s!"jank::runtime::obj::ratio::create({CppInt.str n}, {CppInt.str d})"
  | .long v => s!"_jank_int({v})"
  | .dbl x => s!"_jank_small_real({x})"

/-- What the AOT module's load function builds from that text: the object, or the exception
that aborts loading the module. -/
def aotLoad : JV → Except String JV
  | .big v =>
    match bigInit (bytes (CppInt.str v)) with
    | .ok w => .ok (.big w)
    | .error e => .error e
  | .dec d =>
    match rdString (bytes (decStr d)) with
    | .ok x => .ok (.dec x)
    | .error e => .error e
  | v => .ok v

/-- Same object value (decimals compared limb for limb: `prec_elem`, sign and class too). -/
def sameObj : JV → JV → Bool
  | .big a, .big b => a == b
  | .dec a, .dec b => a.data == b.data && a.exp == b.exp && a.neg == b.neg && a.fpclass == b.fpclass
  | _, _ => false

end Jank.R3.Boost.Codegen
