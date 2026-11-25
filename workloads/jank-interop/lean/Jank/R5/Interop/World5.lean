import Jank.R5.Interop.Ops5
import Jank.R3.Interop.Worlds

/-!
# Round 5, world XXII: operator templates, `=`, `+=`, `aget`, the call operator, `++`, unary `&`

The C++ the cases declare (each test puts it in its own `cpp/raw`):

```cpp
struct mo { int v{}; mo() = default; mo(int x) : v(x) {} mo(mo &&) = default;
            mo &operator=(mo &&) = default; };                       // copy assignment deleted
namespace vt { struct V {}; struct W {};
  template <typename T> int operator+(V const &, T &&) { return std::is_lvalue_reference_v<T> ? 1 : 2; }
  inline int operator-(V const &, int const &) { return 1; }
  inline int operator-(V const &, int &&) { return 2; }
  inline int operator*(int &, V const &) { return 3; } }
struct vr { int operator*(int &&) const { return 1; }
            template <typename T> int operator/(T &&) const { return std::is_lvalue_reference_v<T> ? 1 : 2; } };
struct B6 { int operator()(int) const { return 3; } int operator|(int) const { return 5; } };
struct D6 : B6 { using B6::operator(); using B6::operator|;
                 int operator()(long) const { return 4; } int operator|(long) const { return 6; } };
inline int twice(int x) { return 2 * x; }
struct sf { using fp = int (*)(int); operator fp() const { return &twice; } };   // surrogate (value 7 below)
struct bf { int d[3]{ 1, 2, 3 }; operator int *() { return d; } };
namespace lib { struct P {}; }
namespace ext { inline int operator+(lib::P const &, lib::P const &) { return 9; } }
namespace lib { using ext::operator+; }
namespace tn { struct T { template <typename A> friend int operator&(A const &, T const &) { return 13; } };
  template <typename A> requires std::is_integral_v<std::remove_cvref_t<A>> int operator%(T const &, A &&) { return 11; }
  template <typename A, typename R = long> R operator^(T const &, A) { return 12; } }
struct B9 { B9 &operator=(int) { return *this; } };
struct D9 : B9 { D9() = default; D9(int) {} };
struct Q { operator int() const { return 1; } };
```
with a global of each class (`cpp/gmo`, `cpp/vt.gv`, …).
-/

namespace Jank.R5.Interop.World5

open Jank.Interop
open Jank.R3.Interop
open Jank.R3.Interop.Clang
open Jank.R5.Interop.Ops5

def rc (n : String) : CType := .record n
def cref (t : CType) : CType := .lref (.const t)
def int : CType := .b .int

def world : W5 :=
  { classes :=
      [{ name := "mo", ctorFrom := [int], copyDeleted := true },
       { name := "vt::V", ns := "vt" },
       { name := "vt::W", ns := "vt" },
       { name := "vr" },
       { name := "B6" },
       { name := "D6", bases := ["B6"], usingOps := [("B6", .call), ("B6", .pipe)] },
       { name := "sf", convertsTo := [.ptr (.fn int [int])] },
       { name := "bf", convertsTo := [.ptr int] },
       { name := "lib::P", ns := "lib" },
       { name := "tn::T", ns := "tn" },
       { name := "B9" },
       { name := "D9", bases := ["B9"], ctorFrom := [int] },
       { name := "Q", convertsTo := [int] }],
    fns :=
      [{ id := "vt::operator+<T>(vt::V const&, T&&)", op := .plus, ns := "vt", tparams := 1,
         params := [.fixed (cref (rc "vt::V")), .fwd 0], body := .lrefT 0 1 2 },
       { id := "vt::operator-(vt::V const&, int const&)", op := .minus, ns := "vt",
         params := [.fixed (cref (rc "vt::V")), .fixed (cref int)], body := .const 1 },
       { id := "vt::operator-(vt::V const&, int&&)", op := .minus, ns := "vt",
         params := [.fixed (cref (rc "vt::V")), .fixed (.rref int)], body := .const 2 },
       { id := "vt::operator*(int&, vt::V const&)", op := .star, ns := "vt",
         params := [.fixed (.lref int), .fixed (cref (rc "vt::V"))], body := .const 3 },
       { id := "vr::operator*(int&&) const", op := .star, member := some "vr",
         params := [.fixed (.rref int)], body := .const 1 },
       { id := "vr::operator/<T>(T&&) const", op := .slash, member := some "vr", tparams := 1,
         params := [.fwd 0], body := .lrefT 0 1 2 },
       { id := "B6::operator()(int) const", op := .call, member := some "B6", params := [.fixed int], body := .const 3 },
       { id := "B6::operator|(int) const", op := .pipe, member := some "B6", params := [.fixed int], body := .const 5 },
       { id := "D6::operator()(long) const", op := .call, member := some "D6", params := [.fixed (.b .long)], body := .const 4 },
       { id := "D6::operator|(long) const", op := .pipe, member := some "D6", params := [.fixed (.b .long)], body := .const 6 },
       { id := "ext::operator+(lib::P const&, lib::P const&)", op := .plus, ns := "ext",
         params := [.fixed (cref (rc "lib::P")), .fixed (cref (rc "lib::P"))], body := .const 9 },
       { id := "tn::operator&<A>(A const&, tn::T const&) (hidden friend)", op := .amp, ns := "tn",
         friendOf := some "tn::T", tparams := 1, params := [.cref 0, .fixed (cref (rc "tn::T"))], body := .const 13 },
       { id := "tn::operator%<A>(tn::T const&, A&&) requires integral", op := .percent, ns := "tn", tparams := 1,
         params := [.fixed (cref (rc "tn::T")), .fwd 0], constraint := .integralDecayed 0, body := .const 11 },
       { id := "tn::operator^<A, R = long>(tn::T const&, A)", op := .caret, ns := "tn", tparams := 2,
         defaults := [none, some (.b .long)], params := [.fixed (cref (rc "tn::T")), .byVal 0],
         ret := .param 1, body := .const 12 },
       { id := "B9::operator=(int)", op := .equal, member := some "B9", params := [.fixed int],
         ret := .fixed (.lref (rc "B9")), body := .assign }],
    usingNs := [("lib", "ext::operator+(lib::P const&, lib::P const&)")] }

def operands : List Ops5.Operand :=
  [{ text := "cpp/gmo", type := rc "mo", kind := .global },
   { text := "(cpp/mo. 5)", type := rc "mo", kind := .temp },
   { text := "cpp/vt.gv", type := rc "vt::V", kind := .global },
   { text := "cpp/vt.gw", type := rc "vt::W", kind := .global },
   { text := "(cpp/vt.W.)", type := rc "vt::W", kind := .temp },
   { text := "cpp/gvr", type := rc "vr", kind := .global },
   { text := "cpp/gd6", type := rc "D6", kind := .global },
   { text := "cpp/gsf", type := rc "sf", kind := .global },
   { text := "cpp/gbf", type := rc "bf", kind := .global },
   { text := "cpp/lib.gp", type := rc "lib::P", kind := .global },
   { text := "cpp/tn.gt", type := rc "tn::T", kind := .global },
   { text := "cpp/gd9", type := rc "D9", kind := .global },
   { text := "cpp/gq", type := rc "Q", kind := .global },
   { text := "1", type := int, kind := .literal },
   { text := "x", type := int, kind := .named },
   { text := "2.5", type := .b .double, kind := .literal }]

def binaryOps : List (Cxx.Op × String) :=
  [(.plus, "+"), (.minus, "-"), (.star, "*"), (.slash, "/"), (.pipe, "|"), (.percent, "%"),
   (.caret, "^"), (.amp, "&"), (.equal, "="), (.plusEqual, "+="), (.subscript, "aget")]

def unaryOps : List (Cxx.Op × String) := [(.plusPlus, "++"), (.amp, "&")]

structure Case where
  op : Cxx.Op
  opText : String
  args : List Ops5.Operand
  deriving Inhabited

def Case.text (c : Case) : String :=
  let body := if c.op == .call then s!"({" ".intercalate (c.args.map (·.text))})"
    else s!"(cpp/{c.opText} {" ".intercalate (c.args.map (·.text))})"
  if c.args.any (·.kind == .named) then s!"(let [x (cpp/int. 1)] {body})" else body

def allCases : List Case :=
  (binaryOps.flatMap fun (op, t) => operands.flatMap fun a => operands.map fun b => { op, opText := t, args := [a, b] }) ++
  (unaryOps.flatMap fun (op, t) => operands.map fun a => { op, opText := t, args := [a] }) ++
  ((operands.filter fun o => isRecordType o.type).flatMap fun f => operands.map fun a => { op := .call, opText := "()", args := [f, a] })

def outs (p : Platform) (fx : Fix) (c : Case) : Out × Out :=
  (jankOut p world fx c.op c.args, cppOut p world c.op c.args)

/-- The smallest set of mechanisms (one, then two) whose C++ rule makes the case agree. -/
def classify (p : Platform) (c : Case) : Option String := Id.run do
  let (j, cpp) := outs p {} c
  if agree j cpp then return none
  for (n, fx) in fixNames do
    if agree (jankOut p world fx c.op c.args) cpp then return some n
  for (n1, f1) in fixNames do
    for (n2, f2) in fixNames do
      if n1 < n2 && agree (jankOut p world (f1.union f2) c.op c.args) cpp then return some s!"{n1}+{n2}"
  return some "unexplained"

def allFix : Fix := fixNames.foldl (fun a (_, f) => a.union f) {}

def judge (p : Platform) (c : Case) : Option (String × String) :=
  match classify p c with
  | none => none
  | some cls =>
    let (j, cpp) := outs p {} c
    some (cls, s!"{c.text}: C++ {cpp.show}; jank {j.show}")

def body (skip : List String) : EStateM Determinismo.Stop Jank.Interop.Search.W Unit := do
  let c ← Jank.Interop.Search.pickW "r5.operator.case" allCases
  if let some (cls, d) := judge x86_64 c then
    if !skip.contains cls then Determinismo.violate (σ := Jank.Interop.Search.W) s!"operator5:{cls}" (d.take 500 |>.toString)

end Jank.R5.Interop.World5
