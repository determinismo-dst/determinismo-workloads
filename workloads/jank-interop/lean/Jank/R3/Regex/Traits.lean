/-!
# `std::regex_traits<char>` and `std::ctype<char>` as jank's `std::regex` sees them

libstdc++ 15.3.0 (`deps/libstdcxx-15.3.0/`): `regex.h` (`regex_traits`, lines 99–416),
`regex.tcc` (`lookup_collatename` 118, `lookup_classname` 266, `isctype` 320, `value` 338),
`ctype_base.h` (the GNU/Linux masks) and `ctype_configure_char.cc` (`ctype<char>` reads glibc's
`__ctype_b`, `__ctype_tolower`, `__ctype_toupper` tables of the locale).

jank builds every `std::regex` with the global C++ locale, which `jank_init_base`
(c_api.cpp 1108) sets to `std::locale("")`: the classic "C" locale when the environment names
none (or "C"/"POSIX"), else a named glibc locale (here: a UTF-8 one). `LC_NUMERIC` is set back to
"C" for the C library only; no regex function reads it.

`char` is signed on x86-64: comparisons in ranges and `_M_make_range` use the signed value
(`sval`). Bytes 0x80–0xFF have no class in glibc's C locale (C-ctype.c) and none in a UTF-8 locale
(a single byte ≥ 0x80 is not a character of the UTF-8 charmap) — assumption RXA1.
-/

namespace Jank.R3.Regex

/-- The value of a `char` on x86-64 (signed). -/
def sval (c : Nat) : Int := if c < 128 then (c : Int) else (c : Int) - 256

/-- The global C++ locale jank runs under. -/
inductive Loc where
  /-- `std::locale("")` with no locale in the environment (or "C"/"POSIX"): `locale::classic()`. -/
  | c
  /-- A named glibc UTF-8 locale (`LANG=en_US.UTF-8`, `C.UTF-8`, ...). -/
  | utf8
  deriving BEq, DecidableEq, Repr, Inhabited

def Loc.name : Loc → String
  | .c => "C"
  | .utf8 => "UTF-8"

/-! ## glibc class bits (our encoding of `_ISupper` ...) and libstdc++'s masks (ctype_base.h) -/

def bU : Nat := 1
def bL : Nat := 2
def bA : Nat := 4
def bD : Nat := 8
def bX : Nat := 16
def bS : Nat := 32
def bP : Nat := 64
def bC : Nat := 128
def bPu : Nat := 256
def bB : Nat := 512

/-- ctype_base.h: `graph = _ISalpha | _ISdigit | _ISpunct`, `alnum = _ISalpha | _ISdigit`. -/
def mUpper : Nat := bU
def mLower : Nat := bL
def mAlpha : Nat := bA
def mDigit : Nat := bD
def mXdigit : Nat := bX
def mSpace : Nat := bS
def mPrint : Nat := bP
def mGraph : Nat := bA ||| bD ||| bPu
def mCntrl : Nat := bC
def mPunct : Nat := bPu
def mAlnum : Nat := bA ||| bD
def mBlank : Nat := bB

/-- glibc's class bits of an ASCII code (the C locale's table; a UTF-8 locale classifies ASCII
the same way). -/
def asciiBits (n : Nat) : Nat :=
  let up := 0x41 ≤ n && n ≤ 0x5A
  let lo := 0x61 ≤ n && n ≤ 0x7A
  let di := 0x30 ≤ n && n ≤ 0x39
  let xd := di || (0x41 ≤ n && n ≤ 0x46) || (0x61 ≤ n && n ≤ 0x66)
  let sp := (0x09 ≤ n && n ≤ 0x0D) || n == 0x20
  let bl := n == 0x09 || n == 0x20
  let cn := n < 0x20 || n == 0x7F
  let pr := 0x20 ≤ n && n ≤ 0x7E
  let pu := pr && n != 0x20 && !up && !lo && !di
  (if up then bU else 0) ||| (if lo then bL else 0) ||| (if up || lo then bA else 0) |||
  (if di then bD else 0) ||| (if xd then bX else 0) ||| (if sp then bS else 0) |||
  (if pr then bP else 0) ||| (if cn then bC else 0) ||| (if pu then bPu else 0) |||
  (if bl then bB else 0)

/-- `ctype<char>::_M_table[(unsigned char)c]` in the locale (RXA1: no class at 0x80–0xFF). -/
def ctypeBits (_loc : Loc) (c : Nat) : Nat :=
  if c < 128 then asciiBits c else 0

/-- `ctype<char>::is(m, c)`: `_M_table[c] & m`. -/
def ctypeIs (loc : Loc) (m : Nat) (c : Nat) : Bool := (ctypeBits loc c &&& m) != 0

/-- `ctype<char>::tolower` (glibc's `__ctype_tolower`: ASCII letters only in both locales). -/
def ctolower (_loc : Loc) (c : Nat) : Nat :=
  if 0x41 ≤ c && c ≤ 0x5A then c + 32 else c

def ctoupper (_loc : Loc) (c : Nat) : Nat :=
  if 0x61 ≤ c && c ≤ 0x7A then c - 32 else c

/-! ## `regex_traits<char>` -/

/-- `regex_traits::_RegexMask`: a ctype mask and the `_S_under` extension (`[[:w:]]`). -/
structure RMask where
  base : Nat
  under : Bool
  deriving BEq, DecidableEq, Repr, Inhabited

def RMask.zero : RMask := { base := 0, under := false }
def RMask.or (a b : RMask) : RMask := { base := a.base ||| b.base, under := a.under || b.under }

/-- An ASCII text as bytes. -/
def bytesOf (s : String) : List Nat := s.toList.map Char.toNat

/-- regex.tcc `lookup_classname` (266): the name lowered with `ctype::tolower`, looked up in
`__classnames`; `__icase` maps `lower`/`upper` to `alpha` (jank never sets icase). Not found: 0. -/
def lookupClassname (loc : Loc) (name : List Nat) (icase : Bool := false) : RMask :=
  let s := name.map (ctolower loc)
  let table : List (String × RMask) := [
    ("d", ⟨mDigit, false⟩), ("w", ⟨mAlnum, true⟩), ("s", ⟨mSpace, false⟩),
    ("alnum", ⟨mAlnum, false⟩), ("alpha", ⟨mAlpha, false⟩), ("blank", ⟨mBlank, false⟩),
    ("cntrl", ⟨mCntrl, false⟩), ("digit", ⟨mDigit, false⟩), ("graph", ⟨mGraph, false⟩),
    ("lower", ⟨mLower, false⟩), ("print", ⟨mPrint, false⟩), ("punct", ⟨mPunct, false⟩),
    ("space", ⟨mSpace, false⟩), ("upper", ⟨mUpper, false⟩), ("xdigit", ⟨mXdigit, false⟩)]
  match table.find? (fun (n, _) => bytesOf n == s) with
  | some (_, m) =>
    if icase && (m.base == mLower || m.base == mUpper) then ⟨mAlpha, false⟩ else m
  | none => RMask.zero

/-- regex.tcc `isctype` (320): `is(f._M_base, c) || (f under && c == '_')`. -/
def isctype (loc : Loc) (c : Nat) (f : RMask) : Bool :=
  ctypeIs loc f.base c || (f.under && c == 0x5F)

/-- regex.tcc `__collatenames` (122–250): the 128 names, indexed by their character. -/
def collateNames : List String := [
  "NUL", "SOH", "STX", "ETX", "EOT", "ENQ", "ACK", "alert", "backspace", "tab", "newline",
  "vertical-tab", "form-feed", "carriage-return", "SO", "SI", "DLE", "DC1", "DC2", "DC3", "DC4",
  "NAK", "SYN", "ETB", "CAN", "EM", "SUB", "ESC", "IS4", "IS3", "IS2", "IS1", "space",
  "exclamation-mark", "quotation-mark", "number-sign", "dollar-sign", "percent-sign",
  "ampersand", "apostrophe", "left-parenthesis", "right-parenthesis", "asterisk", "plus-sign",
  "comma", "hyphen", "period", "slash", "zero", "one", "two", "three", "four", "five", "six",
  "seven", "eight", "nine", "colon", "semicolon", "less-than-sign", "equals-sign",
  "greater-than-sign", "question-mark", "commercial-at", "A", "B", "C", "D", "E", "F", "G", "H",
  "I", "J", "K", "L", "M", "N", "O", "P", "Q", "R", "S", "T", "U", "V", "W", "X", "Y", "Z",
  "left-square-bracket", "backslash", "right-square-bracket", "circumflex", "underscore",
  "grave-accent", "a", "b", "c", "d", "e", "f", "g", "h", "i", "j", "k", "l", "m", "n", "o", "p",
  "q", "r", "s", "t", "u", "v", "w", "x", "y", "z", "left-curly-bracket", "vertical-line",
  "right-curly-bracket", "tilde", "DEL"]

/-- regex.tcc `lookup_collatename` (118): a name of the table gives its one character; anything
else (digraphs included) gives "" (invalid). -/
def lookupCollatename (name : List Nat) : List Nat :=
  let rec go (i : Nat) : List String → List Nat
    | [] => []
    | n :: ns => if bytesOf n == name then [i] else go (i + 1) ns
  go 0 collateNames

/-- regex.h `transform_primary` (269): the locale's `collate<char>` is `std::collate<char>` in
both locales (localename.cc 264 builds the base class for a named locale too), so the string is
lowered with `ctype::tolower` and passed to `collate::transform` (`strxfrm_l`). In "C" that is the
identity; in the UTF-8 locale it is taken as an order-preserving key that is equal exactly when
the lowered strings are (assumption RXA2), so the comparison `==` in `_M_apply` gives the same
answers as the lowered strings themselves. -/
def transformPrimary (loc : Loc) (s : List Nat) : List Nat := s.map (ctolower loc)

/-- regex.tcc `value` (338) for `char`: '0'..'7'/'9', then a–f/A–F in radix 16, else -1. -/
def traitsValue (c : Nat) (radix : Nat) : Int :=
  let n := c
  let maxDigit := if radix == 8 then 0x37 else 0x39
  if 0x30 ≤ n && n ≤ maxDigit then (n - 0x30 : Nat)
  else if radix < 16 then -1
  else if n == 0x61 || n == 0x41 then 10
  else if n == 0x62 || n == 0x42 then 11
  else if n == 0x63 || n == 0x43 then 12
  else if n == 0x64 || n == 0x44 then 13
  else if n == 0x65 || n == 0x45 then 14
  else if n == 0x66 || n == 0x46 then 15
  else -1

end Jank.R3.Regex
