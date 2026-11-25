/-!
# Text primitives the code generator prints with

Replicas (paths under `upstream/compiler+runtime/`):

- `include/cpp/jank/util/fmt.hpp` `util::format` / `util::format_to`: jank's own formatter. Each
  argument replaces the next `{}` of the format string; an argument with no `{}` left is dropped;
  the rest of the format string is copied after the last argument (any `{}` left in it is copied
  as is). With no argument at all a `{}` throws (`src/cpp/jank/util/fmt.cpp`).
- `src/cpp/jtl/string_builder.cpp` `operator()` for `bool`, the integer types (`snprintf` with
  `%d`/`%li`/`%lld`/`%lu`/`%llu`), `char`, `char const *` (copied up to the first NUL), and
  `double` (in `Jank.Codegen.Float`).
- `src/cpp/jank/util/escape.cpp` `escape` / `unescape`.
- `src/cpp/jank/runtime/core/munge.cpp` `munge`, `munge_and_replace` (owned by the strings agent;
  replicated here only as far as the code generator calls it).

Text is `List UInt8` where bytes matter (string literal contents), `String` for generated code
whose identifiers are ASCII.
-/

namespace Jank.Codegen

/-- `util::format_to(sb, fmt, args...)` (fmt.hpp:18-44): for each argument in order, the format
string is copied up to the next `{}`, which the argument replaces; when there is none, the copy
reaches the end and the argument is dropped. Then the rest of the format string is copied
(`sb(fmt)`, no check). -/
def formatTo (fmt : String) (args : List String) : String := Id.run do
  let mut rest := fmt.toList
  let mut out : String := ""
  for a in args do
    let mut done := false
    -- fmt.hpp:21-31: `for(; *fmt != '\0'; ++fmt) { if(*fmt == '{' && *(fmt + 1) == '}') ... }`
    let mut fuel := rest.length + 1
    while !done && fuel > 0 do
      fuel := fuel - 1
      match rest with
      | '{' :: '}' :: r => out := out ++ a; rest := r; done := true
      | c :: r => out := out.push c; rest := r
      | [] => done := true
  return out ++ String.ofList rest

/-- `util::format(fmt)` / `format_to(sb, fmt)` with no argument (fmt.cpp:5-25): throws when the
format string contains `{}`. -/
def format0 (fmt : String) : Except String String :=
  if (fmt.splitOn "{}").length > 1 then .error "Format string has extra {} with no matching argument"
  else .ok fmt

/-- `string_builder::operator()(bool)` (string_builder.cpp:59). -/
def sbBool (b : Bool) : String := if b then "true" else "false"

/-- `string_builder::operator()(int|long|long long|unsigned long|unsigned long long)`
(string_builder.cpp:170-233): `snprintf` `%d`, `%li`, `%lld`, `%lu`, `%llu`: the decimal value,
a `-` for negatives. -/
def sbInt (i : Int) : String := toString i

/-- An `i64` as `string_builder` prints it. -/
def sbI64 (v : BitVec 64) : String := sbInt v.toInt
/-- An `i32` as `string_builder` prints it (the `int` overload). -/
def sbI32 (v : BitVec 32) : String := sbInt v.toInt

/-! ## util::escape (escape.cpp:148-201) -/

/-- `util::escape`: `\n \t \r \\ " \a \v \f \b` become two-character escapes; every other byte,
NUL and bytes ≥ 0x80 included, is copied unchanged. -/
def escapeByte (c : UInt8) : List UInt8 :=
  let bs := (92 : UInt8)  -- '\\'
  match c.toNat with
  | 10 => [bs, 110]   -- \n
  | 9 => [bs, 116]    -- \t
  | 13 => [bs, 114]   -- \r
  | 92 => [bs, 92]    -- \\
  | 34 => [bs, 34]    -- \"
  | 7 => [bs, 97]     -- \a
  | 11 => [bs, 118]   -- \v
  | 12 => [bs, 102]   -- \f
  | 8 => [bs, 98]     -- \b
  | _ => [c]

def escape (input : List UInt8) : List UInt8 := input.flatMap escapeByte

/-- `escape` on a `String` (its UTF-8 bytes); the result as a `String` when it is valid UTF-8
(it always is when the input is, since only ASCII bytes are added). -/
def escapeStr (s : String) : String :=
  match String.fromUTF8? (ByteArray.mk (escape s.toUTF8.toList).toArray) with
  | some r => r
  | none => s

/-! ## munge (munge.cpp:9-299) -/

/-- `munge_chars` (munge.cpp:9-36). -/
def mungeChar (c : Char) : Option String :=
  match c with
  | '-' => some "_" | ':' => some "_COLON_" | '+' => some "_PLUS_" | '>' => some "_GT_"
  | '<' => some "_LT_" | '=' => some "_EQ_" | '~' => some "_TILDE_" | '!' => some "_BANG_"
  | '@' => some "_CIRCA_" | '#' => some "_SHARP_" | '\'' => some "_SQUOTE_"
  | '"' => some "_DQUOTE_" | '%' => some "_PERC_" | '^' => some "_CARET_" | '&' => some "_AMP_"
  | '*' => some "_STAR_" | '|' => some "_BAR_" | '{' => some "_LBRACE_" | '}' => some "_RBRACE_"
  | '[' => some "_LBRACK_" | ']' => some "_RBRACK_" | '(' => some "_LPAREN_"
  | ')' => some "_RPAREN_" | '/' => some "_SLASH_" | '\\' => some "_BSLASH_" | '?' => some "_QMARK_"
  | _ => none

/-- `cpp_keywords` (munge.cpp:70-166). -/
def cppKeywords : List String :=
  ["alignas", "alignof", "and", "and_eq", "asm", "atomic_cancel", "atomic_commit",
   "atomic_noexcept", "auto", "bitand", "bitor", "bool", "break", "case", "catch", "char",
   "char8_t", "char16_t", "char32_t", "class", "compl", "concept", "const", "consteval",
   "constexpr", "constinit", "const_cast", "continue", "co_await", "co_return", "co_yield",
   "decltype", "default", "delete", "do", "double", "dynamic_cast", "else", "enum", "explicit",
   "export", "extern", "false", "float", "for", "friend", "goto", "if", "inline", "int", "long",
   "mutable", "namespace", "new", "noexcept", "not", "not_eq", "nullptr", "operator", "or",
   "or_eq", "private", "protected", "public", "reflexpr", "register", "reinterpret_cast",
   "requires", "return", "short", "signed", "sizeof", "static", "static_assert", "static_cast",
   "struct", "switch", "synchronized", "template", "this", "thread_local", "throw", "true", "try",
   "typedef", "typeid", "typename", "union", "unsigned", "using", "virtual", "void", "volatile",
   "wchar_t", "while", "xor", "xor_eq"]

/-- The character loop of `munge` (munge.cpp:270-282), on characters: each one replaced per
`munge_chars`. Every replaced character is ASCII, so looping over `char`s (bytes) or `Char`s is
the same. -/
def mungeCore : List Char → List Char
  | [] => []
  | c :: cs => (match mungeChar c with
      | some r => r.toList
      | none => [c]) ++ mungeCore cs

/-- `munge(immutable_string)` (munge.cpp:268-290): the character loop, then `__` appended when
the whole result is a C++ keyword. -/
def munge (o : String) : String :=
  let munged := String.ofList (mungeCore o.toList)
  if cppKeywords.contains munged then munged ++ "__" else munged

/-- `munge_and_replace(o, "\\.", "_")` (munge.cpp:292-299): munge, then every `.` replaced by `_`
(`std::regex_replace` with the regex `\.`). The code generator only calls it with that regex. -/
def mungeAndReplaceDots (o : String) : String :=
  String.ofList ((munge o).toList.map fun c => if c == '.' then '_' else c)

/-- A plain decimal for counters (`context::unique_string`: `"{}_{}"` of the prefix and the
namespace's incremented `symbol_counter`, context.cpp:380-384). -/
def uniqueString (pfx : String) (counter : Nat) : String := s!"{pfx}_{counter}"

/-! ## Theorems

On the character loop (`decide` cannot evaluate `String` operations; none of these results is a
C++ keyword, so `munge` adds nothing to them: checked when the exe runs). -/

/-- `a-b` and `a_b` munge alike. -/
theorem munge_dash_underscore : mungeCore ['a', '-', 'b'] = mungeCore ['a', '_', 'b'] := by decide

/-- `x?` and `x_QMARK_` munge alike. -/
theorem munge_qmark_collision :
    mungeCore ['x', '?'] = mungeCore ['x', '_', 'Q', 'M', 'A', 'R', 'K', '_'] := by decide

/-- `.` is not munged: a local named `a.b` stays an invalid C++ identifier. -/
theorem munge_keeps_dot : mungeCore ['a', '.', 'b'] = ['a', '.', 'b'] := by decide

end Jank.Codegen
