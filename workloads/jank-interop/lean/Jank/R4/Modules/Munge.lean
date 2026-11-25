/-!
# Round 4, modules: name munging and module ↔ path mapping

jank 7135b7708 (`compiler+runtime/`):

- `runtime/core/munge.cpp`: `munge_chars` (9–36), `demunge_chars` (40–67, longest first, `_` → `-`
  last), `cpp_keywords` (70–168), `munged_cpp_keywords` (170–268), `munge` (270–290: each byte
  replaced, then `__` appended when the whole result is a C++ keyword), `munge_and_replace`
  (292–299: munge, then `std::regex_replace`), `demunge` (318–350: the whole string a munged
  keyword drops its `__`; otherwise each pattern in turn, every occurrence left to right).
- `runtime/module/loader_dynamic.cpp`: `path_to_module` (36–50: demunge the whole path, cut the
  *original* path's extension length, `[\\/]` → `.` unless the text holds `$/`), `module_to_path`
  (52–56: munge, `.` → `/`), `module_to_load_function` (58–64: munge, `.` → `_`,
  `jank_load_` prefix).
- `std::filesystem::path::extension` (C++17 [fs.path.decompose]): from the last `.` of the
  filename, unless the filename is `.`/`..` or its only `.` is its first character.

Clojure 1.12 (`clojure-ref/src/clj/clojure/core.clj`): `root-resource` (5939–5946: `/` + the
lib's name with `-` → `_` and `.` → `/`), `root-directory` (5948–5954).
-/

namespace Jank.R4.Modules

/-- munge.cpp 9–36. -/
def mungeChar : Char → Option String
  | '-' => some "_" | ':' => some "_COLON_" | '+' => some "_PLUS_" | '>' => some "_GT_"
  | '<' => some "_LT_" | '=' => some "_EQ_" | '~' => some "_TILDE_" | '!' => some "_BANG_"
  | '@' => some "_CIRCA_" | '#' => some "_SHARP_" | '\'' => some "_SQUOTE_"
  | '"' => some "_DQUOTE_" | '%' => some "_PERC_" | '^' => some "_CARET_" | '&' => some "_AMP_"
  | '*' => some "_STAR_" | '|' => some "_BAR_" | '{' => some "_LBRACE_" | '}' => some "_RBRACE_"
  | '[' => some "_LBRACK_" | ']' => some "_RBRACK_" | '(' => some "_LPAREN_"
  | ')' => some "_RPAREN_" | '/' => some "_SLASH_" | '\\' => some "_BSLASH_" | '?' => some "_QMARK_"
  | _ => none

/-- munge.cpp 40–67, in the file's order (longest first; `_` → `-` last). -/
def demungeChars : List (String × Char) :=
  [("_LBRACE_", '{'), ("_RBRACE_", '}'), ("_LBRACK_", '['), ("_RBRACK_", ']'),
   ("_LPAREN_", '('), ("_RPAREN_", ')'), ("_BSLASH_", '\\'), ("_SQUOTE_", '\''),
   ("_DQUOTE_", '"'), ("_QMARK_", '?'), ("_COLON_", ':'), ("_TILDE_", '~'), ("_CIRCA_", '@'),
   ("_SHARP_", '#'), ("_CARET_", '^'), ("_SLASH_", '/'), ("_PERC_", '%'), ("_PLUS_", '+'),
   ("_BANG_", '!'), ("_STAR_", '*'), ("_AMP_", '&'), ("_BAR_", '|'), ("_GT_", '>'),
   ("_LT_", '<'), ("_EQ_", '='), ("_", '-')]

/-- munge.cpp 70–168. -/
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

/-- munge.cpp 270–290. -/
def munge (o : String) : String :=
  let m := String.join (o.toList.map fun c => (mungeChar c).getD (String.singleton c))
  if cppKeywords.contains m then m ++ "__" else m

/-- munge.cpp 318–350: `munged_cpp_keywords` is exactly the keywords with `__` appended. -/
def demunge (o : String) : String :=
  if cppKeywords.any (fun k => k ++ "__" == o) then (o.dropEnd 2).toString
  else demungeChars.foldl (fun s (pat, c) => s.replace pat (String.singleton c)) o

/-- The filename part of a path (after the last `/`). -/
def fileName (p : String) : String := ((p.splitOn "/").getLast?).getD p

/-- `std::filesystem::path::extension` of a generic POSIX path. -/
def extension (p : String) : String :=
  let f := fileName p
  if f == "." || f == ".." then ""
  else
    match (f.toList.reverse.findIdx? (· == '.')) with
    | none => ""
    | some k =>
      let i := f.length - 1 - k   -- position of the last '.'
      if i == 0 then "" else (f.drop i).toString

/-- `std::regex_replace(ret, std::regex{ R"([\\/])" }, ".")`. -/
def slashesToDots (s : String) : String := (s.replace "/" ".").replace "\\" "."

/-- loader_dynamic.cpp 36–50 `path_to_module`. -/
def pathToModule (path : String) : String :=
  let s := demunge path
  let ret := (s.take (s.length - (extension path).length)).toString
  if (ret.splitOn "$/").length > 1 then ret else slashesToDots ret

/-- loader_dynamic.cpp 52–56 `module_to_path`. -/
def moduleToPath (m : String) : String := (munge m).replace "." "/"

/-- loader_dynamic.cpp 58–64 `module_to_load_function`. -/
def moduleToLoadFunction (m : String) : String := "jank_load_" ++ (munge m).replace "." "_"

/-- loader_dynamic.cpp 547–549: `loader::find` replaces every `_` of the requested module with `-`. -/
def patchModule (m : String) : String := m.replace "_" "-"

/-! ## Clojure's side -/

/-- core.clj 5939–5946 `root-resource`. -/
def rootResource (lib : String) : String := "/" ++ (lib.replace "-" "_").replace "." "/"

/-- core.clj 5948–5954 `root-directory`. -/
def rootDirectory (lib : String) : String :=
  let d := rootResource lib
  match (d.toList.reverse.findIdx? (· == '/')) with
  | none => d
  | some k => (d.take (d.length - 1 - k)).toString

end Jank.R4.Modules
