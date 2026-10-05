import LexerSpec.Regex

/-!
# The lexicon

The lexical tokens of SMT-LIB and the categories they are built from, in the versions 2.0,
2.5, 2.6 and 2.7, in the order the standard defines them. Each definition states the rule it
formalises. Where the standard is silent or contradicts itself, the definition says so and
which reading it takes.
-/

namespace LexerSpec

open Regex

/-- The versions of the standard. -/
inductive Version where
  | v2_0
  | v2_5
  | v2_6
  | v2_7
  deriving DecidableEq, Repr

/-- The versions up to the version, oldest first. -/
def Version.upTo : Version → List Version
  | .v2_0 => [.v2_0]
  | .v2_5 => [.v2_0, .v2_5]
  | .v2_6 => [.v2_0, .v2_5, .v2_6]
  | .v2_7 => [.v2_0, .v2_5, .v2_6, .v2_7]

/-! ## Characters -/

/-- ⟨white_space_char⟩: 9 (tab), 10 (line feed), 13 (carriage return) or 32 (space). -/
def whiteSpaceChar : Regex := altAll [code 9, code 10, code 13, code 32]

/--
⟨printable_char⟩: a character from 32 to 126, or from 128 on.

In every version, characters from 128 on are allowed where 2.5 and later allow them: in
string literals, quoted symbols and comments. The 2.0 standard limits source files to ASCII
characters; this is not followed, because 2.0 is used mainly to read old scripts into 2.5
and later, or to give a solver that reads 2.5 and later a legacy mode, where accepting these
characters as 2.5 does is what is wanted.
-/
def printableChar : Regex := alt (range 32 126) (range 128 255)

/-- ⟨digit⟩: a character from 48 to 57 (`0` to `9`). -/
def digit : Regex := range 48 57

/-- ⟨letter⟩: a character from 65 to 90 (`A` to `Z`) or from 97 to 122 (`a` to `z`). -/
def letter : Regex := alt (range 65 90) (range 97 122)

/-- A line-breaking character: 10 or 13. -/
def lineBreak : Regex := alt (code 10) (code 13)

/-! ## Comments and whitespace -/

/--
A comment: a sequence that begins with `;` and ends with the first subsequent
line-breaking character.
-/
def comment : Regex := seq (lit ";") (seq (star (minus anyChar lineBreak)) lineBreak)

/--
A comment that runs to the end of the input. The line-breaking character terminates a
comment; a comment need not be terminated to be one.
-/
def commentAtEnd : Regex := seq (lit ";") (star (minus anyChar lineBreak))

/-- Whitespace: comments and white space characters, outside string literals and symbols. -/
def whitespace : Regex := star (alt whiteSpaceChar comment)

/-- Whitespace at the end of the input, which may end with a comment that runs to the end. -/
def whitespaceAtEnd : Regex := seq whitespace (alt (lit "") commentAtEnd)

/-! ## Tokens -/

/-- ⟨numeral⟩: the digit `0`, or a non-empty sequence of digits not starting with `0`. -/
def numeral : Regex := alt (lit "0") (minus (plus digit) (startsWith (lit "0")))

/-- ⟨decimal⟩: ⟨numeral⟩`.``0`*⟨numeral⟩. -/
def decimal : Regex := seq numeral (seq (lit ".") (seq (star (lit "0")) numeral))

/--
⟨hexadecimal⟩: `#x` followed by a non-empty sequence of digits and of letters from `A` to
`F`, capitalised or not.
-/
def hexadecimal : Regex := seq (lit "#x") (plus (altAll [digit, range 65 70, range 97 102]))

/-- ⟨binary⟩: `#b` followed by a non-empty sequence of the characters `0` and `1`. -/
def binary : Regex := seq (lit "#b") (plus (oneOf "01"))

/--
⟨string⟩ from 2.5 on: a sequence of printable and white space characters delimited by `"`.
A `"` within it occurs only duplicated, as `""`.
-/
def string : Regex :=
  seq (lit "\"")
    (seq (star (alt (minus (alt printableChar whiteSpaceChar) (lit "\"")) (lit "\"\"")))
      (lit "\""))

/-- What the inside of a string literal from 2.5 on stands for: each `""` stands for `"`. -/
def unescape : Chars → Chars
  | a :: b :: rest => if a = 34 ∧ b = 34 then 34 :: unescape rest else a :: unescape (b :: rest)
  | x => x

/--
⟨string⟩ in 2.0: a sequence of printable characters delimited by `"`, possibly containing
the escape sequences `\"` and `\\`; a backslash before any other character is just a
backslash, and the character after it is taken with it. In 2.0, the printable characters
include tab and the line-breaking characters: its rules for quoted symbols say so once and
then call the same characters printable, and 2.5 calls its explicit rule a clarification.
-/
def string20 : Regex :=
  seq (lit "\"")
    (seq (star (alt (minus (alt printableChar whiteSpaceChar) (oneOf "\"\\"))
        (seq (lit "\\") (alt printableChar whiteSpaceChar))))
      (lit "\""))

/-- What the inside of a string literal in 2.0 stands for: `\"` stands for `"`, `\\` for `\`. -/
def unescape20 : Chars → Chars
  | a :: b :: rest =>
    if a = 92 ∧ (b = 34 ∨ b = 92) then b :: unescape20 rest else a :: unescape20 (b :: rest)
  | x => x

/-- The reserved words each version adds to the basic set; no version removes one. -/
def addedBasicReservedWords : Version → List String
  | .v2_0 => ["par", "NUMERAL", "DECIMAL", "STRING", "_", "!", "as", "let", "forall", "exists"]
  | .v2_5 => ["BINARY", "HEXADECIMAL"]
  | .v2_6 => ["match"]
  | .v2_7 => ["lambda"]

/-- The basic set of reserved words: those added by the version and by every earlier one. -/
def basicReservedWords (version : Version) : List String :=
  version.upTo.flatMap addedBasicReservedWords

/--
The command names each version adds to the scripting language; no version removes one.
`define-funs-rec` is a command from 2.5 on, although the standard's own lists of reserved
command names leave it out.
-/
def addedCommandNames : Version → List String
  | .v2_0 => ["assert", "check-sat", "declare-sort", "declare-fun", "define-sort",
      "define-fun", "exit", "get-assertions", "get-assignment", "get-info", "get-option",
      "get-proof", "get-unsat-core", "get-value", "pop", "push", "set-logic", "set-info",
      "set-option"]
  | .v2_5 => ["check-sat-assuming", "declare-const", "define-fun-rec", "define-funs-rec",
      "echo", "get-model", "get-unsat-assumptions", "reset", "reset-assertions"]
  | .v2_6 => ["declare-datatype", "declare-datatypes"]
  | .v2_7 => ["declare-sort-parameter", "define-const"]

/--
The command names of the scripting language, each also a reserved word: those added by the
version and by every earlier one.
-/
def commandNames (version : Version) : List String :=
  version.upTo.flatMap addedCommandNames

/-- ⟨reserved⟩: a reserved word, from the basic set or a command name. -/
def reserved (version : Version) : Regex :=
  litOneOf (basicReservedWords version ++ commandNames version)

/-- The characters `~ ! @ $ % ^ & * _ - + = < > . ? /` allowed in simple symbols. -/
def symbolPunctuation : Regex := oneOf "~!@$%^&*_-+=<>.?/"

/--
A simple symbol: a non-empty sequence of letters, digits and the characters of
`symbolPunctuation`, that does not start with a digit and is not a reserved word.
-/
def simpleSymbol (version : Version) : Regex :=
  minus (minus (plus (altAll [letter, digit, symbolPunctuation])) (startsWith digit))
    (reserved version)

/--
A quoted symbol: a sequence of white space and printable characters that starts and ends
with `|` and does not otherwise contain `|` or `\`.
-/
def quotedSymbol : Regex :=
  seq (lit "|") (seq (star (minus (alt whiteSpaceChar printableChar) (oneOf "|\\"))) (lit "|"))

/--
⟨keyword⟩: `:` followed by a non-empty sequence of letters, digits and the characters of
`symbolPunctuation`, as 2.0 states it. From 2.5 on the standard writes `:⟨simple_symbol⟩`,
which read literally would forbid a keyword to start with a digit or to name a reserved
word; its own example `:56` shows that the characters of simple symbols are meant, so the
2.0 rule is taken for every version. In every version, `:` alone is not a keyword.
-/
def keyword : Regex := seq (lit ":") (plus (altAll [letter, digit, symbolPunctuation]))

end LexerSpec
