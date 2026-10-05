import LexerSpec.Reading

/-!
# Claims

What is claimed about the spec and about a lexer. The claims are trusted as much as the
spec: a proof shows that a claim holds, so the claim has to say what is meant.
-/

namespace LexerSpec

/-! ## About the spec -/

/-- Every input has at most one reading. -/
def Unique : Prop :=
  ∀ version input tokens tokens',
    Reads version input tokens → Reads version input tokens' → tokens = tokens'

/-- The characters fed so far can still be continued into an input that has a reading. -/
def Viable (version : Version) (fed : Chars) : Prop :=
  ∃ rest tokens, Reads version (fed ++ rest) tokens

/-- Every reading of every continuation of the characters fed so far starts with the tokens. -/
def Determined (version : Version) (fed : Chars) (tokens : List Token) : Prop :=
  ∀ rest tokens', Reads version (fed ++ rest) tokens' → tokens <+: tokens'

/-! ## What a lexer hands over -/

/-- A location in the input, all zero-based. -/
structure Location where
  offset : Nat
  line : Nat
  column : Nat
  deriving DecidableEq, Repr

/--
The location of `offset` in the input: lines are counted by line feeds (10) alone, and
columns by characters.
-/
def locate (input : Chars) (offset : Nat) : Location :=
  let before := input.take offset
  { offset, line := before.count 10, column := (before.reverse.takeWhile (· ≠ 10)).length }

/-- The token types of the implementation. -/
inductive TokenType where
  | parenOpen
  | parenClose
  | numeral
  | decimal
  | hexadecimal
  | binary
  | string
  | keyword
  | unquotedSymbol
  | quotedSymbol
  | endOfFile
  deriving DecidableEq, Repr

/-- Which kind of reserved word a token is. -/
inductive ReservedKind where
  | general
  | command
  deriving DecidableEq, Repr

/-- A token as the implementation hands it over. -/
structure Handed where
  type : TokenType
  start : Location
  «end» : Location
  reserved : Option ReservedKind
  content : Chars
  deriving DecidableEq, Repr

/-- The type of a token of each kind; a reserved word is an unquoted symbol. -/
def Category.type : Category → TokenType
  | .parenOpen => .parenOpen
  | .parenClose => .parenClose
  | .numeral => .numeral
  | .decimal => .decimal
  | .hexadecimal => .hexadecimal
  | .binary => .binary
  | .string => .string
  | .simpleSymbol | .reserved => .unquotedSymbol
  | .quotedSymbol => .quotedSymbol
  | .keyword => .keyword

/--
The content of a token: what a string literal stands for, the name of a quoted symbol
without its bars, a keyword without its colon, the digits of a hexadecimal or binary without
`#x` or `#b`, and otherwise the characters of the token.
-/
def Token.content (version : Version) (token : Token) : Chars :=
  match token.category with
  | .string => (if version = .v2_0 then unescape20 else unescape) (token.text.drop 1).dropLast
  | .quotedSymbol => (token.text.drop 1).dropLast
  | .keyword => token.text.drop 1
  | .hexadecimal | .binary => token.text.drop 2
  | _ => token.text

/-- Which kind of reserved word a token is, if it is one. -/
def Token.reservedKind (version : Version) (token : Token) : Option ReservedKind :=
  if token.category ≠ .reserved then none
  else if ∃ w ∈ basicReservedWords version, token.text = chars w then some .general
  else some .command

/-- The token as the implementation hands it over. -/
def Token.handed (version : Version) (input : Chars) (token : Token) : Handed :=
  { type := token.category.type
    start := locate input token.offset
    «end» := locate input (token.offset + token.text.length)
    reserved := token.reservedKind version
    content := token.content version }

/-- The end-of-file token after the input. -/
def endOfFile (input : Chars) : Handed :=
  { type := .endOfFile, start := locate input input.length, «end» := locate input input.length,
    reserved := none, content := [] }

/-! ## About a lexer -/

/--
A lexer of whole inputs is correct: it hands over the tokens of the reading and the
end-of-file token exactly when the input has a reading.
-/
def LexerCorrect (lex : Version → Chars → Option (List Handed)) : Prop :=
  ∀ version input handed, lex version input = some handed ↔
    ∃ tokens, Reads version input tokens ∧
      handed = tokens.map (·.handed version input) ++ [endOfFile input]

/--
A lexer fed in slices is correct: `feed version slices` is what it handed over after the
slices, and whether it failed. It fails exactly when the characters fed stop being viable,
and what it hands over is determined by the longest viable part of them.
-/
def StreamingCorrect (feed : Version → List Chars → List Handed × Bool) : Prop :=
  ∀ version slices, let fed := slices.flatten
    ((feed version slices).2 = true ↔ ¬ Viable version fed) ∧
    ∃ viable tokens, viable <+: fed ∧ Viable version viable ∧
      (∀ longer, longer <+: fed → Viable version longer → longer.length ≤ viable.length) ∧
      Determined version viable tokens ∧
      (feed version slices).1 = tokens.map (·.handed version fed)

end LexerSpec
