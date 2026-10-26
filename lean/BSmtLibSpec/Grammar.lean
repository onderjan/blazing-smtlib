module

public import BSmtLibSpec.Lexicon
public import BSmtLibSpec.Grammar.Tree

@[expose] public section

/-!
# Grammar

The syntax of SMT-LIB scripts as the standard defines it, in four parts:

- `Tree`: the syntax trees, one type per syntactic category, which record everything a script
  writes but the whitespace between its tokens.
- `Syntax`: how each tree is written as tokens (`tokens`), and which trees each version has
  (`Valid`).
- `File`: how the characters of a file are read as commands, in the reading mode each command
  leaves.
- `Script`: which sequences of commands, each in its version, make a script.

This module holds what the parts share: a token as the syntactic rules see it (`SyntaxToken`),
the numbers of the versions, and how parentheses and reserved words are written as tokens.

Scripts only: theory declarations, logic declarations and command responses are
not covered.
-/

namespace BSmtLibSpec.Grammar

open BSmtLibSpec.Lexicon
open Regex (Chars chars)

/-- The version is `first` or a later one. -/
def versionAtLeast (version first : Version) : Prop :=
  first ∈ version.upTo

/-- The number of the version, as a decimal. -/
def versionNumber : Version → Chars
  | .v2_0 => chars "2.0"
  | .v2_5 => chars "2.5"
  | .v2_6 => chars "2.6"
  | .v2_7 => chars "2.7"

/-- The version whose number the decimal is, if it is one. -/
def versionOfNumber (decimal : Chars) : Option Version :=
  [Version.v2_0, .v2_5, .v2_6, .v2_7].find? (versionNumber · = decimal)

/--
A token as the syntactic rules see it: what the lexical token stands for, and for a symbol
whether it was quoted.

Standard: 2.7 §3.1 Symbols: a simple symbol and its quoted form are the same symbol.
-/
inductive SyntaxToken where
  | parenOpen
  | parenClose
  | numeral (digits : Chars)
  | decimal (text : Chars)
  | hexadecimal (digits : Chars)
  | binary (digits : Chars)
  | string (content : Chars)
  /--
  A simple or a quoted symbol: `abc` and `|abc|` are the same symbol. Whether it was quoted
  is recorded for printing, not for identity.
  -/
  | symbol (symbol : Tree.Symbol)
  | keyword (name : Chars)
  | reserved (word : Chars)

/--
What a lexical token stands for, and for a symbol whether it was quoted.

Standard: 2.7 §3.1 Symbols, as `SyntaxToken`.
-/
def SyntaxToken.ofToken (version : Version) (token : Token) : SyntaxToken :=
  match token.category with
  | .parenOpen => .parenOpen
  | .parenClose => .parenClose
  | .numeral => .numeral token.text
  | .decimal => .decimal token.text
  | .hexadecimal => .hexadecimal (token.content version)
  | .binary => .binary (token.content version)
  | .string => .string (token.content version)
  | .simpleSymbol => .symbol ⟨token.content version, false⟩
  | .quotedSymbol => .symbol ⟨token.content version, true⟩
  | .keyword => .keyword (token.content version)
  | .reserved => .reserved token.text

/-- `(`, the tokens, `)`. -/
def paren (tokens : List SyntaxToken) : List SyntaxToken := .parenOpen :: tokens ++ [.parenClose]

/-- The reserved word `w`. -/
def word (w : String) : SyntaxToken := .reserved (chars w)

/-- `(`, the command name, the tokens, `)`. -/
def commandTokens (name : String) (tokens : List SyntaxToken) : List SyntaxToken :=
  paren (word name :: tokens)

end BSmtLibSpec.Grammar
