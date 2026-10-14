import BSmtLib.Traits
import BSmtLib.Token.SyntaxToken

/-!
# The parser

One parser for each syntactic category, for commands and for scripts, each a state machine that
takes the tokens one by one and calls a handler as the handler contract states; and the parse
adapter, which runs a parser over the tokens a lexer hands over.

This module holds what the parsers share: the errors of a parse, the tokens as the parsers take
them, the parsers' monad, the result of a step, and how a driver runs a parser (`Parse`).

The parsers step by single tokens: each parser is a state machine whose step takes the version,
its state and one token, makes the handler calls the token completes, and either goes on with a
new state or finishes with a result. A parser that finishes starts its next value from its
initial state.

The tokens come as `Input`, what they stand for in the version they were cut in, so that a step
needs neither the producer nor its token type: the driver (`Parser.Adapter`) is the only part
that reads tokens from a producer.

A parser that a driver runs (`Parse`) takes the tokens one by one. Before it takes a token it is
told that the token has arrived, so that it can make the calls due at a token's arrival; then
it takes the token. A step may finish with the parser's result, or ask its driver to act on the
producer of the tokens: to switch the version, or to discard the rest of the input; the parser
goes on once the producer has done so.
-/

namespace BSmtLib.Parser

open BSmtLib.Nodes BSmtLib.Traits
open BSmtLib.Plain (KeywordView)
open BSmtLib.Token (TokenCategory Version SyntaxToken)
open BSmtLib.Token.Reserved (GeneralReserved)

/-- What a syntax error expected or found wrong. -/
/- LEAN: Rust's `SmtSyntaxErrorKind`, with the same variants. -/
inductive SyntaxErrorKind where
  | expectedToken (categories : Array TokenCategory)
  | expectedSymbol
  | expectedUnderscore
  | expectedSymbolOrUnderscore
  | expectedSymbolOrParenOpen
  | expectedSymbolUnderscoreOrParenOpen
  | expectedUnderscoreOrAs
  | emptyIdentIndices
  | emptySortApplication
  | emptyTermApplication
  | emptyLetBindings
  | emptyAnnotation
  | emptyQuantifierBindings
  | emptyLambdaBindings
  | expectedIndexOrCloseParen
  | expectedOperator
  | expectedSExpr
  | expectedIdent
  | expectedSort
  | expectedSortInner
  | expectedTerm
  | expectedAttribute
  | expectedCommand
  | expectedCommandName
  | expectedDatatype
  | expectedDatatypeKind
  | expectedFunctionBody
  | expectedPropositionalLiteral
  | emptyFunctionSignatures
  | emptyDatatypeIntroductions
  | emptyDatatypeParameters
  | emptyDatatypeConstructors
  | emptyPatternArguments
  | emptyMatchCases
  | emptyGetValueTerms
  | unsupportedVersion
  | tooManyVersionDeclarations (limit : Nat)
  deriving BEq, Repr

/--
The party that failed when a parse failed: the input's syntax, or the handler. The error has no
location: it is at the last token the parser consumed, which its driver knows.
-/
inductive ParseErrorCause (ε : Type) where
  | syntax (kind : SyntaxErrorKind)
  | handler (error : ε)

/--
A token as the parsers take it: what it stands for in the version it was cut in, or the end of
the input. Words reserved in the version are reserved words; every other simple or quoted
symbol is a symbol.
-/
/- LEAN: Rust's parsers match on `SmtSyntaxToken`. The parser has a type of its own for it,
with the constants as one constructor and whitespace and comments as one, which the driver
makes from the syntax token (`Input.ofSyntax`). -/
inductive Input where
  | parenOpen
  | parenClose
  | constant (constant : SpecConstant)
  | symbol (symbol : Symbol)
  | keyword (name : KeywordView)
  | reserved (word : Token.Reserved)
  /-- The end of the input. -/
  | endOfInput
  /-- Whitespace or a comment, which no parser takes. -/
  | layout

namespace Input

/-- Whether the token is the general reserved word. -/
@[inline]
def isWord (token : Input) (word : GeneralReserved) : Bool :=
  match token with
  | .reserved (.general w) => w == word
  | _ => false

end Input

/-- What the token, viewed under its producer's version, stands for. -/
@[inline]
def Input.ofSyntax : SyntaxToken → Input
  | .parenOpen => .parenOpen
  | .parenClose => .parenClose
  | .numeral value => .constant (.numeral value)
  | .decimal value => .constant (.decimal value)
  | .hexadecimal value => .constant (.hexadecimal value)
  | .binary value => .constant (.binary value)
  | .string value => .constant (.string value)
  | .keyword value => .keyword value
  | .symbol value quoted => .symbol ⟨value, quoted⟩
  | .reserved word => .reserved word
  | .whitespace _ | .comment _ => .layout
  | .endOfFile => .endOfInput

/-- The monad of the parsers: the handler's, failing with a parse error. -/
abbrev PM (H : Type) {m : Type → Type} [Handler H m] :=
  ExceptT (ParseErrorCause (Handler.Error H)) (StateT H m)

section

variable {H : Type} {m : Type → Type} [Monad m] [Handler H m]

/-- A handler call in a parse: its failure is the handler's. -/
@[inline]
def call {α : Type} (action : ExceptT (Handler.Error H) (StateT H m) α) : PM H α :=
  ExceptT.adapt ParseErrorCause.handler action

/-- A syntax error. -/
@[inline]
def syntaxError {α : Type} (kind : SyntaxErrorKind) : PM H α :=
  throw (.syntax kind)

end

/-- What a step of a parser gives: a new state to go on from, or its result. -/
inductive Step (σ ρ : Type) where
  | more (state : σ)
  | done (result : ρ)

/-- What a step of a parser asks of its driver, with `μ` the parser's monad. -/
inductive Flow (μ : Type → Type) (σ ρ : Type) where
  /-- Go on with the next token. -/
  | more (state : σ)
  /-- The parser finished, with its result. -/
  | done (result : ρ)
  /-- Switch the producer to the version, then go on as `resume` says. The producer may
  refuse, which fails the parse with `unsupportedVersion`. -/
  | switchVersion (version : Version) (resume : μ (Step σ ρ))
  /-- Make the producer discard the rest of its input, up to the end of the input, then go on
  as `resume` says. -/
  | discardRest (resume : μ (Step σ ρ))

/--
A parser that a driver runs (`SmtParse`): the parser of the type `P`, with the handler of the
type `H` in the monad `m`, whose errors are of the type `E`, finishing with results of the type
`R`.
-/
/- LEAN: Rust's trait `SmtParse`, whose `parse` takes the tokens of a cursor itself. The Lean
parsers step by single tokens, so the loop over the producer's tokens is the driver's
(`Parser.Adapter`), and a parser asks the driver to act on the producer instead of acting on it
itself. Rust has no arrival of its own: its parser makes the calls due at a token's arrival
when `next()` returns it, before it looks at it. -/
class Parse (P : Type) (H : outParam Type) (m : outParam (Type → Type)) (E R : outParam Type)
    where
  /-- The calls due when the token arrives, before the parser takes it. -/
  arrive : P → Input → ExceptT (ParseErrorCause E) (StateT H m) Unit
  /-- The parser takes the token, cut in the version. -/
  step : Version → P → Input →
    ExceptT (ParseErrorCause E) (StateT H m) (Flow (ExceptT (ParseErrorCause E) (StateT H m)) P R)
  /-- The parser from which the next value starts, after it finished. -/
  reset : P → P

end BSmtLib.Parser
