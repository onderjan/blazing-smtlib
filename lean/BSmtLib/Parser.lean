module

public import BSmtLib.Traits
public import BSmtLib.Token.SyntaxToken
public import BSmtLib.Token.Produce

public section

/-!
# The parser

One parser for each syntactic category, for commands and for scripts, each of which takes the
tokens of a cursor and calls a handler as the handler contract states; and the parse adapter,
which runs a parser over the tokens a lexer hands over.

This module holds what the parsers share: the errors of a parse, the resources shared by the
parsers of one input (`ParseState`), the parsers' monad, and how a parser is called (`Parse`).

A parser takes the tokens of a cursor (`Parse.parse`). Given a cursor with a token, it takes at
least one, and returns whether it goes on, its result if it finished, or its error. A parser
that finishes starts its next value from its initial state.
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

/- LEAN: Rust's `SmtParseState` holds the arena and the slots that the standard parsers share,
all crate-private. The parsers of the port keep their state in themselves, so this one holds
nothing; it is handed to every parser and given back unchanged. -/
/--
The resources shared by the parsers of one input (`SmtParseState`).

It is made once for the root parser and handed on to the parsers it calls.
-/
structure ParseState (H : Type) where
  private mk ::

/-- Fresh resources. -/
/- LEAN: Rust's `SmtParseState::new`. -/
def ParseState.new {H : Type} : ParseState H := ⟨⟩

instance {H : Type} : Inhabited (ParseState H) := ⟨.new⟩

/- LEAN: Rust's trait `SmtParse<H>`, with the handler as a parameter of the class, so that a
parser type serves every handler. Rust's `parse` takes `&mut self`, the handler, the parse state
and the cursor; here the handler is the state of the monad, and the parser, the parse state and
the cursor are given back. The cursor is given back with the proof that the parser took a
token of it if it had one: the rule that Rust states in words for `SmtConsumeFrom::consume`. -/
/--
A parser of SMT-LIB input with a handler (`SmtParse`): the parser of the type `P`, with the
handler of the type `H` in the monad `m`, whose errors are of the type `E`, finishing with results
of the type `R`.
-/
class Parse (P : Type) (H : Type) (m : outParam (Type → Type)) (E R : outParam Type) where
  /--
  Parses tokens from the cursor, progressing the parser.

  If the cursor has a token, the parser takes at least one, whatever it returns, an error
  included.

  If the parser returns `ControlFlow.continue`, it has taken all tokens it was handed and wants
  more.

  If the parser returns `ControlFlow.break`, it has finished the input it accepts, taking exactly
  its tokens, and returns its result. It is then back in its initial state, ready for the next
  value.

  If the parser returns an error, it has failed at the last token it took. The state of the
  parser it gives back is unspecified.

  The parse state holds the resources shared by the parsers of one input; it is given back with
  the parser.
  -/
  parse {Z : Type} [Token.Produce Z] : P → ParseState H → (cursor : Z) →
    StateT H m (Except (ParseErrorCause E) (ControlFlow R) × P × ParseState H ×
      { next : Z // Token.Produce.HasNext cursor → Token.Produce.Consumed next cursor })

namespace Internal

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

/-! ## The parsers that step by single tokens

The parsers of the port step by single tokens: each is a state machine whose step takes the
version, its state and one token, makes the handler calls the token completes, and either goes
on with a new state or finishes with a result. Before it takes a token it is told that the token
has arrived, so that it can make the calls due at a token's arrival. A step may ask to act on the
cursor: to switch the version, or to discard the rest of the input; the parser goes on once the
cursor has done so. `Internal.parseByToken` takes the tokens of a cursor one by one with such a
parser: it is the `parse` of each of them.
-/


/--
A token as the parsers take it: what it stands for in the version it was cut in, or the end of
the input. Words reserved in the version are reserved words; every other simple or quoted
symbol is a symbol.
-/
/- LEAN: Rust's parsers match on `SmtSyntaxToken`. The parser has a type of its own for it,
with the constants as one constructor and whitespace and comments as one, which the loop makes
from the syntax token (`Input.ofSyntax`). -/
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

/-- What a step of a parser gives: a new state to go on from, or its result. -/
inductive Step (σ ρ : Type) where
  | more (state : σ)
  | done (result : ρ)

/-- What a step of a parser asks of its loop, with `μ` the parser's monad. -/
inductive Flow (μ : Type → Type) (σ ρ : Type) where
  /-- Go on with the next token. -/
  | more (state : σ)
  /-- The parser finished, with its result. -/
  | done (result : ρ)
  /-- Switch the cursor to the version, then go on as `resume` says. The cursor may refuse,
  which fails the parse with `unsupportedVersion`. -/
  | switchVersion (version : Version) (resume : μ (Step σ ρ))
  /-- Make the cursor discard the rest of its input, up to the end of the input, then go on as
  `resume` says. -/
  | discardRest (resume : μ (Step σ ρ))

/- LEAN: Rust's parsers that step by single tokens call `parse_by_token` with their step; here
the step is a class, so that the proofs about the parsers can speak of the step of every one. -/
/--
A parser that steps by single tokens: the parser of the type `P`, with the handler of the type
`H` in the monad `m`, whose errors are of the type `E`, finishing with results of the type `R`.
-/
class ParseByToken (P : Type) (H : outParam Type) (m : outParam (Type → Type))
    (E R : outParam Type) where
  /-- The calls due when the token arrives, before the parser takes it. -/
  arrive : P → Input → ExceptT (ParseErrorCause E) (StateT H m) Unit
  /-- The parser takes the token, cut in the version. -/
  step : Version → P → Input →
    ExceptT (ParseErrorCause E) (StateT H m) (Flow (ExceptT (ParseErrorCause E) (StateT H m)) P R)
  /-- The parser from which the next value starts, after it finished. -/
  reset : P → P

/-- What the parser did with a token. -/
inductive After (P R E : Type) where
  /-- It goes on: take the next token. -/
  | goOn (parser : P)
  /-- It stops with the answer, and the parser to go on from after. -/
  | stop (answer : Except (ParseErrorCause E) (ControlFlow R)) (parser : P)

/-- What the parser's step asks after the cursor did what the step asked. A parser that
finished goes on from `fresh`, its reset. -/
def resumed {P R E : Type} (fresh : P) : Step P R → After P R E
  | .more parser => .goOn parser
  | .done result => .stop (.ok (.break result)) fresh

section

variable {H P R E : Type} {m : Type → Type} [Monad m] [ParseByToken P H m E R]
variable {Z : Type} [Token.Produce Z]

/- LEAN: as Rust's script parser, the step acts on the cursor and the parser goes on with it. An
action stands when the step fails after it, as in Rust, where the cursor is changed in place.

The reset parser is made before the step, and the parser is not used after it: the step then
holds the only reference to the parser's state, so that the state is updated in place and not
copied at every token. A failed parser goes on from its reset too, as a parser that failed is
in no state it promises. -/
/--
Has the parser take the token, taken from `cursor` and leaving `next`: its arrival, its step, and
what the step asks of the cursor. A refused switch of the version fails with
`unsupportedVersion`.
-/
@[inline]
def takeOne (parser : P) (cursor : Z) (token : Token.Produce.Token Z) (next : Z)
    (consumed : Token.Produce.Consumed next cursor) :
    StateT H m (After P R E × { z : Z // Token.Produce.Consumed z cursor }) := do
  let fresh := ParseByToken.reset parser
  let input := Input.ofSyntax (Token.Produce.«syntax» next token)
  match ← (do
      ParseByToken.arrive parser input
      ParseByToken.step (Token.Produce.version next) parser input).run with
  | .error error => return (.stop (.error error) fresh, ⟨next, consumed⟩)
  | .ok (.more parser) => return (.goOn parser, ⟨next, consumed⟩)
  | .ok (.done result) =>
    return (.stop (.ok (.break result)) fresh, ⟨next, consumed⟩)
  | .ok (.switchVersion declared resume) =>
    match switch : Token.Produce.setVersion next declared with
    | .error _ => return (.stop (.error (.syntax .unsupportedVersion)) fresh, ⟨next, consumed⟩)
    | .ok switched =>
      let after := Token.Produce.setVersion_consumed consumed switch
      match ← resume.run with
      | .error error => return (.stop (.error error) fresh, ⟨switched, after⟩)
      | .ok step => return (resumed fresh step, ⟨switched, after⟩)
  | .ok (.discardRest resume) =>
    let after := Token.Produce.discardRest_consumed consumed
    match ← resume.run with
    | .error error => return (.stop (.error error) fresh, ⟨Token.Produce.discardRest next, after⟩)
    | .ok step => return (resumed fresh step, ⟨Token.Produce.discardRest next, after⟩)

/- LEAN: the loop is the recursion, which ends as every token taken is consumed, by the
producer's well-founded consumption. -/
/-- A producer, ordered by its consumption: the loop over its tokens descends by it. -/
structure Consuming (Z : Type) where
  producer : Z

instance : WellFoundedRelation (Consuming Z) :=
  invImage Consuming.producer ⟨Token.Produce.Consumed, Token.Produce.consumed_wf⟩

/--
Has the parser take the tokens of `cursor`, which comes from `origin` with tokens consumed, one
by one, until there are none or the parser stops.
-/
def rest (origin : Z) (parser : P) (cursor : Z) (consumed : Token.Produce.Consumed cursor origin) :
    StateT H m (Except (ParseErrorCause E) (ControlFlow R) × P ×
      { z : Z // Token.Produce.Consumed z origin }) :=
  match Token.Produce.next? cursor with
  | none => return (.ok .continue, parser, ⟨cursor, consumed⟩)
  | some (token, ⟨next, step⟩) => do
    match ← takeOne parser cursor token next step with
    | (.goOn parser, ⟨later, taken⟩) =>
      rest origin parser later (Token.Produce.consumed_trans taken consumed)
    | (.stop answer parser, ⟨later, taken⟩) =>
      return (answer, parser, ⟨later, Token.Produce.consumed_trans taken consumed⟩)
termination_by (⟨cursor⟩ : Consuming Z)
decreasing_by exact taken

/-- A producer that gives no token has none. -/
theorem not_hasNext {producer : Z} (h : Token.Produce.next? producer = none) :
    ¬ Token.Produce.HasNext producer := fun hn =>
  absurd (Token.Produce.next?_isSome hn) (by rw [h]; exact Bool.false_ne_true)

/- LEAN: Rust's `parse_by_token`, which takes the step as a closure. -/
/--
Parses the cursor one token at a time with the parser's steps, until the cursor is empty or the
parser stops: the `parse` of a parser that steps by single tokens.
-/
def parseByToken (parser : P) (state : ParseState H) (cursor : Z) :
    StateT H m (Except (ParseErrorCause E) (ControlFlow R) × P × ParseState H ×
      { next : Z // Token.Produce.HasNext cursor → Token.Produce.Consumed next cursor }) :=
  match h : Token.Produce.next? cursor with
  | none => return (.ok .continue, parser, state, ⟨cursor, fun hn => absurd hn (not_hasNext h)⟩)
  | some (token, ⟨next, consumed⟩) => do
    match ← takeOne parser cursor token next consumed with
    | (.goOn parser, ⟨later, taken⟩) =>
      let (answer, parser, ⟨done, hd⟩) ← rest cursor parser later taken
      return (answer, parser, state, ⟨done, fun _ => hd⟩)
    | (.stop answer parser, ⟨later, taken⟩) => return (answer, parser, state, ⟨later,
        fun _ => taken⟩)

end

end Internal

end BSmtLib.Parser
