import BSmtLib.Parser.Handler

/-!
# The parser framework

The parsers step by single tokens: each parser is a state machine whose step takes the version,
its state and one token, makes the handler calls the token completes, and either goes on with a
new state or finishes with a result. A parser that finishes starts its next value from its
initial state.

The tokens come as `Input`, what they stand for in the version they were cut in, so that a step
needs neither the producer nor its token type: the driver (`Parser.Adapter`) is the only part
that reads tokens from a producer.
-/

namespace BSmtLib.Parser

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
  | reserved (word : Reserved)
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

section

variable {H : Type} {m : Type → Type} [Monad m] [Handler H m]

/-- Takes a `(`. -/
@[inline]
def expectOpen (token : Input) : PM H Unit :=
  match token with
  | .parenOpen => pure ()
  | _ => syntaxError (.expectedToken #[.parenOpen])

/-- Takes a `)`. -/
@[inline]
def expectClose (token : Input) : PM H Unit :=
  match token with
  | .parenClose => pure ()
  | _ => syntaxError (.expectedToken #[.parenClose])

/-- Takes a symbol. -/
@[inline]
def expectSymbol (token : Input) : PM H Symbol :=
  match token with
  | .symbol symbol => pure symbol
  | _ => syntaxError .expectedSymbol

/-- Takes a numeral. -/
@[inline]
def expectNumeral (token : Input) : PM H NumeralView :=
  match token with
  | .constant (.numeral digits) => pure digits
  | _ => syntaxError (.expectedToken #[.numeral])

/-- Takes a keyword. -/
@[inline]
def expectKeyword (token : Input) : PM H KeywordView :=
  match token with
  | .keyword name => pure name
  | _ => syntaxError (.expectedToken #[.keyword])

/-- Takes a string literal. -/
@[inline]
def expectString (token : Input) : PM H StringContentView :=
  match token with
  | .constant (.string content) => pure content
  | _ => syntaxError (.expectedToken #[.string])

end

/--
The state of a list of elements, each parsed by an inner parser, up to a `)`: whether the `(`
that opens the list is consumed (always, for a list whose `(` belongs to someone else), whether
the parser is between elements, the inner parser's state, and the elements so far.
-/
structure ListState (σ ρ : Type) where
  opened : Bool
  outside : Bool
  inner : σ
  items : Array ρ

namespace ListState

variable {σ ρ : Type}

/-- A list whose `(` is still to come, with the inner parser at its initial state. -/
def paren (init : σ) : ListState σ ρ :=
  { opened := false, outside := true, inner := init, items := #[] }

/-- A list whose `(` is already consumed. -/
def closed (init : σ) : ListState σ ρ :=
  { opened := true, outside := true, inner := init, items := #[] }

variable {H : Type} {m : Type → Type} [Monad m] [Handler H m]

/--
A step of the list: the `(` first, if the list opens with one; between elements, a `)` ends the
list, and with a maximum reached, nothing else may come; any other token goes to the inner
parser, which starts the next element.
-/
/- LEAN: Rust's `SmtParenMultipleParser`, `SmtClosedMultipleParser` and the maximum parsers,
in one. -/
@[specialize inner]
def step (init : σ) (inner : σ → Input → PM H (Step σ ρ)) (maximum : Option Nat)
    (self : ListState σ ρ) (token : Input) : PM H (Step (ListState σ ρ) (Array ρ)) := do
  if !self.opened then
    expectOpen token
    return .more { self with opened := true }
  if self.outside then
    if let .parenClose := token then
      return .done self.items
    if let some limit := maximum then
      if limit ≤ self.items.size then
        syntaxError (.expectedToken #[.parenClose])
  match ← inner self.inner token with
  | .more state => return .more { self with inner := state, outside := false }
  | .done item =>
    return .more { self with inner := init, outside := true, items := self.items.push item }

end ListState

end BSmtLib.Parser
