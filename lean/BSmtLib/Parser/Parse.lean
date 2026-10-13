import BSmtLib.Parser.Command

/-!
# Parsers as their driver runs them

A parser that a driver runs (`Parse`) takes the tokens one by one. Before it takes a token it is
told that the token has arrived, so that it can make the calls due at a token's arrival; then
it takes the token. A step may finish with the parser's result, or ask its driver to act on the
producer of the tokens: to switch the version, or to discard the rest of the input; the parser
goes on once the producer has done so.

This module has the parsers of the categories that a reader may parse on their own: sorts,
s-expressions, terms and commands. The script parser is in `Parser.Script`.
-/

namespace BSmtLib.Parser

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

/-- The parser of one sort (`SmtSortParser`). -/
structure SortParser (H : Type) {m : Type → Type} [Handler H m] where
  state : SortState (Handler.«Sort» H)

/-- The parser of one s-expression (`SmtSExprParser`). -/
structure SExprParser (H : Type) {m : Type → Type} [Handler H m] where
  state : SExprState (Handler.SExpr H)

/-- The parser of one term (`SmtTermParser`). -/
structure TermParser (H : Type) {m : Type → Type} [Handler H m] where
  state : TermStateOf H

/--
The parser of one command (`SmtCommandParser`). It finishes after every command, and after the
end of the input while it awaits a command.

A version declaration switches nothing: the version is a mode of a script. The parser reports
the declaration in its outcome, and its caller decides; `exit` likewise.
-/
structure CommandParser (H : Type) {m : Type → Type} [Handler H m] where
  state : CommandStateOf H

section

variable {H : Type} {m : Type → Type} [Monad m] [Handler H m]

/-- The sort parser before a sort. -/
def SortParser.new : SortParser H := ⟨.init⟩

/-- The s-expression parser before an s-expression. -/
def SExprParser.new : SExprParser H := ⟨[]⟩

/-- The term parser before a term. -/
def TermParser.new : TermParser H := ⟨.init⟩

/-- The command parser before a command. -/
def CommandParser.new : CommandParser H := ⟨.awaiting⟩

instance : Parse (SortParser H) H m (Handler.Error H) (Handler.«Sort» H) where
  arrive _ _ := pure ()
  step version parser token := do
    match ← sortStep version parser.state token with
    | .more state => return .more ⟨state⟩
    | .done result => return .done result
  reset _ := .new

instance : Parse (SExprParser H) H m (Handler.Error H) (Handler.SExpr H) where
  arrive _ _ := pure ()
  step version parser token := do
    match ← sExprStep version parser.state token with
    | .more state => return .more ⟨state⟩
    | .done result => return .done result
  reset _ := .new

instance : Parse (TermParser H) H m (Handler.Error H) (Handler.Term H) where
  arrive _ _ := pure ()
  step version parser token := do
    match ← termStep version parser.state token with
    | .more state => return .more ⟨state⟩
    | .done result => return .done result
  reset _ := .new

end

section

variable {H : Type} {m : Type → Type} [Monad m] [CommandHandler H m]

instance : Parse (CommandParser H) H m (Handler.Error H) CommandOutcome where
  arrive parser token := commandArrive parser.state token
  step version parser token := do
    match ← commandStep version parser.state token with
    | .more state => return .more ⟨state⟩
    | .done result => return .done result
  reset _ := .new

end

end BSmtLib.Parser
