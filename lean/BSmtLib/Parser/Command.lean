module

public import BSmtLib.Parser.Command.Internal.Standard

public section

/-!
# The command parser

A state machine stepped by single tokens over one command: its `(`, its name, then the payload
parser of the command, which finishes at the command's `)`. A command's parts are parsed into
values the parser holds, and handed over at the handler call; every command's last call comes
at its `)`.
-/

namespace BSmtLib.Parser.Command

open BSmtLib.Handler BSmtLib.Parser.Command.Internal.Standard
open BSmtLib (Version)
open BSmtLib.Parser.Internal (PM call syntaxError)

namespace Internal

/-- The state of the command parser. -/
inductive CommandState
    (HandledSExpr HandledAttribute HandledSort HandledTerm Scope Nonstandard : Type) where
  /-- Before a command, or the end of the input. -/
  | awaiting
  /-- After the `(` of a command, before its name. -/
  | opened
  | payload (state : Payload HandledSExpr HandledAttribute HandledSort HandledTerm Scope)
  /-- In the payload of a nonstandard command, with the parser the handler gave for it. -/
  | nonstandard (parser : Nonstandard)

/-- The command parser state of the handler. -/
abbrev CommandStateOf (H : Type) {m : Type → Type} [CommandHandler H m] :=
  CommandState (Handler.SExpr H) (Handler.Attribute H) (Handler.«Sort» H) (Handler.Term H)
    (Handler.Scope H) (CommandHandler.NonstandardParser H)

end Internal

/--
Parses an SMT-LIB command.

The parser finishes after every command, returning `ControlFlow.break` with a `CommandOutcome`
that distinguishes the command `(exit)` and the version-switch command
`(set-info :smt-lib-version <version>)` from the others. It also finishes after an EOF while
awaiting a command. An EOF inside a command is a syntax error.

To read a whole script, use `Parser.Script.ScriptParser`, which also switches versions on
version declarations and discards the input after `(exit)`.
-/
structure CommandParser (H : Type) {m : Type → Type} [CommandHandler H m] where
  private mk ::
  private state : Internal.CommandStateOf H

section

variable {H : Type} {m : Type → Type} [Monad m] [CommandHandler H m]

/-- Creates the parser. -/
def CommandParser.new : CommandParser H := ⟨.awaiting⟩

instance : Inhabited (CommandParser H) := ⟨.new⟩

end

section

variable {H : Type} {m : Type → Type} [Monad m] [CommandHandler H m]

/- LEAN: Rust's command parser hands its cursor and the shared parse state to the non-standard
parser, and clears the state after the command. The parse state holds nothing here, so a fresh
one is handed each time. -/
/--
Hands the cursor to the handler's parser of a nonstandard command's payload: its error, or
whether the command goes on in the parser given back (`some`) or ended at its `)` (`none`); and
the cursor the parser gave back.
-/
@[inline]
def Internal.nonstandardParse {Z : Type} [Token.Cursor Z]
    (parser : CommandHandler.NonstandardParser H) (cursor : Z) :
    StateT H m
      (Except (ParseError (Handler.Error H)) (Option (CommandHandler.NonstandardParser H)) ×
      { next : Z // Token.Cursor.HasNext cursor → Token.Cursor.Consumed next cursor }) := do
  let (answer, parser, _, next) ← Parse.parse parser ParseState.new cursor
  match answer with
  | .error error => return (.error error, next)
  | .ok .continue => return (.ok (some parser), next)
  | .ok (.break ()) => return (.ok none, next)

/- LEAN: the loops over single tokens hand the cursor to the non-standard parser, as Rust's
command parser does (`Parser.Internal.ParseByToken.handOver?`). This step serves a driver that
steps the parser by single tokens: it hands each token on in a producer of that one token
(`Parser.Internal.InputCursor`), as Rust's standard command parsers hand a token they took to
a parser they hold, so that the non-standard parser cannot switch the version and is called once
per token. -/
/--
A step of a nonstandard command's payload: the token goes to the handler's parser, and the
command ends when that parser finishes, at the command's `)`.
-/
def Internal.nonstandardStep (version : Version) (parser : CommandHandler.NonstandardParser H)
    (token : Internal.Input) :
    PM H (Internal.Step (Internal.CommandStateOf H) CommandOutcome) := do
  let (answer, parser, _) ← ExceptT.lift
    (Parse.parse parser ParseState.new (Internal.InputCursor.mk version (some token)))
  match answer with
  | .error error => throw error.kind
  | .ok .continue => return .more (.nonstandard parser)
  -- a nonstandard command cannot be the exit command
  | .ok (.break ()) => return .done .command

/--
A step of the command parser: `(`, the command's name, its payload up to its `)`; or the end of
the input between commands. A symbol as the name, even one spelled as a standard command's
name, names a nonstandard command.
-/
def Internal.commandStep (version : Version) (self : Internal.CommandStateOf H)
    (token : Internal.Input) :
    PM H (Internal.Step (Internal.CommandStateOf H) CommandOutcome) := do
  match self with
  | .awaiting =>
    match token with
    | .parenOpen => return .more .opened
    | .endOfInput => return .done .endOfFile
    | _ => syntaxError (.expected #[.token .parenOpen, .token .endOfFile])
  | .opened =>
    match token with
    | .reserved (.commandName name) => return .more (.payload (Payload.init name version))
    | .symbol name =>
      return .more (.nonstandard (← call (CommandHandler.nonstandardCommand (H := H) name)))
    | _ => syntaxError (.expected #[.commandName])
  | .payload payload =>
    match ← payloadStep version payload token with
    | .more payload => return .more (.payload payload)
    | .done outcome => return .done outcome
  | .nonstandard parser => Internal.nonstandardStep version parser token

/-- The calls due when a token arrives at the command parser: those of its payload parser. -/
def Internal.commandArrive (self : Internal.CommandStateOf H) (token : Internal.Input) :
    PM H Unit :=
  match self with
  | .payload payload => payloadArrive payload token
  | _ => pure ()

@[no_expose]
instance Internal.instParseByTokenCommandParser :
    Internal.ParseByToken (CommandParser H) H m (Handler.Error H) CommandOutcome where
  arrive parser token := Internal.commandArrive parser.state token
  step version parser token := do
    match ← Internal.commandStep version parser.state token with
    | .more state => return .more ⟨state⟩
    | .done result => return .done result
  reset _ := .new
  handOver? parser cursor :=
    match parser.state with
    | .nonstandard nonstandard => some do
      let (answer, next) ← Internal.nonstandardParse nonstandard cursor
      match answer with
      | .error error => return (.stop (.error error) .new, next)
      | .ok (some nonstandard) => return (.goOn ⟨.nonstandard nonstandard⟩, next)
      -- a nonstandard command cannot be the exit command
      | .ok none => return (.stop (.ok (.break .command)) .new, next)
    | _ => none

instance : Parse (CommandParser H) H m (Handler.Error H) CommandOutcome where
  parse := Internal.parseByToken

end

/- LEAN: Rust's trait `SmtCommandRule<H>`, implemented by a type `R` that names the rule. The
parser's result type, which Rust reads from the parser's `SmtParse` impl, is a field here, so that
`handle` can name it. Rust bounds `H` by `SmtCommandHandler`; here a `Handler` is enough, so
that a handler's `CommandHandler` instance can name a payload parser of a rule for that same
handler as its non-standard parser: Lean has no cycles between instances. -/
/--
Handles the result of a command parsed by `CommandPayloadParser`.

A rule separates parsing a command from handling it: `Parser` parses the rest of the command up
to and including its closing parenthesis, and only then is `handle` called with the result. A
command is thus handled once it has been read completely, like a standard command, and a command
that fails to be read, e.g. `(minimize c` at the end of the input, is not handled at all.
-/
class CommandRule (R : Type) (H : Type) {m : outParam (Type → Type)} [Handler H m] where
  /--
  Parses the tokens after the name of the command, up to and including its closing parenthesis.

  For example, the payload of `(minimize c)` is a term followed by the closing parenthesis, which
  `Category.Combinator.ClosedParser H (Category.Term.TermParser H)` parses.

  The closing parenthesis is a part of the payload because a payload that ends with an attribute
  can only end with it: whether an attribute has a value is known only from the token after its
  keyword, e.g. the `)` in `(set-option :print-success)`. Attributes are thus parsed together
  with the closing parenthesis, by `Category.Attribute.ClosedAttributeParser` and
  `Category.Attribute.ClosedMultipleAttributeParser`.
  -/
  Parser : Type
  /-- Result of `Parser`. -/
  Result : Type
  /-- Instance of `Parse` of `Parser`, filled in by instance search. -/
  [parse : Parse Parser H m (Handler.Error H) Result]
  /- LEAN: Rust's `handle(&mut self, handler, result)`: the rule is given and given back, as
  the handler is the state of the monad. -/
  /--
  Handles the result of the parser once the command has been read to its closing parenthesis.
  -/
  handle : R → Result → ExceptT (Handler.Error H) (StateT H m) R

/- The rule's parser's `Parse` instance, found from the rule's. -/
attribute [instance_reducible, instance] CommandRule.parse

/--
Parses the payload of a single command, starting after its name.

The payload is parsed by the parser of the rule, and its result is handed to
`CommandRule.handle` of the rule once the closing parenthesis of the command has been parsed.
The parser can serve as the `Handler.CommandHandler.NonstandardParser` of a command handler.
-/
structure CommandPayloadParser (H R : Type) {m : Type → Type} [Handler H m]
    [CommandRule R H] where
  private mk ::
  private rule : R
  private parser : CommandRule.Parser R H

section

variable {H R : Type} {m : Type → Type} [Handler H m] [CommandRule R H]

/-- Creates the parser with the rule and the payload parser. -/
def CommandPayloadParser.new (rule : R) (parser : CommandRule.Parser R H) :
    CommandPayloadParser H R :=
  ⟨rule, parser⟩

/-- Creates the parser with the rule and its default payload parser. -/
def CommandPayloadParser.withRule [Inhabited (CommandRule.Parser R H)] (rule : R) :
    CommandPayloadParser H R :=
  .new rule default

/- LEAN: Rust's `Default`, where the rule and its parser have one. -/
@[no_expose]
instance [Inhabited R] [Inhabited (CommandRule.Parser R H)] :
    Inhabited (CommandPayloadParser H R) :=
  ⟨.new default default⟩

@[no_expose]
instance [Monad m] : Parse (CommandPayloadParser H R) H m (Handler.Error H) Unit where
  parse self state cursor := do
    let (answer, parser, state, next) ← Parse.parse self.parser state cursor
    match answer with
    | .error cause => return (.error cause, ⟨self.rule, parser⟩, state, next)
    | .ok .continue => return (.ok .continue, ⟨self.rule, parser⟩, state, next)
    | .ok (.break result) =>
      -- the command ends at the last consumed token
      match ← (CommandRule.handle self.rule result).run with
      | .error error =>
        return (.error (ParseError.Internal.new (.handler error)), ⟨self.rule, parser⟩, state,
          next)
      | .ok rule => return (.ok (.break ()), ⟨rule, parser⟩, state, next)

end

end BSmtLib.Parser.Command
