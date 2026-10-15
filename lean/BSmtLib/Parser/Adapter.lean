module

public import BSmtLib.Parser
public import BSmtLib.Token.Produce
public import BSmtLib.Token.ConsumeFrom

public section

/-!
# The parse adapter

The token consumer that runs a parser over the tokens a producer hands over: at the start of
every input, before anything else, it tells the handler the producer's version; then it has the
parser parse the producer's tokens, with the handler and the resources the parsers share.
-/

open BSmtLib.Traits

namespace BSmtLib.Parser.Adapter

/- LEAN: Rust's `SmtParseAdapter`. It holds the handler, which is read back from the adapter
after a run, also after a failure. The adapter is never concrete: it does not take whitespace
and comments. The parse state is the last field, with its fresh value as the default. -/
/-- A parser with its handler, as the token consumer of a lexer (`SmtParseAdapter`). -/
structure ParseAdapter (H P : Type) where
  handler : H
  parser : P
  /-- Whether the handler was told the version of the input being read. -/
  versionSet : Bool
  /-- The resources the parsers share. -/
  parseState : ParseState H := .new

namespace ParseAdapter

variable {H P : Type}

/-- The adapter of the parser over the handler, with fresh resources. -/
def new (handler : H) (parser : P) : ParseAdapter H P :=
  { handler, parser, versionSet := false, parseState := .new }

end ParseAdapter

variable {H P R E : Type}

instance {m : Type → Type} [Monad m] [Parse P H m E R] :
    Token.Consume (ParseAdapter H P) R (ParseErrorCause E) where
  isConcrete := false

/-- Whether the parser is to be told the version before the next hand-over: after its answer,
unless it broke, it is not, as the next hand-over continues the same input. -/
def ParseAdapter.versionSetAfter {R E : Type} : Except (ParseErrorCause E) (ControlFlow R) → Bool
  | .ok (.break _) => false
  | _ => true

/- LEAN: Rust's `impl SmtConsumeFrom<Z> for SmtParseAdapter`, for every producer. The parser
returns the cursor with the proof that it took a token of a cursor that has one, which is the
consumer's obligation. -/
instance {m : Type → Type} [Monad m] [Handler H m] [Parse P H m E R] {Z : Type} [Token.Produce Z] :
    Token.ConsumeFrom (ParseAdapter H P) Z m where
  consume producer h := do
    let adapter ← get
    -- the handler is told the version in force before the first token of every input
    let ((), handler) ← (show StateT H m Unit from
      if adapter.versionSet then pure () else Handler.setVersion
          (Token.Produce.version producer)).run
        adapter.handler
    -- the parser parses the tokens, with the handler and the resources
    let ((answer, parser, parseState, ⟨next, consumed⟩), handler) ←
      (Parse.parse adapter.parser adapter.parseState producer).run handler
    set ({ handler, parser, versionSet := ParseAdapter.versionSetAfter answer, parseState } :
      ParseAdapter H P)
    return (answer, ⟨next, consumed h⟩)

end BSmtLib.Parser.Adapter
