module

public import BSmtLib.Parser
public import BSmtLib.Token.Cursor
public import BSmtLib.Token.ConsumeFrom

public section

/-!
# The parse adapter

The token consumer that runs a parser over the tokens a producer hands over: at the start of
every input, before anything else, it tells the handler the producer's version; then it has the
parser parse the producer's tokens, with the handler and the resources the parsers share.
-/

open BSmtLib.Handler

namespace BSmtLib.Parser.Adapter

/- LEAN: Rust's `SmtParseAdapter`. It holds the handler, which is read back from the adapter
after a run, also after a failure. The adapter is never concrete: it does not take whitespace
and comments. The constructor and the fields are private, as Rust's are; the handler and the
parser are read-only fields, which stand as Rust's getters `handler` and `parser`, and the others
are read by the library through `ParseAdapter.Internal`. -/
/--
Token consumer that adapts a parser to parse the consumed tokens.

The adapter implements `Token.Consume` and hands over to a parser that implements `Parse`,
providing it the handler and the `ParseState`.
-/
structure ParseAdapter (H P : Type) where
  private mk ::
  /-- Returns the handler. -/
  handler : H
  /-- Returns the adapted parser. -/
  parser : P
  /-- Whether the handler was told the version of the input being read. -/
  private versionSet : Bool
  /-- The resources the parsers share. -/
  private parseState : ParseState H

namespace ParseAdapter

variable {H P : Type}

/-- Creates an adapter of `parser` over `handler`, with fresh resources. -/
def new (handler : H) (parser : P) : ParseAdapter H P :=
  { handler, parser, versionSet := false, parseState := .new }

/- LEAN: Rust's `parser_mut`. The adapter is taken apart so that the parser is held once and
changed in place, if the caller does not keep the old adapter. -/
/-- Returns the adapter with its parser changed by `f`. -/
def modifyParser (self : ParseAdapter H P) (f : P → P) : ParseAdapter H P :=
  let { handler, parser, versionSet, parseState } := self
  { handler, parser := f parser, versionSet, parseState }

/- LEAN: Rust's `handler_mut`, taken apart as `modifyParser`. -/
/-- Returns the adapter with its handler changed by `f`. -/
def modifyHandler (self : ParseAdapter H P) (f : H → H) : ParseAdapter H P :=
  let { handler, parser, versionSet, parseState } := self
  { handler := f handler, parser, versionSet, parseState }

/-- Destructures into the parser. -/
def intoParser (self : ParseAdapter H P) : P :=
  self.parser

namespace Internal

/-- The adapter with the given fields. -/
@[inline]
def mk (handler : H) (parser : P) (versionSet : Bool) (parseState : ParseState H) :
    ParseAdapter H P :=
  { handler, parser, versionSet, parseState }

/-- Whether the handler was told the version of the input being read. -/
@[inline]
def versionSet (self : ParseAdapter H P) : Bool :=
  self.versionSet

/-- The resources the parsers share. -/
@[inline]
def parseState (self : ParseAdapter H P) : ParseState H :=
  self.parseState

@[simp]
theorem handler_mk (handler : H) (parser : P) (versionSet : Bool) (parseState : ParseState H) :
    (mk handler parser versionSet parseState).handler = handler :=
  (rfl)

@[simp]
theorem parser_mk (handler : H) (parser : P) (versionSet : Bool) (parseState : ParseState H) :
    (mk handler parser versionSet parseState).parser = parser :=
  (rfl)

@[simp]
theorem versionSet_mk (handler : H) (parser : P) (versionSet : Bool)
    (parseState : ParseState H) :
    Internal.versionSet (mk handler parser versionSet parseState) = versionSet :=
  (rfl)

@[simp]
theorem parseState_mk (handler : H) (parser : P) (versionSet : Bool)
    (parseState : ParseState H) :
    Internal.parseState (mk handler parser versionSet parseState) = parseState :=
  (rfl)

/-- An adapter is the one built from its fields. -/
@[simp]
theorem mk_eta (self : ParseAdapter H P) :
    mk self.handler self.parser (Internal.versionSet self) (Internal.parseState self) = self :=
  (rfl)

/-- Two adapters built from the same fields are equal. -/
theorem mk_inj {handler handler' : H} {parser parser' : P} {versionSet versionSet' : Bool}
    {parseState parseState' : ParseState H} :
    mk handler parser versionSet parseState = mk handler' parser' versionSet' parseState' ↔
      handler = handler' ∧ parser = parser' ∧ versionSet = versionSet' ∧
        parseState = parseState' := by
  constructor
  · intro h
    exact ⟨congrArg ParseAdapter.handler h, congrArg ParseAdapter.parser h,
      congrArg Internal.versionSet h, congrArg Internal.parseState h⟩
  · rintro ⟨rfl, rfl, rfl, rfl⟩
    rfl

/-- The fresh adapter. -/
theorem new_eq (handler : H) (parser : P) :
    ParseAdapter.new handler parser = mk handler parser false .new :=
  (rfl)

/-- The adapter with its parser changed. -/
theorem modifyParser_eq (self : ParseAdapter H P) (f : P → P) :
    self.modifyParser f =
      mk self.handler (f self.parser) (Internal.versionSet self) (Internal.parseState self) :=
  (rfl)

/-- The adapter with its handler changed. -/
theorem modifyHandler_eq (self : ParseAdapter H P) (f : H → H) :
    self.modifyHandler f =
      mk (f self.handler) self.parser (Internal.versionSet self) (Internal.parseState self) :=
  (rfl)

end Internal

end ParseAdapter

variable {H P R E : Type}

instance {m : Type → Type} [Monad m] [Parse P H m E R] :
    Token.Consume (ParseAdapter H P) R (ParseError E) where
  isConcrete := false

/-- Whether the parser is to be told the version before the next hand-over: after its answer,
unless it broke, it is not, as the next hand-over continues the same input. -/
def ParseAdapter.Internal.versionSetAfter {R E : Type} : Except (ParseError E) (ControlFlow R) →
    Bool
  | .ok (.break _) => false
  | _ => true

/- LEAN: Rust's `impl SmtConsumeFrom<Z> for SmtParseAdapter`, for every producer. The parser
returns the cursor with the proof that it took a token of a cursor that has one, which is the
consumer's obligation. -/
instance {m : Type → Type} [Monad m] [Handler H m] [Parse P H m E R] {Z : Type} [Token.Cursor Z] :
    Token.ConsumeFrom (ParseAdapter H P) Z m where
  consume cursor h := do
    let adapter ← get
    -- the handler is told the version in force before the first token of every input
    let ((), handler) ← (show StateT H m Unit from
      if ParseAdapter.Internal.versionSet adapter then pure () else Handler.setVersion
          (Token.Cursor.version cursor)).run
        adapter.handler
    -- the parser parses the tokens, with the handler and the resources
    let ((answer, parser, parseState, ⟨next, consumed⟩), handler) ←
      (Parse.parse adapter.parser (ParseAdapter.Internal.parseState adapter) cursor).run handler
    set (ParseAdapter.Internal.mk handler parser (ParseAdapter.Internal.versionSetAfter answer)
      parseState)
    return (answer, ⟨next, consumed h⟩)

end BSmtLib.Parser.Adapter
