module

public import BSmtLib.Parser.Adapter

@[expose] public section

/-!
# The parse adapter that stops after an action on its producer

The parse adapter runs its parser over every token of a cursor: after the parser has had the
cursor switch the version or discard the rest of the input, it goes on with the cursor
(`Parser.Internal.takeOne`). The consumer here is the parse adapter as it would be if its loop
stopped there instead, with the parser going on: the lexer then hands the tokens left in the
cursor over anew, in a new call, or relexes them, or discards them. The proofs about the reader
are made with this consumer, whose calls each end at an action as those of the stand-in consumer
of the lexer proofs do, and carried over to the parse adapter by `Param.Split`, which shows that
the lexer's handovers to the two are the same.
-/

open BSmtLib.Lexer.Cursor (LexerCursor)

namespace BSmtLib.Facts.Proofs.Reader.Param.Stop

open BSmtLib.Handler
open BSmtLib.Parser (Parse ParseError ParseErrorCause ParseState)
open BSmtLib.Parser.Adapter (ParseAdapter)
open BSmtLib.Parser.Internal (After Consuming ParseByToken)

section

variable {H P R E : Type} {m : Type → Type} [Monad m] [ParseByToken P H m E R]

/-- What the parser's step asks after the producer did what the step asked: a parser that goes
on stops the handover; one that finished goes on from `fresh`, its reset. -/
def resumed (fresh : P) : Parser.Internal.Step P R → After P R E
  | .more parser => .stop (.ok .continue) parser
  | .done result => .stop (.ok (.break result)) fresh

variable {Z : Type} [Token.Cursor Z]

/--
Has the parser take the token, taken from `cursor` and leaving `next`: its arrival, its step, and
what the step asks of the producer, after which the handover stops. A refused version switch fails
with `VersionErrorKind.unsupported`.
-/
def takeOne (parser : P) (cursor : Z) (token : Token.Cursor.Token Z) (next : Z)
    (consumed : Token.Cursor.Consumed next cursor) :
    StateT H m (After P R E × { z : Z // Token.Cursor.Consumed z cursor }) := do
  let fresh := ParseByToken.reset parser
  let input := Parser.Internal.Input.ofSyntax (Token.Cursor.«syntax» next token)
  match ← (do
      ParseByToken.arrive parser input
      ParseByToken.step (Token.Cursor.version next) parser input).run with
  | .error error =>
    return (.stop (.error (ParseError.Internal.new error)) fresh, ⟨next, consumed⟩)
  | .ok (.more parser) => return (.goOn parser, ⟨next, consumed⟩)
  | .ok (.done result) =>
    return (.stop (.ok (.break result)) fresh, ⟨next, consumed⟩)
  | .ok (.switchVersion declared resume) =>
    match switch : Token.Cursor.setVersion next declared with
    | .error _ =>
      return (.stop (.error (ParseError.Internal.new (.version .unsupported))) fresh,
        ⟨next, consumed⟩)
    | .ok switched =>
      let after := Token.Cursor.setVersion_consumed consumed switch
      match ← resume.run with
      | .error error =>
        return (.stop (.error (ParseError.Internal.new error)) fresh, ⟨switched, after⟩)
      | .ok step => return (resumed fresh step, ⟨switched, after⟩)
  | .ok (.discardRest resume) =>
    let after := Token.Cursor.discardRest_consumed consumed
    match ← resume.run with
    | .error error =>
      return (.stop (.error (ParseError.Internal.new error)) fresh,
        ⟨Token.Cursor.discardRest next, after⟩)
    | .ok step => return (resumed fresh step, ⟨Token.Cursor.discardRest next, after⟩)

/--
Has the parser take the tokens of `cursor`, which comes from `origin` with tokens consumed, one
by one, until there are none or the handover stops.
-/
def rest (origin : Z) (parser : P) (cursor : Z) (consumed : Token.Cursor.Consumed cursor origin) :
    StateT H m (Except (ParseError E) (ControlFlow R) × P ×
      { z : Z // Token.Cursor.Consumed z origin }) :=
  match Token.Cursor.next? cursor with
  | none => return (.ok .continue, parser, ⟨cursor, consumed⟩)
  | some (token, ⟨next, step⟩) => do
    match ← takeOne parser cursor token next step with
    | (.goOn parser, ⟨later, taken⟩) =>
      rest origin parser later (Token.Cursor.consumed_trans taken consumed)
    | (.stop answer parser, ⟨later, taken⟩) =>
      return (answer, parser, ⟨later, Token.Cursor.consumed_trans taken consumed⟩)
termination_by (⟨cursor⟩ : Consuming Z)
decreasing_by exact taken

/-- The first token of a producer that has one. -/
def first (cursor : Z) (h : Token.Cursor.HasNext cursor) :
    Token.Cursor.Token Z × { next : Z // Token.Cursor.Consumed next cursor } :=
  match taken : Token.Cursor.next? cursor with
  | some first => first
  | none => absurd (Token.Cursor.next?_isSome h) (by rw [taken]; exact Bool.false_ne_true)

end

variable {H P R E : Type} [Handler H Id] [ParseByToken P H Id E R] [Parse P H Id E R]
  {b : Token.BatchTag}

/-- The handler told the version of the cursor, unless it was told the version of the input
already. -/
def told (adapter : ParseAdapter H P) (cursor : LexerCursor b) : H :=
  ((show StateT H Id Unit from if (ParseAdapter.Internal.versionSet adapter) then pure ()
    else Handler.setVersion (Token.Cursor.version cursor)).run adapter.handler).2

/-- What a call of the consumer gives after its first token: the answer and the cursor, and the
adapter with the handler, the parser and the resources. -/
def finish (cursor : LexerCursor b) (parseState : ParseState H) :
    (After P R E × { z : LexerCursor b // z.Consumed cursor }) × H →
      (Except (ParseError E) (ControlFlow R) ×
        { next : LexerCursor b // next.Consumed cursor }) × ParseAdapter H P
  | ((.stop answer parser, z), handler) =>
    ((answer, z),
      ParseAdapter.Internal.mk handler parser (ParseAdapter.Internal.versionSetAfter answer)
        parseState)
  | ((.goOn parser, ⟨later, taken⟩), handler) =>
    let y := (rest cursor parser later taken).run handler
    ((y.1.1, y.1.2.2),
      ParseAdapter.Internal.mk y.2 y.1.2.1 (ParseAdapter.Internal.versionSetAfter y.1.1) parseState)

/- LEAN: on the lexer's cursors and in the monad of the reader proofs only, so that a call's
result is read off its definition. -/
/-- A call of the consumer: the handler told the version first, unless it was told the version
of the input already; then the parser takes the tokens of the cursor until there are none or
the handover stops. -/
def consume (cursor : LexerCursor b) (h : cursor.HasNext) :
    StateT (ParseAdapter H P) Id
      (Except (ParseError E) (ControlFlow R) ×
        { next : LexerCursor b // next.Consumed cursor }) := fun adapter =>
  finish cursor (ParseAdapter.Internal.parseState adapter)
    ((takeOne adapter.parser cursor (cursor.next h).1 (cursor.next h).2.val
      (cursor.next h).2.property).run (told adapter cursor))

omit [Parse P H Id E R] in
/-- After a call, the handler is to be told the version again only if the parser broke. -/
theorem versionSet_consume (cursor : LexerCursor b) (h : cursor.HasNext)
    (adapter : ParseAdapter H P) :
    ParseAdapter.Internal.versionSet ((consume (H := H) (P := P) cursor h).run adapter).2 =
      ParseAdapter.Internal.versionSetAfter
          ((consume (H := H) (P := P) cursor h).run adapter).1.1 := by
  show ParseAdapter.Internal.versionSet
      (finish cursor (ParseAdapter.Internal.parseState adapter) _).2 =
    ParseAdapter.Internal.versionSetAfter
      (finish cursor (ParseAdapter.Internal.parseState adapter) _).1.1
  generalize (takeOne adapter.parser cursor (cursor.next h).1 (cursor.next h).2.val
    (cursor.next h).2.property).run (told adapter cursor) = x
  obtain ⟨⟨after, ⟨later, taken⟩⟩, handler⟩ := x
  cases after <;> simp only [finish, ParseAdapter.Internal.versionSet_mk]

/-- The consumer that stops after an action on its cursor, on the parse adapter's type. -/
@[reducible]
def consumeFrom : Token.ConsumeFrom (ParseAdapter H P) (LexerCursor b) Id where
  consume := consume

end BSmtLib.Facts.Proofs.Reader.Param.Stop
