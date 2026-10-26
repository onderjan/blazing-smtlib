module

public import BSmtLib.Facts.Parser.Adapters.Cursor

@[expose] public section

/-!
# What a parse of a cursor does

A parse of a cursor breaks with its result, continues or fails, and gives back
the parser and the cursor. `outcome` reads all of it but:

- the parse state, which holds nothing;
- where and in which state a parser stopped that failed with the handler's error, which the
  parser does not promise.

- `HandlerOnly program`: the program fails, if it does, with the handler's error only.
- `Finishes version parser tokens program back`: the parser finishes right after the tokens with
  the program's result, as the parser `back`. That holds on every cursor that has the tokens
  first and then anything read in the version. The parser makes the effects of the program and
  fails where the program fails.
- `Waits version parser tokens program after`: the parser takes the tokens and continues, as the
  parser that `after` gives with the program's result. That holds on every cursor that has exactly
  the tokens, all read in the version. The parser makes the effects of the program and fails
  where the program fails.
- `Rejects version parser tokens program kind`: the parser takes exactly the tokens and fails with
  a syntax error of the kind. That holds on every cursor that has the tokens first and then
  anything read in the version. The parser first makes the effects of the program and fails where
  the program fails.

The program of each is handler-only, so that a syntax error of the parse is the one the statement
names, at the token it names.

These definitions are adapters: the root theorems of `BSmtLib.Facts.Parser` about the category
parsers and the combinators are stated with them, so they are trusted, and are to be read with
the specification formalism (`BSmtLibSpec`).
-/

namespace BSmtLib.Facts.Parser.Adapters.Outcome

open BSmtLib.Token (Cursor)
open BSmtLib.Parser (Parse ParseError ParseErrorCause ParseState SyntaxErrorKind VersionErrorKind)
open BSmtLib.Facts.Parser.Adapters.Cursor (Takes Reads)

/-- What a parse answered, read with the parser and the cursor it gave back. -/
inductive Outcome (R P Z E : Type) where
  /-- It finished with the result, back as the parser, at the cursor. -/
  | finished (result : R) (parser : P) (next : Z)
  /-- It took every token and continues, as the parser. -/
  | waits (parser : P)
  /-- It failed with a syntax error of the kind, at the cursor. -/
  | rejected (kind : SyntaxErrorKind) (next : Z)
  /-- It failed with a version error of the kind, at the cursor. -/
  | rejectedVersion (kind : VersionErrorKind) (next : Z)
  /-- It failed with the handler's error. -/
  | failed (error : E)

section

variable {P H R E : Type} {Z : Type} [Cursor Z] {cursor : Z}

/-- What a parse answered, as an `Outcome`. -/
def outcome : Except (ParseError E) (ControlFlow R) × P × ParseState H ×
      { next : Z // Cursor.HasNext cursor → Cursor.Consumed next cursor } →
    Outcome R P Z E
  | (.ok (.break result), parser, _, next) => .finished result parser next.val
  | (.ok .continue, parser, _, _) => .waits parser
  | (.error error, _, _, next) =>
    match error.cause with
    | .syntax kind => .rejected kind next.val
    | .version kind => .rejectedVersion kind next.val
    | .handler error => .failed error

end

section

variable {P H R E : Type} {m : Type → Type} [Monad m]

/-- The program fails, if it does, with the handler's error only. -/
def HandlerOnly {α : Type} (program : ExceptT (ParseErrorCause E) (StateT H m) α) : Prop :=
  ∃ calls : ExceptT E (StateT H m) α, program = ExceptT.adapt ParseErrorCause.handler calls

/-- The answer of a handler-only program, its result read as `onResult` says. -/
def answer {α Z : Type} (onResult : α → Outcome R P Z E) (next : Z) :
    Except (ParseErrorCause E) α → Outcome R P Z E
  | .ok result => onResult result
  | .error (.handler error) => .failed error
  | .error (.syntax kind) => .rejected kind next
  | .error (.version kind) => .rejectedVersion kind next

variable [Parse P H m E R]

/--
`Finishes version parser tokens program back`: the parser finishes right after the tokens with the
result of the handler-only program, as the parser `back`. That holds on every cursor that has the
tokens first and then any tokens, all read in the version. The parser makes the effects of the
program and fails where the program fails.
-/
def Finishes (version : Version) (parser : P) (tokens : List Parser.Internal.Input)
    (program : ExceptT (ParseErrorCause E) (StateT H m) R) (back : P) : Prop :=
  HandlerOnly program ∧
  ∀ {Z : Type} [Cursor Z] (state : ParseState H) (cursor next : Z)
    (rest : List Parser.Internal.Input),
    Takes version cursor tokens next → Reads version next rest →
    outcome <$> Parse.parse parser state cursor =
      answer (fun result => .finished result back next) next <$> program.run

/--
`Waits version parser tokens program after`: the parser takes the tokens and continues, as the
parser that `after` gives with the result of the handler-only program. That holds on every cursor
that has exactly the tokens, all read in the version. The parser makes the effects of the program
and fails where the program fails.
-/
def Waits {α : Type} (version : Version) (parser : P) (tokens : List Parser.Internal.Input)
    (program : ExceptT (ParseErrorCause E) (StateT H m) α) (after : α → P) : Prop :=
  HandlerOnly program ∧
  ∀ {Z : Type} [Cursor Z] (state : ParseState H) (cursor last : Z),
    Takes version cursor tokens last → Cursor.next? last = none →
    outcome <$> Parse.parse parser state cursor =
      answer (fun result => .waits (after result)) last <$> program.run

/--
`Rejects version parser tokens program kind`: the parser takes exactly the tokens and fails with a
syntax error of the kind. That holds on every cursor that has the tokens first and then any
tokens, all read in the version. The parser first makes the effects of the handler-only program
and fails where the program fails.
-/
def Rejects (version : Version) (parser : P) (tokens : List Parser.Internal.Input)
    (program : ExceptT (ParseErrorCause E) (StateT H m) Unit) (kind : SyntaxErrorKind) : Prop :=
  HandlerOnly program ∧
  ∀ {Z : Type} [Cursor Z] (state : ParseState H) (cursor next : Z)
    (rest : List Parser.Internal.Input),
    Takes version cursor tokens next → Reads version next rest →
    outcome <$> Parse.parse parser state cursor =
      answer (fun () => .rejected kind next) next <$> program.run

end

end BSmtLib.Facts.Parser.Adapters.Outcome
