module

public import BSmtLib.Parser.Script
public import BSmtLib.Parser.Internal.Fused.Reserved

public section

/-!
# What the fused script reader's parts share

The fused script reader (`Parser.Internal.Fused`) runs the script parser over a batch cursor as
its loop over single tokens runs it, with the same handler calls, errors and spans, in one
tail-recursive loop over the tokens. This module has what its parts share: the outcome of a step,
which each step hands to the loop's continuation; handler and parser calls run on the handler;
the token's parts; and the port's own step of a token, which the reader uses for the states it
does not fuse.
-/

namespace BSmtLib.Parser.Internal.Fused.Basic

open BSmtLib.Grammar.Nodes BSmtLib.Handler
open BSmtLib.Lexer.Cursor.LexerCursor.Internal (Follows)
open BSmtLib.Parser.Category.Term BSmtLib.Parser.Command
open BSmtLib.Parser.Category.Term.Internal
open BSmtLib.Parser.Command.Internal
open BSmtLib.Parser.Command.Internal.Definition BSmtLib.Parser.Script
open BSmtLib.Parser.Script.ScriptParser.Internal renaming mk → scriptParser,
  command → commandOf, declarations → declarationsOf
open BSmtLib.Lexicon.Value (Symbol Numeral Decimal HexDigits BinDigits
  StringContent)
open BSmtLib.Token (BatchTag TokenCategory)
open BSmtLib.Lexer.Cursor (LexerCursor LexerToken)
open BSmtLib (Version)
open BSmtLib.Version (VersionPosture)

/-- The cause of a failed parse with the handler. -/
abbrev Cause (H : Type) {m : Type → Type} [Handler H m] := ParseErrorCause (Handler.Error H)

/-- The command around a term that the loop reads in its arguments: `assert`, or a definition,
whose last call it is. -/
inductive TermContext (HandledSort : Type) where
  | assert
  | definition (definition : DefinitionEnd HandledSort)

/-- What the loop does after a token: go on at the command level with the command state; go on
in the command's term, with the command around it and the term's mode and levels; go on from
the parser with the cursor (which follows `next`) after the step acted on it; or stop with the
answer, the parser to go on from, the cursor (which follows `next`) and the handler. -/
inductive Outcome (H σ γ μ L P ε : Type) {batch : BatchTag} (next : LexerCursor batch) where
  | command (h : H) (declarations : Nat) (command : σ)
  | term (h : H) (declarations : Nat) (context : γ) (mode : μ) (levels : L)
  | resume (h : H) (parser : P) (cursor : LexerCursor batch) (follows : Follows cursor next)
  | stop (answer : Except ε (ControlFlow Unit)) (parser : P) (cursor : LexerCursor batch)
      (follows : Follows cursor next) (h : H)

/-- The term mode of the handler. -/
abbrev TermModeOf (H : Type) {m : Type → Type} [Handler H m] :=
  TermMode (Handler.SExpr H) (Handler.Attribute H) (Handler.«Sort» H) (Handler.Term H)
    (Handler.Scope H)

/-- The loop's outcome of a step for the handler. -/
abbrev OutcomeOf (H : Type) {m : Type → Type} [CommandHandler H m] {batch : BatchTag}
    (next : LexerCursor batch) :=
  Outcome H (CommandStateOf H) (TermContext (Handler.«Sort» H)) (TermModeOf H)
    (List (TermLevelOf H)) (ScriptParser H) (ParseError (Handler.Error H)) next

/-- The result of the loop over a hand-over from `origin`. -/
abbrev LoopResult (H : Type) {m : Type → Type} [CommandHandler H m] {batch : BatchTag}
    (origin : LexerCursor batch) :=
  Except (ParseError (Handler.Error H)) (ControlFlow Unit) × ScriptParser H ×
    { cursor : LexerCursor batch // cursor.Consumed origin } × H

section

variable {H : Type} {m : Type → Type} [Monad m]

/-- A handler call, run on the handler. -/
@[inline]
def runHandler [Handler H m] {α : Type} (action : ExceptT (Handler.Error H) (StateT H m) α)
    (h : H) : m (Except (Handler.Error H) α × H) :=
  action.run.run h

/-- A parser call, run on the handler. -/
@[inline]
def runParser [Handler H m] {α : Type} (action : PM H α) (h : H) : m (Except (Cause H) α × H) :=
  action.run.run h

/-- The token's content (`LexerCursor.content`), made where it is used, so that the compiler
drops it where nothing uses it. -/
@[inline]
def contentOf {batch : BatchTag} (next : LexerCursor batch) (token : LexerToken batch) :
    ByteSlice :=
  (Lexer.Cursor.Internal.contentBytes next token).toByteSlice
    (Lexer.Cursor.Internal.contentStart next token) (Lexer.Cursor.Internal.contentStop next token)

/-- The reserved word that the token's content spells in the version, if any, read from the
content's bytes without making the content. -/
@[inline]
def reservedAt? {batch : BatchTag} (version : Version) (next : LexerCursor batch)
    (token : LexerToken batch) : Option Token.Reserved :=
  Reserved.ofBounds? (Lexer.Cursor.Internal.contentBytes next token)
    (Lexer.Cursor.Internal.contentStart next token) (Lexer.Cursor.Internal.contentStop next token)
    version

/-- The constant of a token of a constant's category. -/
@[inline]
def constantOf (category : TokenCategory) (content : ByteSlice) : SpecialConstant :=
  match category with
  | .numeral => .numeral (Numeral.Internal.newUnchecked content)
  | .decimal => .decimal (Decimal.Internal.newUnchecked content)
  | .hexadecimal => .hexadecimal (HexDigits.Internal.newUnchecked content)
  | .binary => .binary (BinDigits.Internal.newUnchecked content)
  | _ => .string (StringContent.Internal.newUnchecked content)

variable [CommandHandler H m]

/-- A failure at the token. -/
@[inline]
def fail {batch : BatchTag} (posture : VersionPosture) (next : LexerCursor batch) (h : H)
    (cause : Cause H) {β : Type} (k : OutcomeOf H next → m β) : m β :=
  k <| .stop (.error (ParseError.Internal.new cause)) (ScriptParser.new posture) next (.refl _) h

/-- The step of the token through the port's script step, as the loop over single tokens takes
it (`Parser.Internal.takeOne`). -/
@[inline]
def portStep {batch : BatchTag} (posture : VersionPosture) (h : H) (declarations : Nat)
    (command : CommandStateOf H) (token : LexerToken batch) (next : LexerCursor batch) {β : Type}
    (k : OutcomeOf H next → m β) : m β := do
  let parser : ScriptParser H := scriptParser posture command declarations
  let fresh : ScriptParser H := ScriptParser.new posture
  let input := Internal.Input.ofSyntax (Token.Cursor.«syntax» next token)
  let version := next.version
  match ← runParser
      (do ScriptParser.Internal.arrive parser input; ScriptParser.Internal.step version parser input)
      h with
  | (.error e, h) => k <| .stop (.error (ParseError.Internal.new e)) fresh next (.refl _) h
  | (.ok (.more p), h) => k <| .command h (declarationsOf p) (commandOf p)
  | (.ok (.done r), h) => k <| .stop (.ok (.break r)) fresh next (.refl _) h
  | (.ok (.switchVersion declared resume), h) =>
    match switch : next.setVersion declared with
    | .error _ =>
      k <| .stop (.error (ParseError.Internal.new (.version .unsupported))) fresh next
        (.refl _) h
    | .ok switched =>
      let follows := LexerCursor.setVersion_follows switch
      match ← runParser resume h with
      | (.error e, h) => k <| .stop (.error (ParseError.Internal.new e)) fresh switched follows h
      | (.ok (.more p), h) => k <| .resume h p switched follows
      | (.ok (.done r), h) => k <| .stop (.ok (.break r)) fresh switched follows h
  | (.ok (.discardRest resume), h) =>
    let discarded := next.discardRest
    let follows := LexerCursor.discardRest_follows next
    match ← runParser resume h with
    | (.error e, h) => k <| .stop (.error (ParseError.Internal.new e)) fresh discarded follows h
    | (.ok (.more p), h) => k <| .resume h p discarded follows
    | (.ok (.done r), h) => k <| .stop (.ok (.break r)) fresh discarded follows h

end

end BSmtLib.Parser.Internal.Fused.Basic
