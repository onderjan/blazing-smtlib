module

public import BSmtLib.Facts.PublicApi.Adapters.Content

@[expose] public section

/-!
# Reprinters and span layers

The shapes of the witnesses that the theorems of `Facts.PublicApi` claim to exist: a handler that is
told contents only, with a printer of what it was told (`Reprinter`), and a layer between the lexer
and the parser that knows where each construct is (`SpanLayer`). The theorems say what the
witnesses do, not how; the witnesses are not trusted.
-/

namespace BSmtLib.Facts.PublicApi.Adapters.Reprinter

open BSmtLib.Parser
open BSmtLib.Facts.PublicApi.Adapters.Content BSmtLib.Lexer.Error BSmtLib.Parser.Script

/-! ## Reprinters -/

/-- A handler that is told contents only, its state before any input, and a printer that
writes, from the handler's state, the tokens of what the handler was told. -/
structure _root_.BSmtLib.Facts.PublicApi.Adapters.Reprinter where
  /-- The handler's type. -/
  H : Type
  /-- The handler's calls, told contents only. -/
  inst : ContentHandler H
  /-- The handler before any input. -/
  handler : H
  /-- The tokens of what the handler was told, from its state. -/
  print : H → List ByteList

instance (r : Reprinter) : ContentHandler r.H := r.inst

/-- The posture that allows the versions from 2.5 on, and any number of version declarations. -/
def from25 : Token.VersionPosture :=
  (Token.VersionPostureBuilder.new.setMaxDeclarations none).build

/-- The script reader over the reprinter's handler, from the version, under the posture. -/
def readerWith (r : Reprinter) (posture : Token.VersionPosture) (version : Token.Version) :
    Reader r.H (ScriptParser r.H) :=
  Reader.script r.handler posture version

/-- The script reader over the reprinter's handler, from the version, allowing every version. -/
def reader (r : Reprinter) (version : Token.Version) : Reader r.H (ScriptParser r.H) :=
  r.readerWith allVersions version

/--
`r.Reprints`: on every input, in any slices, that the script reader over `r`'s handler, allowing
every version, reads to the end, the input up to where the reader began to discard it is the
printed tokens with layout between them, each token as printed or, for a string literal, spelled
otherwise with the same 2.0 meaning.
-/
def Reprints (r : Reprinter) : Prop :=
  ∀ version slices result before after,
    readThrough (r.reader version) slices = .ok (some result, before, after) →
      ∃ written, Spaced written (slices.flatten.take (readUpTo before slices.flatten.length)) ∧
        SameSpellings written (r.print after.handler)

/--
`r.ReprintsExactly`: on every input, in any slices, that the script reader over `r`'s handler,
allowing the versions from 2.5 on and started in one of them, reads to the end, the input up to
where the reader began to discard it is exactly the printed tokens with layout between them.
-/
def ReprintsExactly (r : Reprinter) : Prop :=
  ∀ version slices result before after, version ≠ .v2_0 →
    readThrough (r.readerWith from25 version) slices = .ok (some result, before, after) →
      Spaced (r.print after.handler) (slices.flatten.take (readUpTo before slices.flatten.length))

/-- What a reader's read shows outside its handler's state: the error, or the result, the
printed tokens of the handler, and where the reader began to discard. -/
def observe (r : Reprinter) {R : Type}
    (read : Except (Reader.ReadFailure r.H (ScriptParser r.H))
      (Option (Span.Located R) × Reader r.H (ScriptParser r.H) × Reader r.H (ScriptParser r.H))) :
    Except (Reader.ReadError (ContentHandler.Error r.H))
      (Option (Span.Located R) × List ByteList × Option Span.Location) :=
  match read with
  | .ok (result, before, after) => .ok (result, r.print after.handler, before.discardedFrom)
  | .error failure => .error failure.error

/-! ## Constructs and their spans -/

/-- The categories of the constructs whose spans a layer reports. -/
inductive Kind where
  | sExpr
  | attribute
  | sort
  | term
  | command
  deriving DecidableEq

/-- A construct of the input: its category, the version it is read in, and its span. -/
structure Construct where
  kind : Kind
  version : Token.Version
  span : Span

/-- The bytes of the input from the offset `start` to the offset `stop`. -/
def bytesIn (input : ByteList) (start stop : Nat) : ByteList :=
  (input.drop start).take (stop - start)

/-- Whether the bytes neither start with layout (whitespace or `;`) nor end with whitespace. -/
def Trimmed (bytes : ByteList) : Prop :=
  (∀ c, bytes.head? = some c → ¬ (c = 9 ∨ c = 10 ∨ c = 13 ∨ c = 32 ∨ c = 59)) ∧
    (∀ c, bytes.getLast? = some c → ¬ (c = 9 ∨ c = 10 ∨ c = 13 ∨ c = 32))

/-! ## Span layers -/

/-- An error of the parser held back by a span layer, with the constructs open where it
occurred, outermost first. -/
structure HeldBack (ε : Type) where
  cause : ParseErrorCause ε
  opened : List Construct

/--
A layer between the lexer and the script parser over `r`'s handler: a consumer of the lexer that
passes the tokens on to the parser, knows the span of each, and writes down, at each call that
ends a construct, the construct with its span. It holds back an error of the parser,
returning it with the constructs open where it occurred.
-/
structure SpanLayer (r : Reprinter) where
  /-- The layer's type. -/
  W : Type
  /-- The layer as a consumer of the lexer. -/
  consume : Token.Consume W Unit (HeldBack (ContentHandler.Error r.H))
  /-- The layer's consumption of a cursor. -/
  consumeFrom : ∀ batch, @Token.ConsumeFrom W (Token.BatchCursor batch) Id Unit
    (HeldBack (ContentHandler.Error r.H)) consume _
  /-- The layer around the script parser over `r`'s handler, allowing every version. -/
  wrap : W
  /-- The handler inside the layer. -/
  handler : W → r.H
  /-- The constructs ended so far, in the order of their ends. -/
  constructs : W → List Construct

instance {r : Reprinter} (layer : SpanLayer r) :
    Token.Consume layer.W Unit (HeldBack (ContentHandler.Error r.H)) :=
  layer.consume

instance {r : Reprinter} (layer : SpanLayer r) (batch : Token.BatchTag) :
    Token.ConsumeFrom layer.W (Token.BatchCursor batch) Id :=
  layer.consumeFrom batch

/-- A lexer fed the slices by `Lexer.lexSlice` and then the end of the input by `Lexer.lexEof`:
the result and the lexer after the end of the input, or the first error. -/
def lexThrough {H R E : Type} [Token.Consume H R E]
    [∀ batch, Token.ConsumeFrom H (Token.BatchCursor batch) Id]
    (lexer : Lexer H) : List ByteList → Except (LexError E) (Option (Span.Located R) × Lexer H)
  | [] =>
    match (lexer.lexEof : Id _) with
    | .ok (result, lexer) => .ok (result, lexer)
    | .error (error, _) => .error error
  | slice :: slices =>
    match (lexer.lexSlice slice.toByteArray.toByteSlice : Id _) with
    | .ok lexer => lexThrough lexer slices
    | .error (error, _) => .error error

/-- The bytes of the input in the construct's span. -/
def SpanLayer.bytesOf (input : ByteList) (construct : Construct) : ByteList :=
  bytesIn input construct.span.start.offset construct.span.end.offset

end BSmtLib.Facts.PublicApi.Adapters.Reprinter
