module

public import BSmtLib.Facts.PublicApi.Adapters.Reprinter
public import BSmtLib.Facts.PublicApi.Adapters.Builder

@[expose] public section

/-!
# Where constructs are

What a span layer claims of the spans it reports, judged by the specification: the bytes of a
construct's span are a construct of its category in its version (`Grammar.Syntax.IsSExpr`,
`IsAttribute`, `IsSort`, `IsTerm`, `IsCommand`); at an error, the bytes of an open construct up
to the offending token start one.
-/

namespace BSmtLib.Facts.PublicApi.Adapters.Constructs

open BSmtLib.Parser
open BSmtLib.Facts.PublicApi.Adapters BSmtLib.Facts.PublicApi.Adapters.Builder
open BSmtLib.Facts.PublicApi.Adapters.Reprinter (Kind)
open BSmtLibSpec.Lexicon (Tokenization)
open BSmtLibSpec.Grammar (SyntaxToken)
open BSmtLibSpec.Grammar.Syntax (IsSExpr IsAttribute IsSort IsTerm IsCommand)

/-- `IsKind kind version tokens`: in the version, the tokens are a construct of the kind. -/
def IsKind (kind : Reprinter.Kind) (version : BSmtLibSpec.Lexicon.Version)
    (tokens : List BSmtLibSpec.Grammar.SyntaxToken) : Prop :=
  match kind with
  | .sExpr => ∃ sExpr, IsSExpr version tokens sExpr
  | .attribute => ∃ «attribute», IsAttribute version tokens «attribute»
  | .sort => ∃ sort, IsSort version tokens sort
  | .term => ∃ term, IsTerm version tokens term
  | .command => ∃ command, IsCommand version tokens command

/-- `ReadAs kind version bytes`: in the version, the bytes are tokens, the last ending at their
end, that are a construct of the kind. -/
def ReadAs (kind : Reprinter.Kind) (version : Token.Version) (bytes : ByteList) : Prop :=
  ∃ tokens, Tokenization.Exactly (specVersion version) 0 bytes tokens ∧
    IsKind kind (specVersion version) (tokens.map (SyntaxToken.ofToken (specVersion version)))

/-- `StartsAs kind version bytes`: in the version, the bytes are tokens, with whitespace between
and after them, that some tokens continue into a construct of the kind. -/
def StartsAs (kind : Reprinter.Kind) (version : Token.Version) (bytes : ByteList) : Prop :=
  ∃ tokens more, Tokenization.From (specVersion version) 0 bytes tokens ∧
    IsKind kind (specVersion version)
      (tokens.map (SyntaxToken.ofToken (specVersion version)) ++ more)

end BSmtLib.Facts.PublicApi.Adapters.Constructs

namespace BSmtLib.Facts.PublicApi.Adapters.Reprinter.SpanLayer

open BSmtLib.Parser
open BSmtLib.Facts.PublicApi.Adapters BSmtLib.Facts.PublicApi.Adapters.Reprinter
open BSmtLib.Facts.PublicApi.Adapters.Constructs (ReadAs StartsAs)

variable {r : Reprinter}

/--
`layer.SpansExact`: on every input, in any slices, that the script reader over `r`'s handler
reads to the end, the lexer over the layer reads it to the end too, its handler told what the
reader's is; the commands it writes down are the input up to where the reader began to discard,
with layout between them; and every construct it writes down is trimmed and is, in its version,
a construct of its kind.
-/
def SpansExact (layer : SpanLayer r) : Prop :=
  ∀ version slices result before after,
    readThrough (r.reader version) slices = .ok (some result, before, after) →
      ∃ result' lexer,
        lexThrough (Lexer.new layer.wrap version) slices = .ok (some result', lexer) ∧
        layer.handler lexer.consumer = after.handler ∧
        Spaced (((layer.constructs lexer.consumer).filter (·.kind = .command)).map
            (bytesOf slices.flatten))
          (slices.flatten.take (readUpTo before slices.flatten.length)) ∧
        ∀ construct ∈ layer.constructs lexer.consumer,
          Trimmed (bytesOf slices.flatten construct) ∧
            ReadAs construct.kind construct.version (bytesOf slices.flatten construct)

/--
`layer.HoldsBackErrors`: on every input, in any slices, where the script reader over `r`'s
handler fails with a syntax or a handler error, the lexer over the layer fails with the error
held back, at the same span, with at least one open construct; every open construct ends where
the offending token does, starts at or before it, and its bytes up to the offending token start,
in its version, a construct of its kind.
-/
def HoldsBackErrors (layer : SpanLayer r) : Prop :=
  ∀ version slices failure,
    readThrough (r.reader version) slices = .error failure →
    (∀ io, failure.error.cause ≠ .io io) → (∀ kind, failure.error.cause ≠ .lexical kind) →
      ∃ error held, lexThrough (Lexer.new layer.wrap version) slices = .error error ∧
        error.cause = .consumer held ∧ error.span = failure.error.span ∧
        (∃ parseError : ParseError _, parseError.cause = held.cause ∧
          Reader.ReadError.ofParse parseError error.span = failure.error) ∧
        held.opened ≠ [] ∧
        ∀ construct ∈ held.opened,
          construct.span.end = error.span.end ∧
            construct.span.start.offset ≤ error.span.start.offset ∧
            StartsAs construct.kind construct.version
              (bytesIn slices.flatten construct.span.start.offset error.span.start.offset)

end BSmtLib.Facts.PublicApi.Adapters.Reprinter.SpanLayer
