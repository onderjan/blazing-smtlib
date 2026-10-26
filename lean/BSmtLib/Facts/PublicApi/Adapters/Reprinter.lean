module

public import BSmtLib.Facts.PublicApi.Adapters.Content

@[expose] public section

/-!
# Reprinters

The shape of the witness that `Facts.PublicApi.reprinting` claims to exist, and that the reading
theorems read with: a handler that is told contents only, with a printer of what it was told
(`Reprinter`). The theorems say what the witness does, not how; the witness is not trusted.
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
def from25 : Version.VersionPosture :=
  (Version.VersionPostureBuilder.new.setMaxDeclarations none).build

/-- The script reader over the reprinter's handler, with the initial version, under the posture. -/
def readerWith (r : Reprinter) (posture : Version.VersionPosture) (version : Version) :
    Reader r.H (ScriptParser r.H) :=
  Reader.script r.handler posture version

/-- The script reader over the reprinter's handler, with the initial version, allowing every
version. -/
def reader (r : Reprinter) (version : Version) : Reader r.H (ScriptParser r.H) :=
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

end BSmtLib.Facts.PublicApi.Adapters.Reprinter
