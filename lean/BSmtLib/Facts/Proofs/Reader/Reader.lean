module

public import BSmtLib.Facts.Proofs.Reader.Param.Only
import all BSmtLib.Lexer
import all BSmtLib.Reader

@[expose] public section

/-!
# The library's reader as a recording reader

`libraryReader` is the library's script reader (`Reader.script`) as the
`BSmtLibSpec.Reader.RecordingReader` of the specification formalism (`BSmtLibSpec`) sees it, with
the recording handler and the posture that allows every version. It gives the calls its handler
was told, in order, and whether the end of the input returned a result. The reader is fed the
slices by `Reader.readSlice`, and then the end of the input by `Reader.readEof` if the input has
ended.

Where a call fails, the reader is not given back. The calls are then those held by the handler
that the failure carries, which is the handler of the lexer the failed step leaves
(`readSlice_ofLexer`, `readEof_ofLexer`). `libraryReader` and the definitions it is made of are
adapters, in `Facts.Reader.Adapters`; this module proves what they do.

On a file it reads the traversal's calls and finishes (`reader_reads_files`): the reader's calls
are the lexer's public calls with the parse adapter (`Param.paFeed`), on which
`Param.adapter_feed_file` holds. It finishes only on a file (`reader_finishes_only_on_files`):
where it finishes, those calls do not fail and the end of the input returns a result, which
happens only on a file (`Param.adapter_finishes_only_on_files`).
-/

namespace BSmtLib.Facts.Proofs.Reader.Reader

open BSmtLibSpec
open BSmtLib.Parser.Script (ScriptParser)
open BSmtLib.Parser.Adapter (ParseAdapter)
open BSmtLib.Facts.Lexer.Adapters (toVersion)
open BSmtLib.Facts.Reader.Adapters (PLexer RecAdapter recordingAdapter paFeed)
open BSmtLib.Facts.Reader.Adapters

/-! ## The reader by its lexer -/

theorem readerOf_eq (version : Lexicon.Version) :
    readerOf version = Reader.Internal.ofLexer (Lexer.new recordingAdapter (toVersion version)) :=
  (rfl)

/-- The parse adapter's lexer after the step of a call on a slice, also where it fails. -/
def slicedP (p : PLexer) (slice : ByteSlice) : PLexer :=
  (Lexer.Internal.run p (Lexer.Internal.lexSliceStep (H := RecAdapter) (m := Id)
    (Lexer.Recovery.LexerRecovery.abandon Lexer.Recovery.FailFast)
    (Lexer.Recovery.LexerRecovery.recover Lexer.Recovery.FailFast) slice) :
    Id _).2

/-- The parse adapter's lexer after the step of a call at the end of the input, also where it
fails. -/
def eofedP (p : PLexer) : PLexer :=
  (Lexer.Internal.run p (Lexer.Internal.lexEofStep (H := RecAdapter) (m := Id) (R := Unit)
    (E := Parser.ParseError Unit)
    (Lexer.Recovery.LexerRecovery.abandon Lexer.Recovery.FailFast)
    (Lexer.Recovery.LexerRecovery.recover Lexer.Recovery.FailFast)) : Id _).2

/-- The reader's call on a slice is its lexer's, and a failure carries the handler of the lexer
that the failed step leaves. -/
theorem readSlice_ofLexer (lexer : PLexer) (slice : ByteSlice) :
    ((Reader.Internal.ofLexer lexer : RecReader).readSlice slice : Id _) =
      match (Lexer.lexSlice lexer slice : Id _) with
      | .ok lexer' => .ok (Reader.Internal.ofLexer lexer')
      | .error (error, _) => .error ⟨Reader.ReadError.ofLex error,
          (Lexer.Internal.handler (slicedP lexer slice)).handler⟩ := by
  simp only [Reader.readSlice, Reader.Internal.ofLexer, Lexer.lexSlice, slicedP]
  generalize (Lexer.Internal.run lexer (Lexer.Internal.lexSliceStep (H := RecAdapter) (m := Id)
    (Lexer.Recovery.LexerRecovery.abandon Lexer.Recovery.FailFast)
    (Lexer.Recovery.LexerRecovery.recover Lexer.Recovery.FailFast) slice) : Id _) = r
  rcases r with ⟨e | held, l⟩ <;> rfl

/-- The reader's call at the end of the input is its lexer's, and a failure carries the handler
of the lexer that the failed step leaves. -/
theorem readEof_ofLexer (lexer : PLexer) :
    ((Reader.Internal.ofLexer lexer : RecReader).readEof : Id _) =
      match (Lexer.lexEof lexer : Id _) with
      | .ok (result, lexer') => .ok (result, Reader.Internal.ofLexer lexer')
      | .error (error, _) => .error ⟨Reader.ReadError.ofLex error,
          (Lexer.Internal.handler (eofedP lexer)).handler⟩ := by
  simp only [Reader.readEof, Reader.Internal.ofLexer, Lexer.lexEof, eofedP]
  generalize (Lexer.Internal.run lexer (Lexer.Internal.lexEofStep (H := RecAdapter) (m := Id)
    (R := Unit) (E := Parser.ParseError Unit)
    (Lexer.Recovery.LexerRecovery.abandon Lexer.Recovery.FailFast)
    (Lexer.Recovery.LexerRecovery.recover Lexer.Recovery.FailFast)) : Id _) = r
  rcases r with ⟨e | flow, l⟩ <;> rfl

/-- The calls the handler of the lexer holds, in order. -/
def lexerCalls (lexer : PLexer) : List BSmtLibSpec.Parser.Properties.Event :=
  (Lexer.Internal.handler lexer).handler.reverse

theorem handler_ofLexer (lexer : PLexer) :
    (Reader.Internal.ofLexer lexer : RecReader).handler = (Lexer.Internal.handler lexer).handler :=
    (rfl)

/-- Where the lexer's public calls with the parse adapter do not fail, the reader's run is theirs:
the calls the handler holds after them, and whether the end of the input returned a result. -/
theorem readerRun_paFeed : ∀ (slices : List Regex.Chars) (lexer : PLexer)
    {result : Option (Span.Located Unit)} {lexer' : PLexer},
    paFeed lexer slices = .ok (result, lexer') →
    readerRun (Reader.Internal.ofLexer lexer) slices true = (lexerCalls lexer', result.isSome)
  | [], lexer, result, lexer', h => by
    simp only [paFeed] at h
    simp only [readerRun, readEof_ofLexer]
    revert h
    rcases (Lexer.lexEof lexer : Id _) with ⟨e, _⟩ | ⟨res, l⟩
    · intro h; cases h
    · intro h
      cases h
      rfl
  | slice :: slices, lexer, result, lexer', h => by
    simp only [paFeed] at h
    simp only [readerRun, readSlice_ofLexer]
    revert h
    rcases (Lexer.lexSlice lexer slice.toByteArray.toByteSlice : Id _) with ⟨e, _⟩ | l
    · intro h; cases h
    · intro h
      exact readerRun_paFeed slices l h

/-! ## Reading files -/

/-- The library's reader, fed a file in any slices and then the end of the input, tells the
handler the calls for the file's commands and finishes. -/
theorem libraryReader_readsFiles : BSmtLibSpec.Reader.ReadsFiles libraryReader := by
  intro version slices commands hfile
  obtain ⟨result, lexer, hfeed, hcalls⟩ := Param.Final.adapter_feed_file version slices hfile
  show readerRun (readerOf version) slices true = _
  rw [readerOf_eq, readerRun_paFeed slices _ hfeed]
  exact Prod.ext hcalls rfl

/-! ## Finishing only on files -/

/-- Where the reader's run finishes, the lexer's public calls with the parse adapter do not fail
and the end of the input returns a result. -/
theorem paFeed_of_readerRun : ∀ (slices : List Regex.Chars) (lexer : PLexer),
    (readerRun (Reader.Internal.ofLexer lexer) slices true).2 = true →
    ∃ result lexer', paFeed lexer slices = .ok (some result, lexer')
  | [], lexer, h => by
    simp only [readerRun, readEof_ofLexer] at h
    simp only [paFeed]
    revert h
    rcases (Lexer.lexEof lexer : Id _) with ⟨e, _⟩ | ⟨res, l⟩
    · intro h; cases h
    · intro h
      rcases res with _ | r
      · cases h
      · exact ⟨r, l, rfl⟩
  | slice :: slices, lexer, h => by
    simp only [readerRun, readSlice_ofLexer] at h
    simp only [paFeed]
    revert h
    rcases (Lexer.lexSlice lexer slice.toByteArray.toByteSlice : Id _) with ⟨e, _⟩ | l
    · intro h; cases h
    · intro h
      exact paFeed_of_readerRun slices l h

/-- The library's reader, fed an input in any slices and then the end of the input, finishes only
if the input is a file. -/
theorem libraryReader_finishesOnlyOnFiles : BSmtLibSpec.Reader.FinishesOnlyOnFiles libraryReader :=
    by
  intro version slices h
  change (readerRun (readerOf version) slices true).2 = true at h
  rw [readerOf_eq] at h
  obtain ⟨result, lexer, hfeed⟩ := paFeed_of_readerRun slices _ h
  exact Param.Only.adapter_finishes_only_on_files version slices hfeed

end BSmtLib.Facts.Proofs.Reader.Reader
