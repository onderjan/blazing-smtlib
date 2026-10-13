import BSmtLib.Reader
import BSmtLibSpec.Reader
import BSmtLibSpec.Grammar.Properties
import BSmtLib.EndToEnd.Param.Only
import BSmtLib.EndToEnd.Adapters

/-!
# The library's reader as a recording reader

`libraryReader` is the library's script reader (`Reader.script`), with the recording handler and
the posture that allows every version, as the specification's `BSmtLibSpec.Reader.RecordingReader` sees
it: fed the slices by `Reader.readSlice`, and then the end of the input by `Reader.readEof` if
the input has ended, it gives the calls its handler was told, in order, and whether the end of
the input returned a result. Where a call fails, the reader is not given back; the calls are then
those the handler holds after the failed call, read from the reader's lexer. `libraryReader` and
the definitions it is made of are adapters, in `EndToEnd.Adapters`; this module proves what they
do.

On a file it reads the traversal's calls and finishes (`reader_reads_files`): the reader's calls
are the lexer's public calls with the parse adapter (`Param.paFeed`), on which
`Param.adapter_feed_file` holds. It finishes only on a file (`reader_finishes_only_on_files`):
where it finishes, those calls do not fail and the end of the input returns a result, which
happens only on a file (`Param.adapter_finishes_only_on_files`).
-/

namespace BSmtLib.EndToEnd

open BSmtLib.Lexer.Internal
open BSmtLibSpec BSmtLibSpec.Grammar BSmtLibSpec.Parser
open BSmtLibSpec.Parser.Properties
open BSmtLibSpec.Grammar.Syntax BSmtLibSpec.Grammar.File BSmtLibSpec.Grammar.Properties
open BSmtLib.ParserProofs BSmtLib.ParserProofs.Rejection
open BSmtLib.Parser (ScriptParser ParseAdapter)
open BSmtLib.Proofs.Adapter (toVersion)
open BSmtLib.EndToEnd.Param (PLexer RecAdapter recordingAdapter paFeed)

/-! ## The reader by its lexer -/

theorem readerOf_eq (version : Lexicon.Version) :
    readerOf version = Reader.Internal.ofLexer (Lexer.new recordingAdapter (toVersion version)) :=
  rfl

theorem readSlice_ofLexer (lexer : PLexer) (slice : ByteSlice) :
    ((Reader.Internal.ofLexer lexer : RecReader).readSlice slice : Id _) =
      match (Lexer.lexSlice lexer slice : Id _) with
      | .ok lexer' => .ok (Reader.Internal.ofLexer lexer')
      | .error (error, ()) => .error { error := ReadError.ofLex error } := by
  simp only [Reader.readSlice, Reader.Internal.ofLexer]
  generalize (Lexer.lexSlice lexer slice : Id _) = r
  rcases r with ⟨e, ⟨⟩⟩ | l <;> rfl

theorem readEof_ofLexer (lexer : PLexer) :
    ((Reader.Internal.ofLexer lexer : RecReader).readEof : Id _) =
      match (Lexer.lexEof lexer : Id _) with
      | .ok (result, lexer') => .ok (result, Reader.Internal.ofLexer lexer')
      | .error (error, ()) => .error { error := ReadError.ofLex error } := by
  simp only [Reader.readEof, Reader.Internal.ofLexer]
  generalize (Lexer.lexEof lexer : Id _) = r
  rcases r with ⟨e, ⟨⟩⟩ | ⟨res, l⟩ <;> rfl

theorem handler_ofLexer (lexer : PLexer) :
    (Reader.Internal.ofLexer lexer : RecReader).handler = (handler lexer).handler := rfl

/-- Where the lexer's public calls with the parse adapter do not fail, the reader's run is theirs:
the calls the handler holds after them, and whether the end of the input returned a result. -/
theorem readerRun_paFeed : ∀ (slices : List Regex.Chars) (lexer : PLexer)
    {result : Option (Located Unit)} {lexer' : PLexer},
    paFeed lexer slices = .ok (result, lexer') →
    readerRun (Reader.Internal.ofLexer lexer) slices true = (lexerCalls lexer', result.isSome)
  | [], lexer, result, lexer', h => by
    simp only [paFeed] at h
    simp only [readerRun, readEof_ofLexer]
    revert h
    rcases (Lexer.lexEof lexer : Id _) with ⟨e, ⟨⟩⟩ | ⟨res, l⟩
    · intro h; cases h
    · intro h
      cases h
      rfl
  | slice :: slices, lexer, result, lexer', h => by
    simp only [paFeed] at h
    simp only [readerRun, readSlice_ofLexer]
    revert h
    rcases (Lexer.lexSlice lexer slice.toByteArray.toByteSlice : Id _) with ⟨e, ⟨⟩⟩ | l
    · intro h; cases h
    · intro h
      exact readerRun_paFeed slices l h

/-! ## Reading files -/

/-- The library's reader, fed a file in any slices and then the end of the input, tells the
handler the calls for the file's commands and finishes. -/
theorem libraryReader_readsFiles : BSmtLibSpec.Reader.ReadsFiles libraryReader := by
  intro version slices commands hfile
  obtain ⟨result, lexer, hfeed, hcalls⟩ := Param.adapter_feed_file version slices hfile
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
    rcases (Lexer.lexEof lexer : Id _) with ⟨e, ⟨⟩⟩ | ⟨res, l⟩
    · intro h; cases h
    · intro h
      rcases res with _ | r
      · cases h
      · exact ⟨r, l, rfl⟩
  | slice :: slices, lexer, h => by
    simp only [readerRun, readSlice_ofLexer] at h
    simp only [paFeed]
    revert h
    rcases (Lexer.lexSlice lexer slice.toByteArray.toByteSlice : Id _) with ⟨e, ⟨⟩⟩ | l
    · intro h; cases h
    · intro h
      exact paFeed_of_readerRun slices l h

/-- The library's reader, fed an input in any slices and then the end of the input, finishes only
if the input is a file. -/
theorem libraryReader_finishesOnlyOnFiles : BSmtLibSpec.Reader.FinishesOnlyOnFiles libraryReader := by
  intro version slices h
  change (readerRun (readerOf version) slices true).2 = true at h
  rw [readerOf_eq] at h
  obtain ⟨result, lexer, hfeed⟩ := paFeed_of_readerRun slices _ h
  exact Param.adapter_finishes_only_on_files version slices hfeed

end BSmtLib.EndToEnd
