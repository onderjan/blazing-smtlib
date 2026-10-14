module

public import BSmtLib.Facts.PublicApi.Adapters
public import BSmtLib.Facts.Reader
public import BSmtLib.Facts.Proofs.Reader.ValidOpen
import all BSmtLib.Lexer
import all BSmtLib.Parser.Adapter
import all BSmtLib.Reader

@[expose] public section

/-!
# Where the reader began to discard

The reader's lexer, after the slices and before the end of the input, has the fields of the
library's lexer with the script consumer of the end-to-end proofs fed the same slices
(`feed_core`), so it began to discard where that lexer's session, the input not ended, says
(`reader_discardedFrom`). Facts of the library, from the end-to-end proofs.

Any lexer correct with every consumer, with the script consumer, fed a file without the end of
the input, goes through the file's readings (`Reader.ValidOpen.runs_group_open`), so with no
`exit` it does not discard, and with `exit` it discards from the end of its `)`
(`open_session_discard`).
-/

open BSmtLib.Facts.Proofs.Reader.Consumer BSmtLib.Facts.Proofs.Reader.Feed
open BSmtLib.Facts.Proofs.Reader.Lexes.Good BSmtLib.Facts.Proofs.Reader.Lexes.NoLayout
open BSmtLib.Facts.Proofs.Reader.Lexes.Told BSmtLib.Facts.Proofs.Reader.Param.Adapter
open BSmtLib.Facts.Proofs.Reader.Param.Final BSmtLib.Facts.Proofs.Reader.Param.Finish
open BSmtLib.Facts.Proofs.Reader.Param.General BSmtLib.Facts.Proofs.Reader.Param.Link
open BSmtLib.Facts.Proofs.Reader.Param.Run BSmtLib.Facts.Proofs.Reader.Reader
open BSmtLib.Facts.Proofs.Reader.Valid BSmtLib.Facts.Proofs.Reader.ValidOpen
open BSmtLib.Facts.PublicApi.Adapters BSmtLib.Facts.Reader.Adapters

namespace BSmtLib.Facts.Proofs.PublicApi.Discard

open BSmtLib.Lexer
open BSmtLibSpec BSmtLibSpec.Grammar BSmtLibSpec.Parser
open BSmtLibSpec.Parser.Properties
open BSmtLibSpec.Lexer (Handed)
open BSmtLib.Facts.Parser.Adapters.Bridge.Rejection
open BSmtLib.Facts.Lexer.Adapters (toVersion Answering AnswerM LexOps lexing)
open BSmtLib.Facts.PublicApi.Adapters (feed)
open BSmtLib.Facts.Proofs.Reader.Param.Flagged (flaggedOps)
open BSmtLibSpec.Facts.Proofs.Grammar.RoundTrip (FileReadingFrom)
open BSmtLibSpec.Facts.Proofs.Lexicon.RoundTrip.Tokens (Concrete)

variable {version : Lexicon.Version}

/-- Fed the slices without the end of the input, the reader over a lexer related to a lexer with
the script consumer ends, where it does not fail, with the fields that lexer ends with. -/
theorem feed_core (hnl : NoLayout (scriptConsumer version) (toVersion version)) :
    ∀ (slices : List Regex.Chars) (a : FLexer version) (p : PLexer) (taken : List Handed),
      InvF version a p taken →
      Reach (scriptConsumer version) (toVersion version) (Internal.core a) →
      Reader.Param.Dom.Good version ((flaggedOps.runInput a false slices).run taken).2 →
      ∀ reader, feed (Reader.Internal.ofLexer p : RecReader) slices = .ok reader →
        Internal.core (Reader.Internal.lexer reader) =
          Internal.core ((flaggedOps.runInput a false slices).run taken).1.2
  | [], a, p, taken, hI, _, _, reader, hfeed => by
    simp only [feed, Except.ok.injEq] at hfeed
    subst hfeed
    exact hI.1.symm
  | slice :: slices, a, p, taken, hI, hR, hgood, reader, hfeed => by
    simp only [LexOps.runInput, StateT.run_bind] at hgood ⊢
    generalize hr : (flaggedOps.lexSliceStep a slice.toByteArray.toByteSlice).run taken = r
      at hgood ⊢
    obtain ⟨⟨res, a'⟩, taken'⟩ := r
    rw [id_bind_eq] at hgood ⊢
    have hgood' : Reader.Param.Dom.Good version taken' := by
      dsimp only at hgood
      rcases res with e | held₁
      · exact hgood
      · obtain ⟨more, hmore⟩ := runInput_extendsT false slices
          (flaggedOps.withHeld a' (held₁.or (flaggedOps.held a'))) taken'
        rw [hmore] at hgood
        exact hgood.of_append
    simp only [feed, readSlice_ofLexer] at hfeed
    rcases slice_stepT hnl _ ⟨slice, rfl⟩ a p taken hI hR hr hgood' with
        ⟨held₁, rfl, p₂, held₂, hp, hI', hR'⟩ | ⟨e, rfl, ⟨e₂, x, hp⟩, -⟩
    · rw [hp] at hfeed
      exact feed_core hnl slices _ _ taken' hI' hR' hgood reader hfeed
    · rw [hp] at hfeed
      cases hfeed

open BSmtLib.Facts.Lexer.Adapters (toVersion toLocation lexing)

/-- The reader, fed the slices without the end of the input, began to discard where the library's
lexer with the script consumer, the input not ended, did. -/
theorem reader_discardedFrom (version : BSmtLibSpec.Lexicon.Version) (slices : List ByteList)
    {reader : RecReader} (hfeed : feed (readerOf version) slices = .ok reader) :
    reader.discardedFrom.map toLocation =
      (lexing Lexer.Adapters.Lexer.lexOps (scriptConsumer version) version [] slices
        false).discardedFrom := by
  have hgood := lexing_good _ Facts.Lexer.correctWithConsumers version slices false
  rw [Reader.Param.Flagged.lexing_flagged] at hgood ⊢
  let a₀ : FLexer version :=
    Lexer.new { errored := false, version := toVersion version, spoiled := false, layout := false }
      (toVersion version)
  have htaken : (lexing flaggedOps (scriptConsumer version) version [] slices false).taken =
      ((flaggedOps.runInput a₀ false slices).run []).2 := rfl
  rw [htaken] at hgood
  have hI : InvF version a₀ (Lexer.new recordingAdapter (toVersion version)) [] := by
    refine ⟨rfl, trivial, rfl, rfl, rfl, [], rfl, ?_⟩
    unfold AdapterAtG
    rw [recRun_nil]
    exact ⟨toVersion_eq_libVersion version, rfl, by rw [toVersion_eq_libVersion]; rfl, rfl⟩
  have hR : Reach (scriptConsumer version) (toVersion version) (Internal.core a₀) := Reach.new
  have hnl := noLayout (scriptConsumer version) (scriptConsumer_concrete version)
      (toVersion version)
  have hcore := feed_core hnl slices a₀ _ [] hI hR hgood reader
    (by rw [← readerOf_eq]; exact hfeed)
  have e : (lexing flaggedOps (scriptConsumer version) version [] slices false).discardedFrom =
      (flaggedOps.discardedFrom ((flaggedOps.runInput a₀ false slices).run []).1.2).map
        toLocation := rfl
  rw [e]
  show (Internal.core (Reader.Internal.lexer reader)).discardedFrom.map toLocation = _
  rw [hcore]
  rfl

/-- A lexer correct with every consumer, with the script consumer, fed a file without the end of
the input, began to discard at the end of `exit` if the file ends with it, where its unread rest
begins, and did not discard otherwise. -/
theorem open_session_discard (lexing : BSmtLibSpec.Lexer.Lexing)
    (h : BSmtLibSpec.Lexer.CorrectWithConsumers lexing) (version : BSmtLibSpec.Lexicon.Version)
    (slices : List ByteList) {commands : List BSmtLibSpec.Grammar.Tree.Command}
    {segments : List (BSmtLibSpec.Lexicon.Version × Concrete)}
    {final : ByteList}
    (hreading : FileReadingFrom version 0 slices.flatten commands segments
      final) :
    (commands.getLast? = some .exit →
        (lexing (scriptConsumer version) version [] slices false).discardedFrom.map (·.offset) =
          some (slices.flatten.length - final.length)) ∧
      (commands.getLast? ≠ some .exit →
        (lexing (scriptConsumer version) version [] slices false).discardedFrom = none) := by
  have hfile := hreading.file
  have hscript := script_of_file hfile
  have hruns := h.2.1 (scriptConsumer version) version slices false
    (scriptConsumer_breaksAtEnd version)
  rw [scriptConsumer_concrete, readyFrom_false] at hruns
  obtain ⟨tokens, eof, hg⟩ := group_of_file hfile
  have hg' : Group version 0 (slices.flatten.drop 0) commands tokens eof := by simpa using hg
  have hfr : FileReadingFrom version 0 (slices.flatten.drop 0) commands
      segments final := by simpa using hreading
  obtain ⟨tail, hseg, htail⟩ := segment_group_open h.1 hg' (Nat.zero_le _)
  rw [hseg] at hruns
  exact runs_group_open h.1 hscript commands [] version 0 tokens eof [] tail _ segments
    final _ rfl (by simp) (by simp [doneTokens]) hg' (Nat.zero_le _) hfr htail hruns

/-- A read through the end of the input fed the slices first. -/
theorem feed_of_readThrough {H P E R : Type} [Parser.Parse P H Id E R] [Traits.Handler H Id]
    {reader : Reader H P} {slices : List ByteList} {result : Option (Span.Located R)}
    {before after : Reader H P}
    (h : readThrough reader slices = .ok (result, before, after)) :
    feed reader slices = .ok before := by
  unfold readThrough at h
  split at h
  · cases h
  · rename_i before' hfeed
    split at h
    · cases h
      exact hfeed
    · cases h

end BSmtLib.Facts.Proofs.PublicApi.Discard
