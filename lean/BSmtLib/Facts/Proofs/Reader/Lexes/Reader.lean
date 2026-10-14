import BSmtLib.Facts.Proofs.Reader.Lexes.NoLayout

/-!
# The library's reader lexes, then parses

`BSmtLibSpec.Reader.LexesThenParses` for the library's reader (`libraryReader_lexesThenParses`),
with the library's lexer (`Facts.Lexer.correctWithConsumers`), the library's parser
(`Rejection.libraryParser`, with `Rejection.library_follows` and `Rejection.library_rejects`) and
the parser's item for each token (`libItem`, which stands for what the token stands for:
`libItem_stands`).

The parser as a consumer of the specification answers as the script consumer does
(`Param.consumer_agrees`), so the lexer takes the same tokens with both and finishes alike
(`Param.lexing_congr`); with the script consumer the tokens are good, ended or not
(`Param.lexing_good`); the lexer hands no whitespace or comment to the adapter's consumer for
the script consumer (`Param.noLayout`); and so the reader tells its handler the calls of the
parser's run on the tokens taken, none before the first, and finishes where the lexer with the
script consumer does (`Param.feed_told`, `Param.calls_of_invG`).
-/

namespace BSmtLib.Facts.Proofs.Reader.Lexes.Reader

open BSmtLib.Lexer BSmtLib.Lexer.Internal
open BSmtLibSpec BSmtLibSpec.Lexicon
open BSmtLibSpec.Parser.Properties
open BSmtLibSpec.Regex (chars)
open BSmtLibSpec.Parser.Traversal
open BSmtLibSpec.Lexer (Handed)
open BSmtLib.Facts.Lexer.Adapters (toVersion LexOps lexing)
open BSmtLib.Facts.Parser.Adapters.Bridge BSmtLib.Facts.Parser.Adapters.Bridge.Rejection
open BSmtLib.Facts.Parser.Adapters.Run.Rejection BSmtLib.Facts.Proofs.Parser.Rejection.Discard
open BSmtLib.Facts.Proofs.Parser.Rejection.Library BSmtLib.Facts.Proofs.Reader.Consumer
open BSmtLib.Facts.Proofs.Reader.Lexes.Congr BSmtLib.Facts.Proofs.Reader.Lexes.Good
open BSmtLib.Facts.Proofs.Reader.Lexes.NoLayout BSmtLib.Facts.Proofs.Reader.Lexes.Requests
open BSmtLib.Facts.Proofs.Reader.Lexes.Told BSmtLib.Facts.Proofs.Reader.Param.Final
open BSmtLib.Facts.Proofs.Reader.Param.Finish BSmtLib.Facts.Proofs.Reader.Param.General
open BSmtLib.Facts.Proofs.Reader.Param.Link BSmtLib.Facts.Proofs.Reader.Param.Run
open BSmtLib.Facts.Proofs.Reader.Reader BSmtLib.Facts.Reader.Adapters

/-- The parser's item for a token that a lexer of some version can hand over stands for what
the token stands for. -/
theorem libItem_stands (handed : Handed) (received : Received) (version : Lexicon.Version)
    (h : handed.received = some received) (hof : received.OfVersion version) :
    libraryParser.stands (libItem handed) = received := by
  show rcv (itemOf handed) = received
  obtain ⟨type, start, «end», reserved, content⟩ := handed
  cases type with
  | parenOpen => cases h; rfl
  | parenClose => cases h; rfl
  | numeral =>
    cases h
    show Received.token (.numeral (Bridge.chars (bytesOf content))) = _
    rw [chars_bytesOf]
  | decimal =>
    cases h
    show Received.token (.decimal (Bridge.chars (bytesOf content))) = _
    rw [chars_bytesOf]
  | hexadecimal =>
    cases h
    show Received.token (.hexadecimal (Bridge.chars (bytesOf content))) = _
    rw [chars_bytesOf]
  | binary =>
    cases h
    show Received.token (.binary (Bridge.chars (bytesOf content))) = _
    rw [chars_bytesOf]
  | string =>
    cases h
    show Received.token (.string (Bridge.chars (bytesOf content))) = _
    rw [chars_bytesOf]
  | keyword =>
    cases h
    show Received.token (.keyword (Bridge.chars (bytesOf content))) = _
    rw [chars_bytesOf]
  | quotedSymbol =>
    cases h
    show Received.token (.symbol ⟨Bridge.chars (bytesOf content), true⟩) = _
    rw [chars_bytesOf]
  | whitespace => cases h
  | comment => cases h
  | endOfFile => cases h; rfl
  | unquotedSymbol =>
    cases reserved with
    | none =>
      simp only [BSmtLibSpec.Lexer.Handed.received, Option.isSome_none, Bool.false_eq_true,
          ite_false,
        Option.some.injEq] at h
      subst h
      show Received.token (.symbol ⟨Bridge.chars (bytesOf content), false⟩) = _
      rw [chars_bytesOf]
    | some kind =>
      simp only [BSmtLibSpec.Lexer.Handed.received, Option.isSome_some, ite_true,
        Option.some.injEq] at h
      subst h
      have hmem : content ∈ (basicReservedWords version ++ commandNames version).map chars := hof
      obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hmem
      obtain ⟨r, hr⟩ := Option.isSome_iff_exists.mp (decodeReserved_isSome version s hs)
      simp only [itemOf, hr, rcv, Bridge.received, Option.getD_some, decodeReserved_spec hr]

/-- The library's parser as a consumer of the specification never continues at the end of the
input. -/
theorem specConsumer_breaksAtEnd (version : Lexicon.Version) :
    (specConsumer version).BreaksAtEnd := by
  intro taken token htype
  have h : (specConsumer version).answer (taken ++ [token]) =
      match (libraryParser.parse version ((taken ++ [token]).map libItem)).2 with
      | .finished => .break ()
      | .waiting =>
        if (taken ++ [token]).getLast?.map (·.type) = some .endOfFile then .fail ()
        else .continue
      | .rejected | .failed _ => .fail () := rfl
  rw [h]
  generalize (libraryParser.parse version ((taken ++ [token]).map libItem)).2 = ending
  cases ending <;> simp [htype]

/-- What the library's reader tells its handler and whether it finishes, given that the lexer
hands no whitespace or comment to the adapter's consumer for the script consumer. -/
theorem libraryReader_read (version : Lexicon.Version) (slices : List Regex.Chars)
    (ended : Bool) (hnl : NoLayout (scriptConsumer version) (toVersion version)) :
    let session := lexing Lexer.Adapters.Lexer.lexOps (specConsumer version) version [] slices
      ended
    libraryReader.read version slices ended =
      (if session.taken = [] then []
        else (libraryParser.parse version (session.taken.map libItem)).1.filter Event.isCall,
        session.outcome.isFinished) := by
  intro session
  have hsame := lexing_congr _ Facts.Lexer.correctWithConsumers (consumer_agrees version)
    (scriptConsumer_breaksAtEnd version) (specConsumer_breaksAtEnd version) version slices ended
  have hgood := lexing_good _ Facts.Lexer.correctWithConsumers version slices ended
  rw [Param.Flagged.lexing_flagged] at hsame hgood
  let a₀ : FLexer version :=
    Lexer.new { errored := false, version := toVersion version, spoiled := false, layout := false }
      (toVersion version)
  have htaken : (lexing Param.Flagged.flaggedOps (scriptConsumer version) version [] slices
      ended).taken =
      ((Param.Flagged.flaggedOps.runInput a₀ ended slices).run []).2 := rfl
  have hout : (lexing Param.Flagged.flaggedOps (scriptConsumer version) version [] slices
      ended).outcome =
      ((Param.Flagged.flaggedOps.runInput a₀ ended slices).run []).1.1 := rfl
  rw [htaken] at hgood
  have hI : InvF version a₀ (Lexer.new recordingAdapter (toVersion version)) [] := by
    refine ⟨rfl, trivial, rfl, rfl, rfl, [], rfl, ?_⟩
    unfold AdapterAtG
    rw [recRun_nil]
    exact ⟨toVersion_eq_libVersion version, rfl, by rw [toVersion_eq_libVersion]; rfl, rfl⟩
  have hR : Reach (scriptConsumer version) (toVersion version) (core a₀) := Reach.new
  obtain ⟨fl, adapter, hread, hinv⟩ := feed_told hnl ended slices a₀ _ [] hI hR hgood
  have hcalls := calls_of_invG hinv hgood
  obtain ⟨htk, hfin⟩ := hsame
  rw [htaken] at htk
  rw [hout] at hfin
  show readerRun (readerOf version) slices ended = _
  rw [readerOf_eq, hread, hcalls, hfin, htk, ← Param.Flagged.lexing_flagged]

/-- The library's reader lexes, then parses. -/
theorem libraryReader_lexesThenParses : BSmtLibSpec.Reader.LexesThenParses libraryReader :=
  ⟨lexing Lexer.Adapters.Lexer.lexOps, libraryParser, libItem, Facts.Lexer.correctWithConsumers,
    library_follows, library_rejects, libItem_stands,
    fun version slices ended => libraryReader_read version slices ended
      (noLayout (scriptConsumer version) (scriptConsumer_concrete version) (toVersion version))⟩

end BSmtLib.Facts.Proofs.Reader.Lexes.Reader
