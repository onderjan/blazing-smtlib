import BSmtLib.EndToEnd.Param.Run
import BSmtLib.EndToEnd.Valid
import BSmtLib.Proofs

/-!
# The library's lexer with the parse adapter on a file

The run of the library's lexer with the stand-in consumer on a file (`EndToEnd.lexing_file`) is
the run with `Flagged (scriptConsumer version)` (`lexing_flagged`); on it nothing goes wrong and
the tokens taken stand for what a parser receives for the script, so the run with the parse
adapter does not fail, returns a result at the end of the input, and leaves the adapter's
recording handler with the calls of the traversal (`adapter_feed_file`).
-/

namespace BSmtLib.EndToEnd.Param

open BSmtLib.Lexer BSmtLib.Lexer.Internal
open BSmtLib.Spec BSmtLib.Spec.Grammar BSmtLib.Spec.Parser
open BSmtLib.Spec.Lexer (Handed)
open BSmtLib.ParserProofs BSmtLib.ParserProofs.Rejection
open BSmtLib.Parser (Input ScriptParser Parse ParseAdapter)
open BSmtLib.Proofs.Adapter (toVersion Answering AnswerM LexOps lexing)

/-- After the end of the script, the adapter's handler holds the recording run's log with the
events that are not calls left out. -/
theorem adapterAt_handler {version : Lexicon.Version} {items : List LibItem} {v : Version}
    {adapter : RecAdapter} (h : AdapterAt version items v adapter)
    {r : Unit × List Parser.Input} (hend : (recRun version items).1 = .ok (.inr r)) :
    adapter.handler = calls (recRun version items).2 := by
  unfold AdapterAt at h
  generalize recRun version items = R at h hend
  obtain ⟨res, log⟩ := R
  simp only at hend
  subst hend
  exact h

theorem recRun_nil (version : Lexicon.Version) :
    recRun version [] =
      (.ok (.inl (Bridge.libVersion version, ScriptParser.new unrestrictedPosture)),
        startEvents (Bridge.libVersion version)) := rfl

/-- The library's lexer with the parse adapter, fed a file of commands cut into any slices and
then the end of the input: it returns a result at the end of the input, and the adapter's
recording handler has recorded the calls of the traversal of the script, in order. -/
theorem adapter_feed_file (version : Lexicon.Version) (slices : List Lexicon.Chars)
    {commands : List Tree.Command} (hfile : File version slices.flatten commands) :
    ∃ result lexer,
      paFeed (Lexer.new recordingAdapter (toVersion version)) slices = .ok (some result, lexer) ∧
      (handler lexer).handler.reverse = (record version commands).filter Event.isCall := by
  have hscript := script_of_file hfile
  obtain ⟨hfin, htaken, -⟩ := lexing_file _ Proofs.Lexer.correctWithConsumers version slices hfile
  rw [lexing_flagged] at hfin htaken
  let a₀ : FLexer version :=
    Lexer.new { errored := false, version := toVersion version, spoiled := false, layout := false }
      (toVersion version)
  have hrun : ∀ ops : LexOps, ops = flaggedOps →
      (lexing ops (scriptConsumer version) version [] slices true).outcome.isFinished =
        ((flaggedOps.runInput a₀ true slices).run []).1.1.isFinished ∧
      (lexing ops (scriptConsumer version) version [] slices true).taken =
        ((flaggedOps.runInput a₀ true slices).run []).2 := by
    rintro _ rfl
    exact ⟨rfl, rfl⟩
  rw [(hrun _ rfl).1] at hfin
  rw [(hrun _ rfl).2] at htaken
  have hv : Viable commands ((flaggedOps.runInput a₀ true slices).run []).2 := by
    refine ⟨by rw [← List.length_map (f := rcv ∘ itemOf), htaken]; exact Nat.le_refl _, ?_⟩
    rw [htaken, ← List.length_map (f := rcv ∘ itemOf), htaken, List.take_length]
  have hI : Inv version commands a₀ (Lexer.new recordingAdapter (toVersion version)) [] := by
    refine ⟨rfl, trivial, rfl, rfl, fun _ _ => ⟨[], rfl, ?_⟩⟩
    unfold AdapterAt
    rw [recRun_nil]
    exact ⟨toVersion_eq_libVersion version, rfl, by rw [toVersion_eq_libVersion]; rfl⟩
  obtain ⟨result, lexer, hfeed, items, hst, hat⟩ :=
    feed_agree hscript slices a₀ _ [] hI hfin hv
  refine ⟨result, lexer, hfeed, ?_⟩
  rw [htaken] at hst
  have hlen : items.length = (received commands).length := by
    simpa only [List.length_map] using congrArg List.length hst
  have hparse := parse_items (takes_of_script hscript) (items := items)
    (by rw [hst, hlen, List.take_length]) (Nat.le_of_eq hlen)
  rw [parse_recRun] at hparse
  have hend : ∃ r, (recRun version items).1 = .ok (.inr r) := by
    have hend := congrArg Prod.snd hparse
    simp only [hlen, Nat.lt_irrefl, ite_false] at hend
    revert hend
    rcases (recRun version items).1 with e | (x | r)
    · rcases e with (_ | _) | _ <;> simp [libEnding]
    · simp [libEnding]
    · intro _; exact ⟨r, rfl⟩
  obtain ⟨r, hr⟩ := hend
  rw [adapterAt_handler hat hr]
  have hevents := congrArg Prod.fst hparse
  simp only at hevents
  have harr : (record version commands).countP isArrival = (received commands).length := by
    rw [countP_arrival, (SpecChecks.Parser.record_items hscript).1]
  rw [hlen, ← harr, eventsBefore_all] at hevents
  unfold calls
  rw [← List.filter_reverse, hevents]

end BSmtLib.EndToEnd.Param
