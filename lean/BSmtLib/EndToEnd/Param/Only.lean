import BSmtLib.EndToEnd.Param.Finish
import BSmtLib.EndToEnd.Param.Final
import BSmtLib.EndToEnd.Session

/-!
# The library's lexer with the parse adapter finishes only on files

The tokens that the library's lexer takes with the stand-in consumer, after the end of the input,
are `Good` (`good_of_classified`, from `lexing_classified`): every start of them stands for a start
of what a parser takes, or for such a start and the first item no script continues with, and the
stand-in consumer went on at all but the last. So where the run with the parse adapter returns a
result at the end of the input, the run with the stand-in consumer finishes (`feed_finishes`),
which it does only on a file (`lexing_finishes_iff`): `adapter_finishes_only_on_files`.
-/

namespace BSmtLib.EndToEnd.Param

open BSmtLib.Lexer BSmtLib.Lexer.Internal
open BSmtLib.Spec BSmtLib.Spec.Grammar BSmtLib.Spec.Parser
open BSmtLib.Spec.Parser.Traversal
open BSmtLib.Spec.Lexer (Handed)
open BSmtLib.ParserProofs BSmtLib.ParserProofs.Rejection
open BSmtLib.Parser (Input ScriptParser Parse ParseAdapter)
open BSmtLib.Proofs.Adapter (toVersion Answering AnswerM LexOps lexing)

/-! ## The tokens taken are good -/

section

variable {version : Lexicon.Version} {commands : List Tree.Command} {taken : List Received}
  {ending : Ending}

/-- Every start of tokens that stand for a start of what a parser takes stands for one too. -/
theorem viable_take (htakes : Takes version commands taken ending) {handed : List Handed}
    (hpre : handed.map (rcv ∘ itemOf) <+: taken) (n : Nat) :
    Spec.Parser.Viable version ((handed.take n).map (rcv ∘ itemOf)) :=
  ⟨commands, taken, ending, htakes, by
    rw [List.map_take]
    exact (List.take_prefix n _).trans hpre⟩

/-- On tokens that stand for a start of what a parser takes, the stand-in consumer goes on at
every proper start of what it takes. -/
theorem continue_take (htakes : Takes version commands taken ending) {handed : List Handed}
    (hpre : handed.map (rcv ∘ itemOf) <+: taken) {n : Nat} (hn : n ≤ handed.length)
    (hlt : n < taken.length) :
    (scriptConsumer version).answer (handed.take n) = .continue := by
  have hlen : (handed.take n).length = n := by rw [List.length_take]; omega
  have hst : (handed.take n).map (rcv ∘ itemOf) = taken.take (handed.take n).length := by
    rw [hlen, List.map_take]
    have := List.prefix_iff_eq_take.mp ((List.take_prefix n _).trans hpre)
    rw [this, List.length_take, List.length_map]
    congr 1
    omega
  rw [answer_takes htakes hst (by rw [hlen]; omega), hlen, ite_eq_left hlt]
  rfl

/-- Tokens that stand for a start of what a parser takes are good. -/
theorem good_of_prefix (htakes : Takes version commands taken ending) {handed : List Handed}
    (hpre : handed.map (rcv ∘ itemOf) <+: taken) : Good version handed := by
  have hle : handed.length ≤ taken.length := by
    simpa only [List.length_map] using hpre.length_le
  refine ⟨fun n _ => .inl (viable_take htakes hpre n), fun n _ hlt => ?_⟩
  exact continue_take htakes hpre (Nat.le_of_lt hlt) (by omega)

end

/-- The tokens a session with the stand-in consumer takes, ending as `Classified` says, are
good. -/
theorem good_of_classified {feed : Lexicon.Version → List Lexicon.Chars → Bool → Spec.Lexer.Fed}
    {version : Lexicon.Version} {input : Lexicon.Chars}
    {session : Spec.Lexer.Session Unit ScriptError}
    (h : Classified feed version input session) : Good version session.taken := by
  rcases h with ⟨-, commands, htakes, -⟩ | ⟨-, commands, htakes⟩ |
      ⟨-, commands, taken, ending, before, last, htaken, htakes, hpre, hlt, hof, hnot, hne⟩ |
      ⟨-, commands, taken, ending, htakes, hpre, -⟩
  · exact good_of_prefix htakes (List.prefix_refl _)
  · exact good_of_prefix htakes (List.prefix_refl _)
  · rw [htaken] at hnot ⊢
    have hgood := good_of_prefix htakes hpre
    refine ⟨fun n hn => ?_, fun n hn hlt' => ?_⟩
    · simp only [List.length_append, List.length_singleton] at hn
      rcases Nat.lt_or_ge n (before.length + 1) with hn' | hn'
      · rw [List.take_append_of_le_length (by omega)]
        exact hgood.1 n (by omega)
      · have hn'' : n = before.length + 1 := by omega
        subst hn''
        rw [List.take_of_length_le (by simp)]
        refine .inr ⟨commands, taken, ending, before.map (rcv ∘ itemOf), rcv (itemOf last),
          htakes, by simp, hpre, by simpa using hlt, by simpa using hof, hnot, hne⟩
    · simp only [List.length_append, List.length_singleton] at hlt'
      rw [List.take_append_of_le_length (by omega)]
      exact continue_take htakes hpre (by omega) (by omega)
  · exact good_of_prefix htakes hpre

/-! ## Finishing -/

/-- The library's lexer with the parse adapter, over the recording handler and the script parser
that allows every version, fed the characters of an input cut into any slices, by its public
calls, and then the end of the input: where the end of the input returns a result, the input reads
as a file. -/
theorem adapter_finishes_only_on_files (version : Lexicon.Version) (slices : List Lexicon.Chars)
    {result : Located Unit} {lexer : PLexer}
    (hfeed : paFeed (Lexer.new recordingAdapter (toVersion version)) slices =
      .ok (some result, lexer)) :
    ∃ commands, File version slices.flatten commands := by
  have hcls := lexing_classified _ Proofs.Lexer.correctWithConsumers version slices
  rw [lexing_flagged] at hcls
  have hgood := good_of_classified hcls
  let a₀ : FLexer version :=
    Lexer.new { errored := false, version := toVersion version, spoiled := false, layout := false }
      (toVersion version)
  have htaken : (lexing flaggedOps (scriptConsumer version) version [] slices true).taken =
      ((flaggedOps.runInput a₀ true slices).run []).2 := rfl
  rw [htaken] at hgood
  have hI : InvF version a₀ (Lexer.new recordingAdapter (toVersion version)) [] := by
    refine ⟨rfl, trivial, rfl, rfl, rfl, [], rfl, ?_⟩
    unfold AdapterAtG
    rw [recRun_nil]
    exact ⟨toVersion_eq_libVersion version, rfl, by rw [toVersion_eq_libVersion]; rfl, rfl⟩
  have hfin := feed_finishes slices a₀ _ [] hI hgood hfeed
  have hout : (lexing flaggedOps (scriptConsumer version) version [] slices true).outcome =
      ((flaggedOps.runInput a₀ true slices).run []).1.1 := rfl
  rw [← hout, ← lexing_flagged] at hfin
  exact (lexing_finishes_iff _ Proofs.Lexer.correctWithConsumers version slices).mp hfin

end BSmtLib.EndToEnd.Param
