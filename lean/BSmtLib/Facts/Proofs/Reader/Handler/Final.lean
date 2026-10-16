module

public import BSmtLib.Facts.Proofs.Reader.Handler.Run
public import BSmtLib.Facts.Proofs.Reader.Param.Final
import all BSmtLib.Lexer
import all BSmtLib.Parser.Adapter
import all BSmtLib.Parser.Script

@[expose] public section

/-!
# The library's lexer with the parse adapter over any handler that never fails, on a file

As `Param.Final` for the recording handler: fed a file of commands cut into any slices and then
the end of the input, the library's lexer with the parse adapter over a handler whose calls
never fail returns a result at the end of the input, and the handler holds what the script
parser's driver over items standing for what a parser receives for the script leaves it with,
the driver having finished the script (`adapter_feed_file`).
-/

namespace BSmtLib.Facts.Proofs.Reader.Handler.Final

open BSmtLib.Lexer
open BSmtLibSpec BSmtLibSpec.Grammar
open BSmtLibSpec.Parser.Properties
open BSmtLib.Traits
open BSmtLib.Parser (Parse)
open BSmtLib.Parser.Script (ScriptParser)
open BSmtLib.Parser.Adapter (ParseAdapter)
open BSmtLib.Facts.Lexer.Adapters (toVersion Answering AnswerM LexOps lexing)
open BSmtLib.Facts.Parser.Adapters.Bridge BSmtLib.Facts.Parser.Adapters.Bridge.Rejection
open BSmtLib.Facts.Parser.Adapters.Run BSmtLib.Facts.Parser.Adapters.Run.Rejection
open BSmtLib.Facts.Proofs.Parser.Cut
open BSmtLib.Facts.Proofs.Parser.Rejection.Library (takes_of_script)
open BSmtLib.Facts.Proofs.Reader.Param.Link (parse_items parse_recRun toVersion_eq_libVersion)
open BSmtLib.Facts.Proofs.Reader.Param (Flagged)
open BSmtLib.Facts.Proofs.Reader.Param.Run (FLexer)
open BSmtLib.Facts.Proofs.Reader.Param.Final (recRun_nil)
open BSmtLib.Facts.Proofs.Reader.Valid
open BSmtLib.Facts.Proofs.Reader.Handler.Loop BSmtLib.Facts.Proofs.Reader.Handler.Run
open BSmtLib.Facts.Proofs.Parser.Blank.Basic
open BSmtLib.Facts.Reader.Adapters

variable {H : Type} [CommandHandler H Id] [NoFails H]

omit [NoFails H] in
theorem hRun_nil (version : Lexicon.Version) (init : H) :
    hRun version init [] =
      (.ok (.inl (Bridge.libVersion version, ScriptParser.new unrestrictedPosture)),
        ((Handler.setVersion (H := H) (Bridge.libVersion version)).run init).2) := rfl

/-- The library's lexer with the parse adapter over a handler that never fails, fed a file of
commands cut into any slices and then the end of the input: it returns a result at the end of the
input, and the handler holds what the driver over items standing for what a parser receives for
the script leaves it with, the driver having finished the script. -/
theorem adapter_feed_file (version : Lexicon.Version) (slices : List Regex.Chars) (init : H)
    {commands : List Tree.Command} (hfile : File version slices.flatten commands) :
    ∃ result lexer, hFeed (Lexer.new (ParseAdapter.new init (ScriptParser.new unrestrictedPosture))
        (toVersion version)) slices = .ok (some result, lexer) ∧
      ∃ items : List LibItem, items.map (rcv ∘ Subtype.val) = received commands ∧
        ∃ r, hRun version init items = (.ok (.inr r), (Internal.handler lexer).handler) := by
  have hscript := script_of_file hfile
  obtain ⟨hfin, htaken, -⟩ := lexing_file _ Facts.Lexer.correctWithConsumers version slices hfile
  rw [Param.Flagged.lexing_flagged] at hfin htaken
  let a₀ : FLexer version :=
    Lexer.new { errored := false, version := toVersion version, spoiled := false, layout := false }
      (toVersion version)
  have hrun : ∀ ops : LexOps, ops = Param.Flagged.flaggedOps →
      (lexing ops (scriptConsumer version) version [] slices true).outcome.isFinished =
        ((Param.Flagged.flaggedOps.runInput a₀ true slices).run []).1.1.isFinished ∧
      (lexing ops (scriptConsumer version) version [] slices true).taken =
        ((Param.Flagged.flaggedOps.runInput a₀ true slices).run []).2 := by
    rintro _ rfl
    exact ⟨rfl, rfl⟩
  rw [(hrun _ rfl).1] at hfin
  rw [(hrun _ rfl).2] at htaken
  have hv : Param.Link.Viable commands
      ((Param.Flagged.flaggedOps.runInput a₀ true slices).run []).2 := by
    refine ⟨by rw [← List.length_map (f := rcv ∘ itemOf), htaken]; exact Nat.le_refl _, ?_⟩
    rw [htaken, ← List.length_map (f := rcv ∘ itemOf), htaken, List.take_length]
  have hI : Inv version commands init a₀
      (Lexer.new (ParseAdapter.new init (ScriptParser.new unrestrictedPosture))
        (toVersion version)) [] := by
    refine ⟨rfl, trivial, rfl, rfl, fun _ _ => ⟨[], rfl, ?_⟩⟩
    unfold At
    rw [hRun_nil, recRun_nil]
    refine ⟨toVersion_eq_libVersion version, toVersion_eq_libVersion version, rfl, ?_, rfl⟩
    show ((Handler.setVersion (H := H) (toVersion version)).run init).2 = _
    rw [toVersion_eq_libVersion]
  obtain ⟨result, lexer, hfeed, items, hst, hat⟩ :=
    feed_agree hscript slices a₀ _ [] hI hfin hv
  refine ⟨result, lexer, hfeed, items, ?_⟩
  rw [htaken] at hst
  have hlen : items.length = (received commands).length := by
    simpa only [List.length_map] using congrArg List.length hst
  refine ⟨hst, ?_⟩
  have hparse := parse_items (takes_of_script hscript) (items := items)
    (by rw [hst, hlen, List.take_length]) (Nat.le_of_eq hlen)
  rw [parse_recRun] at hparse
  have hend : ∃ r, (Param.Link.recRun version items).1 = .ok (.inr r) := by
    have hend := congrArg Prod.snd hparse
    simp only [hlen, Nat.lt_irrefl, ite_false] at hend
    revert hend
    rcases (Param.Link.recRun version items).1 with e | (x | r)
    · rcases e with _ | (_ | _) | _ <;> simp [libEnding]
    · simp [libEnding]
    · intro _; exact ⟨r, rfl⟩
  obtain ⟨r, hr⟩ := hend
  unfold At at hat
  revert hat
  generalize hRun version init items = D
  generalize hR : Param.Link.recRun version items = R at hr
  obtain ⟨res, s⟩ := D
  obtain ⟨resr, log⟩ := R
  dsimp only at hr
  subst hr
  rcases res with e | (_ | r') <;> intro hat <;> (try exact absurd hat id)
  exact ⟨r', by rw [hat]⟩

end BSmtLib.Facts.Proofs.Reader.Handler.Final
