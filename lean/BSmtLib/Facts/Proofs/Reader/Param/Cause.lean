module

public import BSmtLib.Facts.Proofs.Reader.Param.Failing
import all BSmtLib.Parser.Adapter

@[expose] public section

/-!
# The parse adapter's error, against the stand-in consumer

Where the stand-in consumer `Flagged (scriptConsumer version)` and the parse adapter are related as
`Failing.linkRelatorG` says, a call at which the parse adapter fails, with the error `ae`, is one
at which the stand-in consumer was handed whitespace or a comment, or one after which the tokens
the stand-in consumer took stand for items on which the recording run fails with `ae`
(`consume_errG`).
-/

open BSmtLib.Lexer.Cursor (LexerCursor)

namespace BSmtLib.Facts.Proofs.Reader.Param.Cause

open BSmtLibSpec
open BSmtLibSpec.Lexer (Handed)
open BSmtLib.Parser (Parse)
open BSmtLib.Parser.Script (ScriptParser)
open BSmtLib.Parser.Adapter (ParseAdapter)
open BSmtLib.Facts.Lexer.Adapters (toVersion Answering AnswerM toHanded)
open BSmtLib.Facts.Parser.Adapters.Bridge.Rejection BSmtLib.Facts.Parser.Adapters.Run.Rejection
open BSmtLib.Facts.Proofs.Reader.Param.Adapter BSmtLib.Facts.Proofs.Reader.Param.Basic
open BSmtLib.Facts.Proofs.Reader.Param.General BSmtLib.Facts.Proofs.Reader.Param.HandOver
open BSmtLib.Facts.Proofs.Reader.Param.Layout BSmtLib.Facts.Proofs.Reader.Param.Link
open BSmtLib.Facts.Proofs.Reader.Param.Loop BSmtLib.Facts.Proofs.Reader.Param.Relate
open BSmtLib.Facts.Proofs.Reader.Param.UnarySteps BSmtLib.Facts.Reader.Adapters
open BSmtLib.Facts.Proofs.Reader.Param.Failing
open BSmtLib.Lexer.Cursor.LexerCursor.Internal (remaining)

/-- The parse adapter's error `ae`, after the stand-in consumer took the tokens `taken`: the tokens
stand for items on which the recording run fails with it. -/
def CauseOf (version : Lexicon.Version) (ae : Parser.ParseError Unit) (taken : List Handed) :
    Prop :=
  ∃ items : List LibItem, items.map (rcv ∘ Subtype.val) = taken.map (rcv ∘ itemOf) ∧
    ∃ log, recRun version items = (.error ae.kind, log)

attribute [local instance high] Stop.consumeFrom

theorem consume_errG (version : Lexicon.Version) {b : Token.BatchTag}
    (cursor : LexerCursor b) (h : cursor.HasNext)
    (flagged : Flagged (scriptConsumer version)) (taken : List Handed) (adapter : RecAdapter)
    (hinv : InvG version flagged taken adapter)
    (hgood : Dom.Good version
      (((Flagged.consume (scriptConsumer version) cursor h).run flagged).run taken).2)
    (hsp : (((Flagged.consume (scriptConsumer version) cursor h).run flagged).run
      taken).1.2.spoiled = false) :
    ∀ ae, ((Token.ConsumeFrom.consume (m := Id) cursor h : StateT RecAdapter Id _).run
        adapter).1.1 = .error ae →
      Flagged.isLayoutAnswer
          (((Flagged.consume (scriptConsumer version) cursor h).run flagged).run taken).1.1.1 =
        true ∨
      CauseOf version ae
        (((Flagged.consume (scriptConsumer version) cursor h).run flagged).run taken).2 := by
  have hans : ∀ taken, ansRest version cursor taken =
      ((((Answering.consume (scriptConsumer version) cursor h).run taken).1.1,
        ((Answering.consume (scriptConsumer version) cursor h).run taken).1.2.val),
        ((Answering.consume (scriptConsumer version) cursor h).run taken).2) := fun taken => by
    (unfold ansRest; rw [dite_eq_left_of_eq_true (eq_true h)]) <;> rfl
  have hrun := flagged_run (scriptConsumer version) cursor h flagged taken
  change ((Flagged.consume (scriptConsumer version) cursor h).run flagged).run taken = _ at hrun
  rw [hrun] at hgood hsp ⊢
  dsimp only at hgood hsp ⊢
  have hA := hans taken
  simp only [Bool.or_eq_false_iff, bne_eq_false_iff_eq] at hsp
  obtain ⟨⟨-, -⟩, hcv⟩ := hsp
  have hgood' : Dom.Good version (ansRest version cursor taken).2 := by rw [hA]; exact hgood
  obtain ⟨items, hst, hat⟩ := hinv
  have hq := consume_eq cursor h adapter
  simp only at hq
  unfold AdapterAtG at hat
  generalize hR : recRun version items = R at hat
  obtain ⟨res, log⟩ := R
  intro ae hae
  rcases res with e | (⟨v', parser⟩ | r)
  rotate_left
  · obtain ⟨rfl, hparser, hlog, -⟩ := hat
    obtain ⟨-, -, -, h4⟩ := loop_agreeG (remaining cursor + 1) cursor taken items
      parser log (Nat.lt_succ_self _) hst (by rw [hR, hcv]) (.inr h) hgood'
    rw [hcv, hlog, hparser] at hq
    simp only [Prod.mk.injEq] at hq
    rw [hq.1] at hae
    rw [hA] at h4
    exact h4 ae hae
  all_goals
    have hnot : ∀ v parser log, recRun version items ≠ (.ok (.inl (v, parser)), log) := by
      intro v parser log h'
      rw [hR] at h'
      cases h'
    cases hh : toHanded cursor (cursor.next h).1 with
    | none =>
      have hstep := ansRest_step version h taken
      rw [hh] at hstep
      rw [hA] at hstep
      have hs1 := congrArg (fun p => p.1.1) hstep
      dsimp only at hs1
      left
      rw [hs1]
      rfl
    | some handed =>
      exfalso
      obtain ⟨more, hmore⟩ := ansRest_handed version h taken hh
      have hlen : items.length = taken.length := by
        simpa only [List.length_map] using congrArg List.length hst
      have hpos : 0 < taken.length := by
        refine Nat.pos_of_ne_zero fun h0 => ?_
        have hnil : items = [] := List.length_eq_zero_iff.mp (by omega)
        subst hnil
        exact hnot _ _ _ rfl
      have htake : (ansRest version cursor taken).2.take taken.length = taken := by
        rw [hmore, List.append_assoc, List.take_left']
        rfl
      have hcont := hgood'.2 taken.length hpos (by rw [hmore]; simp)
      rw [htake] at hcont
      have hdom := hgood'.1 taken.length (by rw [hmore]; simp)
      rw [htake] at hdom
      exact answer_ne_continue hdom hst hnot hcont

end BSmtLib.Facts.Proofs.Reader.Param.Cause
