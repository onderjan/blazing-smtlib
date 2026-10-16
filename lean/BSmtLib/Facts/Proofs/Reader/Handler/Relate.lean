module

public import BSmtLib.Facts.Proofs.Reader.Handler.Loop
public import BSmtLib.Facts.Proofs.Reader.Param.Relate
import all BSmtLib.Lexer
import all BSmtLib.Parser.Adapter
import all BSmtLib.Token
import all BSmtLib.Facts.Proofs.Reader.Param.Stop

@[expose] public section

/-!
# The link of the stand-in consumer and the parse adapter with any handler that never fails

As `Param.Relate` for the recording handler: the relator `linkRelator` relates computations of
`Flagged (scriptConsumer version)` and of the parse adapter over a handler whose calls never fail;
while nothing went wrong and the tokens taken stand for a start of the script, the values are
related and the adapter stands where the driver over items standing for the tokens leaves it
(`InvB`, `Loop.At`). Every call of the two on the same cursor is so related (`link_calls`), so
the lexer's steps on the two are related (`link_consumers`).
-/

namespace BSmtLib.Facts.Proofs.Reader.Handler.Relate

open BSmtLibSpec BSmtLibSpec.Grammar
open BSmtLibSpec.Parser.Properties
open BSmtLibSpec.Lexer (Handed)
open BSmtLib.Traits
open BSmtLib.Parser (Parse ParseError ParseErrorCause ParseState)
open BSmtLib.Token.BatchCursor.Internal (remaining)
open BSmtLib.Parser.Script (ScriptParser)
open BSmtLib.Parser.Adapter (ParseAdapter)
open BSmtLib.Facts.Lexer.Adapters (toVersion Answering AnswerM toHanded)
open BSmtLib.Facts.Parser.Adapters.Bridge.Rejection BSmtLib.Facts.Parser.Adapters.Run.Rejection
open BSmtLib.Facts.Proofs.Reader.Param.Adapter BSmtLib.Facts.Proofs.Reader.Param.Basic
open BSmtLib.Facts.Proofs.Reader.Param.HandOver
open BSmtLib.Facts.Proofs.Reader.Param.Loop (ansRest ansRest_extends ansRest_grows Shape)
open BSmtLib.Facts.Proofs.Reader.Param.Relate (flagged_run partnerOf)
open BSmtLib.Facts.Proofs.Reader.Param (Stop.takeOne Stop.rest Stop.consume Stop.told
  Stop.finish Flagged Split.handOver_eq)
open BSmtLib.Facts.Proofs.Reader.Handler.Loop
open BSmtLib.Facts.Proofs.Parser.Blank.Basic
open BSmtLib.Facts.Reader.Adapters

variable {H : Type} [CommandHandler H Id]

/-! ## The adapter's call is its loop -/

theorem rest_eq {b : Token.BatchTag} (origin : Token.BatchCursor b) :
    ∀ (n : Nat) (parser : ScriptParser H) (cursor : Token.BatchCursor b)
      (consumed : Token.Cursor.Consumed cursor origin) (handler : H), remaining cursor < n →
      let r := (Stop.rest (m := Id) origin parser cursor consumed).run handler
      ((r.1.1, r.1.2.1, r.1.2.2.val), r.2) = (loop parser cursor).run handler
  | 0, _, _, _, _, hn => absurd hn (Nat.not_lt_zero _)
  | n + 1, parser, cursor, consumed, handler, hn => by
    intro r
    simp only [r]
    rw [Stop.rest, loop]
    by_cases h : cursor.HasNext
    · rw [Parser.Blank.Loop.next?_hasNext cursor h, dite_eq_left_of_eq_true (eq_true h)]
      simp only [StateT.run_bind]
      generalize (Stop.takeOne (m := Id) parser cursor (cursor.next h).1
        (cursor.next h).2.val (cursor.next h).2.property).run handler = t
      obtain ⟨⟨after, ⟨later, taken⟩⟩, handler'⟩ := t
      cases after with
      | goOn parser' =>
        exact rest_eq origin n parser' later _ handler'
          (Nat.lt_of_lt_of_le (Token.BatchCursor.Consumed.remaining_lt taken)
              (Nat.le_of_lt_succ hn))
      | stop answer parser' => rfl
    · rw [Parser.Blank.Loop.next?_not cursor h, dite_eq_right_of_eq_false (eq_false h)]
      rfl

theorem told_eq {b : Token.BatchTag} (adapter : ParseAdapter H (ScriptParser H))
    (cursor : Token.BatchCursor b) : Stop.told adapter cursor = toldAt adapter cursor.version := by
  unfold Stop.told toldAt
  cases ParseAdapter.Internal.versionSet adapter <;> rfl

section

attribute [local instance high] Param.Stop.consumeFrom

/-- A call of the reader proofs' adapter is its loop over the cursor, from its parser and its
handler told the cursor's version unless it was told the version already. -/
theorem consume_eq {b : Token.BatchTag} (cursor : Token.BatchCursor b) (h : cursor.HasNext)
    (adapter : ParseAdapter H (ScriptParser H)) :
    let q := (Token.ConsumeFrom.consume (m := Id) cursor h :
      StateT (ParseAdapter H (ScriptParser H)) Id _).run adapter
    let r := (loop adapter.parser cursor).run (toldAt adapter cursor.version)
    (q.1.1, q.1.2.val, q.2) = (r.1.1, r.1.2.2,
      ParseAdapter.Internal.mk r.2 r.1.2.1 (ParseAdapter.Internal.versionSetAfter r.1.1)
        (ParseAdapter.Internal.parseState adapter)) := by
  intro q r
  simp only [q, r]
  rw [loop, dite_eq_left_of_eq_true (eq_true h)]
  show ((Stop.consume cursor h adapter).1.1, (Stop.consume cursor h adapter).1.2.val,
    (Stop.consume cursor h adapter).2) = _
  unfold Stop.consume
  rw [← told_eq]
  simp only [StateT.run_bind, Drive.id_bind]
  generalize (Stop.takeOne (m := Id) adapter.parser cursor
    (cursor.next h).1 (cursor.next h).2.val (cursor.next h).2.property).run
      (Stop.told adapter cursor) = t
  obtain ⟨⟨after, ⟨later, taken⟩⟩, handler'⟩ := t
  cases after with
  | stop answer parser' => rfl
  | goOn parser' =>
    simp only [Stop.finish]
    have := rest_eq cursor (remaining later + 1) parser' later taken handler' (Nat.lt_succ_self _)
    simp only at this
    exact congrArg (fun x : (Except (ParseError (Handler.Error H)) (ControlFlow Unit) ×
      ScriptParser H × Token.BatchCursor b) × H =>
        (x.1.1, x.1.2.2, (ParseAdapter.Internal.mk x.2 x.1.2.1
          (ParseAdapter.Internal.versionSetAfter x.1.1) (ParseAdapter.Internal.parseState adapter) :
            ParseAdapter H (ScriptParser H)))) this
end


/-! ## The link -/

section

variable (version : Lexicon.Version) (commands : List Tree.Command) (init : H)

/-- While nothing went wrong and the tokens taken stand for a start of the script, the adapter
stands where the driver over items standing for them leaves it. -/
def InvB (flagged : Flagged (scriptConsumer version)) (taken : List Handed)
    (adapter : ParseAdapter H (ScriptParser H)) : Prop :=
  flagged.errored = false → Param.Link.Viable commands taken →
    ∃ items : List LibItem, items.map (rcv ∘ Subtype.val) = taken.map (rcv ∘ itemOf) ∧
      At version init items flagged.version adapter

/-- The relator of `Flagged (scriptConsumer version)` and the parse adapter over the handler. -/
def linkRelator : Relator (Flagged (scriptConsumer version)) AnswerM
    (ParseAdapter H (ScriptParser H)) Id where
  rel Q x y :=
    (∀ flagged taken,
      (∃ more, ((x.run flagged).run taken).2 = taken ++ more) ∧
      (flagged.errored = true → ((x.run flagged).run taken).1.2.errored = true) ∧
      ∃ b, Q ((x.run flagged).run taken).1.1 b) ∧
    (∀ flagged taken adapter, InvB version commands init flagged taken adapter →
      ((x.run flagged).run taken).1.2.errored = false →
      Param.Link.Viable commands ((x.run flagged).run taken).2 →
      Q ((x.run flagged).run taken).1.1 (y.run adapter).1 ∧
      InvB version commands init ((x.run flagged).run taken).1.2 ((x.run flagged).run taken).2
        (y.run adapter).2)
  pure {_ _ _ a b} h :=
    ⟨fun _ taken => ⟨⟨[], (List.append_nil taken).symm⟩, id, ⟨b, h⟩⟩,
      fun _ _ _ hinv _ _ => ⟨h, hinv⟩⟩
  bind {_ _ _ _ _ _ x y f g} hx hk := by
    have e₁ : ∀ flagged taken, ((x >>= f).run flagged).run taken =
        ((f ((x.run flagged).run taken).1.1).run ((x.run flagged).run taken).1.2).run
          ((x.run flagged).run taken).2 := fun _ _ => rfl
    have e₂ : ∀ adapter, (y >>= g).run adapter = (g (y.run adapter).1).run (y.run adapter).2 :=
      fun _ => rfl
    refine ⟨fun flagged taken => ?_, fun flagged taken adapter hinv he hv => ?_⟩
    · obtain ⟨⟨more, hmore⟩, hmono, ⟨b', hb'⟩⟩ := hx.1 flagged taken
      rw [e₁]
      generalize (x.run flagged).run taken = X at hmore hmono hb'
      obtain ⟨⟨a, flagged₁⟩, taken₁⟩ := X
      obtain ⟨⟨more', hmore'⟩, hmono', hpart⟩ := (hk a b' hb').1 flagged₁ taken₁
      dsimp only at hmore hmono ⊢
      exact ⟨⟨more ++ more', by rw [hmore', hmore, List.append_assoc]⟩,
        fun he => hmono' (hmono he), hpart⟩
    · obtain ⟨_, hmono, ⟨b', hb'⟩⟩ := hx.1 flagged taken
      have hrel := hx.2 flagged taken adapter hinv
      rw [e₁] at he hv ⊢
      rw [e₂]
      generalize (x.run flagged).run taken = X at hmono hb' hrel he hv
      generalize y.run adapter = Y at hrel
      obtain ⟨⟨a, flagged₁⟩, taken₁⟩ := X
      obtain ⟨b, adapter₁⟩ := Y
      obtain ⟨⟨more', hmore'⟩, hmono', -⟩ := (hk a b' hb').1 flagged₁ taken₁
      have he₁ : flagged₁.errored = false := by
        cases h₁ : flagged₁.errored
        · rfl
        · exact absurd (hmono' h₁) (by rw [he]; decide)
      have hv₁ : Param.Link.Viable commands taken₁ := by
        rw [hmore'] at hv
        exact hv.of_append
      obtain ⟨hab, hinv₁⟩ := hrel he₁ hv₁
      exact (hk a b hab).2 flagged₁ taken₁ adapter₁ hinv₁ he hv
  mono hQ h :=
    ⟨fun flagged taken =>
      let ⟨h₁, h₂, ⟨b, hb⟩⟩ := h.1 flagged taken
      ⟨h₁, h₂, ⟨b, hQ _ _ hb⟩⟩,
     fun flagged taken adapter hinv he hv =>
      let ⟨hq, hinv'⟩ := h.2 flagged taken adapter hinv he hv
      ⟨hQ _ _ hq, hinv'⟩⟩

/-- The link of `Flagged (scriptConsumer version)` and the parse adapter over the handler. -/
def linkLink :
    Link (Flagged (scriptConsumer version)) AnswerM (scriptConsumer version).Result
      (Option (scriptConsumer version).Error) (ParseAdapter H (ScriptParser H)) Id Unit
      (ParseError (Handler.Error H)) :=
  { rc := linkRelator version commands init, rr := fun _ _ => True, re := fun _ _ => True }

end

/-- A value of the adapter's side that stands for one of the first side's, as the link relates
them. -/
def partnerOfH {ε α : Type} :
    Except ε (ControlFlow α) → Except (ParseError (Handler.Error H)) (ControlFlow α)
  | .error _ => .error (ParseError.Internal.new (.version .unsupported))
  | .ok flow => .ok flow

section

attribute [local instance high] Param.Stop.consumeFrom

theorem link_calls [NoFails H] {version : Lexicon.Version} {commands : List Tree.Command}
    (hscript : Script version commands) (init : H) : Calls (linkLink version commands init) where
  concrete := rfl
  consume {b} cursor h := by
    refine ⟨fun flagged taken => ?_, fun flagged taken adapter hinv => ?_⟩
    all_goals
      have hrun := flagged_run (scriptConsumer version) cursor h flagged taken
      have hans : ansRest version cursor taken =
          ((((Answering.consume (scriptConsumer version) cursor h).run taken).1.1,
            ((Answering.consume (scriptConsumer version) cursor h).run taken).1.2.val),
            ((Answering.consume (scriptConsumer version) cursor h).run taken).2) := by
        (unfold ansRest; rw [dite_eq_left_of_eq_true (eq_true h)]) <;> rfl
      have hext := ansRest_extends version (remaining cursor + 1) cursor taken (Nat.lt_succ_self _)
      generalize (Answering.consume (scriptConsumer version) cursor h).run taken = A at hrun hans
      obtain ⟨⟨answer, next⟩, taken'⟩ := A
      change ((Flagged.consume (scriptConsumer version) cursor h).run flagged).run taken = _ at hrun
      erw [hrun]
      rw [hans] at hext
      dsimp only at hext hans
      dsimp only
    · refine ⟨hext, fun he => by simp [he], (partnerOfH answer, next), ?_, rfl⟩
      rcases answer with _ | (_ | _) <;> exact trivial
    · intro he hv
      have hq := consume_eq cursor h adapter
      simp only at hq
      simp only [Bool.or_eq_false_iff, bne_eq_false_iff_eq] at he
      obtain ⟨⟨hfl, hver⟩, herr⟩ := he
      obtain ⟨more, hmore⟩ := hext
      have hv0 : Param.Link.Viable commands taken := by rw [hmore] at hv; exact hv.of_append
      obtain ⟨items, hst, hat⟩ := hinv hfl hv0
      have herr' : Param.Flagged.isError (ansRest version cursor taken).1.1 = false
          := by rw [hans]; exact herr
      have hvia' : Param.Link.Viable commands (ansRest version cursor taken).2 := by
        rw [hans]; exact hv
      unfold At at hat
      generalize hD : hRun version init items = D at hat
      generalize hR : Param.Link.recRun version items = R at hat
      obtain ⟨res, s⟩ := D
      obtain ⟨resr, log⟩ := R
      rcases res with e | (⟨v', parser⟩ | r) <;> rcases resr with er | (⟨vr, pr⟩ | rr) <;>
        (try exact absurd hat id)
      · obtain ⟨rfl, rfl, hparser, htold, hblank⟩ := hat
        rw [← hver] at htold
        obtain ⟨hshape, hcur, items', hst', hat'⟩ := loop_agree hscript init
          (remaining cursor + 1) cursor taken items pr log parser s (Nat.lt_succ_self _) hst
          (by rw [hR, hver]) (by rw [hD, hver]) hblank herr' hvia'
        rw [htold, hparser] at hq
        simp only [Prod.mk.injEq] at hq
        rw [hq.1, hq.2.2]
        rw [hans] at hshape hcur hst' hat'
        refine ⟨⟨hshape, Subtype.ext (hcur.trans hq.2.1.symm)⟩, fun _ _ => ⟨items', hst', ?_⟩⟩
        unfold At at hat' ⊢
        exact hat'
      · have hgrow := ansRest_grows version h taken herr'
        have hfull := Param.Relate.recRun_inr_full hscript hv0 hst hR
        rw [hans] at hgrow
        exact absurd (Nat.lt_of_lt_of_le hgrow hv.1) hfull

theorem link_consumers_stop [NoFails H] {version : Lexicon.Version} {commands : List Tree.Command}
    (hscript : Script version commands) (init : H) : Consumers (linkLink version commands init) :=
  .ofCalls (link_calls hscript init)

end

theorem script_handOver_eq [NoFails H] (floor : Option Nat) (low : Nat)
    (batch : Token.Internal.TokenBatch)
    (bytesAfter : ByteArray) (hfloor : ∀ p, floor = some p → batch.EndsAfter p) :
    @Lexer.Internal.handOver (ParseAdapter H (ScriptParser H)) Id Unit
        (ParseError (Handler.Error H)) _ _ (fun _ => inferInstance)
        floor low batch bytesAfter hfloor =
      @Lexer.Internal.handOver (ParseAdapter H (ScriptParser H)) Id Unit
        (ParseError (Handler.Error H)) _ _
        (fun _ => Param.Stop.consumeFrom) floor low batch bytesAfter hfloor :=
  Param.Split.handOver_eq
    (fun parser state cursor => Proofs.Parser.Fused.Step.parse_eq parser state cursor)
    (Proofs.Parser.HandOver.script_noHandOver NoFails.noNonstandard)
    floor low batch bytesAfter hfloor

theorem link_consumers [NoFails H] {version : Lexicon.Version} {commands : List Tree.Command}
    (hscript : Script version commands) (init : H) : Consumers (linkLink version commands init) :=
  Consumers.ofEq₂ script_handOver_eq (link_consumers_stop hscript init)

end BSmtLib.Facts.Proofs.Reader.Handler.Relate
