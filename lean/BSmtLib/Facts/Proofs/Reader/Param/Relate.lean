module

public import BSmtLib.Facts.Proofs.Reader.Param.Loop
public import BSmtLib.Facts.Proofs.Reader.Param.Split

@[expose] public section

/-!
# The link of the stand-in consumer and the parse adapter

The relator `linkRelator` relates computations of `Flagged (scriptConsumer version)` and of the
parse adapter with the recording handler: the first only adds to the tokens taken and keeps what
went wrong; and while nothing went wrong and the tokens taken stand for a start of the script,
the values are related and the adapter stands where the recording run over items standing for
the tokens leaves the parser (`InvB`). Every call of the stand-in consumer and of the adapter that
stops after an action on its cursor (`Param.Stop`) on the same cursor is so related
(`link_calls`), and the lexer's handovers to that adapter and to the parse adapter are the same
(`Split.script_handOver_eq`), so step 1 relates the library's lexer's steps on the stand-in
consumer and the parse adapter (`link_consumers`).
-/

namespace BSmtLib.Facts.Proofs.Reader.Param.Relate

open BSmtLibSpec BSmtLibSpec.Grammar
open BSmtLib.Token.BatchCursor.Internal (remaining)
open BSmtLibSpec.Parser.Properties
open BSmtLibSpec.Lexer (Handed)
open BSmtLib.Parser (Parse)
open BSmtLib.Parser.Script (ScriptParser)
open BSmtLib.Parser.Adapter (ParseAdapter)
open BSmtLib.Facts.Lexer.Adapters (toVersion Answering AnswerM toHanded)
open BSmtLib.Facts.Parser.Adapters.Bridge.Rejection BSmtLib.Facts.Parser.Adapters.Run.Rejection
open BSmtLib.Facts.Proofs.Parser.Rejection.Library BSmtLib.Facts.Proofs.Reader.Param.Adapter
open BSmtLib.Facts.Proofs.Reader.Param.Basic BSmtLib.Facts.Proofs.Reader.Param.HandOver
open BSmtLib.Facts.Proofs.Reader.Param.Link BSmtLib.Facts.Proofs.Reader.Param.Loop
open BSmtLib.Facts.Reader.Adapters

section

variable (version : Lexicon.Version) (commands : List Tree.Command)

/-- While nothing went wrong and the tokens taken stand for a start of the script, the adapter
stands where the recording run over items standing for them leaves the parser. -/
def InvB (flagged : Flagged (scriptConsumer version)) (taken : List Handed)
    (adapter : RecAdapter) : Prop :=
  flagged.errored = false → Link.Viable commands taken →
    ∃ items : List LibItem, items.map (rcv ∘ Subtype.val) = taken.map (rcv ∘ itemOf) ∧
      AdapterAt version items flagged.version adapter

/- The relator says two things. Of the first computation alone, from any state: it only adds to
the tokens taken, keeps what went wrong, and its value has a related value of the second side;
the last lets `bind` reach the first side's continuation also where the two runs have parted.
Of both, from states in `InvB`: while nothing went wrong and the tokens taken stand for a start
of the script, the values are related and the states are in `InvB` again. -/
/-- The relator of `Flagged (scriptConsumer version)` and the parse adapter. -/
def linkRelator : Relator (Flagged (scriptConsumer version)) AnswerM RecAdapter Id where
  rel Q x y :=
    (∀ flagged taken,
      (∃ more, ((x.run flagged).run taken).2 = taken ++ more) ∧
      (flagged.errored = true → ((x.run flagged).run taken).1.2.errored = true) ∧
      ∃ b, Q ((x.run flagged).run taken).1.1 b) ∧
    (∀ flagged taken adapter, InvB version commands flagged taken adapter →
      ((x.run flagged).run taken).1.2.errored = false →
      Link.Viable commands ((x.run flagged).run taken).2 →
      Q ((x.run flagged).run taken).1.1 (y.run adapter).1 ∧
      InvB version commands ((x.run flagged).run taken).1.2 ((x.run flagged).run taken).2
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
    · -- the first side alone, through the continuation reached by a partner
      obtain ⟨⟨more, hmore⟩, hmono, ⟨b', hb'⟩⟩ := hx.1 flagged taken
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
      -- nothing went wrong after the continuation: nothing went wrong before it
      have he₁ : flagged₁.errored = false := by
        cases h₁ : flagged₁.errored
        · rfl
        · exact absurd (hmono' h₁) (by rw [he]; decide)
      have hv₁ : Link.Viable commands taken₁ := by
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

end

/-- After the end of the script, the tokens taken are all that a parser receives for it. -/
theorem recRun_inr_full {version : Lexicon.Version} {commands : List Tree.Command}
    (hscript : Script version commands) {taken : List Handed} (hvia : Link.Viable commands taken)
    {items : List LibItem} (hst : items.map (rcv ∘ Subtype.val) = taken.map (rcv ∘ itemOf))
    {r : Unit × List Parser.Internal.Input} {log : List Event}
    (hrun : recRun version items = (.ok (.inr r), log)) :
    ¬ taken.length < (received commands).length := by
  intro hlt
  have hlen : items.length = taken.length := by
    have := congrArg List.length hst
    simpa only [List.length_map] using this
  have hparse := parse_items (takes_of_script hscript) (items := items)
    (by rw [hst, hlen]; exact hvia.2) (by rw [hlen]; exact hvia.1)
  rw [parse_recRun, hrun, hlen] at hparse
  have hend := congrArg Prod.snd hparse
  simp only [hlt, ite_true] at hend
  simp [libEnding] at hend

theorem flagged_run (consumer : BSmtLibSpec.Lexer.Consumer) {b : Token.BatchTag}
    (cursor : Token.BatchCursor b)
    (h : cursor.HasNext) (flagged : Flagged consumer) (taken : List Handed) :
    ((Flagged.consume consumer cursor h).run flagged).run taken =
      ((((Answering.consume consumer cursor h).run taken).1,
        { errored := flagged.errored || cursor.version != flagged.version ||
            Flagged.isError ((Answering.consume consumer cursor h).run taken).1.1
          version := ((Answering.consume consumer cursor h).run taken).1.2.val.version
          spoiled := flagged.spoiled || flagged.errored || cursor.version != flagged.version
          layout := if flagged.errored then flagged.layout
            else Flagged.isLayoutAnswer ((Answering.consume consumer cursor h).run taken).1.1 }),
        ((Answering.consume consumer cursor h).run taken).2) := rfl

/-- The link of `Flagged (scriptConsumer version)` and the parse adapter. -/
def linkLink (version : Lexicon.Version) (commands : List Tree.Command) :
    Link (Flagged (scriptConsumer version)) AnswerM (scriptConsumer version).Result
      (Option (scriptConsumer version).Error) RecAdapter Id Unit
      (Parser.ParseError Unit) :=
  { rc := linkRelator version commands, rr := fun _ _ => True, re := fun _ _ => True }

/-- A value of the adapter's side that stands for one of the first side's, as the link relates
them. -/
def partnerOf {ε α : Type} :
    Except ε (ControlFlow α) → Except (Parser.ParseError Unit) (ControlFlow α)
  | .error _ => .error (Parser.ParseError.Internal.new (.handler ()))
  | .ok flow => .ok flow

section

attribute [local instance high] Stop.consumeFrom

theorem link_calls {version : Lexicon.Version} {commands : List Tree.Command}
    (hscript : Script version commands) : Calls (linkLink version commands) where
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
    · refine ⟨hext, fun he => by simp [he], (partnerOf answer, next), ?_, rfl⟩
      rcases answer with _ | (_ | _) <;> exact trivial
    · intro he hv
      have hq := consume_eq cursor h adapter
      simp only at hq
      simp only [Bool.or_eq_false_iff, bne_eq_false_iff_eq] at he
      obtain ⟨⟨hfl, hver⟩, herr⟩ := he
      obtain ⟨more, hmore⟩ := hext
      have hv0 : Link.Viable commands taken := by rw [hmore] at hv; exact hv.of_append
      obtain ⟨items, hst, hat⟩ := hinv hfl hv0
      have herr' : Flagged.isError (ansRest version cursor taken).1.1 = false
          := by rw [hans]; exact herr
      have hvia' : Link.Viable commands (ansRest version cursor taken).2 := by rw [hans]; exact hv
      unfold AdapterAt at hat
      generalize hR : recRun version items = R at hat
      obtain ⟨res, log⟩ := R
      rcases res with e | (⟨v', parser⟩ | r)
      · exact absurd hat id
      · obtain ⟨rfl, hparser, hlog⟩ := hat
        obtain ⟨hshape, hcur, items', hst', hat'⟩ := loop_agree hscript (remaining cursor + 1)
          cursor taken items parser log (Nat.lt_succ_self _) hst (by rw [hR, hver]) herr' hvia'
        rw [hver, hlog, hparser] at hq
        simp only [Prod.mk.injEq] at hq
        rw [hq.1, hq.2.2]
        rw [hans] at hshape hcur hst' hat'
        exact ⟨⟨hshape, Subtype.ext (hcur.trans hq.2.1.symm)⟩, fun _ _ => ⟨items', hst', hat'⟩⟩
      · have hgrow := ansRest_grows version h taken herr'
        have hfull := recRun_inr_full hscript hv0 hst hR
        rw [hans] at hgrow
        exact absurd (Nat.lt_of_lt_of_le hgrow hv.1) hfull

theorem link_consumers_stop {version : Lexicon.Version} {commands : List Tree.Command}
    (hscript : Script version commands) : Consumers (linkLink version commands) :=
  .ofCalls (link_calls hscript)

end

theorem link_consumers {version : Lexicon.Version} {commands : List Tree.Command}
    (hscript : Script version commands) : Consumers (linkLink version commands) :=
  Consumers.ofEq₂ Split.script_handOver_eq (link_consumers_stop hscript)

end BSmtLib.Facts.Proofs.Reader.Param.Relate
