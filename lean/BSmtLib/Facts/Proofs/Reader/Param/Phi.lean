module

public import BSmtLib.Facts.Proofs.Reader.Param.Cause
public import BSmtLib.Facts.Proofs.Reader.Param.Split
public import BSmtLib.Facts.Proofs.Reader.Param.RecCanon
import all BSmtLib.Parser.Adapter

@[expose] public section

/-!
# The stand-in consumer that reports the tokens it took when it fails

`Phi version` answers as `Flagged (scriptConsumer version)`, and where it fails, it reports with
its error the tokens taken by then. Its calls and the parse adapter's are related as
`Failing.linkRelatorG` relates the stand-in consumer's (`linkPhi`), and where both fail, the parse
adapter's error is one on which the recording run over items standing for the reported tokens
fails (`Cause.CauseOf`, `causeOfT`), unless the stand-in consumer was handed whitespace or a
comment. That error is unique (`causeOf_unique`).
-/

namespace BSmtLib.Facts.Proofs.Reader.Param.Phi

open BSmtLibSpec
open BSmtLibSpec.Lexer (Handed)
open BSmtLib.Parser.Script (ScriptParser)
open BSmtLib.Facts.Lexer.Adapters (toVersion Answering AnswerM toHanded)
open BSmtLib.Facts.Parser.Adapters.Run.Rejection
open BSmtLib.Facts.Proofs.Reader.Param.Basic BSmtLib.Facts.Proofs.Reader.Param.HandOver
open BSmtLib.Facts.Proofs.Reader.Param.Failing BSmtLib.Facts.Proofs.Reader.Param.Cause
open BSmtLib.Facts.Proofs.Reader.Param.General
open BSmtLib.Facts.Reader.Adapters

/-- The stand-in consumer that reports the tokens it took when it fails. -/
structure _root_.BSmtLib.Facts.Proofs.Reader.Param.Phi (version : Lexicon.Version) where
  fl : Flagged (scriptConsumer version)

variable {version : Lexicon.Version}

instance : Token.Consume (Phi version) Unit (Option ScriptError × List Handed) where
  isConcrete := false

/-- Takes the tokens as the stand-in consumer does; an error comes with the tokens taken. -/
def consume {b : Token.BatchTag} (cursor : Token.BatchCursor b) (h : cursor.HasNext) :
    StateT (Phi version) AnswerM
      (Except (Option ScriptError × List Handed) (ControlFlow Unit) ×
        {c : Token.BatchCursor b // c.Consumed cursor}) :=
  fun s taken =>
    let r := ((Flagged.consume (scriptConsumer version) cursor h).run s.fl).run taken
    (((r.1.1.1.mapError fun e => (e, r.2), r.1.1.2), ⟨r.1.2⟩), r.2)

instance {b : Token.BatchTag} : Token.ConsumeFrom (Phi version) (Token.BatchCursor b) AnswerM where
  consume cursor h := consume cursor h

/-- A computation of `Phi version` as one of the stand-in consumer. -/
def lift {α : Type} (x : StateT (Phi version) AnswerM α) :
    StateT (Flagged (scriptConsumer version)) AnswerM α :=
  fun fl taken => let r := (x ⟨fl⟩).run taken; ((r.1.1, r.1.2.fl), r.2)

theorem lift_pure {α : Type} (a : α) :
    lift (Pure.pure a : StateT (Phi version) AnswerM α) = Pure.pure a := rfl

theorem lift_bind {α β : Type} (x : StateT (Phi version) AnswerM α)
    (f : α → StateT (Phi version) AnswerM β) : lift (x >>= f) = lift x >>= fun a => lift (f a) :=
  rfl

/-- The relator of `Phi version` and the parse adapter: that of the stand-in consumer. -/
def relatorPhi (version : Lexicon.Version) : Relator (Phi version) AnswerM RecAdapter Id where
  rel Q x y := (linkRelatorG version).rel Q (lift x) y
  pure h := by rw [lift_pure]; exact (linkRelatorG version).pure h
  bind hx hk := by rw [lift_bind]; exact (linkRelatorG version).bind hx hk
  mono hQ h := (linkRelatorG version).mono hQ h

/-- Two errors on which recording runs over items standing for the same tokens fail are the
same. -/
theorem causeOf_unique {x y : Parser.ParseError Unit} {t : List Handed}
    (hx : CauseOf version x t) (hy : CauseOf version y t) : x = y := by
  obtain ⟨i₁, h₁, l₁, r₁⟩ := hx
  obtain ⟨i₂, h₂, l₂, r₂⟩ := hy
  have := (RecCanon.recRun_congr version (h₁.trans h₂.symm)).1
  rw [r₁, r₂] at this
  have hc : x.cause = y.cause := by simpa [Except.map] using this
  rw [← Parser.ParseError.Internal.new_eta x, ← Parser.ParseError.Internal.new_eta y, hc]

open Classical in
/-- The error on which the recording runs over items standing for the tokens fail, if they
fail. -/
noncomputable def causeOfT (version : Lexicon.Version) (t : List Handed) :
    Parser.ParseError Unit :=
  if h : ∃ x, CauseOf version x t then h.choose
  else Parser.ParseError.Internal.new (.handler ())

theorem causeOfT_eq {ae : Parser.ParseError Unit} {t : List Handed}
    (h : CauseOf version ae t) : causeOfT version t = ae := by
  unfold causeOfT
  rw [dite_eq_left_of_eq_true (eq_true ⟨ae, h⟩)]
  exact causeOf_unique (Classical.choose_spec (⟨ae, h⟩ : ∃ x, CauseOf version x t)) h

/-- The parse adapter's error `ae` against the error `fe` of the stand-in consumer that took the
tokens: the stand-in consumer was handed whitespace or a comment, or the recording runs over items
standing for the tokens fail with `ae`. -/
def ReE (version : Lexicon.Version) (fe : Option ScriptError × List Handed)
    (ae : Parser.ParseError Unit) : Prop :=
  fe.1 = none ∨ ae = causeOfT version fe.2

/-- The link of `Phi version` and the parse adapter. -/
def linkPhi (version : Lexicon.Version) :
    Link (Phi version) AnswerM Unit (Option ScriptError × List Handed) RecAdapter Id Unit
      (Parser.ParseError Unit) :=
  { rc := relatorPhi version, rr := fun _ _ => True, re := ReE version }

theorem lift_consume {b : Token.BatchTag} (cursor : Token.BatchCursor b) (h : cursor.HasNext)
    (fl : Flagged (scriptConsumer version)) (taken : List Handed) :
    ((lift (Token.ConsumeFrom.consume (m := AnswerM) cursor h :
      StateT (Phi version) AnswerM _)).run fl).run taken =
      let r := ((Flagged.consume (scriptConsumer version) cursor h).run fl).run taken
      (((r.1.1.1.mapError fun e => (e, r.2), r.1.1.2), r.1.2), r.2) := rfl

section

attribute [local instance high] Stop.consumeFrom

theorem callsPhi (version : Lexicon.Version) : Calls (linkPhi version) where
  concrete := rfl
  consume {b} cursor h := by
    have hc := (link_callsG version).consume cursor h
    dsimp only [linkPhi, relatorPhi]
    refine ⟨fun fl taken => ?_, fun fl taken adapter he hinv hgood hsp => ?_,
      fun fl taken adapter he hsp => ?_⟩
    · obtain ⟨h1, h2, h3, h4, -⟩ := hc.1 fl taken
      rw [lift_consume]
      refine ⟨h1, h2, h3, h4, ?_⟩
      dsimp only
      generalize ((Flagged.consume (scriptConsumer version) cursor h).run fl).run taken = r
      obtain ⟨⟨⟨a, c⟩, fl'⟩, t⟩ := r
      rcases a with e | flow
      · exact ⟨(.error (causeOfT version t), c), .inr rfl, rfl⟩
      · exact ⟨(.ok flow, c), by cases flow <;> trivial, rfl⟩
    · have hq := hc.2.1 fl taken adapter he hinv hgood hsp
      have herr := consume_errG version cursor h fl taken adapter hinv hgood hsp
      rw [lift_consume]
      dsimp only
      obtain ⟨⟨hE, hC⟩, hI, hF⟩ := hq
      refine ⟨⟨?_, hC⟩, hI, hF⟩
      revert hE herr
      generalize ((Flagged.consume (scriptConsumer version) cursor h).run fl).run taken = r
      generalize ((Token.ConsumeFrom.consume (m := Id) cursor h : StateT RecAdapter Id _).run
        adapter) = q
      obtain ⟨⟨⟨a, c⟩, fl'⟩, t⟩ := r
      obtain ⟨⟨a', c'⟩, ad'⟩ := q
      intro herr hE
      dsimp only at hE herr ⊢
      rcases a with e | flow <;> rcases a' with e' | flow' <;> simp only [ERel] at hE ⊢
      · rcases herr e' rfl with hl | hcause
        · left
          cases e with
          | none => rfl
          | some _ => simp [Flagged.isLayoutAnswer] at hl
        · exact .inr (causeOfT_eq hcause).symm
      · exact hE
    · exfalso
      have hrun := Relate.flagged_run (scriptConsumer version) cursor h fl taken
      rw [lift_consume] at hsp
      dsimp only at hsp
      change ((Flagged.consume (scriptConsumer version) cursor h).run fl).run taken = _ at hrun
      rw [hrun] at hsp
      simp [he] at hsp

theorem consumersPhi_stop (version : Lexicon.Version) : Consumers (linkPhi version) :=
  .ofCalls (callsPhi version)

end

theorem consumersPhi (version : Lexicon.Version) : Consumers (linkPhi version) :=
  Consumers.ofEq₂ Split.script_handOver_eq (consumersPhi_stop version)

end BSmtLib.Facts.Proofs.Reader.Param.Phi
