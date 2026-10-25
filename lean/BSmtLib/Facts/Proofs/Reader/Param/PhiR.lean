module

public import BSmtLib.Facts.Proofs.Reader.Param.Phi

@[expose] public section

/-!
# The stand-in consumer that reports the tokens it took, as a consumer of the spec

`replay version` is the script consumer of the spec with, as its error, the tokens taken where it
fails. The adapter's consumer for it takes the tokens as the script consumer's does, and fails
where that fails, with the tokens taken (`answering_replay`). `Phi version` and it are related
call by call (`consumersR`): the same values, and where `Phi version` fails reporting the tokens
taken, the other fails with them.
-/

open BSmtLib.Lexer.Cursor (LexerCursor)

namespace BSmtLib.Facts.Proofs.Reader.Param.PhiR

open BSmtLibSpec
open BSmtLibSpec.Lexer (Handed Consumer Answer)
open BSmtLib.Facts.Lexer.Adapters (toVersion Answering AnswerM toHanded)
open BSmtLib.Facts.Proofs.Reader.Param.Basic BSmtLib.Facts.Proofs.Reader.Param.HandOver
open BSmtLib.Facts.Proofs.Reader.Param.Phi
open BSmtLib.Facts.Reader.Adapters
open BSmtLib.Lexer.Cursor.LexerCursor.Internal (remaining)

/-- The script consumer, failing with the tokens taken. -/
def replay (version : Lexicon.Version) : Consumer where
  Result := Unit
  Error := List Handed
  concrete := false
  answer taken :=
    match (scriptConsumer version).answer taken with
    | .fail _ => .fail taken
    | .break r => .break r
    | .continue => .continue
  switchTo := (scriptConsumer version).switchTo
  discards := (scriptConsumer version).discards

variable {version : Lexicon.Version}

/-- The adapter's consumer for `replay version` takes the tokens as the one for the script
consumer does, and fails where it fails, with the tokens taken. -/
theorem answering_replay {b : Token.BatchTag} : ∀ (n : Nat) (cursor : LexerCursor b)
    (h : cursor.HasNext) (taken : List Handed), remaining cursor < n →
    ((Answering.consume (replay version) cursor h).run taken).2 =
        ((Answering.consume (scriptConsumer version) cursor h).run taken).2 ∧
      ((Answering.consume (replay version) cursor h).run taken).1.2 =
        ((Answering.consume (scriptConsumer version) cursor h).run taken).1.2 ∧
      ((Answering.consume (replay version) cursor h).run taken).1.1 =
        ((Answering.consume (scriptConsumer version) cursor h).run taken).1.1.mapError
          (Option.map fun _ => ((Answering.consume (scriptConsumer version) cursor h).run
            taken).2)
  | 0, _, _, _, hn => absurd hn (Nat.not_lt_zero _)
  | n + 1, cursor, h, taken, hn => by
    rw [Answering.consume, Answering.consume]
    split
    rename_i token next consumed hnext
    have hentry : Answering.entry (replay version) cursor token =
        Answering.entry (scriptConsumer version) cursor token := rfl
    rw [hentry]
    cases hx : Answering.entry (scriptConsumer version) cursor token with
    | none => exact ⟨rfl, rfl, rfl⟩
    | some handed =>
      simp only [StateT.run_bind, StateT.run_get, StateT.run_set, pure_bind]
      have hreq : ∀ t, Answering.requests (replay version) t next =
          Answering.requests (scriptConsumer version) t next := fun _ => rfl
      cases ha : (scriptConsumer version).answer (taken ++ [handed]) with
      | fail e =>
        have hr : (replay version).answer (taken ++ [handed]) = .fail (taken ++ [handed]) := by
          simp only [replay, ha]
        simp only [hr, hreq]
        exact ⟨rfl, rfl, rfl⟩
      | «break» r =>
        have hr : (replay version).answer (taken ++ [handed]) = .break r := by
          simp only [replay, ha]
        simp only [hr, hreq]
        exact ⟨rfl, rfl, rfl⟩
      | «continue» =>
        have hr : (replay version).answer (taken ++ [handed]) = .continue := by
          simp only [replay, ha]
        have hs : (replay version).switchTo = (scriptConsumer version).switchTo := rfl
        have hd : (replay version).discards = (scriptConsumer version).discards := rfl
        simp only [hr, hreq, hs, hd]
        split
        · exact ⟨rfl, rfl, rfl⟩
        · split
          · rename_i h'
            have ih := answering_replay n next h' (taken ++ [handed])
              (Nat.lt_of_lt_of_le consumed.remaining_lt (Nat.le_of_lt_succ hn))
            simp only [StateT.run_bind]
            generalize (Answering.consume (replay version) next h').run (taken ++ [handed]) = A
              at ih ⊢
            generalize (Answering.consume (scriptConsumer version) next h').run
              (taken ++ [handed]) = B at ih ⊢
            obtain ⟨⟨a, ⟨la, ca⟩⟩, ta⟩ := A
            obtain ⟨⟨b, ⟨lb, cb⟩⟩, tb⟩ := B
            obtain ⟨h1, h2, h3⟩ := ih
            simp only at h1 h2 h3
            subst h1
            cases h2
            subst h3
            exact ⟨rfl, rfl, rfl⟩
          · exact ⟨rfl, rfl, rfl⟩

variable (version) in
/-- The relator of `Phi version` and the adapter's consumer for `replay version`: from the same
tokens taken, related values and the same tokens taken. -/
def relatorR : Relator (Phi version) AnswerM (Answering (replay version)) AnswerM where
  rel Q x y := ∀ p a l, Q ((x.run p).run l).1.1 ((y.run a).run l).1.1 ∧
    ((x.run p).run l).2 = ((y.run a).run l).2
  pure h _ _ _ := ⟨h, rfl⟩
  bind {_ _ _ _ _ _ x y f g} hx hk p a l := by
    obtain ⟨h₁, h₂⟩ := hx p a l
    have e₁ : ((x >>= f).run p).run l =
        ((f ((x.run p).run l).1.1).run ((x.run p).run l).1.2).run ((x.run p).run l).2 := rfl
    have e₂ : ((y >>= g).run a).run l =
        ((g ((y.run a).run l).1.1).run ((y.run a).run l).1.2).run ((y.run a).run l).2 := rfl
    rw [e₁, e₂, h₂]
    exact hk _ _ h₁ _ _ _
  mono hQ h p a l := ⟨hQ _ _ (h p a l).1, (h p a l).2⟩

variable (version) in
/-- The link of `Phi version` and the adapter's consumer for `replay version`: equal results, and
where the first fails reporting the tokens taken, the second fails with them. -/
def linkR : Link (Phi version) AnswerM Unit (Option ScriptError × List Handed)
    (Answering (replay version)) AnswerM Unit (Option (List Handed)) where
  rc := relatorR version
  rr := (· = ·)
  re fe e := e = fe.1.map fun _ => fe.2

theorem callsR : Calls (linkR version) where
  concrete := rfl
  consume cursor h p a l := by
    obtain ⟨h1, h2, h3⟩ := answering_replay (version := version) (remaining cursor + 1) cursor h l
      (Nat.lt_succ_self _)
    have hrun := Relate.flagged_run (scriptConsumer version) cursor h p.fl l
    have eP : ((Token.ConsumeFrom.consume (m := AnswerM) cursor h :
        StateT (Phi version) AnswerM _).run p).run l =
        let r := ((Flagged.consume (scriptConsumer version) cursor h).run p.fl).run l
        (((r.1.1.1.mapError fun e => (e, r.2), r.1.1.2), ⟨r.1.2⟩), r.2) := rfl
    have eA : ((Token.ConsumeFrom.consume (m := AnswerM) cursor h :
        StateT (Answering (replay version)) AnswerM _).run a).run l =
        ((((Answering.consume (replay version) cursor h).run l).1, a),
          ((Answering.consume (replay version) cursor h).run l).2) := rfl
    erw [eA, eP]
    change ((Flagged.consume (scriptConsumer version) cursor h).run p.fl).run l = _ at hrun
    dsimp only
    rw [hrun]
    dsimp only
    rw [h1, h2, h3]
    refine ⟨⟨?_, rfl⟩, rfl⟩
    generalize ((Answering.consume (scriptConsumer version) cursor h).run l).1.1 = x
    rcases x with e | (_ | r) <;> simp [ERel, FlowRel, linkR, Except.mapError] <;> rfl

theorem consumersR : Consumers (linkR version) := .ofCalls callsR

/-! ## `Phi version` and the stand-in consumer -/

variable (version) in
/-- The relator of `Phi version` and the stand-in consumer: from the same state of the stand-in
consumer and the same tokens taken, related values, and the same state and tokens taken. -/
def relatorF : Relator (Phi version) AnswerM (Flagged (scriptConsumer version)) AnswerM where
  rel Q x y := ∀ fl l, Q (((lift x).run fl).run l).1.1 ((y.run fl).run l).1.1 ∧
    (((lift x).run fl).run l).1.2 = ((y.run fl).run l).1.2 ∧
    (((lift x).run fl).run l).2 = ((y.run fl).run l).2
  pure h _ _ := ⟨h, rfl, rfl⟩
  bind {_ _ _ _ _ _ x y f g} hx hk fl l := by
    obtain ⟨h₁, h₂, h₃⟩ := hx fl l
    rw [lift_bind]
    have e₁ : (((lift x >>= fun a => lift (f a)).run fl).run l) =
        (((lift (f (((lift x).run fl).run l).1.1)).run (((lift x).run fl).run l).1.2).run
          (((lift x).run fl).run l).2) := rfl
    have e₂ : ((y >>= g).run fl).run l =
        ((g ((y.run fl).run l).1.1).run ((y.run fl).run l).1.2).run ((y.run fl).run l).2 := rfl
    rw [e₁, e₂, h₂, h₃]
    exact hk _ _ h₁ _ _
  mono hQ h fl l := ⟨hQ _ _ (h fl l).1, (h fl l).2⟩

variable (version) in
/-- The link of `Phi version` and the stand-in consumer: the same results, and the same errors but
for the tokens reported. -/
def linkF : Link (Phi version) AnswerM Unit (Option ScriptError × List Handed)
    (Flagged (scriptConsumer version)) AnswerM Unit (Option ScriptError) where
  rc := relatorF version
  rr := (· = ·)
  re fe e := fe.1 = e

theorem callsF : Calls (linkF version) where
  concrete := rfl
  consume cursor h fl l := by
    have eF : (Token.ConsumeFrom.consume (m := AnswerM) cursor h :
        StateT (Flagged (scriptConsumer version)) AnswerM _) =
        Flagged.consume (scriptConsumer version) cursor h := rfl
    erw [lift_consume, eF]
    refine ⟨⟨?_, rfl⟩, rfl, rfl⟩
    show ERel _ _ ((((Flagged.consume (scriptConsumer version) cursor h).run fl).run
      l).1.1.1.mapError _) (((Flagged.consume (scriptConsumer version) cursor h).run fl).run
      l).1.1.1
    cases (((Flagged.consume (scriptConsumer version) cursor h).run fl).run l).1.1.1 with
    | error e => rfl
    | ok f => cases f <;> trivial

theorem consumersF : Consumers (linkF version) := .ofCalls callsF

end BSmtLib.Facts.Proofs.Reader.Param.PhiR
