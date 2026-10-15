module

public import BSmtLib.Facts.Proofs.Reader.ParamW.Slice
public import BSmtLib.Facts.Proofs.Reader.Param.Calls
import all BSmtLib.Lexer.Internal.WRustPort

@[expose] public section

/-!
# The Rust port's steps of the calls on two consumers

The steps that the Rust port's public calls run on a slice (`lexSliceStep`) and at the end of
the input (`lexEofStep`), with its operations `Rust.ops`, on two consumers whose handovers are
related, and given related recovery actions, are related: the same result, with related held
results and errors, the same lexer state, and the consumers' states related as the relator says.
-/

namespace BSmtLib.Facts.Proofs.Reader.ParamW.Calls

open BSmtLib.Lexer
open BSmtLib.Lexer.Internal (BATCH_CAPACITY Stop Interrupted Failure LexerCore InnerM StepM LexM)
open BSmtLib.Facts.Proofs.Reader.Param.Basic BSmtLib.Facts.Proofs.Reader.Param.Walk
open BSmtLib.Facts.Proofs.Reader.Param.Slice (FlowLRel HeldRel)
open BSmtLib.Facts.Proofs.Reader.Param.Calls (EofFlowRel SliceRel EofRel)
open BSmtLib.Facts.Proofs.Reader.ParamW.HandOver BSmtLib.Facts.Proofs.Reader.ParamW.Slice
open BSmtLib.Lexer.Internal.WRustPort BSmtLib.Lexer.Error

attribute [local instance] Rust.ops

section

variable {H₁ H₂ : Type} {m₁ m₂ : Type → Type} [Monad m₁] [Monad m₂] {R₁ R₂ E₁ E₂ : Type}
  {L : Link H₁ m₁ R₁ E₁ H₂ m₂ R₂ E₂}

theorem reset_sim : SSim L (· = ·) (reset (H := H₁) (m := m₁)) (reset (H := H₂) (m := m₂)) := by
  unfold reset; lsimW

theorem executeStep_sim
    (step₁ : Lexer.Internal.WRustPort.InnerM H₁ m₁ (Except (Failure E₁) (ControlFlow R₁)))
    (step₂ : Lexer.Internal.WRustPort.InnerM H₂ m₂ (Except (Failure E₂) (ControlFlow R₂)))
    (h : SSim L (FlowLRel L) step₁ step₂) :
    SSim L (EofFlowRel L) (executeStep step₁) (executeStep step₂) := by
  unfold executeStep
  refine SSim.bind h ?_
  intro r₁ r₂ hr
  match r₁, r₂, hr with
  | .ok .continue, .ok .continue, _ => exact SSim.pure trivial
  | .ok (.break v₁), .ok (.break v₂), hv =>
    exact SSim.bind_eq SSim.getThe fun _ => SSim.pure ⟨hv, rfl⟩
  | .error f₁, .error f₂, hf => exact SSim.pure hf

/-- The Rust port turns related failures into related errors, given related abandoning. -/
theorem fail_sim (abandon₁ : Span.Location → StateT H₁ m₁ Unit)
    (abandon₂ : Span.Location → StateT H₂ m₂ Unit)
    (habandon : ∀ l, L.rc.rel (· = ·) (abandon₁ l) (abandon₂ l))
    (failure₁ : Failure E₁) (failure₂ : Failure E₂) (hf : FailRel L.re failure₁ failure₂)
    (atEnd : Bool) :
    SSim L (LexErrRel L.re) (fail abandon₁ failure₁ atEnd) (fail abandon₂ failure₂ atEnd) := by
  obtain ⟨c₁, s₁, l₁⟩ := failure₁
  obtain ⟨c₂, s₂, l₂⟩ := failure₂
  obtain ⟨hcause, hs, hl⟩ := hf
  cases hs
  cases hl
  unfold fail
  refine SSim.bind_eq SSim.getThe fun core => ?_
  refine SSim.ite (fun _ => SSim.pure ⟨hcause, rfl, rfl⟩) (fun _ => ?_)
  match c₁, c₂, hcause with
  | .lexical e₁, .lexical e₂, he =>
    cases he
    lsimW
    exact SSim.pure ⟨rfl, rfl, rfl⟩
  | .consumer x₁, .consumer x₂, hx =>
    lsimW
    exact SSim.pure ⟨hx, rfl, rfl⟩

theorem skipSlice_sim (slice skip) :
    SSim L (· = ·) (skipSlice (H := H₁) (m := m₁) slice skip)
        (skipSlice (H := H₂) (m := m₂) slice skip) := by
  unfold skipSlice; lsimW

variable [Token.Consume H₁ R₁ E₁] [Token.Consume H₂ R₂ E₂] [∀ b, Token.ConsumeFrom H₁
    (Token.BatchCursor b) m₁]
  [∀ b, Token.ConsumeFrom H₂ (Token.BatchCursor b) m₂]

theorem lexEofInner_sim (hc : ConsumersW L) :
    SSim L (FlowLRel L) (lexEofInner (H := H₁) (m := m₁) (R := R₁) (E := E₁))
        (lexEofInner (H := H₂) (m := m₂) (R := R₂) (E := E₂)) := by
  intro c
  show L.rc.rel _ (lexEofInner c) (lexEofInner c)
  unfold lexEofInner
  dsimp only
  refine L.rc.bind (XSim.run_rel (Qe := IRel L.rr L.re) (Q := (· = ·)) ?_ _) ?_
  · refine XSim.bind_eq (XSim.tryCatch ?_ ?_ (fun _ => rfl)) fun _ => ?_
    · lsimW
    · rintro ⟨r₁, sp₁, l₁, a₁⟩ ⟨r₂, sp₂, l₂, a₂⟩ ⟨hl, hs, hr⟩
      cases hl
      cases hs
      cases r₁ <;> cases r₂ <;> try exact absurd hr id
      · exact XSim.throw ⟨rfl, rfl, hr⟩
      · rename_i s₁ s₂
        cases s₁ <;> cases s₂ <;> try exact absurd hr id
        · exact XSim.pure rfl
        · exact XSim.throw ⟨rfl, rfl, hr⟩
        · rename_i o₁ o₂
          cases o₁ <;> cases o₂ <;> try exact absurd hr id
          · exact modifyCore_sim _ _
          · exact XSim.throw ⟨rfl, rfl, hr⟩
    · lsimW
  · rintro ⟨res₁, c₁⟩ ⟨res₂, c₂⟩ ⟨hres, hcore⟩
    cases hcore
    match res₁, res₂, hres with
    | .ok (), .ok (), _ => exact L.rc.pure ⟨trivial, rfl⟩
    | .error ⟨r₁, sp₁, l₁, a₁⟩, .error ⟨r₂, sp₂, l₂, a₂⟩, ⟨hl, hs, hr⟩ =>
      cases hl
      cases hs
      cases r₁ <;> cases r₂ <;> try exact absurd hr id
      · exact L.rc.pure ⟨⟨hr, rfl, rfl⟩, rfl⟩
      · rename_i s₁ s₂
        cases s₁ <;> cases s₂ <;> try exact absurd hr id
        · exact L.rc.pure ⟨trivial, rfl⟩
        · exact L.rc.pure ⟨hr, rfl⟩
        · rename_i o₁ o₂
          cases o₁ <;> cases o₂ <;> try exact absurd hr id
          · exact L.rc.pure ⟨trivial, rfl⟩
          · exact L.rc.pure ⟨hr, rfl⟩

theorem lexEofStep_sim (hc : ConsumersW L)
    (abandon₁ recover₁ : Span.Location → StateT H₁ m₁ Unit)
    (abandon₂ recover₂ : Span.Location → StateT H₂ m₂ Unit)
    (habandon : ∀ l, L.rc.rel (· = ·) (abandon₁ l) (abandon₂ l))
    (hrecover : ∀ l, L.rc.rel (· = ·) (recover₁ l) (recover₂ l)) :
    SSim L (EofRel L) (lexEofStep abandon₁ recover₁) (lexEofStep abandon₂ recover₂) := by
  unfold lexEofStep
  refine SSim.bind_eq SSim.getThe fun core => ?_
  dsimp only
  lsimW
  all_goals refine SSim.bind (executeStep_sim _ _ (lexEofInner_sim hc)) ?_
  all_goals
    intro r₁ r₂ hr
    match r₁, r₂, hr with
    | .ok f₁, .ok f₂, hf => exact SSim.bind_eq reset_sim fun _ => SSim.pure hf
    | .error f₁, .error f₂, hf =>
      first
        | exact SSim.bind_eq reset_sim fun _ => SSim.pure ⟨hf.1, hf.2.1, rfl⟩
        | exact SSim.bind (fail_sim abandon₁ abandon₂ habandon f₁ f₂ hf true) fun _ _ he =>
            SSim.pure he

theorem lexSliceStep_sim (hc : ConsumersW L)
    (abandon₁ recover₁ : Span.Location → StateT H₁ m₁ Unit)
    (abandon₂ recover₂ : Span.Location → StateT H₂ m₂ Unit)
    (habandon : ∀ l, L.rc.rel (· = ·) (abandon₁ l) (abandon₂ l))
    (hrecover : ∀ l, L.rc.rel (· = ·) (recover₁ l) (recover₂ l)) (slice : ByteSlice) :
    SSim L (SliceRel L) (lexSliceStep abandon₁ recover₁ slice)
      (lexSliceStep abandon₂ recover₂ slice) := by
  unfold lexSliceStep
  lsimW
  all_goals first
    | exact SSim.pure trivial
    | refine SSim.bind (lexSliceInner_sim hc _) ?_
      intro r₁ r₂ hr
      match r₁, r₂, hr with
      | .ok h₁, .ok h₂, hh => exact SSim.pure hh
      | .error f₁, .error f₂, hf =>
        exact SSim.bind (fail_sim abandon₁ abandon₂ habandon f₁ f₂ hf false) fun _ _ he =>
          SSim.pure he
    | intro r₁ r₂ hr
      match r₁, r₂, hr with
      | .ok h₁, .ok h₂, hh => exact SSim.pure hh
      | .error f₁, .error f₂, hf =>
        exact SSim.bind (fail_sim abandon₁ abandon₂ habandon f₁ f₂ hf false) fun _ _ he =>
          SSim.pure he
end

end BSmtLib.Facts.Proofs.Reader.ParamW.Calls
