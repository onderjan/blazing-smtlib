module

public import BSmtLib.Facts.Proofs.Reader.Param.Slice
import all BSmtLib.Lexer
import all BSmtLib.Lexer.Error
import all BSmtLib.Span

@[expose] public section

/-!
# The steps of the calls on two consumers

The steps that the lexer's public calls run on a slice (`lexSliceStep`) and at the end of the
input (`lexEofStep`), on two consumers whose calls are related, and given related recovery
actions, are related: the same result, with related held results and errors, the same lexer
state, and the consumers' states related as the relator says.
-/

open BSmtLib.Lexer.Cursor (LexerCursor)

namespace BSmtLib.Facts.Proofs.Reader.Param.Calls

open BSmtLib.Lexer
open BSmtLib.Lexer.Internal (BATCH_CAPACITY Stop Interrupted Failure LexerCore InnerM StepM LexM)
open BSmtLib.Facts.Proofs.Reader.Param.Basic BSmtLib.Facts.Proofs.Reader.Param.HandOver
open BSmtLib.Facts.Proofs.Reader.Param.Slice BSmtLib.Lexer.Error

section

variable {H₁ H₂ : Type} {m₁ m₂ : Type → Type} [Monad m₁] [Monad m₂] {R₁ R₂ E₁ E₂ : Type}

/-- The same answer of a step at the end of the input, located, with related results and
failures. -/
abbrev EofFlowRel (L : Link H₁ m₁ R₁ E₁ H₂ m₂ R₂ E₂) :
    Except (Failure E₁) (ControlFlow (Span.Located R₁)) →
      Except (Failure E₂) (ControlFlow (Span.Located R₂)) → Prop :=
  ERel (FailRel L.re) (FlowRel (LocRel L.rr))

/-- The same result of a call on a slice, with related held results and errors. -/
abbrev SliceRel (L : Link H₁ m₁ R₁ E₁ H₂ m₂ R₂ E₂) :
    Except (LexerError E₁) (Option (Span.Located R₁)) → Except (LexerError E₂)
        (Option (Span.Located R₂)) →
      Prop :=
  ERel (LexErrRel L.re) (ORel (LocRel L.rr))

/-- The same result of a call at the end of the input, with related results and errors. -/
abbrev EofRel (L : Link H₁ m₁ R₁ E₁ H₂ m₂ R₂ E₂) :
    Except (LexerError E₁) (ControlFlow (Span.Located R₁)) →
      Except (LexerError E₂) (ControlFlow (Span.Located R₂)) → Prop :=
  ERel (LexErrRel L.re) (FlowRel (LocRel L.rr))

variable {L : Link H₁ m₁ R₁ E₁ H₂ m₂ R₂ E₂}

theorem reset_sim : SSim L (· = ·) (Internal.reset (H := H₁) (m := m₁))
    (Internal.reset (H := H₂) (m := m₂)) := by
  unfold Internal.reset; lsim

theorem skipSlice_sim (slice skip) :
    SSim L (· = ·) (Internal.skipSlice (H := H₁) (m := m₁) slice skip)
        (Internal.skipSlice slice skip) := by
  unfold Internal.skipSlice; lsim

theorem executeStep_sim (step₁ : InnerM H₁ m₁ (Except (Failure E₁) (ControlFlow R₁)))
    (step₂ : InnerM H₂ m₂ (Except (Failure E₂) (ControlFlow R₂)))
    (h : SSim L (FlowLRel L) step₁ step₂) :
    SSim L (EofFlowRel L) (Internal.executeStep step₁) (Internal.executeStep step₂) := by
  unfold Internal.executeStep
  refine SSim.bind h ?_
  intro r₁ r₂ hr
  match r₁, r₂, hr with
  | .ok .continue, .ok .continue, _ => exact SSim.pure trivial
  | .ok (.break v₁), .ok (.break v₂), hv =>
    exact SSim.bind_eq SSim.getThe fun _ => SSim.pure ⟨hv, rfl⟩
  | .error f₁, .error f₂, hf => exact SSim.pure hf

theorem failCall_sim (abandon₁ : Span.Location → StateT H₁ m₁ Unit)
    (abandon₂ : Span.Location → StateT H₂ m₂ Unit)
    (habandon : ∀ l, L.rc.rel (· = ·) (abandon₁ l) (abandon₂ l))
    (failure₁ : Failure E₁) (failure₂ : Failure E₂) (hf : FailRel L.re failure₁ failure₂)
    (atEnd : Bool) :
    SSim L (LexErrRel L.re) (Internal.failCall abandon₁ failure₁ atEnd)
      (Internal.failCall abandon₂ failure₂ atEnd) := by
  obtain ⟨c₁, s₁, l₁⟩ := failure₁
  obtain ⟨c₂, s₂, l₂⟩ := failure₂
  obtain ⟨hcause, hs, hl⟩ := hf
  cases hs
  cases hl
  unfold Internal.failCall
  refine SSim.bind_eq SSim.getThe fun core => ?_
  refine SSim.ite (fun _ => SSim.pure ⟨hcause, rfl, rfl⟩) (fun _ => ?_)
  match c₁, c₂, hcause with
  | .lexical e₁, .lexical e₂, he =>
    cases he
    lsim
    exact SSim.pure ⟨rfl, rfl, rfl⟩
  | .consumer x₁, .consumer x₂, hx =>
    lsim
    exact SSim.pure ⟨hx, rfl, rfl⟩

variable [Token.Consume H₁ R₁ E₁] [Token.Consume H₂ R₂ E₂] [∀ b, Token.ConsumeFrom H₁
    (LexerCursor b) m₁]
  [∀ b, Token.ConsumeFrom H₂ (LexerCursor b) m₂]

theorem lexEofInner_sim (hc : Consumers L) :
    SSim L (FlowLRel L) (Internal.lexEofInner (H := H₁) (m := m₁) (R := R₁) (E := E₁))
        Internal.lexEofInner := by
  intro c
  show L.rc.rel _ (Internal.lexEofInner c) (Internal.lexEofInner c)
  unfold Internal.lexEofInner
  dsimp only
  refine L.rc.bind (XSim.run_rel (Qe := IRel L.rr L.re) (Q := (· = ·)) ?_ _) ?_
  · refine XSim.bind_eq (XSim.tryCatch ?_ ?_ (fun _ => rfl)) fun _ => ?_
    · lsim
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
    · lsim
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

theorem lexEofStep_sim (hc : Consumers L) (abandon₁ recover₁ : Span.Location → StateT H₁ m₁ Unit)
    (abandon₂ recover₂ : Span.Location → StateT H₂ m₂ Unit)
    (habandon : ∀ l, L.rc.rel (· = ·) (abandon₁ l) (abandon₂ l))
    (hrecover : ∀ l, L.rc.rel (· = ·) (recover₁ l) (recover₂ l)) :
    SSim L (EofRel L) (Internal.lexEofStep abandon₁ recover₁)
        (Internal.lexEofStep abandon₂ recover₂) := by
  unfold Internal.lexEofStep
  refine SSim.bind_eq SSim.getThe fun core => ?_
  dsimp only
  have hrest : SSim L (EofRel L)
      (do
        match ← Internal.executeStep Internal.lexEofInner with
        | .ok flow => do Internal.reset; pure (.ok flow)
        | .error failure =>
          if core.recoveryState.isSome = true then do
            Internal.reset
            pure (.error
              (BSmtLib.Lexer.Error.LexerError.Internal.new failure.cause failure.span none))
          else do
            pure (.error (← Internal.failCall abandon₁ failure true)))
      (do
        match ← Internal.executeStep Internal.lexEofInner with
        | .ok flow => do Internal.reset; pure (.ok flow)
        | .error failure =>
          if core.recoveryState.isSome = true then do
            Internal.reset
            pure (.error
              (BSmtLib.Lexer.Error.LexerError.Internal.new failure.cause failure.span none))
          else do
            pure (.error (← Internal.failCall abandon₂ failure true))) := by
    refine SSim.bind (executeStep_sim _ _ (lexEofInner_sim hc)) ?_
    intro r₁ r₂ hr
    match r₁, r₂, hr with
    | .ok f₁, .ok f₂, hf => exact SSim.bind_eq reset_sim fun _ => SSim.pure hf
    | .error f₁, .error f₂, hf =>
      refine SSim.ite (fun _ => SSim.bind_eq reset_sim fun _ => SSim.pure ⟨hf.1, hf.2.1, rfl⟩)
        (fun _ => ?_)
      exact SSim.bind (failCall_sim abandon₁ abandon₂ habandon f₁ f₂ hf true) fun _ _ he =>
        SSim.pure he
  refine SSim.ite (fun _ => ?_) (fun _ => hrest)
  refine SSim.bind_eq (SSim.modifyThe _) fun _ => ?_
  refine SSim.bind_eq SSim.getThe fun core' => ?_
  refine SSim.bind_eq (SSim.liftM (hrecover _)) fun _ => hrest

theorem lexFitting_sim (hc : Consumers L) (abandon₁ : Span.Location → StateT H₁ m₁ Unit)
    (abandon₂ : Span.Location → StateT H₂ m₂ Unit)
    (habandon : ∀ l, L.rc.rel (· = ·) (abandon₁ l) (abandon₂ l)) (slice h) :
    SSim L (SliceRel L) (Internal.lexFitting abandon₁ slice h)
        (Internal.lexFitting abandon₂ slice h) := by
  unfold Internal.lexFitting
  refine SSim.bind (lexSliceInner_sim hc _) ?_
  intro r₁ r₂ hr
  match r₁, r₂, hr with
  | .ok h₁, .ok h₂, hh => exact SSim.pure hh
  | .error f₁, .error f₂, hf =>
    exact SSim.bind (failCall_sim abandon₁ abandon₂ habandon f₁ f₂ hf false) fun _ _ he =>
      SSim.pure he

theorem lexSliceFitting_sim (hc : Consumers L) (abandon₁ recover₁ : Span.Location → StateT H₁ m₁
    Unit)
    (abandon₂ recover₂ : Span.Location → StateT H₂ m₂ Unit)
    (habandon : ∀ l, L.rc.rel (· = ·) (abandon₁ l) (abandon₂ l))
    (hrecover : ∀ l, L.rc.rel (· = ·) (recover₁ l) (recover₂ l)) (slice h) :
    SSim L (SliceRel L) (Internal.lexSliceFitting abandon₁ recover₁ slice h)
      (Internal.lexSliceFitting abandon₂ recover₂ slice h) := by
  unfold Internal.lexSliceFitting
  refine SSim.bind_eq SSim.getThe fun core => ?_
  refine SSim.ite (fun _ => SSim.pure trivial)
    (fun _ => ?_)
  refine SSim.bind_eq SSim.getThe fun core' => ?_
  split
  · refine SSim.ite (fun _ => SSim.pure trivial) (fun _ => ?_)
    refine SSim.bind_eq (skipSlice_sim _ _) fun skipped => ?_
    split
    · lsim
    · exact SSim.pure trivial
  · exact lexFitting_sim hc abandon₁ abandon₂ habandon _ _

theorem lexChunks_sim (hc : Consumers L) (abandon₁ recover₁ : Span.Location → StateT H₁ m₁ Unit)
    (abandon₂ recover₂ : Span.Location → StateT H₂ m₂ Unit)
    (habandon : ∀ l, L.rc.rel (· = ·) (abandon₁ l) (abandon₂ l))
    (hrecover : ∀ l, L.rc.rel (· = ·) (recover₁ l) (recover₂ l)) (slice : ByteSlice)
    (position : Nat) (held₁ : Option (Span.Located R₁)) (held₂ : Option (Span.Located R₂))
    (hh : ORel (LocRel L.rr) held₁ held₂) :
    SSim L (SliceRel L) (Internal.lexChunks abandon₁ recover₁ slice position held₁)
      (Internal.lexChunks abandon₂ recover₂ slice position held₂) := by
  rw [Internal.lexChunks.eq_def, Internal.lexChunks.eq_def]
  refine SSim.dite (fun hlt => ?_) (fun _ => SSim.pure hh)
  refine SSim.bind (lexSliceFitting_sim hc abandon₁ recover₁ abandon₂ recover₂ habandon hrecover
    _ _) ?_
  intro r₁ r₂ hr
  match r₁, r₂, hr with
  | .ok c₁, .ok c₂, hch =>
    refine lexChunks_sim hc abandon₁ recover₁ abandon₂ recover₂ habandon hrecover slice _ _ _ ?_
    match c₁, c₂, hch with
    | some _, some _, hch => exact hch
    | none, none, _ => exact hh
  | .error e₁, .error e₂, he => exact SSim.pure he
termination_by slice.size - position
decreasing_by simp only [Internal.CHUNK_SIZE] at *; omega

theorem lexSliceStep_sim (hc : Consumers L) (abandon₁ recover₁ : Span.Location → StateT H₁ m₁ Unit)
    (abandon₂ recover₂ : Span.Location → StateT H₂ m₂ Unit)
    (habandon : ∀ l, L.rc.rel (· = ·) (abandon₁ l) (abandon₂ l))
    (hrecover : ∀ l, L.rc.rel (· = ·) (recover₁ l) (recover₂ l)) (slice : ByteSlice) :
    SSim L (SliceRel L) (Internal.lexSliceStep abandon₁ recover₁ slice)
      (Internal.lexSliceStep abandon₂ recover₂ slice) := by
  unfold Internal.lexSliceStep
  exact SSim.dite (fun _ => lexSliceFitting_sim hc abandon₁ recover₁ abandon₂ recover₂ habandon
      hrecover _ _)
    (fun _ => lexChunks_sim hc abandon₁ recover₁ abandon₂ recover₂ habandon hrecover _ _ none none
      trivial)

end

end BSmtLib.Facts.Proofs.Reader.Param.Calls
