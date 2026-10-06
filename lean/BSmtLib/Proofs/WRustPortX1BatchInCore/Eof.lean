import BSmtLib.Proofs.WRustPortX1BatchInCore.Slice

/-!
# The end of the input

At the end of the input the two runs finish the token in progress and hand over the end of file
token (`lexEofInner`). The batches they start with are given by the operations
(`Ops.eofBatch`), and have no tokens, as every call returns with its batch handed over; the
simulation is not strict (`ErZ false`). Every interruption is thrown from states whose batches
have no tokens, so that the lexer states the call returns with have none either.
-/

namespace BSmtLib.Proofs.WRustPortX1BatchInCore

open BSmtLib.Proofs.Simulation
open BSmtLib.Lexer (BATCH_CAPACITY Interrupted Failure Stop)
open BSmtLib.Proofs.Lexer.WRustPort (Ops)

section

variable {H : Type} {m : Type → Type} {R E : Type} [Monad m] [LawfulMonad m] [Consume H m R E]
  {o₁ o₂ : Ops H m R E}
  {LRel : Ops.Locals H m R E (self := o₁) → Ops.Locals H m R E (self := o₂) → Nat → Nat → Prop}

omit [Consume H m R E] in
/-- From states that correspond, whose batches have no tokens, with any line and line start. -/
theorem SimR.of_sr0 {floor : Option Nat} {low : Nat} {α β : Type}
    {Er : St floor low → St floor low → Prop} {Q : α → β → St floor low → St floor low → Prop}
    {f : Lexer.WRustPort.LexM H m R E floor low α} {g : Lexer.WRustPort.LexM H m R E floor low β}
    (h : ∀ l ls, ESim Er (SRLbZ false l ls) Q f g) : ESim Er SR0 Q f g :=
  SimR.intro fun s _ _ => SimR.pre (fun _ _ h' => by
    obtain ⟨⟨h', hz⟩, rfl, rfl⟩ := h'
    exact ⟨⟨sr_srl h', nofun⟩, hz⟩) (h s.val.line s.val.lineStart)

set_option hygiene false in
/-- A branch of the token in progress at the end of the input, from `lemma` for any line and
line start. -/
local macro "eof_branch " lemma:term:max : tactic => `(tactic|
  exact SimR.of_sr0 fun l ls => SimR.post (fun _ _ _ _ h => ⟨h.1.1.1, h.1.2⟩) ($lemma l ls))

set_option hygiene false in
/-- A token in progress at the end of the input that is handed over as it is. -/
local macro "eof_stored" : tactic => `(tactic|
  eof_branch (fun l ls => SimR.pre (fun _ _ h => h.1) (sinkStored_simZ ho l ls _ _ _ _ _)))

/-- What the two calls give back correspond: the same result, and states that correspond with
batches without tokens. -/
def CallRel (a b : Except (Failure E) (ControlFlow R) × Core) : Prop :=
  a.1 = b.1 ∧ CoreRel a.2 b.2 ∧ a.2.batch.len = 0

theorem lexEofInner_sim (ho : OpsSim o₁ o₂ LRel) (w x : Core) (hwx : CoreRel w x)
    (hlen : w.batch.len = 0) :
    Couple CallRel (Lexer.WRustPort.lexEofInner (ops := o₁) (H := H) (m := m) (R := R) (E := E) w)
      (Lexer.WRustPort.lexEofInner (ops := o₂) x) := by
  obtain ⟨version, initialVersion, state, discard, recovers, consumedDepth, lexedDepth,
    recoveryState, tokenStart, tokenContent, offset, base, line, lineStart, batch, tokenStarted,
    batchEnded⟩ := w
  obtain ⟨version', initialVersion', state', discard', recovers', consumedDepth', lexedDepth',
    recoveryState', tokenStart', tokenContent', offset', base', line', lineStart', batch',
    tokenStarted', batchEnded'⟩ := x
  have hoffset : offset = offset' := hwx.offset
  have hstate : state = state' := hwx.state
  have htoken : tokenStart = tokenStart' := hwx.tokenStart
  subst hoffset hstate htoken
  have heb := ho.eofBatch _ _ hwx hlen
  unfold Lexer.WRustPort.lexEofInner
  generalize Ops.eofBatch H m R E (self := o₁) _ = eb₁ at heb
  generalize Ops.eofBatch H m R E (self := o₂) _ = eb₂ at heb
  obtain ⟨b₁, e₁⟩ := eb₁
  obtain ⟨b₂, e₂⟩ := eb₂
  dsimp only at heb ⊢
  refine Couple.bind (SimR.couple (Er := ErZ false) (P := SR0)
    (Q := fun _ _ s t => SR s t ∧ s.val.batch.len = 0) ?_ ?_) fun a b hab => ?_
  · refine SimR.seq (SimR.tryCatch (Er := ErZ false) (Q := fun _ _ => SR0) ?_ fun e => ?_) ?_
    · cases state <;> dsimp only
      case comment =>
        simp only [Lexer.WRustPort.consumesWhitespaceAndComments, pure_bind]
        generalize Consume.consumesWhitespaceAndComments (H := H) = cw
        cases cw <;> simp only [Bool.false_eq_true, ↓reduceIte]
        · exact SimR.pure fun _ _ h => h
        · eof_stored
      case normal => exact SimR.pure fun _ _ h => h
      case fraction => eof_branch (fun l ls => finishDecimal_simZ ho l ls _ _ _ _)
      case keyword => eof_branch (fun l ls => finishKeyword_simZ ho l ls _ _ _ _)
      case hexadecimal | binary => eof_branch (fun l ls => finishDigitRun_simZ ho l ls _ _ _ _ _)
      case baseSelection | stringLiteral | stringLiteralBackslashEscape | quotedSymbol =>
        exact SimR.of_sr0 fun l ls => error_simZ l ls _ _ _
      case numeralOrDecimal =>
        unfold Lexer.WRustPort.finishNumeral
        eof_stored
      case stringLiteralDoubleQuote =>
        unfold Lexer.WRustPort.finishStringLiteral
        eof_stored
      case simpleSymbol =>
        unfold Lexer.WRustPort.finishSimpleSymbol
        eof_stored
      case whitespace | quotedSymbolClosed => eof_stored
    · split
      · exact SimR.pure fun _ _ h => ⟨h.1.1, h.2⟩
      · exact SimR.throw rfl fun _ _ h => h
    · refine SimR.intro fun s₀ t₀ hst => SimR.pre (fun _ _ h => ?_)
        (P := SRE s₀.val.line s₀.val.lineStart) (SimR.bind (startToken_sim s₀.val.line
          s₀.val.lineStart NoTokens _ _ _ _ _) fun a b => ?_)
      · obtain ⟨-, rfl, rfl⟩ := h
        exact ⟨sr_srl hst.1, hst.2⟩
      · obtain ⟨a, ha⟩ := a
        obtain ⟨b, hb⟩ := b
        refine SimR.of_fact' (Er := ErZ false) (P := fun s t =>
          SRE s₀.val.line s₀.val.lineStart s t ∧ s.val.tokenContent.len = 0)
          fun (e : a = b) => ?_
        subst e
        exact SimR.post (fun _ _ _ _ h => ⟨h.1.1, h.2⟩)
          (ho.sinkEof s₀.val.line s₀.val.lineStart a)
  · refine ⟨{ hwx with base := rfl, batch := ?_, capacity := ?_ }, heb.1⟩
    · exact agree_of_len_zero heb.1 heb.2
    · dsimp only
      rw [heb.1]
      exact zero_lt_capacity
  · obtain ⟨r, c⟩ := a
    obtain ⟨r', c'⟩ := b
    cases r <;> cases r' <;> simp only [GoodR'] at hab
    · obtain ⟨rfl, ⟨hcr, -⟩, hz⟩ := hab
      rename_i i
      obtain ⟨result, location, stopAfter⟩ := i
      dsimp only
      cases result with
      | error cause => exact Couple.pure ⟨rfl, hcr, hz⟩
      | ok stop =>
        cases stop with
        | relex => exact Couple.pure ⟨rfl, hcr, hz⟩
        | finished r => exact Couple.pure ⟨rfl, hcr, hz⟩
    · exact Couple.pure ⟨rfl, hab.1, hab.2⟩

end

end BSmtLib.Proofs.WRustPortX1BatchInCore
