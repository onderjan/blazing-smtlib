import BSmtLib.Proofs.WRustPortX1BatchInCore.Slice

/-!
# The end of the input

At the end of the input the two lexers finish the token in progress and hand over the end of
file token (`lexEofInner`). The Rust port makes a fresh batch, the other keeps its own, which
has no tokens, as every call of the lexers returns with its batch handed over; the simulation is
not strict (`ErZ false`). Every interruption is thrown from states whose batches have no tokens,
so that the lexer states the call returns with have none either.
-/

namespace BSmtLib.Proofs.WRustPortX1BatchInCore

open BSmtLib.Proofs.Simulation (M runM)
open BSmtLib.Lexer (BATCH_CAPACITY Interrupted Failure Stop)

section

variable {H : Type} {m : Type → Type} {R E : Type} [Monad m] [LawfulMonad m] [Consume H m R E]
  {floor : Option Nat} {low : Nat}

omit [Consume H m R E] in
/-- From states that correspond, whose batches have no tokens, with any line and line start of
the Rust port. -/
theorem ESim.of_sr0 {α β : Type} {Er : WS floor low → XS floor low → Prop}
    {Q : α → β → WS floor low → XS floor low → Prop}
    {f : Lexer.WRustPort.LexM H m R E floor low α}
    {g : Lexer.X1BatchInCore.LexM H m R E floor low β}
    (h : ∀ l ls, ESim Er (SRLbZ false l ls) Q f g) : ESim Er SR0 Q f g :=
  SimR.intro fun s t hst => SimR.pre (fun _ _ h' => by
    obtain ⟨⟨h', hz⟩, rfl, rfl⟩ := h'
    exact ⟨⟨sr_srl h', nofun⟩, hz⟩) (h s.val.line s.val.lineStart)

omit [Consume H m R E] in
/-- The start of the end of file token, which clears the content buffer. -/
theorem startToken_simE {Er : WS floor low → XS floor low → Prop} (l ls : Nat) (offset : Nat)
    (base position : Nat) (hframe : Lexer.WRustPort.Frame floor low offset)
    (hframe' : Lexer.X1BatchInCore.Frame floor low offset) :
    ESim (H := H) (m := m) (R := R) (E := E) Er (SRE l ls)
      (fun a b s t => a.val = b.val ∧ SRE l ls s t ∧ s.val.tokenContent = ByteArray.empty)
      (Lexer.WRustPort.startToken offset base position hframe)
      (Lexer.X1BatchInCore.startToken offset base position hframe') := by
  unfold Lexer.WRustPort.startToken Lexer.X1BatchInCore.startToken
  refine getCore_bind_P fun s₀ t₀ h₀ => ?_
  obtain ⟨⟨hst, hl, hls⟩, hz⟩ := h₀
  refine SimR.seq (P' := SRE l ls) (modifyCore_sim _ _ fun s t h => ?_) ?_
  · obtain ⟨⟨h, hl', hls'⟩, hz'⟩ := h
    exact ⟨⟨{ h with tokenStart := by simp only [hst.line, hst.lineStart], state := rfl }, hl',
      hls'⟩, hz'⟩
  refine SimR.seq (P' := fun s t => SRE l ls s t ∧ s.val.tokenContent = ByteArray.empty)
    (modifyCore_sim _ _ fun s t h => ?_) ?_
  · obtain ⟨⟨h, hl', hls'⟩, hz'⟩ := h
    exact ⟨⟨⟨{ h with tokenContent := rfl }, hl', hls'⟩, hz'⟩, rfl⟩
  exact SimR.pure fun s t h => ⟨by simp only [hst.line, hst.lineStart], h⟩

/-- A branch of the token in progress at the end of the input, from `lemma` for any line and
line start. -/
local macro "eof_branch " lemma:term:max : tactic => `(tactic|
  exact ESim.of_sr0 fun l ls => SimR.post (fun _ _ _ _ h => ⟨h.1.1.1, h.1.2⟩) ($lemma l ls))

/-- What the two calls of the lexers give back correspond. -/
def CallRel (a : Except (Failure E) (ControlFlow R) × WCore)
    (b : Except (Failure E) (ControlFlow R) × XCore) : Prop :=
  a.1 = b.1 ∧ CoreRel a.2 b.2 ∧ a.2.batch.len = 0

theorem lexEofInner_sim (hcons : ConsumesAlike H m R E) (w : WCore) (x : XCore)
    (hwx : CoreRel w x) (hlen : w.batch.len = 0) :
    Couple CallRel (Lexer.WRustPort.lexEofInner (H := H) (m := m) (R := R) (E := E) w)
      (Lexer.X1BatchInCore.lexEofInner x) := by
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
  unfold Lexer.WRustPort.lexEofInner Lexer.X1BatchInCore.lexEofInner
  dsimp only
  refine Couple.bind (SimR.couple (Er := ErZ false) (P := SR0)
    (Q := fun _ _ s t => SR s t ∧ s.val.batch.len = 0) ?_ ?_) fun a b hab => ?_
  · refine SimR.seq (SimR.tryCatch (Er := ErZ false) (Q := fun _ _ => SR0) ?_ fun e => ?_) ?_
    · cases state <;> dsimp only
      case comment =>
        simp only [Lexer.WRustPort.consumesWhitespaceAndComments,
          Lexer.X1BatchInCore.consumesWhitespaceAndComments, pure_bind]
        generalize Consume.consumesWhitespaceAndComments (H := H) = cw
        cases cw <;> simp only [Bool.false_eq_true, ↓reduceIte]
        · exact SimR.pure fun _ _ h => h
        · eof_branch (fun l ls => sinkStored_simZ hcons l ls _ _ _ _ _ _ _)
      case normal => exact SimR.pure fun _ _ h => h
      case fraction => eof_branch (fun l ls => finishDecimal_simZ hcons l ls _ _ _ _ _)
      case keyword => eof_branch (fun l ls => finishKeyword_simZ hcons l ls _ _ _ _ _)
      case hexadecimal | binary =>
        eof_branch (fun l ls => finishDigitRun_simZ hcons l ls _ _ _ _ _ _ _)
      case baseSelection | stringLiteral | stringLiteralBackslashEscape | quotedSymbol =>
        exact ESim.of_sr0 fun l ls => error_simZ l ls _ _ _
      case numeralOrDecimal =>
        unfold Lexer.WRustPort.finishNumeral Lexer.X1BatchInCore.finishNumeral
        eof_branch (fun l ls => sinkStored_simZ hcons l ls _ _ _ _ _ _ _)
      case stringLiteralDoubleQuote =>
        unfold Lexer.WRustPort.finishStringLiteral Lexer.X1BatchInCore.finishStringLiteral
        eof_branch (fun l ls => sinkStored_simZ hcons l ls _ _ _ _ _ _ _)
      case simpleSymbol =>
        unfold Lexer.WRustPort.finishSimpleSymbol Lexer.X1BatchInCore.finishSimpleSymbol
        eof_branch (fun l ls => sinkStored_simZ hcons l ls _ _ _ _ _ _ _)
      case whitespace | quotedSymbolClosed =>
        eof_branch (fun l ls => sinkStored_simZ hcons l ls _ _ _ _ _ _ _)
    · split_both
      · exact SimR.pure fun _ _ h => ⟨h.1.1, h.2⟩
      · rename_i _ h1 _ h2
        exact (h2 h1).elim
      · rename_i _ h1 _ h2
        exact (h1 h2).elim
      · exact SimR.throw rfl fun _ _ h => h
    · refine SimR.intro fun s₀ t₀ hst => SimR.pre (fun _ _ h => ?_)
        (P := SRE s₀.val.line s₀.val.lineStart) (SimR.bind (startToken_simE s₀.val.line
          s₀.val.lineStart _ _ _ _ _) fun a b => ?_)
      · obtain ⟨-, rfl, rfl⟩ := h
        exact ⟨sr_srl hst.1, hst.2⟩
      · obtain ⟨a, ha⟩ := a
        obtain ⟨b, hb⟩ := b
        refine SimR.of_fact' (Er := ErZ false) (P := fun s t =>
          SRE s₀.val.line s₀.val.lineStart s t ∧ s.val.tokenContent = ByteArray.empty)
          fun (e : a = b) => ?_
        subst e
        exact SimR.post (fun _ _ _ _ h => ⟨h.1.1, h.2⟩)
          (handOverEof_simZ hcons s₀.val.line s₀.val.lineStart a)
  · refine ⟨{ hwx with base := rfl, batch := ?_, capacity := zero_lt_capacity }, rfl⟩
    exact agree_of_len_zero rfl (hwx.batch.len ▸ hlen)
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
