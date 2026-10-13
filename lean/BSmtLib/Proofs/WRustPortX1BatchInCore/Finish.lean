import BSmtLib.Proofs.WRustPortX1BatchInCore.Held

/-!
# The tokens finished from the content buffer

A token in progress is finished from the content buffer and handed over alone, by the operation
`sinkStoredAt`, which leaves the batches in the states without tokens (the finishers `…_simE`).
At the end of the input the batches have no tokens before either, and every interruption is
thrown from states whose first batch has none (the finishers `…_simZ`).
-/

namespace BSmtLib.Proofs.WRustPortX1BatchInCore

open BSmtLib.Proofs.Simulation
open BSmtLib.Lexer (BATCH_CAPACITY Interrupted)
open BSmtLib.Proofs.Lexer.WRustPort (Ops)

section

variable {H : Type} {m : Type → Type} {R E : Type} [Monad m] [LawfulMonad m] [Consume H R E]
  [∀ batch, ConsumeFrom H (BatchCursor batch) m]
  {floor : Option Nat} {low : Nat} {strict : Bool} {o₁ o₂ : Ops H m R E}
  {LRel : Ops.Locals H m R E (self := o₁) → Ops.Locals H m R E (self := o₂) → Nat → Nat → Prop}

omit [Consume H R E] [∀ batch, ConsumeFrom H (BatchCursor batch) m] in
theorem sinkStored_simZ (ho : OpsSim o₁ o₂ LRel) (l ls : Nat) (ty : TokenCategory)
    (tokenEnd : Lexer.Slice.TokenEnd) (start : Location) (base : Nat)
    (h : Lexer.WRustPort.Started floor low start) :
    ESim (H := H) (m := m) (R := R) (E := E) (ErZ strict) (SRLb strict l ls)
      (fun _ _ => SREb strict l ls)
      (Lexer.WRustPort.sinkStored (ops := o₁) ty tokenEnd start base h)
      (Lexer.WRustPort.sinkStored (ops := o₂) ty tokenEnd start base h) := by
  unfold Lexer.WRustPort.sinkStored
  refine SimR.bind (locationFrom_sim l ls _ base tokenEnd.position) fun a b => ?_
  obtain ⟨a, ha⟩ := a
  obtain ⟨b, hb⟩ := b
  refine SimR.of_fact' (Er := ErZ strict) fun (e : a = b) => ?_
  subst e
  exact ho.sinkStoredAt l ls ty start a _ _

omit [Consume H R E] [∀ batch, ConsumeFrom H (BatchCursor batch) m] in
theorem sinkStored_sim (ho : OpsSim o₁ o₂ LRel) (l ls : Nat) (ty : TokenCategory)
    (tokenEnd : Lexer.Slice.TokenEnd) (start : Location) (base : Nat)
    (h : Lexer.WRustPort.Started floor low start) :
    LSim strict (H := H) (m := m) (R := R) (E := E) (SRLb strict l ls)
      (fun _ _ => SREb strict l ls)
      (Lexer.WRustPort.sinkStored (ops := o₁) ty tokenEnd start base h)
      (Lexer.WRustPort.sinkStored (ops := o₂) ty tokenEnd start base h) :=
  SimR.mono (fun _ _ h => h) (fun _ _ _ _ h => h) (fun _ _ h => h.1)
    (sinkStored_simZ ho l ls ty tokenEnd start base h)

/-- A finisher: the check of the token and the delimiter, and then `sinkStored_sim`. -/
local macro "finish_checked" : tactic => `(tactic| (
  dsimp only
  refine getCore_bind_P fun s t hst => ?_
  simp only [throw_bind]
  refine SimR.ite (by rw [hst.1.1.tokenContent]) (fun _ => error_sim _ _ _ _ _) fun _ => ?_
  cases ‹Option UInt8› with
  | some next =>
    exact SimR.seq (expectDelimiter_sim _ _ _ _) (sinkStored_sim ‹_› _ _ _ _ _ _ _)
  | none => exact sinkStored_sim ‹_› _ _ _ _ _ _ _))

omit [Consume H R E] [∀ batch, ConsumeFrom H (BatchCursor batch) m] in
theorem finishDecimal_sim (ho : OpsSim o₁ o₂ LRel) (l ls : Nat)
    (tokenEnd : Lexer.Slice.TokenEnd) (next : Option UInt8) (start : Location) (base : Nat)
    (h : Lexer.WRustPort.Started floor low start) :
    LSim strict (H := H) (m := m) (R := R) (E := E) (SRLb strict l ls) (fun _ _ => SREb strict l ls)
      (Lexer.WRustPort.finishDecimal (ops := o₁) tokenEnd next start base h)
      (Lexer.WRustPort.finishDecimal (ops := o₂) tokenEnd next start base h) := by
  unfold Lexer.WRustPort.finishDecimal
  finish_checked

omit [Consume H R E] [∀ batch, ConsumeFrom H (BatchCursor batch) m] in
theorem finishDigitRun_sim (ho : OpsSim o₁ o₂ LRel) (l ls : Nat) (run : Lexer.DigitRun)
    (tokenEnd : Lexer.Slice.TokenEnd) (next : Option UInt8) (start : Location) (base : Nat)
    (h : Lexer.WRustPort.Started floor low start) :
    LSim strict (H := H) (m := m) (R := R) (E := E) (SRLb strict l ls) (fun _ _ => SREb strict l ls)
      (Lexer.WRustPort.finishDigitRun (ops := o₁) run tokenEnd next start base h)
      (Lexer.WRustPort.finishDigitRun (ops := o₂) run tokenEnd next start base h) := by
  unfold Lexer.WRustPort.finishDigitRun
  finish_checked

omit [Consume H R E] [∀ batch, ConsumeFrom H (BatchCursor batch) m] in
theorem finishKeyword_sim (ho : OpsSim o₁ o₂ LRel) (l ls : Nat)
    (tokenEnd : Lexer.Slice.TokenEnd) (next : Option UInt8) (start : Location) (base : Nat)
    (h : Lexer.WRustPort.Started floor low start) :
    LSim strict (H := H) (m := m) (R := R) (E := E) (SRLb strict l ls) (fun _ _ => SREb strict l ls)
      (Lexer.WRustPort.finishKeyword (ops := o₁) tokenEnd next start base h)
      (Lexer.WRustPort.finishKeyword (ops := o₂) tokenEnd next start base h) := by
  unfold Lexer.WRustPort.finishKeyword
  finish_checked

/-! The finishers at the end of the input, where the batches have no tokens: an interruption is
thrown from states whose first batch has none either. -/

/-- A finisher at the end of the input: the check of the token, and then `sinkStored_simZ`. -/
local macro "finish_eof" : tactic => `(tactic| (
  dsimp only
  refine getCore_bind_P fun s t hst => ?_
  simp only [throw_bind]
  refine SimR.ite (by rw [hst.1.1.1.tokenContent]) (fun _ => error_simZ _ _ _ _ _)
    fun _ => SimR.pre (fun _ _ h => h.1) (sinkStored_simZ ‹_› _ _ _ _ _ _ _)))

omit [Consume H R E] [∀ batch, ConsumeFrom H (BatchCursor batch) m] in
theorem finishDecimal_simZ (ho : OpsSim o₁ o₂ LRel) (l ls : Nat)
    (tokenEnd : Lexer.Slice.TokenEnd) (start : Location) (base : Nat)
    (h : Lexer.WRustPort.Started floor low start) :
    ESim (H := H) (m := m) (R := R) (E := E) (ErZ strict) (SRLbZ strict l ls)
      (fun _ _ => SREb strict l ls)
      (Lexer.WRustPort.finishDecimal (ops := o₁) tokenEnd none start base h)
      (Lexer.WRustPort.finishDecimal (ops := o₂) tokenEnd none start base h) := by
  unfold Lexer.WRustPort.finishDecimal
  finish_eof

omit [Consume H R E] [∀ batch, ConsumeFrom H (BatchCursor batch) m] in
theorem finishDigitRun_simZ (ho : OpsSim o₁ o₂ LRel) (l ls : Nat) (run : Lexer.DigitRun)
    (tokenEnd : Lexer.Slice.TokenEnd) (start : Location) (base : Nat)
    (h : Lexer.WRustPort.Started floor low start) :
    ESim (H := H) (m := m) (R := R) (E := E) (ErZ strict) (SRLbZ strict l ls)
      (fun _ _ => SREb strict l ls)
      (Lexer.WRustPort.finishDigitRun (ops := o₁) run tokenEnd none start base h)
      (Lexer.WRustPort.finishDigitRun (ops := o₂) run tokenEnd none start base h) := by
  unfold Lexer.WRustPort.finishDigitRun
  finish_eof

omit [Consume H R E] [∀ batch, ConsumeFrom H (BatchCursor batch) m] in
theorem finishKeyword_simZ (ho : OpsSim o₁ o₂ LRel) (l ls : Nat)
    (tokenEnd : Lexer.Slice.TokenEnd) (start : Location) (base : Nat)
    (h : Lexer.WRustPort.Started floor low start) :
    ESim (H := H) (m := m) (R := R) (E := E) (ErZ strict) (SRLbZ strict l ls)
      (fun _ _ => SREb strict l ls)
      (Lexer.WRustPort.finishKeyword (ops := o₁) tokenEnd none start base h)
      (Lexer.WRustPort.finishKeyword (ops := o₂) tokenEnd none start base h) := by
  unfold Lexer.WRustPort.finishKeyword
  finish_eof

end

end BSmtLib.Proofs.WRustPortX1BatchInCore
