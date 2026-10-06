import BSmtLib.Proofs.WRustPortX1BatchInCore.Flush

/-!
# The tokens finished from the content buffer

A token in progress is finished from the content buffer and handed over alone: the two lexers
check it alike and hand it over as `handOverStored_sim` shows, which leaves the batches in the
states without tokens (the finishers `…_simE`). At the end of the input the batches have no
tokens before either, and every interruption is thrown from states whose batches have none
(the finishers `…_simZ`).
-/

namespace BSmtLib.Proofs.WRustPortX1BatchInCore

open BSmtLib.Proofs.Simulation (M runM)
open BSmtLib.Lexer (BATCH_CAPACITY Interrupted)

section

variable {H : Type} {m : Type → Type} {R E : Type} [Monad m] [LawfulMonad m] [Consume H m R E]
  {floor : Option Nat} {low : Nat} {strict : Bool}

theorem sinkStored_sim (hcons : ConsumesAlike H m R E) (l ls : Nat) (ty : TokenCategory)
    (hty : ty ≠ .endOfFile) (tokenEnd : Lexer.Slice.TokenEnd) (start : Location) (base : Nat)
    (h : Lexer.WRustPort.Started floor low start)
    (h' : Lexer.X1BatchInCore.Started floor low start) :
    LSim strict (H := H) (m := m) (R := R) (E := E) (SRLb strict l ls)
      (fun _ _ => SREb strict l ls)
      (Lexer.WRustPort.sinkStored ty hty tokenEnd start base h)
      (Lexer.X1BatchInCore.sinkStored ty hty tokenEnd start base h') := by
  unfold Lexer.WRustPort.sinkStored Lexer.X1BatchInCore.sinkStored
  refine SimR.bind (locationFrom_sim l ls _ base tokenEnd.position) fun a b => ?_
  obtain ⟨a, ha⟩ := a
  obtain ⟨b, hb⟩ := b
  refine SimR.of_fact' (Er := ErS strict) fun (e : a = b) => ?_
  subst e
  exact handOverStored_sim hcons l ls ty hty start a _ _ _

/-- A finished token, in the state where the step goes on: corresponding, with the same arrays
of contents of the batches where the simulation is strict. -/
abbrev FinQ (strict : Bool) (l ls : Nat) : Unit → Unit → WS floor low → XS floor low → Prop :=
  fun _ _ => SRLb strict l ls

/-- `sinkStored_sim`, with the batches in the states left as any. -/
theorem sinkStored_sim' (hcons : ConsumesAlike H m R E) (l ls : Nat) (ty : TokenCategory)
    (hty : ty ≠ .endOfFile) (tokenEnd : Lexer.Slice.TokenEnd) (start : Location) (base : Nat)
    (h : Lexer.WRustPort.Started floor low start)
    (h' : Lexer.X1BatchInCore.Started floor low start) :
    LSim strict (H := H) (m := m) (R := R) (E := E) (SRLb strict l ls) (FinQ strict l ls)
      (Lexer.WRustPort.sinkStored ty hty tokenEnd start base h)
      (Lexer.X1BatchInCore.sinkStored ty hty tokenEnd start base h') :=
  SimR.post (fun _ _ _ _ h => ⟨h.1.1, h.2⟩)
    (sinkStored_sim hcons l ls ty hty tokenEnd start base h h')

theorem finishDecimal_simE (hcons : ConsumesAlike H m R E) (l ls : Nat)
    (tokenEnd : Lexer.Slice.TokenEnd) (next : Option UInt8) (start : Location) (base : Nat)
    (h : Lexer.WRustPort.Started floor low start)
    (h' : Lexer.X1BatchInCore.Started floor low start) :
    LSim strict (H := H) (m := m) (R := R) (E := E) (SRLb strict l ls) (fun _ _ => SREb strict l ls)
      (Lexer.WRustPort.finishDecimal tokenEnd next start base h)
      (Lexer.X1BatchInCore.finishDecimal tokenEnd next start base h') := by
  unfold Lexer.WRustPort.finishDecimal Lexer.X1BatchInCore.finishDecimal
  dsimp only
  refine getCore_bind_P fun s t hst => ?_
  simp only [throw_bind, fail_bind]
  refine SimR.ite (by rw [hst.1.1.tokenContent]; exact Iff.rfl) (fun _ => error_sim l ls _ _ _)
    fun _ => ?_
  cases next with
  | some next =>
    exact SimR.seq (expectDelimiter_sim l ls _ _) (sinkStored_sim hcons l ls _ _ _ _ _ _ _)
  | none => exact sinkStored_sim hcons l ls _ _ _ _ _ _ _

theorem finishNumeral_simE (hcons : ConsumesAlike H m R E) (l ls : Nat)
    (tokenEnd : Lexer.Slice.TokenEnd) (start : Location) (base : Nat)
    (h : Lexer.WRustPort.Started floor low start)
    (h' : Lexer.X1BatchInCore.Started floor low start) :
    LSim strict (H := H) (m := m) (R := R) (E := E) (SRLb strict l ls) (fun _ _ => SREb strict l ls)
      (Lexer.WRustPort.finishNumeral tokenEnd start base h)
      (Lexer.X1BatchInCore.finishNumeral tokenEnd start base h') :=
  sinkStored_sim hcons l ls _ _ _ _ _ _ _

theorem finishSimpleSymbol_simE (hcons : ConsumesAlike H m R E) (l ls : Nat)
    (tokenEnd : Lexer.Slice.TokenEnd) (start : Location) (base : Nat)
    (h : Lexer.WRustPort.Started floor low start)
    (h' : Lexer.X1BatchInCore.Started floor low start) :
    LSim strict (H := H) (m := m) (R := R) (E := E) (SRLb strict l ls) (fun _ _ => SREb strict l ls)
      (Lexer.WRustPort.finishSimpleSymbol tokenEnd start base h)
      (Lexer.X1BatchInCore.finishSimpleSymbol tokenEnd start base h') :=
  sinkStored_sim hcons l ls _ _ _ _ _ _ _

theorem finishStringLiteral_simE (hcons : ConsumesAlike H m R E) (l ls : Nat)
    (tokenEnd : Lexer.Slice.TokenEnd) (start : Location) (base : Nat)
    (h : Lexer.WRustPort.Started floor low start)
    (h' : Lexer.X1BatchInCore.Started floor low start) :
    LSim strict (H := H) (m := m) (R := R) (E := E) (SRLb strict l ls) (fun _ _ => SREb strict l ls)
      (Lexer.WRustPort.finishStringLiteral tokenEnd start base h)
      (Lexer.X1BatchInCore.finishStringLiteral tokenEnd start base h') :=
  sinkStored_sim hcons l ls _ _ _ _ _ _ _

theorem finishWhitespace_simE (hcons : ConsumesAlike H m R E) (l ls : Nat)
    (tokenEnd : Lexer.Slice.TokenEnd) (start : Location) (base : Nat)
    (h : Lexer.WRustPort.Started floor low start)
    (h' : Lexer.X1BatchInCore.Started floor low start) :
    LSim strict (H := H) (m := m) (R := R) (E := E) (SRLb strict l ls) (fun _ _ => SREb strict l ls)
      (Lexer.WRustPort.finishWhitespace tokenEnd start base h)
      (Lexer.X1BatchInCore.finishWhitespace tokenEnd start base h') :=
  sinkStored_sim hcons l ls _ _ _ _ _ _ _

theorem finishDigitRun_simE (hcons : ConsumesAlike H m R E) (l ls : Nat) (run : Lexer.DigitRun)
    (hrun : run = Lexer.HEXADECIMAL_RUN ∨ run = Lexer.BINARY_RUN)
    (tokenEnd : Lexer.Slice.TokenEnd) (next : Option UInt8) (start : Location) (base : Nat)
    (h : Lexer.WRustPort.Started floor low start)
    (h' : Lexer.X1BatchInCore.Started floor low start) :
    LSim strict (H := H) (m := m) (R := R) (E := E) (SRLb strict l ls) (fun _ _ => SREb strict l ls)
      (Lexer.WRustPort.finishDigitRun run hrun tokenEnd next start base h)
      (Lexer.X1BatchInCore.finishDigitRun run hrun tokenEnd next start base h') := by
  unfold Lexer.WRustPort.finishDigitRun Lexer.X1BatchInCore.finishDigitRun
  dsimp only
  refine getCore_bind_P fun s t hst => ?_
  simp only [throw_bind, fail_bind]
  refine SimR.ite (by rw [hst.1.1.tokenContent]; exact Iff.rfl) (fun _ => error_sim l ls _ _ _)
    fun _ => ?_
  cases next with
  | some next =>
    exact SimR.seq (expectDelimiter_sim l ls _ _) (sinkStored_sim hcons l ls _ _ _ _ _ _ _)
  | none => exact sinkStored_sim hcons l ls _ _ _ _ _ _ _

theorem finishKeyword_simE (hcons : ConsumesAlike H m R E) (l ls : Nat)
    (tokenEnd : Lexer.Slice.TokenEnd) (next : Option UInt8) (start : Location) (base : Nat)
    (h : Lexer.WRustPort.Started floor low start)
    (h' : Lexer.X1BatchInCore.Started floor low start) :
    LSim strict (H := H) (m := m) (R := R) (E := E) (SRLb strict l ls) (fun _ _ => SREb strict l ls)
      (Lexer.WRustPort.finishKeyword tokenEnd next start base h)
      (Lexer.X1BatchInCore.finishKeyword tokenEnd next start base h') := by
  unfold Lexer.WRustPort.finishKeyword Lexer.X1BatchInCore.finishKeyword
  dsimp only
  refine getCore_bind_P fun s t hst => ?_
  simp only [throw_bind, fail_bind]
  refine SimR.ite (by rw [hst.1.1.tokenContent]; exact Iff.rfl) (fun _ => error_sim l ls _ _ _)
    fun _ => ?_
  cases next with
  | some next =>
    exact SimR.seq (expectDelimiter_sim l ls _ _) (sinkStored_sim hcons l ls _ _ _ _ _ _ _)
  | none => exact sinkStored_sim hcons l ls _ _ _ _ _ _ _


/-! The finishers with the batches in the states left as any. -/

/-- Forgets that the batches have no tokens. -/
theorem finQ_of_sreb {l ls : Nat} {a b : Unit} {s : WS floor low} {t : XS floor low}
    (h : SREb strict l ls s t) : FinQ strict l ls a b s t :=
  ⟨h.1.1, h.2⟩

theorem finishDecimal_sim (hcons : ConsumesAlike H m R E) (l ls : Nat)
    (tokenEnd : Lexer.Slice.TokenEnd) (next : Option UInt8) (start : Location) (base : Nat)
    (h : Lexer.WRustPort.Started floor low start)
    (h' : Lexer.X1BatchInCore.Started floor low start) :
    LSim strict (H := H) (m := m) (R := R) (E := E) (SRLb strict l ls) (FinQ strict l ls)
      (Lexer.WRustPort.finishDecimal tokenEnd next start base h)
      (Lexer.X1BatchInCore.finishDecimal tokenEnd next start base h') :=
  SimR.post (fun _ _ _ _ h => finQ_of_sreb h) (finishDecimal_simE hcons l ls _ _ _ _ _ _)

theorem finishNumeral_sim (hcons : ConsumesAlike H m R E) (l ls : Nat)
    (tokenEnd : Lexer.Slice.TokenEnd) (start : Location) (base : Nat)
    (h : Lexer.WRustPort.Started floor low start)
    (h' : Lexer.X1BatchInCore.Started floor low start) :
    LSim strict (H := H) (m := m) (R := R) (E := E) (SRLb strict l ls) (FinQ strict l ls)
      (Lexer.WRustPort.finishNumeral tokenEnd start base h)
      (Lexer.X1BatchInCore.finishNumeral tokenEnd start base h') :=
  SimR.post (fun _ _ _ _ h => finQ_of_sreb h) (finishNumeral_simE hcons l ls _ _ _ _ _)

theorem finishSimpleSymbol_sim (hcons : ConsumesAlike H m R E) (l ls : Nat)
    (tokenEnd : Lexer.Slice.TokenEnd) (start : Location) (base : Nat)
    (h : Lexer.WRustPort.Started floor low start)
    (h' : Lexer.X1BatchInCore.Started floor low start) :
    LSim strict (H := H) (m := m) (R := R) (E := E) (SRLb strict l ls) (FinQ strict l ls)
      (Lexer.WRustPort.finishSimpleSymbol tokenEnd start base h)
      (Lexer.X1BatchInCore.finishSimpleSymbol tokenEnd start base h') :=
  SimR.post (fun _ _ _ _ h => finQ_of_sreb h) (finishSimpleSymbol_simE hcons l ls _ _ _ _ _)

theorem finishStringLiteral_sim (hcons : ConsumesAlike H m R E) (l ls : Nat)
    (tokenEnd : Lexer.Slice.TokenEnd) (start : Location) (base : Nat)
    (h : Lexer.WRustPort.Started floor low start)
    (h' : Lexer.X1BatchInCore.Started floor low start) :
    LSim strict (H := H) (m := m) (R := R) (E := E) (SRLb strict l ls) (FinQ strict l ls)
      (Lexer.WRustPort.finishStringLiteral tokenEnd start base h)
      (Lexer.X1BatchInCore.finishStringLiteral tokenEnd start base h') :=
  SimR.post (fun _ _ _ _ h => finQ_of_sreb h) (finishStringLiteral_simE hcons l ls _ _ _ _ _)

theorem finishWhitespace_sim (hcons : ConsumesAlike H m R E) (l ls : Nat)
    (tokenEnd : Lexer.Slice.TokenEnd) (start : Location) (base : Nat)
    (h : Lexer.WRustPort.Started floor low start)
    (h' : Lexer.X1BatchInCore.Started floor low start) :
    LSim strict (H := H) (m := m) (R := R) (E := E) (SRLb strict l ls) (FinQ strict l ls)
      (Lexer.WRustPort.finishWhitespace tokenEnd start base h)
      (Lexer.X1BatchInCore.finishWhitespace tokenEnd start base h') :=
  SimR.post (fun _ _ _ _ h => finQ_of_sreb h) (finishWhitespace_simE hcons l ls _ _ _ _ _)

theorem finishDigitRun_sim (hcons : ConsumesAlike H m R E) (l ls : Nat) (run : Lexer.DigitRun)
    (hrun : run = Lexer.HEXADECIMAL_RUN ∨ run = Lexer.BINARY_RUN)
    (tokenEnd : Lexer.Slice.TokenEnd) (next : Option UInt8) (start : Location) (base : Nat)
    (h : Lexer.WRustPort.Started floor low start)
    (h' : Lexer.X1BatchInCore.Started floor low start) :
    LSim strict (H := H) (m := m) (R := R) (E := E) (SRLb strict l ls) (FinQ strict l ls)
      (Lexer.WRustPort.finishDigitRun run hrun tokenEnd next start base h)
      (Lexer.X1BatchInCore.finishDigitRun run hrun tokenEnd next start base h') :=
  SimR.post (fun _ _ _ _ h => finQ_of_sreb h) (finishDigitRun_simE hcons l ls _ _ _ _ _ _ _ _)

theorem finishKeyword_sim (hcons : ConsumesAlike H m R E) (l ls : Nat)
    (tokenEnd : Lexer.Slice.TokenEnd) (next : Option UInt8) (start : Location) (base : Nat)
    (h : Lexer.WRustPort.Started floor low start)
    (h' : Lexer.X1BatchInCore.Started floor low start) :
    LSim strict (H := H) (m := m) (R := R) (E := E) (SRLb strict l ls) (FinQ strict l ls)
      (Lexer.WRustPort.finishKeyword tokenEnd next start base h)
      (Lexer.X1BatchInCore.finishKeyword tokenEnd next start base h') :=
  SimR.post (fun _ _ _ _ h => finQ_of_sreb h) (finishKeyword_simE hcons l ls _ _ _ _ _ _)


/-! The finishers at the end of the input, where the batches have no tokens: an interruption is
thrown from states whose batches have none either. -/

/-- `SRLb`, and the Rust port's batch has no tokens. -/
abbrev SRLbZ (strict : Bool) (l ls : Nat) (s : WS floor low) (t : XS floor low) : Prop :=
  SRLb strict l ls s t ∧ s.val.batch.len = 0

theorem sinkStored_simZ (hcons : ConsumesAlike H m R E) (l ls : Nat) (ty : TokenCategory)
    (hty : ty ≠ .endOfFile) (tokenEnd : Lexer.Slice.TokenEnd) (start : Location) (base : Nat)
    (h : Lexer.WRustPort.Started floor low start)
    (h' : Lexer.X1BatchInCore.Started floor low start) :
    ESim (H := H) (m := m) (R := R) (E := E) (ErZ strict) (SRLbZ strict l ls)
      (fun _ _ => SREb strict l ls)
      (Lexer.WRustPort.sinkStored ty hty tokenEnd start base h)
      (Lexer.X1BatchInCore.sinkStored ty hty tokenEnd start base h') := by
  unfold Lexer.WRustPort.sinkStored Lexer.X1BatchInCore.sinkStored
  refine SimR.pre (fun _ _ h => h.1) ?_
  refine SimR.bind (locationFrom_sim l ls _ base tokenEnd.position) fun a b => ?_
  obtain ⟨a, ha⟩ := a
  obtain ⟨b, hb⟩ := b
  refine SimR.of_fact' (Er := ErZ strict) fun (e : a = b) => ?_
  subst e
  exact handOverStored_simZ hcons l ls ty hty start a _ _ _

/-- A finisher at the end of the input: the check of the token, and then `sinkStored_simZ`. -/
local macro "finish_eof" : tactic => `(tactic| (
  dsimp only
  refine getCore_bind_P fun s t hst => ?_
  simp only [throw_bind, fail_bind]
  refine SimR.ite (by rw [hst.1.1.1.tokenContent]; exact Iff.rfl) (fun _ => error_simZ _ _ _ _ _)
    fun _ => sinkStored_simZ ‹_› _ _ _ _ _ _ _ _ _))

theorem finishDecimal_simZ (hcons : ConsumesAlike H m R E) (l ls : Nat)
    (tokenEnd : Lexer.Slice.TokenEnd) (start : Location) (base : Nat)
    (h : Lexer.WRustPort.Started floor low start)
    (h' : Lexer.X1BatchInCore.Started floor low start) :
    ESim (H := H) (m := m) (R := R) (E := E) (ErZ strict) (SRLbZ strict l ls)
      (fun _ _ => SREb strict l ls)
      (Lexer.WRustPort.finishDecimal tokenEnd none start base h)
      (Lexer.X1BatchInCore.finishDecimal tokenEnd none start base h') := by
  unfold Lexer.WRustPort.finishDecimal Lexer.X1BatchInCore.finishDecimal
  finish_eof

theorem finishDigitRun_simZ (hcons : ConsumesAlike H m R E) (l ls : Nat) (run : Lexer.DigitRun)
    (hrun : run = Lexer.HEXADECIMAL_RUN ∨ run = Lexer.BINARY_RUN)
    (tokenEnd : Lexer.Slice.TokenEnd) (start : Location) (base : Nat)
    (h : Lexer.WRustPort.Started floor low start)
    (h' : Lexer.X1BatchInCore.Started floor low start) :
    ESim (H := H) (m := m) (R := R) (E := E) (ErZ strict) (SRLbZ strict l ls)
      (fun _ _ => SREb strict l ls)
      (Lexer.WRustPort.finishDigitRun run hrun tokenEnd none start base h)
      (Lexer.X1BatchInCore.finishDigitRun run hrun tokenEnd none start base h') := by
  unfold Lexer.WRustPort.finishDigitRun Lexer.X1BatchInCore.finishDigitRun
  finish_eof

theorem finishKeyword_simZ (hcons : ConsumesAlike H m R E) (l ls : Nat)
    (tokenEnd : Lexer.Slice.TokenEnd) (start : Location) (base : Nat)
    (h : Lexer.WRustPort.Started floor low start)
    (h' : Lexer.X1BatchInCore.Started floor low start) :
    ESim (H := H) (m := m) (R := R) (E := E) (ErZ strict) (SRLbZ strict l ls)
      (fun _ _ => SREb strict l ls)
      (Lexer.WRustPort.finishKeyword tokenEnd none start base h)
      (Lexer.X1BatchInCore.finishKeyword tokenEnd none start base h') := by
  unfold Lexer.WRustPort.finishKeyword Lexer.X1BatchInCore.finishKeyword
  finish_eof

end

end BSmtLib.Proofs.WRustPortX1BatchInCore
