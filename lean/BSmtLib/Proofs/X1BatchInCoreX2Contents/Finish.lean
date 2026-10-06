import BSmtLib.Proofs.X1BatchInCoreX2Contents.HandOver

/-!
# The finishing of a token in progress, in both lexers

A token in progress is finished from its content, which the lexer with the content buffer reads
from the buffer and the lexer with the batch kept in the lexer's state from its byte array:
both read the same bytes (`last?_stored`, `size_stored`).
-/

namespace BSmtLib.Proofs.X1BatchInCoreX2Contents

open BSmtLib.Proofs.Simulation

theorem coreMap_tokenContent (c : Core2) : (coreMap c).tokenContent = contentBytes c.tokenContent :=
  rfl

section

variable {H : Type} {m : Type → Type} {R E : Type} [Monad m] [LawfulMonad m] [Consume H m R E]
  {floor : Option Nat} {low : Nat} (hblind : ContentBlind H m R E)
include hblind

/-- Takes the steps of finishing a token, as long as they are the same in both lexers. -/
local macro "sim_finish" : tactic => `(tactic| repeat (first
    | (with_reducible refine getCore_bind fun _ _ => ?_)
    | dsimp only
    | ((with_reducible refine SimF.ite ?_ (fun _ => ?_) fun _ => ?_); exact Iff.rfl)
    | (with_reducible refine SimF.seq (fail_sim (ψ := id) _ _ _) fun _ => ?_)
    | (with_reducible refine SimF.seq (expectDelimiter_sim _ _) fun _ => ?_)
    | ((with_reducible refine SimF.pure (fun _ h => h) ?_); rfl)
    | (with_reducible exact sinkStored_sim hblind _ _ _ _ _ _ _ _)))

theorem finishDecimal_sim (te : Lexer.Slice.TokenEnd) (next : Option UInt8) (s : Location)
    (base : Nat) (h h') :
    SimF BFits BFits (fun _ => BFits) (boundMap (floor := floor) (low := low)) id
      (Lexer.X2Contents.finishDecimal (H := H) (m := m) (R := R) (E := E) te next s base h)
      (Lexer.X1BatchInCore.finishDecimal te next s base h') := by
  unfold Lexer.X2Contents.finishDecimal Lexer.X1BatchInCore.finishDecimal
  refine getCore_bind fun c hc => ?_
  rw [coreMap_tokenContent, last?_stored hc]
  cases next <;> sim_finish

theorem finishNumeral_sim (te : Lexer.Slice.TokenEnd) (s : Location) (base : Nat) (h h') :
    SimF BFits BFits (fun _ => BFits) (boundMap (floor := floor) (low := low)) id
      (Lexer.X2Contents.finishNumeral (H := H) (m := m) (R := R) (E := E) te s base h)
      (Lexer.X1BatchInCore.finishNumeral te s base h') :=
  sinkStored_sim hblind _ _ _ _ _ _ _ _

theorem finishDigitRun_sim (run : Lexer.DigitRun) (hrun hrun') (te : Lexer.Slice.TokenEnd)
    (next : Option UInt8) (s : Location) (base : Nat) (h h') :
    SimF BFits BFits (fun _ => BFits) (boundMap (floor := floor) (low := low)) id
      (Lexer.X2Contents.finishDigitRun (H := H) (m := m) (R := R) (E := E) run hrun te next s
        base h)
      (Lexer.X1BatchInCore.finishDigitRun run hrun' te next s base h') := by
  unfold Lexer.X2Contents.finishDigitRun Lexer.X1BatchInCore.finishDigitRun
  refine getCore_bind fun c hc => ?_
  rw [coreMap_tokenContent, size_stored hc]
  cases next <;> sim_finish

theorem finishSimpleSymbol_sim (te : Lexer.Slice.TokenEnd) (s : Location) (base : Nat) (h h') :
    SimF BFits BFits (fun _ => BFits) (boundMap (floor := floor) (low := low)) id
      (Lexer.X2Contents.finishSimpleSymbol (H := H) (m := m) (R := R) (E := E) te s base h)
      (Lexer.X1BatchInCore.finishSimpleSymbol te s base h') :=
  sinkStored_sim hblind _ _ _ _ _ _ _ _

theorem finishKeyword_sim (te : Lexer.Slice.TokenEnd) (next : Option UInt8) (s : Location)
    (base : Nat) (h h') :
    SimF BFits BFits (fun _ => BFits) (boundMap (floor := floor) (low := low)) id
      (Lexer.X2Contents.finishKeyword (H := H) (m := m) (R := R) (E := E) te next s base h)
      (Lexer.X1BatchInCore.finishKeyword te next s base h') := by
  unfold Lexer.X2Contents.finishKeyword Lexer.X1BatchInCore.finishKeyword
  refine getCore_bind fun c hc => ?_
  rw [coreMap_tokenContent, size_stored hc]
  cases next <;> sim_finish

theorem finishStringLiteral_sim (te : Lexer.Slice.TokenEnd) (s : Location) (base : Nat) (h h') :
    SimF BFits BFits (fun _ => BFits) (boundMap (floor := floor) (low := low)) id
      (Lexer.X2Contents.finishStringLiteral (H := H) (m := m) (R := R) (E := E) te s base h)
      (Lexer.X1BatchInCore.finishStringLiteral te s base h') :=
  sinkStored_sim hblind _ _ _ _ _ _ _ _

theorem finishWhitespace_sim (te : Lexer.Slice.TokenEnd) (s : Location) (base : Nat) (h h') :
    SimF BFits BFits (fun _ => BFits) (boundMap (floor := floor) (low := low)) id
      (Lexer.X2Contents.finishWhitespace (H := H) (m := m) (R := R) (E := E) te s base h)
      (Lexer.X1BatchInCore.finishWhitespace te s base h') :=
  sinkStored_sim hblind _ _ _ _ _ _ _ _

end

end BSmtLib.Proofs.X1BatchInCoreX2Contents
