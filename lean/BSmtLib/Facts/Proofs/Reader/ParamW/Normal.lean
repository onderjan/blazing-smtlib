module

public import BSmtLib.Facts.Proofs.Reader.ParamW.HandOver
import all BSmtLib.Lexer.Internal.WRustPort

@[expose] public section

/-!
# The Rust port's normal state on two consumers

The lemmas for the helpers of the Rust port's normal state, with its operations `Rust.ops`, and
for its loop `lexNormalFrom`. The recursive functions are related by recursion on what they
recurse on.
-/

namespace BSmtLib.Facts.Proofs.Reader.ParamW.Normal

open BSmtLib.Lexer
open BSmtLib.Facts.Proofs.Reader.Param.Basic BSmtLib.Facts.Proofs.Reader.Param.Walk
open BSmtLib.Facts.Proofs.Reader.ParamW.HandOver
open BSmtLib.Lexer.Internal.WRustPort

attribute [local instance] Rust.ops

section

variable {H₁ H₂ : Type} {m₁ m₂ : Type → Type} [Monad m₁] [Monad m₂] {R₁ R₂ E₁ E₂ : Type}
  [Token.Consume H₁ R₁ E₁] [Token.Consume H₂ R₂ E₂] [∀ b, Token.ConsumeFrom H₁
      (Token.BatchCursor b) m₁]
  [∀ b, Token.ConsumeFrom H₂ (Token.BatchCursor b) m₂]
  {L : Link H₁ m₁ R₁ E₁ H₂ m₂ R₂ E₂} {floor : Option Nat} {low : Nat}

theorem loadLocals_sim :
    LSim L (· = ·) (Ops.loadLocals (self := Rust.ops (H := H₁) (m := m₁) (R := R₁) (E := E₁))
        (floor := floor) (low := low))
      (Ops.loadLocals (self := Rust.ops (H := H₂) (m := m₂) (R := R₂) (E := E₂))) :=
  load_sim

theorem storeLocals_sim (s : FastState) :
    LSim L (· = ·) (Ops.storeLocals (self := Rust.ops (H := H₁) (m := m₁) (R := R₁) (E := E₁))
        (floor := floor) (low := low) s)
      (Ops.storeLocals (self := Rust.ops (H := H₂) (m := m₂) (R := R₂) (E := E₂)) s) :=
  store_sim s

theorem sinkStored_sim (hc : ConsumersW L) (ty tokenEnd start base h) :
    LSim L (· = ·)
      (sinkStored (H := H₁) (m := m₁) (R := R₁) (E := E₁) (floor := floor) (low := low)
        ty tokenEnd start base h)
      (sinkStored (H := H₂) (m := m₂) (R := R₂) (E := E₂)
        ty tokenEnd start base h) := by
  unfold sinkStored; lsimW

theorem finishDecimal_sim (hc : ConsumersW L) (tokenEnd next start base h) :
    LSim L (· = ·)
      (finishDecimal (H := H₁) (m := m₁) (R := R₁) (E := E₁) (floor := floor) (low := low)
        tokenEnd next start base h)
      (finishDecimal (H := H₂) (m := m₂) (R := R₂) (E := E₂)
        tokenEnd next start base h) := by
  unfold finishDecimal; lsimW

theorem finishNumeral_sim (hc : ConsumersW L) (tokenEnd start base h) :
    LSim L (· = ·)
      (finishNumeral (H := H₁) (m := m₁) (R := R₁) (E := E₁) (floor := floor) (low := low)
        tokenEnd start base h)
      (finishNumeral (H := H₂) (m := m₂) (R := R₂) (E := E₂)
        tokenEnd start base h) := by
  unfold finishNumeral; lsimW

theorem finishDigitRun_sim (hc : ConsumersW L) (run tokenEnd next start base h) :
    LSim L (· = ·)
      (finishDigitRun (H := H₁) (m := m₁) (R := R₁) (E := E₁) (floor := floor) (low := low)
        run tokenEnd next start base h)
      (finishDigitRun (H := H₂) (m := m₂) (R := R₂) (E := E₂)
        run tokenEnd next start base h) := by
  unfold finishDigitRun; lsimW

theorem finishSimpleSymbol_sim (hc : ConsumersW L) (tokenEnd start base h) :
    LSim L (· = ·)
      (finishSimpleSymbol (H := H₁) (m := m₁) (R := R₁) (E := E₁) (floor := floor) (low := low)
        tokenEnd start base h)
      (finishSimpleSymbol (H := H₂) (m := m₂) (R := R₂) (E := E₂)
        tokenEnd start base h) := by
  unfold finishSimpleSymbol; lsimW

theorem finishKeyword_sim (hc : ConsumersW L) (tokenEnd next start base h) :
    LSim L (· = ·)
      (finishKeyword (H := H₁) (m := m₁) (R := R₁) (E := E₁) (floor := floor) (low := low)
        tokenEnd next start base h)
      (finishKeyword (H := H₂) (m := m₂) (R := R₂) (E := E₂)
        tokenEnd next start base h) := by
  unfold finishKeyword; lsimW

theorem finishStringLiteral_sim (hc : ConsumersW L) (tokenEnd start base h) :
    LSim L (· = ·)
      (finishStringLiteral (H := H₁) (m := m₁) (R := R₁) (E := E₁) (floor := floor) (low := low)
        tokenEnd start base h)
      (finishStringLiteral (H := H₂) (m := m₂) (R := R₂) (E := E₂)
        tokenEnd start base h) := by
  unfold finishStringLiteral; lsimW

theorem finishWhitespace_sim (hc : ConsumersW L) (tokenEnd start base h) :
    LSim L (· = ·)
      (finishWhitespace (H := H₁) (m := m₁) (R := R₁) (E := E₁) (floor := floor) (low := low)
        tokenEnd start base h)
      (finishWhitespace (H := H₂) (m := m₂) (R := R₂) (E := E₂)
        tokenEnd start base h) := by
  unfold finishWhitespace; lsimW

omit [Token.Consume H₁ R₁ E₁] [Token.Consume H₂ R₂ E₂]
  [∀ b, Token.ConsumeFrom H₁ (Token.BatchCursor b) m₁]
  [∀ b, Token.ConsumeFrom H₂ (Token.BatchCursor b) m₂] in
theorem leave_sim (offset base position batch hframe hbatch) :
    LSim L (· = ·)
      (leave (H := H₁) (m := m₁) (R := R₁) (E := E₁) (floor := floor) (low := low)
        offset base position batch hframe hbatch)
      (leave (H := H₂) (m := m₂) (R := R₂) (E := E₂)
        offset base position batch hframe hbatch) := by
  unfold leave; lsimW

omit [Token.Consume H₁ R₁ E₁] [Token.Consume H₂ R₂ E₂]
  [∀ b, Token.ConsumeFrom H₁ (Token.BatchCursor b) m₁]
  [∀ b, Token.ConsumeFrom H₂ (Token.BatchCursor b) m₂] in
theorem leavePending_sim (state start offset base position batch hframe hbatch hstart hfloor) :
    LSim L (· = ·)
      (leavePending (H := H₁) (m := m₁) (R := R₁) (E := E₁) (floor := floor) (low := low)
        state start offset base position batch hframe hbatch hstart hfloor)
      (leavePending (H := H₂) (m := m₂) (R := R₂) (E := E₂)
        state start offset base position batch hframe hbatch hstart hfloor) := by
  unfold leavePending; lsimW

theorem pushBorrowed_sim (hc : ConsumersW L)
    (input batch offset base ty contentStart contentStop start tokenEnd hty hafter hend hfloor) :
    LSim L (· = ·)
      (pushBorrowed (H := H₁) (m := m₁) (R := R₁) (E := E₁) (floor := floor) (low := low)
        input batch offset base ty contentStart contentStop start tokenEnd hty hafter hend
        hfloor)
      (pushBorrowed (H := H₂) (m := m₂) (R := R₂) (E := E₂)
        input batch offset base ty contentStart contentStop start tokenEnd hty hafter hend
        hfloor) := by
  unfold pushBorrowed; lsimW

omit [Token.Consume H₁ R₁ E₁] [Token.Consume H₂ R₂ E₂]
  [∀ b, Token.ConsumeFrom H₁ (Token.BatchCursor b) m₁]
  [∀ b, Token.ConsumeFrom H₂ (Token.BatchCursor b) m₂] in
theorem storeUnfinishedSymbolRun_sim
    (input entry offset base index after runEndAt batch hframe hindex hrun hbatch) :
    LSim L (· = ·)
      (storeUnfinishedSymbolRun (H := H₁) (m := m₁) (R := R₁) (E := E₁) (floor := floor)
        (low := low) input entry offset base index after runEndAt batch hframe hindex hrun hbatch)
      (storeUnfinishedSymbolRun (H := H₂) (m := m₂) (R := R₂) (E := E₂)
        input entry offset base index after runEndAt batch hframe hindex hrun hbatch) := by
  unfold storeUnfinishedSymbolRun; lsimW

theorem startWhitespaceFrom_sim (hc : ConsumersW L) (input : ByteSlice) (offset : Nat)
    (base index «end» : Nat) (start : Span.Location) (batch : Token.Internal.TokenBatch)
    (hframe hstart hend hrun hbatch) :
    LSim L (· = ·)
      (startWhitespaceFrom (H := H₁) (m := m₁) (R := R₁) (E := E₁) (floor := floor) (low := low)
        input offset base index «end» start batch hframe hstart hend hrun hbatch)
      (startWhitespaceFrom (H := H₂) (m := m₂) (R := R₂) (E := E₂)
        input offset base index «end» start batch hframe hstart hend hrun hbatch) := by
  rw [startWhitespaceFrom.eq_1, startWhitespaceFrom.eq_1]
  lsimW
  all_goals exact startWhitespaceFrom_sim hc _ _ _ _ _ _ _ _ _ _ _ _
termination_by input.size - «end»
decreasing_by
  all_goals lsim_omega [Lexer.Internal.WRustPort.Slice.le_runEnd,
    Lexer.Internal.WRustPort.Slice.le_runEndAll]

theorem startWhitespace_sim (hc : ConsumersW L) (input offset base index batch hrun hframe hindex
    hbatch) :
    LSim L (· = ·)
      (startWhitespace (H := H₁) (m := m₁) (R := R₁) (E := E₁) (floor := floor) (low := low)
        input offset base index batch hrun hframe hindex hbatch)
      (startWhitespace (H := H₂) (m := m₂) (R := R₂) (E := E₂)
        input offset base index batch hrun hframe hindex hbatch) := by
  unfold startWhitespace; lsimW

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 8192 in
theorem lexNormalFrom_sim (hc : ConsumersW L) (input : ByteSlice) (offset : Nat)
    (base index : Nat) (batch : Token.Internal.TokenBatch) (locals : FastState)
    (hframe hindex hbatch)
    (origin : Nat) (horigin) :
    LSim L (· = ·)
      (lexNormalFrom (H := H₁) (m := m₁) (R := R₁) (E := E₁) (floor := floor) (low := low)
        input offset base index batch locals hframe hindex hbatch origin horigin)
      (lexNormalFrom (H := H₂) (m := m₂) (R := R₂) (E := E₂)
        input offset base index batch locals hframe hindex hbatch origin horigin) := by
  rw [lexNormalFrom.eq_1, lexNormalFrom.eq_1]
  lsimW
  all_goals exact lexNormalFrom_sim hc _ _ _ _ _ _ _ _ _ _ _
termination_by input.size - index
decreasing_by
  all_goals lsim_omega [Lexer.Internal.WRustPort.Slice.le_runEnd,
    Lexer.Internal.WRustPort.Slice.le_runEndAll]

theorem lexNormal_sim (hc : ConsumersW L) (input start hstart) :
    LSim L (· = ·)
      (lexNormal (H := H₁) (m := m₁) (R := R₁) (E := E₁) (floor := floor) (low := low)
        input start hstart)
      (lexNormal (H := H₂) (m := m₂) (R := R₂) (E := E₂) input start hstart) := by
  unfold lexNormal; lsimW

end

end BSmtLib.Facts.Proofs.Reader.ParamW.Normal
