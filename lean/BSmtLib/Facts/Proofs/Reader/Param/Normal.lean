module

public import BSmtLib.Facts.Proofs.Reader.Param.HandOver
import all BSmtLib.Lexer

@[expose] public section

/-!
# The normal state of the lexer on two consumers

The lemmas for the helpers of the lexer's normal state and for its loop `lexNormalFrom`. The
recursive functions are related by recursion on what they recurse on; the walk leaves the
recursive calls, which the lemma itself relates.
-/

namespace BSmtLib.Facts.Proofs.Reader.Param.Normal

open BSmtLib.Lexer
open BSmtLib.Facts.Proofs.Reader.Param.Basic BSmtLib.Facts.Proofs.Reader.Param.HandOver

section

variable {H₁ H₂ : Type} {m₁ m₂ : Type → Type} [Monad m₁] [Monad m₂] {R₁ R₂ E₁ E₂ : Type}
  [Token.Consume H₁ R₁ E₁] [Token.Consume H₂ R₂ E₂] [∀ b, Token.ConsumeFrom H₁
      (Token.BatchCursor b) m₁]
  [∀ b, Token.ConsumeFrom H₂ (Token.BatchCursor b) m₂]
  {L : Link H₁ m₁ R₁ E₁ H₂ m₂ R₂ E₂} {floor : Option Nat} {low : Nat}

theorem consumesWhitespaceAndComments_sim (hc : Consumers L) :
    LSim L (· = ·) (Internal.consumesWhitespaceAndComments (floor := floor) (low := low))
      Internal.consumesWhitespaceAndComments := by
  unfold Internal.consumesWhitespaceAndComments
  rw [hc.concrete]
  exact XSim.pure_eq _

theorem sinkStored_sim (hc : Consumers L) (ty tokenEnd start base h) :
    LSim L (· = ·) (Internal.sinkStored (floor := floor) (low := low) ty tokenEnd start base h)
      (Internal.sinkStored ty tokenEnd start base h) := by
  unfold Internal.sinkStored; lsim

theorem finishDecimal_sim (hc : Consumers L) (tokenEnd next start base h) :
    LSim L (· = ·) (Internal.finishDecimal (floor := floor) (low := low) tokenEnd next start base h)
      (Internal.finishDecimal tokenEnd next start base h) := by
  unfold Internal.finishDecimal; lsim

theorem finishNumeral_sim (hc : Consumers L) (tokenEnd start base h) :
    LSim L (· = ·) (Internal.finishNumeral (floor := floor) (low := low) tokenEnd start base h)
      (Internal.finishNumeral tokenEnd start base h) := by
  unfold Internal.finishNumeral; lsim

theorem finishDigitRun_sim (hc : Consumers L) (run tokenEnd next start base h) :
    LSim L (· = ·) (Internal.finishDigitRun (floor := floor)
        (low := low) run tokenEnd next start base h)
      (Internal.finishDigitRun run tokenEnd next start base h) := by
  unfold Internal.finishDigitRun; lsim

theorem finishSimpleSymbol_sim (hc : Consumers L) (tokenEnd start base h) :
    LSim L (· = ·) (Internal.finishSimpleSymbol (floor := floor) (low := low) tokenEnd start base h)
      (Internal.finishSimpleSymbol tokenEnd start base h) := by
  unfold Internal.finishSimpleSymbol; lsim

theorem finishKeyword_sim (hc : Consumers L) (tokenEnd next start base h) :
    LSim L (· = ·) (Internal.finishKeyword (floor := floor) (low := low) tokenEnd next start base h)
      (Internal.finishKeyword tokenEnd next start base h) := by
  unfold Internal.finishKeyword; lsim

theorem finishStringLiteral_sim (hc : Consumers L) (tokenEnd start base h) :
    LSim L (· = ·) (Internal.finishStringLiteral (floor := floor)
        (low := low) tokenEnd start base h)
      (Internal.finishStringLiteral tokenEnd start base h) := by
  unfold Internal.finishStringLiteral; lsim

theorem finishWhitespace_sim (hc : Consumers L) (tokenEnd start base h) :
    LSim L (· = ·) (Internal.finishWhitespace (floor := floor) (low := low) tokenEnd start base h)
      (Internal.finishWhitespace tokenEnd start base h) := by
  unfold Internal.finishWhitespace; lsim

omit [Token.Consume H₁ R₁ E₁] [Token.Consume H₂ R₂ E₂] [∀ b, Token.ConsumeFrom H₁
    (Token.BatchCursor b) m₁]
  [∀ b, Token.ConsumeFrom H₂ (Token.BatchCursor b) m₂] in
theorem leave_sim (offset base position batch hframe hbatch) :
    LSim L (· = ·) (Internal.leave (floor := floor)
        (low := low) offset base position batch hframe hbatch)
      (Internal.leave offset base position batch hframe hbatch) := by
  unfold Internal.leave; lsim

omit [Token.Consume H₁ R₁ E₁] [Token.Consume H₂ R₂ E₂] [∀ b, Token.ConsumeFrom H₁
    (Token.BatchCursor b) m₁]
  [∀ b, Token.ConsumeFrom H₂ (Token.BatchCursor b) m₂] in
theorem leavePending_sim (state start offset base position batch hframe hbatch hstart hfloor) :
    LSim L (· = ·)
      (Internal.leavePending (floor := floor) (low := low) state start offset base position batch
          hframe
        hbatch hstart hfloor)
      (Internal.leavePending state start offset base position batch hframe hbatch hstart hfloor) :=
          by
  unfold Internal.leavePending; lsim

theorem flushHeld_sim (hc : Consumers L) (batch origin hbatch) :
    LSim L (· = ·) (Internal.flushHeld (floor := floor) (low := low) batch origin hbatch)
      (Internal.flushHeld batch origin hbatch) := by
  unfold Internal.flushHeld; lsim

theorem pushFast_sim (hc : Consumers L) (batch offset base ty contentStart contentStop start «end»
    emit hty hstart hend hframe hbatch) :
    LSim L (· = ·)
      (Internal.pushFast (floor := floor) (low := low) batch offset base ty contentStart
          contentStop start
        «end» emit hty hstart hend hframe hbatch)
      (Internal.pushFast batch offset base ty contentStart contentStop start «end» emit hty hstart
          hend
        hframe hbatch) := by
  unfold Internal.pushFast; lsim

theorem pushBorrowed_sim (hc : Consumers L) (batch offset base ty contentStart contentStop start
    tokenEnd hty hafter hend hfloor) :
    LSim L (· = ·)
      (Internal.pushBorrowed (floor := floor) (low := low) batch offset base ty contentStart
          contentStop
        start tokenEnd hty hafter hend hfloor)
      (Internal.pushBorrowed batch offset base ty contentStart contentStop start tokenEnd hty
          hafter hend
        hfloor) := by
  unfold Internal.pushBorrowed; lsim

omit [Token.Consume H₁ R₁ E₁] [Token.Consume H₂ R₂ E₂] [∀ b, Token.ConsumeFrom H₁
    (Token.BatchCursor b) m₁]
  [∀ b, Token.ConsumeFrom H₂ (Token.BatchCursor b) m₂] in
theorem storeUnfinishedSymbolRun_sim (input entry offset base index after runEndAt batch hframe
    hindex hrun hbatch) :
    LSim L (· = ·)
      (Internal.storeUnfinishedSymbolRun (floor := floor)
          (low := low) input entry offset base index after
        runEndAt batch hframe hindex hrun hbatch)
      (Internal.storeUnfinishedSymbolRun input entry offset base index after runEndAt batch hframe
          hindex
        hrun hbatch) := by
  unfold Internal.storeUnfinishedSymbolRun; lsim

theorem startWhitespaceFrom_sim (hc : Consumers L) (input : Internal.CharClass.Input) (offset : Nat)
    (base index «end» : USize) (start : Span.Location) (batch : Token.Internal.TokenBatch)
    (hframe hstart hend hrun
    hbatch) :
    LSim L (· = ·)
      (Internal.startWhitespaceFrom (floor := floor)
          (low := low) input offset base index «end» start batch
        hframe hstart hend hrun hbatch)
      (Internal.startWhitespaceFrom input offset base index «end» start batch hframe hstart hend
          hrun
        hbatch) := by
  rw [Internal.startWhitespaceFrom.eq_1, Internal.startWhitespaceFrom.eq_1]
  lsim
  all_goals exact startWhitespaceFrom_sim hc _ _ _ _ _ _ _ _ _ _ _ _
termination_by input.stop.toNat - «end».toNat
decreasing_by
  all_goals
    have := Internal.CharClass.le_runEnd input «end» Internal.CharClass.RUN_NON_LF_WHITESPACE
    simp +zetaDelta only at *
    omega
theorem startWhitespace_sim (hc : Consumers L) (input offset base index batch hrun hframe hindex
    hbatch) :
    LSim L (· = ·)
      (Internal.startWhitespace (floor := floor) (low := low) input offset base index batch hrun
          hframe
        hindex hbatch)
      (Internal.startWhitespace input offset base index batch hrun hframe hindex hbatch) := by
  unfold Internal.startWhitespace; lsim

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 8192 in
theorem lexNormalFrom_sim (hc : Consumers L) (input : Internal.CharClass.Input) (offset : Nat)
    (base index : USize)
    (batch : Token.Internal.TokenBatch) (hframe hindex hbatch) (origin : USize) (horigin) :
    LSim L (· = ·)
      (Internal.lexNormalFrom (floor := floor) (low := low) input offset base index batch hframe
          hindex
        hbatch origin horigin)
      (Internal.lexNormalFrom input offset base index batch hframe hindex hbatch origin horigin) :=
          by
  rw [Internal.lexNormalFrom.eq_1, Internal.lexNormalFrom.eq_1]
  lsim
  all_goals exact lexNormalFrom_sim hc _ _ _ _ _ _ _ _ _ _
termination_by input.stop.toNat - index.toNat
decreasing_by all_goals lsim_omega [Internal.CharClass.le_runEnd, Internal.CharClass.le_runEndAll]

end

end BSmtLib.Facts.Proofs.Reader.Param.Normal
