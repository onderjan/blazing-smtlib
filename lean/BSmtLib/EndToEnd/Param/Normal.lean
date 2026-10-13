import BSmtLib.EndToEnd.Param.HandOver

/-!
# The normal state of the lexer on two consumers

The lemmas for the helpers of the lexer's normal state and for its loop `lexNormalFrom`. The
recursive functions are related by recursion on what they recurse on; the walk leaves the
recursive calls, which the lemma itself relates.
-/

namespace BSmtLib.EndToEnd.Param

open BSmtLib.Lexer BSmtLib.Lexer.Internal

section

variable {H₁ H₂ : Type} {m₁ m₂ : Type → Type} [Monad m₁] [Monad m₂] {R₁ R₂ E₁ E₂ : Type}
  [Consume H₁ R₁ E₁] [Consume H₂ R₂ E₂] [∀ b, ConsumeFrom H₁ (BatchCursor b) m₁]
  [∀ b, ConsumeFrom H₂ (BatchCursor b) m₂]
  {L : Link H₁ m₁ R₁ E₁ H₂ m₂ R₂ E₂} {floor : Option Nat} {low : Nat}

theorem consumesWhitespaceAndComments_sim (hc : Consumers L) :
    LSim L (· = ·) (consumesWhitespaceAndComments (floor := floor) (low := low))
      consumesWhitespaceAndComments := by
  unfold consumesWhitespaceAndComments
  rw [hc.concrete]
  exact XSim.pure_eq _

theorem sinkStored_sim (hc : Consumers L) (ty tokenEnd start base h) :
    LSim L (· = ·) (sinkStored (floor := floor) (low := low) ty tokenEnd start base h)
      (sinkStored ty tokenEnd start base h) := by
  unfold sinkStored; lsim

theorem finishDecimal_sim (hc : Consumers L) (tokenEnd next start base h) :
    LSim L (· = ·) (finishDecimal (floor := floor) (low := low) tokenEnd next start base h)
      (finishDecimal tokenEnd next start base h) := by
  unfold finishDecimal; lsim

theorem finishNumeral_sim (hc : Consumers L) (tokenEnd start base h) :
    LSim L (· = ·) (finishNumeral (floor := floor) (low := low) tokenEnd start base h)
      (finishNumeral tokenEnd start base h) := by
  unfold finishNumeral; lsim

theorem finishDigitRun_sim (hc : Consumers L) (run tokenEnd next start base h) :
    LSim L (· = ·) (finishDigitRun (floor := floor) (low := low) run tokenEnd next start base h)
      (finishDigitRun run tokenEnd next start base h) := by
  unfold finishDigitRun; lsim

theorem finishSimpleSymbol_sim (hc : Consumers L) (tokenEnd start base h) :
    LSim L (· = ·) (finishSimpleSymbol (floor := floor) (low := low) tokenEnd start base h)
      (finishSimpleSymbol tokenEnd start base h) := by
  unfold finishSimpleSymbol; lsim

theorem finishKeyword_sim (hc : Consumers L) (tokenEnd next start base h) :
    LSim L (· = ·) (finishKeyword (floor := floor) (low := low) tokenEnd next start base h)
      (finishKeyword tokenEnd next start base h) := by
  unfold finishKeyword; lsim

theorem finishStringLiteral_sim (hc : Consumers L) (tokenEnd start base h) :
    LSim L (· = ·) (finishStringLiteral (floor := floor) (low := low) tokenEnd start base h)
      (finishStringLiteral tokenEnd start base h) := by
  unfold finishStringLiteral; lsim

theorem finishWhitespace_sim (hc : Consumers L) (tokenEnd start base h) :
    LSim L (· = ·) (finishWhitespace (floor := floor) (low := low) tokenEnd start base h)
      (finishWhitespace tokenEnd start base h) := by
  unfold finishWhitespace; lsim

omit [Consume H₁ R₁ E₁] [Consume H₂ R₂ E₂] [∀ b, ConsumeFrom H₁ (BatchCursor b) m₁]
  [∀ b, ConsumeFrom H₂ (BatchCursor b) m₂] in
theorem leave_sim (offset base position batch hframe hbatch) :
    LSim L (· = ·) (leave (floor := floor) (low := low) offset base position batch hframe hbatch)
      (leave offset base position batch hframe hbatch) := by
  unfold leave; lsim

omit [Consume H₁ R₁ E₁] [Consume H₂ R₂ E₂] [∀ b, ConsumeFrom H₁ (BatchCursor b) m₁]
  [∀ b, ConsumeFrom H₂ (BatchCursor b) m₂] in
theorem leavePending_sim (state start offset base position batch hframe hbatch hstart hfloor) :
    LSim L (· = ·)
      (leavePending (floor := floor) (low := low) state start offset base position batch hframe
        hbatch hstart hfloor)
      (leavePending state start offset base position batch hframe hbatch hstart hfloor) := by
  unfold leavePending; lsim

theorem flushHeld_sim (hc : Consumers L) (batch origin hbatch) :
    LSim L (· = ·) (flushHeld (floor := floor) (low := low) batch origin hbatch)
      (flushHeld batch origin hbatch) := by
  unfold flushHeld; lsim

theorem pushFast_sim (hc : Consumers L) (batch offset base ty contentStart contentStop start «end»
    emit hty hstart hend hframe hbatch) :
    LSim L (· = ·)
      (pushFast (floor := floor) (low := low) batch offset base ty contentStart contentStop start
        «end» emit hty hstart hend hframe hbatch)
      (pushFast batch offset base ty contentStart contentStop start «end» emit hty hstart hend
        hframe hbatch) := by
  unfold pushFast; lsim

theorem pushBorrowed_sim (hc : Consumers L) (batch offset base ty contentStart contentStop start
    tokenEnd hty hafter hend hfloor) :
    LSim L (· = ·)
      (pushBorrowed (floor := floor) (low := low) batch offset base ty contentStart contentStop
        start tokenEnd hty hafter hend hfloor)
      (pushBorrowed batch offset base ty contentStart contentStop start tokenEnd hty hafter hend
        hfloor) := by
  unfold pushBorrowed; lsim

omit [Consume H₁ R₁ E₁] [Consume H₂ R₂ E₂] [∀ b, ConsumeFrom H₁ (BatchCursor b) m₁]
  [∀ b, ConsumeFrom H₂ (BatchCursor b) m₂] in
theorem storeUnfinishedSymbolRun_sim (input entry offset base index after runEndAt batch hframe
    hindex hrun hbatch) :
    LSim L (· = ·)
      (storeUnfinishedSymbolRun (floor := floor) (low := low) input entry offset base index after
        runEndAt batch hframe hindex hrun hbatch)
      (storeUnfinishedSymbolRun input entry offset base index after runEndAt batch hframe hindex
        hrun hbatch) := by
  unfold storeUnfinishedSymbolRun; lsim

theorem startWhitespaceFrom_sim (hc : Consumers L) (input : Input) (offset : Nat)
    (base index «end» : USize) (start : Location) (batch : TokenBatch) (hframe hstart hend hrun
    hbatch) :
    LSim L (· = ·)
      (startWhitespaceFrom (floor := floor) (low := low) input offset base index «end» start batch
        hframe hstart hend hrun hbatch)
      (startWhitespaceFrom input offset base index «end» start batch hframe hstart hend hrun
        hbatch) := by
  rw [startWhitespaceFrom.eq_1, startWhitespaceFrom.eq_1]
  lsim
  all_goals exact startWhitespaceFrom_sim hc _ _ _ _ _ _ _ _ _ _ _ _
termination_by input.stop.toNat - «end».toNat
decreasing_by
  all_goals
    have := le_runEnd input «end» RUN_NON_LF_WHITESPACE
    simp +zetaDelta only at *
    omega
theorem startWhitespace_sim (hc : Consumers L) (input offset base index batch hrun hframe hindex
    hbatch) :
    LSim L (· = ·)
      (startWhitespace (floor := floor) (low := low) input offset base index batch hrun hframe
        hindex hbatch)
      (startWhitespace input offset base index batch hrun hframe hindex hbatch) := by
  unfold startWhitespace; lsim

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 8192 in
theorem lexNormalFrom_sim (hc : Consumers L) (input : Input) (offset : Nat) (base index : USize)
    (batch : TokenBatch) (hframe hindex hbatch) (origin : USize) (horigin) :
    LSim L (· = ·)
      (lexNormalFrom (floor := floor) (low := low) input offset base index batch hframe hindex
        hbatch origin horigin)
      (lexNormalFrom input offset base index batch hframe hindex hbatch origin horigin) := by
  rw [lexNormalFrom.eq_1, lexNormalFrom.eq_1]
  lsim
  all_goals exact lexNormalFrom_sim hc _ _ _ _ _ _ _ _ _ _
termination_by input.stop.toNat - index.toNat
decreasing_by all_goals lsim_omega [le_runEnd, le_runEndAll]

end

end BSmtLib.EndToEnd.Param
