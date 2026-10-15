module

public import BSmtLib.Facts.Proofs.Reader.Param.Normal
import all BSmtLib.Lexer

@[expose] public section

/-!
# The steps of the lexer on two consumers

The lemmas for the steps of the lexer in the states of a token in progress, and for `lexStep`,
which dispatches on the state.
-/

namespace BSmtLib.Facts.Proofs.Reader.Param.Steps

open BSmtLib.Lexer
open BSmtLib.Facts.Proofs.Reader.Param.Basic BSmtLib.Facts.Proofs.Reader.Param.HandOver

section

variable {H₁ H₂ : Type} {m₁ m₂ : Type → Type} [Monad m₁] [Monad m₂] {R₁ R₂ E₁ E₂ : Type}
  [Token.Consume H₁ R₁ E₁] [Token.Consume H₂ R₂ E₂] [∀ b, Token.ConsumeFrom H₁
      (Token.BatchCursor b) m₁]
  [∀ b, Token.ConsumeFrom H₂ (Token.BatchCursor b) m₂]
  {L : Link H₁ m₁ R₁ E₁ H₂ m₂ R₂ E₂} {floor : Option Nat} {low : Nat}

theorem lexNormal_sim (hc : Consumers L) (input start hstart) :
    LSim L (· = ·) (Internal.lexNormal (floor := floor) (low := low) input start hstart)
      (Internal.lexNormal input start hstart) := by
  unfold Internal.lexNormal; lsim

theorem lexFractionFrom_sim (hc : Consumers L) (input start tokenStart base h) :
    LSim L (· = ·) (Internal.lexFractionFrom (floor := floor)
        (low := low) input start tokenStart base h)
      (Internal.lexFractionFrom input start tokenStart base h) := by
  unfold Internal.lexFractionFrom; lsim

theorem lexNumeralOrDecimal_sim (hc : Consumers L) (input start tokenStart base h) :
    LSim L (· = ·)
      (Internal.lexNumeralOrDecimal (floor := floor) (low := low) input start tokenStart base h)
      (Internal.lexNumeralOrDecimal input start tokenStart base h) := by
  unfold Internal.lexNumeralOrDecimal; lsim

omit [Token.Consume H₁ R₁ E₁] [Token.Consume H₂ R₂ E₂] [∀ b, Token.ConsumeFrom H₁
    (Token.BatchCursor b) m₁]
  [∀ b, Token.ConsumeFrom H₂ (Token.BatchCursor b) m₂] in
theorem lexBaseSelection_sim (input start hstart tokenStart h) :
    LSim L (· = ·)
      (Internal.lexBaseSelection (H := H₁) (m := m₁) (R := R₁) (E := E₁) (floor := floor)
          (low := low)
        input start hstart tokenStart h)
      (Internal.lexBaseSelection input start hstart tokenStart h) := by
  unfold Internal.lexBaseSelection; lsim

theorem lexDigitRun_sim (hc : Consumers L) (input start run tokenStart base h) :
    LSim L (· = ·) (Internal.lexDigitRun (floor := floor)
        (low := low) input start run tokenStart base h)
      (Internal.lexDigitRun input start run tokenStart base h) := by
  unfold Internal.lexDigitRun; lsim

theorem lexStringLiteralLegacy_sim (hc : Consumers L) (input : Internal.CharClass.Input)
    (consumed origin : USize)
    (horigin tokenStart base h) :
    LSim L (· = ·)
      (Internal.lexStringLiteralLegacy (floor := floor) (low := low) input consumed origin horigin
        tokenStart base h)
      (Internal.lexStringLiteralLegacy input consumed origin horigin tokenStart base h) := by
  rw [Internal.lexStringLiteralLegacy.eq_1, Internal.lexStringLiteralLegacy.eq_1]
  lsim
  all_goals exact lexStringLiteralLegacy_sim hc _ _ _ _ _ _ _
termination_by input.stop.toNat - consumed.toNat
decreasing_by all_goals lsim_omega [Internal.CharClass.le_runEnd, Internal.CharClass.le_runEndAll]

theorem lexStringLiteralFrom_sim (hc : Consumers L) (input : Internal.CharClass.Input)
    (consumed origin : USize)
    (horigin tokenStart base h) :
    LSim L (· = ·)
      (Internal.lexStringLiteralFrom (floor := floor) (low := low) input consumed origin horigin
        tokenStart base h)
      (Internal.lexStringLiteralFrom input consumed origin horigin tokenStart base h) := by
  rw [Internal.lexStringLiteralFrom.eq_1, Internal.lexStringLiteralFrom.eq_1]
  lsim
  all_goals exact lexStringLiteralFrom_sim hc _ _ _ _ _ _ _
termination_by input.stop.toNat - consumed.toNat
decreasing_by all_goals lsim_omega [Internal.CharClass.le_runEnd, Internal.CharClass.le_runEndAll]

theorem lexStringLiteral_sim (hc : Consumers L) (input start tokenStart base h) :
    LSim L (· = ·)
      (Internal.lexStringLiteral (floor := floor) (low := low) input start tokenStart base h)
      (Internal.lexStringLiteral input start tokenStart base h) := by
  unfold Internal.lexStringLiteral; lsim

theorem lexSimpleSymbol_sim (hc : Consumers L) (input start tokenStart base h) :
    LSim L (· = ·)
      (Internal.lexSimpleSymbol (floor := floor) (low := low) input start tokenStart base h)
      (Internal.lexSimpleSymbol input start tokenStart base h) := by
  unfold Internal.lexSimpleSymbol; lsim

theorem lexQuotedSymbol_sim (hc : Consumers L) (input : Internal.CharClass.Input)
    (consumed origin : USize)
    (horigin hconsumed tokenStart base h) :
    LSim L (· = ·)
      (Internal.lexQuotedSymbol (floor := floor) (low := low) input consumed origin horigin
          hconsumed
        tokenStart base h)
      (Internal.lexQuotedSymbol input consumed origin horigin hconsumed tokenStart base h) := by
  rw [Internal.lexQuotedSymbol.eq_1, Internal.lexQuotedSymbol.eq_1]
  lsim
  all_goals exact lexQuotedSymbol_sim hc _ _ _ _ _ _ _ _
termination_by input.stop.toNat - consumed.toNat
decreasing_by all_goals lsim_omega [Internal.CharClass.le_runEnd, Internal.CharClass.le_runEndAll]

theorem lexKeyword_sim (hc : Consumers L) (input start tokenStart base h) :
    LSim L (· = ·) (Internal.lexKeyword (floor := floor) (low := low) input start tokenStart base h)
      (Internal.lexKeyword input start tokenStart base h) := by
  unfold Internal.lexKeyword; lsim

theorem lexQuotedSymbolClosed_sim (hc : Consumers L) (input start hstart tokenStart base h) :
    LSim L (· = ·)
      (Internal.lexQuotedSymbolClosed (floor := floor)
          (low := low) input start hstart tokenStart base h)
      (Internal.lexQuotedSymbolClosed input start hstart tokenStart base h) := by
  unfold Internal.lexQuotedSymbolClosed; lsim

theorem lexWhitespace_sim (hc : Consumers L) (input : Internal.CharClass.Input)
    (start origin : USize)
    (horigin hstart tokenStart base h) :
    LSim L (· = ·)
      (Internal.lexWhitespace (floor := floor) (low := low) input start origin horigin hstart
          tokenStart
        base h)
      (Internal.lexWhitespace input start origin horigin hstart tokenStart base h) := by
  rw [Internal.lexWhitespace.eq_1, Internal.lexWhitespace.eq_1]
  lsim
  all_goals exact lexWhitespace_sim hc _ _ _ _ _ _ _ _
termination_by input.stop.toNat - start.toNat
decreasing_by all_goals lsim_omega [Internal.CharClass.le_runEnd, Internal.CharClass.le_runEndAll]

theorem lexComment_sim (hc : Consumers L) (input start hstart tokenStart base h) :
    LSim L (· = ·)
      (Internal.lexComment (floor := floor) (low := low) input start hstart tokenStart base h)
      (Internal.lexComment input start hstart tokenStart base h) := by
  unfold Internal.lexComment; lsim

theorem afterStep_sim (hc : Consumers L) (input start hstart next) :
    LSim L (· = ·) (Internal.afterStep (floor := floor) (low := low) input start hstart next)
      (Internal.afterStep input start hstart next) := by
  unfold Internal.afterStep; lsim

theorem lexStep_sim (hc : Consumers L) (input start hstart state tokenStart base hpending) :
    LSim L (· = ·)
      (Internal.lexStep (floor := floor) (low := low) input start hstart state tokenStart base
          hpending)
      (Internal.lexStep input start hstart state tokenStart base hpending) := by
  unfold Internal.lexStep; lsim

end

end BSmtLib.Facts.Proofs.Reader.Param.Steps
