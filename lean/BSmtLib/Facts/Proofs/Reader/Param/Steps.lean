import BSmtLib.Facts.Proofs.Reader.Param.Normal

/-!
# The steps of the lexer on two consumers

The lemmas for the steps of the lexer in the states of a token in progress, and for `lexStep`,
which dispatches on the state.
-/

namespace BSmtLib.Facts.Proofs.Reader.Param.Steps

open BSmtLib.Lexer BSmtLib.Lexer.Internal
open BSmtLib.Facts.Proofs.Reader.Param.Basic BSmtLib.Facts.Proofs.Reader.Param.HandOver

section

variable {H₁ H₂ : Type} {m₁ m₂ : Type → Type} [Monad m₁] [Monad m₂] {R₁ R₂ E₁ E₂ : Type}
  [Token.Consume H₁ R₁ E₁] [Token.Consume H₂ R₂ E₂] [∀ b, Token.ConsumeFrom H₁
      (Token.BatchCursor b) m₁]
  [∀ b, Token.ConsumeFrom H₂ (Token.BatchCursor b) m₂]
  {L : Link H₁ m₁ R₁ E₁ H₂ m₂ R₂ E₂} {floor : Option Nat} {low : Nat}

theorem lexNormal_sim (hc : Consumers L) (input start hstart) :
    LSim L (· = ·) (lexNormal (floor := floor) (low := low) input start hstart)
      (lexNormal input start hstart) := by
  unfold lexNormal; lsim

theorem lexFractionFrom_sim (hc : Consumers L) (input start tokenStart base h) :
    LSim L (· = ·) (lexFractionFrom (floor := floor) (low := low) input start tokenStart base h)
      (lexFractionFrom input start tokenStart base h) := by
  unfold lexFractionFrom; lsim

theorem lexNumeralOrDecimal_sim (hc : Consumers L) (input start tokenStart base h) :
    LSim L (· = ·)
      (lexNumeralOrDecimal (floor := floor) (low := low) input start tokenStart base h)
      (lexNumeralOrDecimal input start tokenStart base h) := by
  unfold lexNumeralOrDecimal; lsim

omit [Token.Consume H₁ R₁ E₁] [Token.Consume H₂ R₂ E₂] [∀ b, Token.ConsumeFrom H₁
    (Token.BatchCursor b) m₁]
  [∀ b, Token.ConsumeFrom H₂ (Token.BatchCursor b) m₂] in
theorem lexBaseSelection_sim (input start hstart tokenStart h) :
    LSim L (· = ·)
      (lexBaseSelection (H := H₁) (m := m₁) (R := R₁) (E := E₁) (floor := floor) (low := low)
        input start hstart tokenStart h)
      (lexBaseSelection input start hstart tokenStart h) := by
  unfold lexBaseSelection; lsim

theorem lexDigitRun_sim (hc : Consumers L) (input start run tokenStart base h) :
    LSim L (· = ·) (lexDigitRun (floor := floor) (low := low) input start run tokenStart base h)
      (lexDigitRun input start run tokenStart base h) := by
  unfold lexDigitRun; lsim

theorem lexStringLiteralLegacy_sim (hc : Consumers L) (input : CharClass.Input)
    (consumed origin : USize)
    (horigin tokenStart base h) :
    LSim L (· = ·)
      (lexStringLiteralLegacy (floor := floor) (low := low) input consumed origin horigin
        tokenStart base h)
      (lexStringLiteralLegacy input consumed origin horigin tokenStart base h) := by
  rw [lexStringLiteralLegacy.eq_1, lexStringLiteralLegacy.eq_1]
  lsim
  all_goals exact lexStringLiteralLegacy_sim hc _ _ _ _ _ _ _
termination_by input.stop.toNat - consumed.toNat
decreasing_by all_goals lsim_omega [CharClass.le_runEnd, CharClass.le_runEndAll]

theorem lexStringLiteralFrom_sim (hc : Consumers L) (input : CharClass.Input)
    (consumed origin : USize)
    (horigin tokenStart base h) :
    LSim L (· = ·)
      (lexStringLiteralFrom (floor := floor) (low := low) input consumed origin horigin
        tokenStart base h)
      (lexStringLiteralFrom input consumed origin horigin tokenStart base h) := by
  rw [lexStringLiteralFrom.eq_1, lexStringLiteralFrom.eq_1]
  lsim
  all_goals exact lexStringLiteralFrom_sim hc _ _ _ _ _ _ _
termination_by input.stop.toNat - consumed.toNat
decreasing_by all_goals lsim_omega [CharClass.le_runEnd, CharClass.le_runEndAll]

theorem lexStringLiteral_sim (hc : Consumers L) (input start tokenStart base h) :
    LSim L (· = ·)
      (lexStringLiteral (floor := floor) (low := low) input start tokenStart base h)
      (lexStringLiteral input start tokenStart base h) := by
  unfold lexStringLiteral; lsim

theorem lexSimpleSymbol_sim (hc : Consumers L) (input start tokenStart base h) :
    LSim L (· = ·)
      (lexSimpleSymbol (floor := floor) (low := low) input start tokenStart base h)
      (lexSimpleSymbol input start tokenStart base h) := by
  unfold lexSimpleSymbol; lsim

theorem lexQuotedSymbol_sim (hc : Consumers L) (input : CharClass.Input) (consumed origin : USize)
    (horigin hconsumed tokenStart base h) :
    LSim L (· = ·)
      (lexQuotedSymbol (floor := floor) (low := low) input consumed origin horigin hconsumed
        tokenStart base h)
      (lexQuotedSymbol input consumed origin horigin hconsumed tokenStart base h) := by
  rw [lexQuotedSymbol.eq_1, lexQuotedSymbol.eq_1]
  lsim
  all_goals exact lexQuotedSymbol_sim hc _ _ _ _ _ _ _ _
termination_by input.stop.toNat - consumed.toNat
decreasing_by all_goals lsim_omega [CharClass.le_runEnd, CharClass.le_runEndAll]

theorem lexKeyword_sim (hc : Consumers L) (input start tokenStart base h) :
    LSim L (· = ·) (lexKeyword (floor := floor) (low := low) input start tokenStart base h)
      (lexKeyword input start tokenStart base h) := by
  unfold lexKeyword; lsim

theorem lexQuotedSymbolClosed_sim (hc : Consumers L) (input start hstart tokenStart base h) :
    LSim L (· = ·)
      (lexQuotedSymbolClosed (floor := floor) (low := low) input start hstart tokenStart base h)
      (lexQuotedSymbolClosed input start hstart tokenStart base h) := by
  unfold lexQuotedSymbolClosed; lsim

theorem lexWhitespace_sim (hc : Consumers L) (input : CharClass.Input) (start origin : USize)
    (horigin hstart tokenStart base h) :
    LSim L (· = ·)
      (lexWhitespace (floor := floor) (low := low) input start origin horigin hstart tokenStart
        base h)
      (lexWhitespace input start origin horigin hstart tokenStart base h) := by
  rw [lexWhitespace.eq_1, lexWhitespace.eq_1]
  lsim
  all_goals exact lexWhitespace_sim hc _ _ _ _ _ _ _ _
termination_by input.stop.toNat - start.toNat
decreasing_by all_goals lsim_omega [CharClass.le_runEnd, CharClass.le_runEndAll]

theorem lexComment_sim (hc : Consumers L) (input start hstart tokenStart base h) :
    LSim L (· = ·)
      (lexComment (floor := floor) (low := low) input start hstart tokenStart base h)
      (lexComment input start hstart tokenStart base h) := by
  unfold lexComment; lsim

theorem afterStep_sim (hc : Consumers L) (input start hstart next) :
    LSim L (· = ·) (afterStep (floor := floor) (low := low) input start hstart next)
      (afterStep input start hstart next) := by
  unfold afterStep; lsim

theorem lexStep_sim (hc : Consumers L) (input start hstart state tokenStart base hpending) :
    LSim L (· = ·)
      (lexStep (floor := floor) (low := low) input start hstart state tokenStart base hpending)
      (lexStep input start hstart state tokenStart base hpending) := by
  unfold lexStep; lsim

end

end BSmtLib.Facts.Proofs.Reader.Param.Steps
