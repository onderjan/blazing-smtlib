module

public import BSmtLib.Facts.Proofs.Reader.ParamW.Normal
import all BSmtLib.Lexer.Internal.WRustPort

@[expose] public section

/-!
# The Rust port's steps on two consumers

The lemmas for the steps of the Rust port in the states of a token in progress, and for
`lexStep`, which dispatches on the state.
-/

open BSmtLib.Lexer.Cursor (LexerCursor)

namespace BSmtLib.Facts.Proofs.Reader.ParamW.Steps

open BSmtLib.Lexer
open BSmtLib.Facts.Proofs.Reader.Param.Basic BSmtLib.Facts.Proofs.Reader.Param.Walk
open BSmtLib.Facts.Proofs.Reader.ParamW.HandOver
open BSmtLib.Lexer.Internal.WRustPort

attribute [local instance] Rust.ops

section

variable {H₁ H₂ : Type} {m₁ m₂ : Type → Type} [Monad m₁] [Monad m₂] {R₁ R₂ E₁ E₂ : Type}
  [Token.Consume H₁ R₁ E₁] [Token.Consume H₂ R₂ E₂] [∀ b, Token.ConsumeFrom H₁
      (LexerCursor b) m₁]
  [∀ b, Token.ConsumeFrom H₂ (LexerCursor b) m₂]
  {L : Link H₁ m₁ R₁ E₁ H₂ m₂ R₂ E₂} {floor : Option Nat} {low : Nat}

theorem lexFractionFrom_sim (hc : ConsumersW L) (input start tokenStart base h) :
    LSim L (· = ·)
      (lexFractionFrom (H := H₁) (m := m₁) (R := R₁) (E := E₁) (floor := floor) (low := low)
        input start tokenStart base h)
      (lexFractionFrom (H := H₂) (m := m₂) (R := R₂) (E := E₂)
        input start tokenStart base h) := by
  unfold lexFractionFrom; lsimW

theorem lexNumeralOrDecimal_sim (hc : ConsumersW L) (input start tokenStart base h) :
    LSim L (· = ·)
      (lexNumeralOrDecimal (H := H₁) (m := m₁) (R := R₁) (E := E₁) (floor := floor) (low := low)
        input start tokenStart base h)
      (lexNumeralOrDecimal (H := H₂) (m := m₂) (R := R₂) (E := E₂)
        input start tokenStart base h) := by
  unfold lexNumeralOrDecimal; lsimW

omit [Token.Consume H₁ R₁ E₁] [Token.Consume H₂ R₂ E₂]
  [∀ b, Token.ConsumeFrom H₁ (LexerCursor b) m₁]
  [∀ b, Token.ConsumeFrom H₂ (LexerCursor b) m₂] in
theorem lexBaseSelection_sim (input start hstart tokenStart h) :
    LSim L (· = ·)
      (lexBaseSelection (H := H₁) (m := m₁) (R := R₁) (E := E₁) (floor := floor) (low := low)
        input start hstart tokenStart h)
      (lexBaseSelection (H := H₂) (m := m₂) (R := R₂) (E := E₂)
        input start hstart tokenStart h) := by
  unfold lexBaseSelection; lsimW

theorem lexDigitRun_sim (hc : ConsumersW L) (input start run tokenStart base h) :
    LSim L (· = ·)
      (lexDigitRun (H := H₁) (m := m₁) (R := R₁) (E := E₁) (floor := floor) (low := low)
        input start run tokenStart base h)
      (lexDigitRun (H := H₂) (m := m₂) (R := R₂) (E := E₂)
        input start run tokenStart base h) := by
  unfold lexDigitRun; lsimW

theorem lexStringLiteralLegacy_sim (hc : ConsumersW L)
    (input : ByteSlice) (consumed origin : Nat) (horigin tokenStart base h) :
    LSim L (· = ·)
      (lexStringLiteralLegacy (H := H₁) (m := m₁) (R := R₁) (E := E₁) (floor := floor) (low := low)
        input consumed origin horigin tokenStart base h)
      (lexStringLiteralLegacy (H := H₂) (m := m₂) (R := R₂) (E := E₂)
        input consumed origin horigin tokenStart base h) := by
  rw [lexStringLiteralLegacy.eq_1, lexStringLiteralLegacy.eq_1]
  lsimW
  all_goals exact lexStringLiteralLegacy_sim hc _ _ _ _ _ _ _
termination_by input.size - consumed
decreasing_by
  all_goals lsim_omega [Lexer.Internal.WRustPort.Slice.le_runEnd,
    Lexer.Internal.WRustPort.Slice.le_runEndAll]

theorem lexStringLiteralFrom_sim (hc : ConsumersW L)
    (input : ByteSlice) (consumed origin : Nat) (horigin tokenStart base h) :
    LSim L (· = ·)
      (lexStringLiteralFrom (H := H₁) (m := m₁) (R := R₁) (E := E₁) (floor := floor) (low := low)
        input consumed origin horigin tokenStart base h)
      (lexStringLiteralFrom (H := H₂) (m := m₂) (R := R₂) (E := E₂)
        input consumed origin horigin tokenStart base h) := by
  rw [lexStringLiteralFrom.eq_1, lexStringLiteralFrom.eq_1]
  lsimW
  all_goals exact lexStringLiteralFrom_sim hc _ _ _ _ _ _ _
termination_by input.size - consumed
decreasing_by
  all_goals lsim_omega [Lexer.Internal.WRustPort.Slice.le_runEnd,
    Lexer.Internal.WRustPort.Slice.le_runEndAll]

theorem lexStringLiteral_sim (hc : ConsumersW L) (input start tokenStart base h) :
    LSim L (· = ·)
      (lexStringLiteral (H := H₁) (m := m₁) (R := R₁) (E := E₁) (floor := floor) (low := low)
        input start tokenStart base h)
      (lexStringLiteral (H := H₂) (m := m₂) (R := R₂) (E := E₂)
        input start tokenStart base h) := by
  unfold lexStringLiteral; lsimW

theorem lexSimpleSymbol_sim (hc : ConsumersW L) (input start tokenStart base h) :
    LSim L (· = ·)
      (lexSimpleSymbol (H := H₁) (m := m₁) (R := R₁) (E := E₁) (floor := floor) (low := low)
        input start tokenStart base h)
      (lexSimpleSymbol (H := H₂) (m := m₂) (R := R₂) (E := E₂)
        input start tokenStart base h) := by
  unfold lexSimpleSymbol; lsimW

theorem lexQuotedSymbol_sim (hc : ConsumersW L)
    (input : ByteSlice) (consumed origin : Nat) (horigin hconsumed tokenStart base h) :
    LSim L (· = ·)
      (lexQuotedSymbol (H := H₁) (m := m₁) (R := R₁) (E := E₁) (floor := floor) (low := low)
        input consumed origin horigin hconsumed tokenStart base h)
      (lexQuotedSymbol (H := H₂) (m := m₂) (R := R₂) (E := E₂)
        input consumed origin horigin hconsumed tokenStart base h) := by
  rw [lexQuotedSymbol.eq_1, lexQuotedSymbol.eq_1]
  lsimW
  all_goals exact lexQuotedSymbol_sim hc _ _ _ _ _ _ _ _
termination_by input.size - consumed
decreasing_by
  all_goals lsim_omega [Lexer.Internal.WRustPort.Slice.le_runEnd,
    Lexer.Internal.WRustPort.Slice.le_runEndAll]

theorem lexKeyword_sim (hc : ConsumersW L) (input start tokenStart base h) :
    LSim L (· = ·)
      (lexKeyword (H := H₁) (m := m₁) (R := R₁) (E := E₁) (floor := floor) (low := low)
        input start tokenStart base h)
      (lexKeyword (H := H₂) (m := m₂) (R := R₂) (E := E₂)
        input start tokenStart base h) := by
  unfold lexKeyword; lsimW

theorem lexQuotedSymbolClosed_sim (hc : ConsumersW L) (input start hstart tokenStart base h) :
    LSim L (· = ·)
      (lexQuotedSymbolClosed (H := H₁) (m := m₁) (R := R₁) (E := E₁) (floor := floor) (low := low)
        input start hstart tokenStart base h)
      (lexQuotedSymbolClosed (H := H₂) (m := m₂) (R := R₂) (E := E₂)
        input start hstart tokenStart base h) := by
  unfold lexQuotedSymbolClosed; lsimW

theorem lexWhitespace_sim (hc : ConsumersW L)
    (input : ByteSlice) (start origin : Nat) (horigin hstart tokenStart base h) :
    LSim L (· = ·)
      (lexWhitespace (H := H₁) (m := m₁) (R := R₁) (E := E₁) (floor := floor) (low := low)
        input start origin horigin hstart tokenStart base h)
      (lexWhitespace (H := H₂) (m := m₂) (R := R₂) (E := E₂)
        input start origin horigin hstart tokenStart base h) := by
  rw [lexWhitespace.eq_1, lexWhitespace.eq_1]
  lsimW
  all_goals exact lexWhitespace_sim hc _ _ _ _ _ _ _ _
termination_by input.size - start
decreasing_by
  all_goals lsim_omega [Lexer.Internal.WRustPort.Slice.le_runEnd,
    Lexer.Internal.WRustPort.Slice.le_runEndAll]

theorem lexComment_sim (hc : ConsumersW L) (input start hstart tokenStart base h) :
    LSim L (· = ·)
      (lexComment (H := H₁) (m := m₁) (R := R₁) (E := E₁) (floor := floor) (low := low)
        input start hstart tokenStart base h)
      (lexComment (H := H₂) (m := m₂) (R := R₂) (E := E₂)
        input start hstart tokenStart base h) := by
  unfold lexComment; lsimW

theorem afterStep_sim (hc : ConsumersW L) (input start hstart next) :
    LSim L (· = ·)
      (afterStep (H := H₁) (m := m₁) (R := R₁) (E := E₁) (floor := floor) (low := low)
        input start hstart next)
      (afterStep (H := H₂) (m := m₂) (R := R₂) (E := E₂)
        input start hstart next) := by
  unfold afterStep; lsimW

theorem lexStep_sim (hc : ConsumersW L) (input start hstart state tokenStart base hpending) :
    LSim L (· = ·)
      (lexStep (H := H₁) (m := m₁) (R := R₁) (E := E₁) (floor := floor) (low := low)
        input start hstart state tokenStart base hpending)
      (lexStep (H := H₂) (m := m₂) (R := R₂) (E := E₂)
        input start hstart state tokenStart base hpending) := by
  unfold lexStep; lsimW

end

end BSmtLib.Facts.Proofs.Reader.ParamW.Steps
