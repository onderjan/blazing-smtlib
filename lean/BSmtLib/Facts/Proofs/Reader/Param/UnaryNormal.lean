module

public import BSmtLib.Facts.Proofs.Reader.Param.UnarySteps
import all BSmtLib.Lexer

@[expose] public section

/-!
# The facts of `UL` for the steps of the lexer

Every function of the lexer above the handover, taken apart by `usim`; the recursive ones by
recursion on what they recurse on, as in step 1.
-/

namespace BSmtLib.Facts.Proofs.Reader.Param.UnaryNormal

open BSmtLib.Lexer
open BSmtLib.Facts.Proofs.Reader.Param.Unary

section

variable {F σ R E : Type} [Token.Consume F R (Option E)]
  [∀ b, Token.ConsumeFrom F (Token.BatchCursor b) (StateM σ)] [Watched F σ R E]
  {floor : Option Nat} {low : Nat}

theorem flushBatch_usim : UL (Internal.flushBatch : FM F σ floor low Unit) := by
  unfold Internal.flushBatch; usim

theorem handOverStored_usim (ty start «end» hend hfloor) :
    UL (Internal.handOverStored ty start «end» hend hfloor : FM F σ floor low Unit) := by
  unfold Internal.handOverStored; usim

theorem handOverEof_usim (location) : UL (Internal.handOverEof location : FM F σ none low Unit) :=
    by
  unfold Internal.handOverEof; usim

theorem sinkStored_usim (ty tokenEnd start base h) :
    UL (Internal.sinkStored ty tokenEnd start base h : FM F σ floor low Unit) := by
  unfold Internal.sinkStored; usim

theorem finishDecimal_usim (tokenEnd next start base h) :
    UL (Internal.finishDecimal tokenEnd next start base h : FM F σ floor low Unit) := by
  unfold Internal.finishDecimal; usim

theorem finishNumeral_usim (tokenEnd start base h) :
    UL (Internal.finishNumeral tokenEnd start base h : FM F σ floor low Unit) := by
  unfold Internal.finishNumeral; usim

theorem finishDigitRun_usim (run tokenEnd next start base h) :
    UL (Internal.finishDigitRun run tokenEnd next start base h : FM F σ floor low Unit) := by
  unfold Internal.finishDigitRun; usim

theorem finishSimpleSymbol_usim (tokenEnd start base h) :
    UL (Internal.finishSimpleSymbol tokenEnd start base h : FM F σ floor low Unit) := by
  unfold Internal.finishSimpleSymbol; usim

theorem finishKeyword_usim (tokenEnd next start base h) :
    UL (Internal.finishKeyword tokenEnd next start base h : FM F σ floor low Unit) := by
  unfold Internal.finishKeyword; usim

theorem finishStringLiteral_usim (tokenEnd start base h) :
    UL (Internal.finishStringLiteral tokenEnd start base h : FM F σ floor low Unit) := by
  unfold Internal.finishStringLiteral; usim

theorem finishWhitespace_usim (tokenEnd start base h) :
    UL (Internal.finishWhitespace tokenEnd start base h : FM F σ floor low Unit) := by
  unfold Internal.finishWhitespace; usim

theorem flushHeld_usim (batch origin hbatch) :
    UL (Internal.flushHeld batch origin hbatch : FM F σ floor low _) := by
  unfold Internal.flushHeld; usim

theorem pushFast_usim (batch offset base ty contentStart contentStop start «end» emit hty hstart
    hend hframe hbatch) :
    UL (Internal.pushFast batch offset base ty contentStart contentStop start «end» emit hty hstart
        hend
      hframe hbatch : FM F σ floor low _) := by
  unfold Internal.pushFast; usim

theorem pushBorrowed_usim (batch offset base ty contentStart contentStop start tokenEnd hty hafter
    hend hfloor) :
    UL (Internal.pushBorrowed batch offset base ty contentStart contentStop start tokenEnd hty
        hafter hend
      hfloor : FM F σ floor low _) := by
  unfold Internal.pushBorrowed; usim

theorem storeUnfinishedSymbolRun_usim (input entry offset base index after runEndAt batch hframe
    hindex hrun hbatch) :
    UL (Internal.storeUnfinishedSymbolRun input entry offset base index after runEndAt batch hframe
        hindex
      hrun hbatch : FM F σ floor low Unit) := by
  unfold Internal.storeUnfinishedSymbolRun; usim

theorem startWhitespaceFrom_usim (input : CharClass.Input) (offset : Nat) (base index «end» : USize)
    (start : Span.Location) (batch : Token.TokenBatch) (hframe hstart hend hrun hbatch) :
    UL (Internal.startWhitespaceFrom input offset base index «end» start batch hframe hstart hend
        hrun
      hbatch : FM F σ floor low _) := by
  rw [Internal.startWhitespaceFrom.eq_1]
  usim
  all_goals exact startWhitespaceFrom_usim _ _ _ _ _ _ _ _ _ _ _ _
termination_by input.stop.toNat - «end».toNat
decreasing_by all_goals lsim_omega [CharClass.le_runEnd, CharClass.le_runEndAll]

theorem startWhitespace_usim (input offset base index batch hrun hframe hindex hbatch) :
    UL (Internal.startWhitespace input offset base index batch hrun hframe hindex hbatch :
      FM F σ floor low _) := by
  unfold Internal.startWhitespace; usim

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 8192 in
theorem lexNormalFrom_usim (input : CharClass.Input) (offset : Nat) (base index : USize)
    (batch : Token.TokenBatch) (hframe hindex hbatch) (origin : USize) (horigin) :
    UL (Internal.lexNormalFrom input offset base index batch hframe hindex hbatch origin horigin :
      FM F σ floor low _) := by
  rw [Internal.lexNormalFrom.eq_1]
  usim
  all_goals exact lexNormalFrom_usim _ _ _ _ _ _ _ _ _ _
termination_by input.stop.toNat - index.toNat
decreasing_by all_goals lsim_omega [CharClass.le_runEnd, CharClass.le_runEndAll]

theorem lexNormal_usim (input start hstart) :
    UL (Internal.lexNormal input start hstart : FM F σ floor low _) := by
  unfold Internal.lexNormal; usim

theorem lexFractionFrom_usim (input start tokenStart base h) :
    UL (Internal.lexFractionFrom input start tokenStart base h : FM F σ floor low _) := by
  unfold Internal.lexFractionFrom; usim

theorem lexNumeralOrDecimal_usim (input start tokenStart base h) :
    UL (Internal.lexNumeralOrDecimal input start tokenStart base h : FM F σ floor low _) := by
  unfold Internal.lexNumeralOrDecimal; usim

theorem lexBaseSelection_usim (input start hstart tokenStart h) :
    UL (Internal.lexBaseSelection input start hstart tokenStart h : FM F σ floor low _) := by
  unfold Internal.lexBaseSelection; usim

theorem lexDigitRun_usim (input start run tokenStart base h) :
    UL (Internal.lexDigitRun input start run tokenStart base h : FM F σ floor low _) := by
  unfold Internal.lexDigitRun; usim

theorem lexStringLiteralLegacy_usim (input : CharClass.Input) (consumed origin : USize)
    (horigin tokenStart base h) :
    UL (Internal.lexStringLiteralLegacy input consumed origin horigin tokenStart base h :
      FM F σ floor low _) := by
  rw [Internal.lexStringLiteralLegacy.eq_1]
  usim
  all_goals exact lexStringLiteralLegacy_usim _ _ _ _ _ _ _
termination_by input.stop.toNat - consumed.toNat
decreasing_by all_goals lsim_omega [CharClass.le_runEnd, CharClass.le_runEndAll]

theorem lexStringLiteralFrom_usim (input : CharClass.Input) (consumed origin : USize)
    (horigin tokenStart base h) :
    UL (Internal.lexStringLiteralFrom input consumed origin horigin tokenStart base h :
      FM F σ floor low _) := by
  rw [Internal.lexStringLiteralFrom.eq_1]
  usim
  all_goals exact lexStringLiteralFrom_usim _ _ _ _ _ _ _
termination_by input.stop.toNat - consumed.toNat
decreasing_by all_goals lsim_omega [CharClass.le_runEnd, CharClass.le_runEndAll]

theorem lexStringLiteral_usim (input start tokenStart base h) :
    UL (Internal.lexStringLiteral input start tokenStart base h : FM F σ floor low _) := by
  unfold Internal.lexStringLiteral; usim

theorem lexSimpleSymbol_usim (input start tokenStart base h) :
    UL (Internal.lexSimpleSymbol input start tokenStart base h : FM F σ floor low _) := by
  unfold Internal.lexSimpleSymbol; usim

theorem lexQuotedSymbol_usim (input : CharClass.Input) (consumed origin : USize)
    (horigin hconsumed tokenStart base h) :
    UL (Internal.lexQuotedSymbol input consumed origin horigin hconsumed tokenStart base h :
      FM F σ floor low _) := by
  rw [Internal.lexQuotedSymbol.eq_1]
  usim
  all_goals exact lexQuotedSymbol_usim _ _ _ _ _ _ _ _
termination_by input.stop.toNat - consumed.toNat
decreasing_by all_goals lsim_omega [CharClass.le_runEnd, CharClass.le_runEndAll]

theorem lexKeyword_usim (input start tokenStart base h) :
    UL (Internal.lexKeyword input start tokenStart base h : FM F σ floor low _) := by
  unfold Internal.lexKeyword; usim

theorem lexQuotedSymbolClosed_usim (input start hstart tokenStart base h) :
    UL (Internal.lexQuotedSymbolClosed input start hstart tokenStart base h : FM F σ floor low _)
        := by
  unfold Internal.lexQuotedSymbolClosed; usim

theorem lexWhitespace_usim (input : CharClass.Input) (start origin : USize)
    (horigin hstart tokenStart base h) :
    UL (Internal.lexWhitespace input start origin horigin hstart tokenStart base h :
      FM F σ floor low _) := by
  rw [Internal.lexWhitespace.eq_1]
  usim
  all_goals exact lexWhitespace_usim _ _ _ _ _ _ _ _
termination_by input.stop.toNat - start.toNat
decreasing_by all_goals lsim_omega [CharClass.le_runEnd, CharClass.le_runEndAll]

theorem lexComment_usim (input start hstart tokenStart base h) :
    UL (Internal.lexComment input start hstart tokenStart base h : FM F σ floor low _) := by
  unfold Internal.lexComment; usim

theorem afterStep_usim (input start hstart next) :
    UL (Internal.afterStep input start hstart next : FM F σ floor low _) := by
  unfold Internal.afterStep; usim

theorem lexStep_usim (input start hstart state tokenStart base hpending) :
    UL (Internal.lexStep input start hstart state tokenStart base hpending : FM F σ floor low _) :=
        by
  unfold Internal.lexStep; usim

end

end BSmtLib.Facts.Proofs.Reader.Param.UnaryNormal
