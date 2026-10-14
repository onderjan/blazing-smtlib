import BSmtLib.Facts.Proofs.Reader.Param.UnarySteps

/-!
# The facts of `UL` for the steps of the lexer

Every function of the lexer above the handover, taken apart by `usim`; the recursive ones by
recursion on what they recurse on, as in step 1.
-/

namespace BSmtLib.Facts.Proofs.Reader.Param.UnaryNormal

open BSmtLib.Lexer BSmtLib.Lexer.Internal
open BSmtLib.Facts.Proofs.Reader.Param.Unary

section

variable {consumer : BSmtLibSpec.Lexer.Consumer} {floor : Option Nat} {low : Nat}

theorem flushBatch_usim : UL (flushBatch : FM consumer floor low Unit) := by
  unfold flushBatch; usim

theorem handOverStored_usim (ty start «end» hend hfloor) :
    UL (handOverStored ty start «end» hend hfloor : FM consumer floor low Unit) := by
  unfold handOverStored; usim

theorem handOverEof_usim (location) : UL (handOverEof location : FM consumer none low Unit) := by
  unfold handOverEof; usim

theorem sinkStored_usim (ty tokenEnd start base h) :
    UL (sinkStored ty tokenEnd start base h : FM consumer floor low Unit) := by
  unfold sinkStored; usim

theorem finishDecimal_usim (tokenEnd next start base h) :
    UL (finishDecimal tokenEnd next start base h : FM consumer floor low Unit) := by
  unfold finishDecimal; usim

theorem finishNumeral_usim (tokenEnd start base h) :
    UL (finishNumeral tokenEnd start base h : FM consumer floor low Unit) := by
  unfold finishNumeral; usim

theorem finishDigitRun_usim (run tokenEnd next start base h) :
    UL (finishDigitRun run tokenEnd next start base h : FM consumer floor low Unit) := by
  unfold finishDigitRun; usim

theorem finishSimpleSymbol_usim (tokenEnd start base h) :
    UL (finishSimpleSymbol tokenEnd start base h : FM consumer floor low Unit) := by
  unfold finishSimpleSymbol; usim

theorem finishKeyword_usim (tokenEnd next start base h) :
    UL (finishKeyword tokenEnd next start base h : FM consumer floor low Unit) := by
  unfold finishKeyword; usim

theorem finishStringLiteral_usim (tokenEnd start base h) :
    UL (finishStringLiteral tokenEnd start base h : FM consumer floor low Unit) := by
  unfold finishStringLiteral; usim

theorem finishWhitespace_usim (tokenEnd start base h) :
    UL (finishWhitespace tokenEnd start base h : FM consumer floor low Unit) := by
  unfold finishWhitespace; usim

theorem flushHeld_usim (batch origin hbatch) :
    UL (flushHeld batch origin hbatch : FM consumer floor low _) := by
  unfold flushHeld; usim

theorem pushFast_usim (batch offset base ty contentStart contentStop start «end» emit hty hstart
    hend hframe hbatch) :
    UL (pushFast batch offset base ty contentStart contentStop start «end» emit hty hstart hend
      hframe hbatch : FM consumer floor low _) := by
  unfold pushFast; usim

theorem pushBorrowed_usim (batch offset base ty contentStart contentStop start tokenEnd hty hafter
    hend hfloor) :
    UL (pushBorrowed batch offset base ty contentStart contentStop start tokenEnd hty hafter hend
      hfloor : FM consumer floor low _) := by
  unfold pushBorrowed; usim

theorem storeUnfinishedSymbolRun_usim (input entry offset base index after runEndAt batch hframe
    hindex hrun hbatch) :
    UL (storeUnfinishedSymbolRun input entry offset base index after runEndAt batch hframe hindex
      hrun hbatch : FM consumer floor low Unit) := by
  unfold storeUnfinishedSymbolRun; usim

theorem startWhitespaceFrom_usim (input : CharClass.Input) (offset : Nat) (base index «end» : USize)
    (start : Span.Location) (batch : Token.TokenBatch) (hframe hstart hend hrun hbatch) :
    UL (startWhitespaceFrom input offset base index «end» start batch hframe hstart hend hrun
      hbatch : FM consumer floor low _) := by
  rw [startWhitespaceFrom.eq_1]
  usim
  all_goals exact startWhitespaceFrom_usim _ _ _ _ _ _ _ _ _ _ _ _
termination_by input.stop.toNat - «end».toNat
decreasing_by all_goals lsim_omega [CharClass.le_runEnd, CharClass.le_runEndAll]

theorem startWhitespace_usim (input offset base index batch hrun hframe hindex hbatch) :
    UL (startWhitespace input offset base index batch hrun hframe hindex hbatch :
      FM consumer floor low _) := by
  unfold startWhitespace; usim

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 8192 in
theorem lexNormalFrom_usim (input : CharClass.Input) (offset : Nat) (base index : USize)
    (batch : Token.TokenBatch) (hframe hindex hbatch) (origin : USize) (horigin) :
    UL (lexNormalFrom input offset base index batch hframe hindex hbatch origin horigin :
      FM consumer floor low _) := by
  rw [lexNormalFrom.eq_1]
  usim
  all_goals exact lexNormalFrom_usim _ _ _ _ _ _ _ _ _ _
termination_by input.stop.toNat - index.toNat
decreasing_by all_goals lsim_omega [CharClass.le_runEnd, CharClass.le_runEndAll]

theorem lexNormal_usim (input start hstart) :
    UL (lexNormal input start hstart : FM consumer floor low _) := by
  unfold lexNormal; usim

theorem lexFractionFrom_usim (input start tokenStart base h) :
    UL (lexFractionFrom input start tokenStart base h : FM consumer floor low _) := by
  unfold lexFractionFrom; usim

theorem lexNumeralOrDecimal_usim (input start tokenStart base h) :
    UL (lexNumeralOrDecimal input start tokenStart base h : FM consumer floor low _) := by
  unfold lexNumeralOrDecimal; usim

theorem lexBaseSelection_usim (input start hstart tokenStart h) :
    UL (lexBaseSelection input start hstart tokenStart h : FM consumer floor low _) := by
  unfold lexBaseSelection; usim

theorem lexDigitRun_usim (input start run tokenStart base h) :
    UL (lexDigitRun input start run tokenStart base h : FM consumer floor low _) := by
  unfold lexDigitRun; usim

theorem lexStringLiteralLegacy_usim (input : CharClass.Input) (consumed origin : USize)
    (horigin tokenStart base h) :
    UL (lexStringLiteralLegacy input consumed origin horigin tokenStart base h :
      FM consumer floor low _) := by
  rw [lexStringLiteralLegacy.eq_1]
  usim
  all_goals exact lexStringLiteralLegacy_usim _ _ _ _ _ _ _
termination_by input.stop.toNat - consumed.toNat
decreasing_by all_goals lsim_omega [CharClass.le_runEnd, CharClass.le_runEndAll]

theorem lexStringLiteralFrom_usim (input : CharClass.Input) (consumed origin : USize)
    (horigin tokenStart base h) :
    UL (lexStringLiteralFrom input consumed origin horigin tokenStart base h :
      FM consumer floor low _) := by
  rw [lexStringLiteralFrom.eq_1]
  usim
  all_goals exact lexStringLiteralFrom_usim _ _ _ _ _ _ _
termination_by input.stop.toNat - consumed.toNat
decreasing_by all_goals lsim_omega [CharClass.le_runEnd, CharClass.le_runEndAll]

theorem lexStringLiteral_usim (input start tokenStart base h) :
    UL (lexStringLiteral input start tokenStart base h : FM consumer floor low _) := by
  unfold lexStringLiteral; usim

theorem lexSimpleSymbol_usim (input start tokenStart base h) :
    UL (lexSimpleSymbol input start tokenStart base h : FM consumer floor low _) := by
  unfold lexSimpleSymbol; usim

theorem lexQuotedSymbol_usim (input : CharClass.Input) (consumed origin : USize)
    (horigin hconsumed tokenStart base h) :
    UL (lexQuotedSymbol input consumed origin horigin hconsumed tokenStart base h :
      FM consumer floor low _) := by
  rw [lexQuotedSymbol.eq_1]
  usim
  all_goals exact lexQuotedSymbol_usim _ _ _ _ _ _ _ _
termination_by input.stop.toNat - consumed.toNat
decreasing_by all_goals lsim_omega [CharClass.le_runEnd, CharClass.le_runEndAll]

theorem lexKeyword_usim (input start tokenStart base h) :
    UL (lexKeyword input start tokenStart base h : FM consumer floor low _) := by
  unfold lexKeyword; usim

theorem lexQuotedSymbolClosed_usim (input start hstart tokenStart base h) :
    UL (lexQuotedSymbolClosed input start hstart tokenStart base h : FM consumer floor low _) := by
  unfold lexQuotedSymbolClosed; usim

theorem lexWhitespace_usim (input : CharClass.Input) (start origin : USize)
    (horigin hstart tokenStart base h) :
    UL (lexWhitespace input start origin horigin hstart tokenStart base h :
      FM consumer floor low _) := by
  rw [lexWhitespace.eq_1]
  usim
  all_goals exact lexWhitespace_usim _ _ _ _ _ _ _ _
termination_by input.stop.toNat - start.toNat
decreasing_by all_goals lsim_omega [CharClass.le_runEnd, CharClass.le_runEndAll]

theorem lexComment_usim (input start hstart tokenStart base h) :
    UL (lexComment input start hstart tokenStart base h : FM consumer floor low _) := by
  unfold lexComment; usim

theorem afterStep_usim (input start hstart next) :
    UL (afterStep input start hstart next : FM consumer floor low _) := by
  unfold afterStep; usim

theorem lexStep_usim (input start hstart state tokenStart base hpending) :
    UL (lexStep input start hstart state tokenStart base hpending : FM consumer floor low _) := by
  unfold lexStep; usim

end

end BSmtLib.Facts.Proofs.Reader.Param.UnaryNormal
