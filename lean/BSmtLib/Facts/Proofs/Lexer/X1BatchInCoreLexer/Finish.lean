import BSmtLib.Facts.Proofs.Lexer.X1BatchInCoreLexer.HandOver

/-!
# The finishing of a stored token by the library's lexer and `X1BatchInCore`
-/

namespace BSmtLib.Facts.Proofs.Lexer.X1BatchInCoreLexer.Finish

open BSmtLib.Facts.Proofs.Lexer.Simulation.Steps
open BSmtLib.Facts.Proofs.Lexer.X1BatchInCoreLexer.Core
open BSmtLib.Facts.Proofs.Lexer.X1BatchInCoreLexer.HandOver

section

variable {H : Type} {m : Type → Type} {R E : Type} [Monad m] [LawfulMonad m] [Token.Consume H R E]
  [∀ batch, Token.ConsumeFrom H (Token.BatchCursor batch) m]
  {floor : Option Nat} {low : Nat} (start : Nat) (b : USize)

omit [Token.Consume H R E] [∀ batch, Token.ConsumeFrom H (Token.BatchCursor batch) m] in
theorem locationFrom_sim (base position : USize) (hb : start ≤ base.toNat)
    (hp : base.toNat ≤ position.toNat) :
    SimP (BaseIs b) (fun _ => BaseIs b) (boundMap start (floor := floor) (low := low)) id
      (BSmtLib.Lexer.Internal.locationFrom (H := H) (m := m) (R := R) (E := E) base position)
      (Lexer.Internal.WRustPort.locationFrom (ix start base) (ix start position)) := by
  unfold BSmtLib.Lexer.Internal.locationFrom Lexer.Internal.WRustPort.locationFrom
  refine getCore_bind start b fun c _ => SimP.pure (fun _ h => h) ?_
  simp only [id, coreMap, sub_toNat_ix hb hp]

theorem sinkStored_sim (ty : Token.TokenCategory)
    (te : Lexer.Helpers.TokenEnd) (s : Span.Location) (base : USize) (hb : start ≤ base.toNat)
    (hp : base.toNat ≤ te.position.toNat) (h h') :
    SimP (BaseIs b) (fun _ => BaseIs b) (boundMap start (floor := floor) (low := low)) id
      (BSmtLib.Lexer.Internal.sinkStored (H := H) (m := m) (R := R) (E := E) ty te s base h)
      (Lexer.Internal.WRustPort.sinkStored ty (endMap start te) s (ix start base) h') := by
  unfold BSmtLib.Lexer.Internal.sinkStored Lexer.Internal.WRustPort.sinkStored
  refine SimP.seq (locationFrom_sim start b base te.position hb hp) fun x => ?_
  obtain ⟨e, he⟩ := x
  exact handOverStored_sim start b _ _ _ _ _ _

/-- Takes the steps of finishing a stored token, as long as they are the same on both sides; the
conditions on the positions are among the hypotheses. -/
local macro "sim_finish" : tactic => `(tactic| repeat (first
    | (with_reducible refine getCore_bind _ _ fun _ _ => ?_)
    | dsimp only
    | (with_reducible exact fail_bind_sim _ (ψ := id) _ _ _ ‹_› ‹_› ‹_› _ _ _)
    | (with_reducible refine SimP.seq (expectDelimiter_sim _ _ _ _ ‹_› ‹_› ‹_›) fun _ => ?_)
    | (with_reducible exact sinkStored_sim _ _ _ _ _ _ ‹_› ‹_› _ _)
    | (refine SimP.ite Iff.rfl (fun _ => ?_) fun _ => ?_)))

/-- What a finishing step needs of the positions: the base is in the slice, and the token end
is at it or after it, with room for the byte after it. -/
structure EndOk (start : Nat) (b base : USize) (te : Lexer.Helpers.TokenEnd) : Prop where
  hb : start ≤ b.toNat
  hbase : start ≤ base.toNat
  hp : b.toNat ≤ te.position.toNat
  hbp : base.toNat ≤ te.position.toNat
  hno : te.position.toNat + 1 < USize.size

theorem finishDecimal_sim (te : Lexer.Helpers.TokenEnd) (next : Option UInt8) (s : Span.Location)
    (base : USize) (ok : EndOk start b base te) (h h') :
    SimP (BaseIs b) (fun _ => BaseIs b) (boundMap start (floor := floor) (low := low)) id
      (BSmtLib.Lexer.Internal.finishDecimal (H := H) (m := m) (R := R) (E := E) te next s base h)
      (Lexer.Internal.WRustPort.finishDecimal (endMap start te) next s (ix start base) h') := by
  have := ok.hb; have := ok.hbase; have := ok.hp; have := ok.hbp; have := ok.hno
  unfold BSmtLib.Lexer.Internal.finishDecimal Lexer.Internal.WRustPort.finishDecimal
  cases next <;> sim_finish

theorem finishNumeral_sim (te : Lexer.Helpers.TokenEnd) (s : Span.Location) (base : USize)
    (ok : EndOk start b base te) (h h') :
    SimP (BaseIs b) (fun _ => BaseIs b) (boundMap start (floor := floor) (low := low)) id
      (BSmtLib.Lexer.Internal.finishNumeral (H := H) (m := m) (R := R) (E := E) te s base h)
      (Lexer.Internal.WRustPort.finishNumeral (endMap start te) s (ix start base) h') :=
  sinkStored_sim start b _ _ _ _ ok.hbase ok.hbp _ _

theorem finishDigitRun_sim (run : Lexer.Helpers.DigitRun) (te : Lexer.Helpers.TokenEnd)
    (next : Option UInt8) (s : Span.Location) (base : USize) (ok : EndOk start b base te) (h h') :
    SimP (BaseIs b) (fun _ => BaseIs b) (boundMap start (floor := floor) (low := low)) id
      (BSmtLib.Lexer.Internal.finishDigitRun (H := H) (m := m) (R := R) (E := E) run te next
        s base h)
      (Lexer.Internal.WRustPort.finishDigitRun run (endMap start te) next s (ix start base) h') :=
          by
  have := ok.hb; have := ok.hbase; have := ok.hp; have := ok.hbp; have := ok.hno
  unfold BSmtLib.Lexer.Internal.finishDigitRun Lexer.Internal.WRustPort.finishDigitRun
  cases next <;> sim_finish

theorem finishSimpleSymbol_sim (te : Lexer.Helpers.TokenEnd) (s : Span.Location) (base : USize)
    (ok : EndOk start b base te) (h h') :
    SimP (BaseIs b) (fun _ => BaseIs b) (boundMap start (floor := floor) (low := low)) id
      (BSmtLib.Lexer.Internal.finishSimpleSymbol (H := H) (m := m) (R := R) (E := E) te s base h)
      (Lexer.Internal.WRustPort.finishSimpleSymbol (endMap start te) s (ix start base) h') :=
  sinkStored_sim start b _ _ _ _ ok.hbase ok.hbp _ _

theorem finishKeyword_sim (te : Lexer.Helpers.TokenEnd) (next : Option UInt8) (s : Span.Location)
    (base : USize) (ok : EndOk start b base te) (h h') :
    SimP (BaseIs b) (fun _ => BaseIs b) (boundMap start (floor := floor) (low := low)) id
      (BSmtLib.Lexer.Internal.finishKeyword (H := H) (m := m) (R := R) (E := E) te next s base h)
      (Lexer.Internal.WRustPort.finishKeyword (endMap start te) next s (ix start base) h') := by
  have := ok.hb; have := ok.hbase; have := ok.hp; have := ok.hbp; have := ok.hno
  unfold BSmtLib.Lexer.Internal.finishKeyword Lexer.Internal.WRustPort.finishKeyword
  cases next <;> sim_finish

theorem finishStringLiteral_sim (te : Lexer.Helpers.TokenEnd) (s : Span.Location) (base : USize)
    (ok : EndOk start b base te) (h h') :
    SimP (BaseIs b) (fun _ => BaseIs b) (boundMap start (floor := floor) (low := low)) id
      (BSmtLib.Lexer.Internal.finishStringLiteral (H := H) (m := m) (R := R) (E := E) te s base
        h)
      (Lexer.Internal.WRustPort.finishStringLiteral (endMap start te) s (ix start base) h') :=
  sinkStored_sim start b _ _ _ _ ok.hbase ok.hbp _ _

theorem finishWhitespace_sim (te : Lexer.Helpers.TokenEnd) (s : Span.Location) (base : USize)
    (ok : EndOk start b base te) (h h') :
    SimP (BaseIs b) (fun _ => BaseIs b) (boundMap start (floor := floor) (low := low)) id
      (BSmtLib.Lexer.Internal.finishWhitespace (H := H) (m := m) (R := R) (E := E) te s base h)
      (Lexer.Internal.WRustPort.finishWhitespace (endMap start te) s (ix start base) h') :=
  sinkStored_sim start b _ _ _ _ ok.hbase ok.hbp _ _

end

end BSmtLib.Facts.Proofs.Lexer.X1BatchInCoreLexer.Finish
