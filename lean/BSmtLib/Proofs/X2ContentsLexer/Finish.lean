import BSmtLib.Proofs.X2ContentsLexer.HandOver

/-!
# The finishing of a stored token by the library's lexer and the lexer with the content buffer
-/

namespace BSmtLib.Proofs.X2ContentsLexer

open BSmtLib.Proofs.Simulation

section

variable {H : Type} {m : Type → Type} {R E : Type} [Monad m] [LawfulMonad m] [Consume H m R E]
  {floor : Option Nat} {low : Nat} (start : Nat) (b : USize)

omit [Consume H m R E] in
theorem locationFrom_sim (base position : USize) (hb : start ≤ base.toNat)
    (hp : base.toNat ≤ position.toNat) :
    SimP (BaseIs b) (fun _ => BaseIs b) (boundMap start (floor := floor) (low := low)) id
      (BSmtLib.Lexer.Internal.locationFrom (H := H) (m := m) (R := R) (E := E) base position)
      (Lexer.X2Contents.locationFrom (ix start base) (ix start position)) := by
  unfold BSmtLib.Lexer.Internal.locationFrom Lexer.X2Contents.locationFrom
  refine getCore_bind start b fun c _ => SimP.pure (fun _ h => h) ?_
  simp only [id, coreMap, sub_toNat_ix hb hp]

theorem sinkStored_sim (ty : TokenCategory) (hty : ty ≠ .endOfFile)
    (te : BSmtLib.Lexer.TokenEnd) (s : Location) (base : USize) (hb : start ≤ base.toNat)
    (hp : base.toNat ≤ te.position.toNat) (h h') :
    SimP (BaseIs b) (fun _ => BaseIs b) (boundMap start (floor := floor) (low := low)) id
      (BSmtLib.Lexer.Internal.sinkStored (H := H) (m := m) (R := R) (E := E) ty hty te s base h)
      (Lexer.X2Contents.sinkStored ty hty (endMap start te) s (ix start base) h') := by
  unfold BSmtLib.Lexer.Internal.sinkStored Lexer.X2Contents.sinkStored
  refine SimP.seq (locationFrom_sim start b base te.position hb hp) fun x => ?_
  obtain ⟨e, he⟩ := x
  exact handOverStored_sim start b _ _ _ _ _ _ _

/-- Takes the steps of finishing a stored token, as long as they are the same on both sides; the
conditions on the positions are among the hypotheses. -/
local macro "sim_finish" : tactic => `(tactic| repeat (first
    | (with_reducible refine getCore_bind _ _ fun _ _ => ?_)
    | dsimp only
    | (with_reducible refine SimP.seq (fail_sim _ (ψ := id) _ _ _ ‹_› ‹_› ‹_› _) fun _ => ?_)
    | (with_reducible refine SimP.seq (expectDelimiter_sim _ _ _ _ ‹_› ‹_› ‹_›) fun _ => ?_)
    | (with_reducible exact sinkStored_sim _ _ _ _ _ _ _ ‹_› ‹_› _ _)
    | (refine SimP.ite Iff.rfl (fun _ => ?_) fun _ => ?_)))

/-- What a finishing step needs of the positions: the base is in the slice, and the token end
is at it or after it, with room for the byte after it. -/
structure EndOk (start : Nat) (b base : USize) (te : BSmtLib.Lexer.TokenEnd) : Prop where
  hb : start ≤ b.toNat
  hbase : start ≤ base.toNat
  hp : b.toNat ≤ te.position.toNat
  hbp : base.toNat ≤ te.position.toNat
  hno : te.position.toNat + 1 < USize.size

theorem finishDecimal_sim (te : BSmtLib.Lexer.TokenEnd) (next : Option UInt8) (s : Location)
    (base : USize) (ok : EndOk start b base te) (h h') :
    SimP (BaseIs b) (fun _ => BaseIs b) (boundMap start (floor := floor) (low := low)) id
      (BSmtLib.Lexer.Internal.finishDecimal (H := H) (m := m) (R := R) (E := E) te next s base h)
      (Lexer.X2Contents.finishDecimal (endMap start te) next s (ix start base) h') := by
  have := ok.hb; have := ok.hbase; have := ok.hp; have := ok.hbp; have := ok.hno
  unfold BSmtLib.Lexer.Internal.finishDecimal Lexer.X2Contents.finishDecimal
  cases next <;> sim_finish

theorem finishNumeral_sim (te : BSmtLib.Lexer.TokenEnd) (s : Location) (base : USize)
    (ok : EndOk start b base te) (h h') :
    SimP (BaseIs b) (fun _ => BaseIs b) (boundMap start (floor := floor) (low := low)) id
      (BSmtLib.Lexer.Internal.finishNumeral (H := H) (m := m) (R := R) (E := E) te s base h)
      (Lexer.X2Contents.finishNumeral (endMap start te) s (ix start base) h') :=
  sinkStored_sim start b _ _ _ _ _ ok.hbase ok.hbp _ _

theorem finishDigitRun_sim (run : Lexer.DigitRun) (hrun hrun') (te : BSmtLib.Lexer.TokenEnd)
    (next : Option UInt8) (s : Location) (base : USize) (ok : EndOk start b base te) (h h') :
    SimP (BaseIs b) (fun _ => BaseIs b) (boundMap start (floor := floor) (low := low)) id
      (BSmtLib.Lexer.Internal.finishDigitRun (H := H) (m := m) (R := R) (E := E) run hrun te next
        s base h)
      (Lexer.X2Contents.finishDigitRun run hrun' (endMap start te) next s (ix start base) h') := by
  have := ok.hb; have := ok.hbase; have := ok.hp; have := ok.hbp; have := ok.hno
  unfold BSmtLib.Lexer.Internal.finishDigitRun Lexer.X2Contents.finishDigitRun
  cases next <;> sim_finish

theorem finishSimpleSymbol_sim (te : BSmtLib.Lexer.TokenEnd) (s : Location) (base : USize)
    (ok : EndOk start b base te) (h h') :
    SimP (BaseIs b) (fun _ => BaseIs b) (boundMap start (floor := floor) (low := low)) id
      (BSmtLib.Lexer.Internal.finishSimpleSymbol (H := H) (m := m) (R := R) (E := E) te s base h)
      (Lexer.X2Contents.finishSimpleSymbol (endMap start te) s (ix start base) h') :=
  sinkStored_sim start b _ _ _ _ _ ok.hbase ok.hbp _ _

theorem finishKeyword_sim (te : BSmtLib.Lexer.TokenEnd) (next : Option UInt8) (s : Location)
    (base : USize) (ok : EndOk start b base te) (h h') :
    SimP (BaseIs b) (fun _ => BaseIs b) (boundMap start (floor := floor) (low := low)) id
      (BSmtLib.Lexer.Internal.finishKeyword (H := H) (m := m) (R := R) (E := E) te next s base h)
      (Lexer.X2Contents.finishKeyword (endMap start te) next s (ix start base) h') := by
  have := ok.hb; have := ok.hbase; have := ok.hp; have := ok.hbp; have := ok.hno
  unfold BSmtLib.Lexer.Internal.finishKeyword Lexer.X2Contents.finishKeyword
  cases next <;> sim_finish

theorem finishStringLiteral_sim (te : BSmtLib.Lexer.TokenEnd) (s : Location) (base : USize)
    (ok : EndOk start b base te) (h h') :
    SimP (BaseIs b) (fun _ => BaseIs b) (boundMap start (floor := floor) (low := low)) id
      (BSmtLib.Lexer.Internal.finishStringLiteral (H := H) (m := m) (R := R) (E := E) te s base
        h)
      (Lexer.X2Contents.finishStringLiteral (endMap start te) s (ix start base) h') :=
  sinkStored_sim start b _ _ _ _ _ ok.hbase ok.hbp _ _

theorem finishWhitespace_sim (te : BSmtLib.Lexer.TokenEnd) (s : Location) (base : USize)
    (ok : EndOk start b base te) (h h') :
    SimP (BaseIs b) (fun _ => BaseIs b) (boundMap start (floor := floor) (low := low)) id
      (BSmtLib.Lexer.Internal.finishWhitespace (H := H) (m := m) (R := R) (E := E) te s base h)
      (Lexer.X2Contents.finishWhitespace (endMap start te) s (ix start base) h') :=
  sinkStored_sim start b _ _ _ _ _ ok.hbase ok.hbp _ _

end

end BSmtLib.Proofs.X2ContentsLexer
