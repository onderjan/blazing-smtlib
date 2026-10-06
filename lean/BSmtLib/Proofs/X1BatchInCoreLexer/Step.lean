import BSmtLib.Proofs.X1BatchInCoreLexer.Normal

/-!
# The step of the library's lexer and of `X1BatchInCore`

`lexStep` dispatches on the lexer state to the loop of the normal state (`Normal`) or to the step
of the token in progress (`Steps`), and `afterStep` goes on in the normal state where a step that
finished a token consumed nothing. Both are simulated here from the position of the lexer's base,
where the loop over the slice calls them. After a step the base is in the slice, at or before the
position returned: the steps of a token in progress keep it, and the normal state leaves it at
that position.
-/

namespace BSmtLib.Proofs.X1BatchInCoreLexer

open BSmtLib.Proofs.Simulation

/-- What a step leaves: the base in the slice that starts at `start`, at or before the position
returned. -/
abbrev StepPost (start : Nat) {floor : Option Nat} {low : Nat} {lo : USize}
    (r : {next : USize // lo.toNat < next.toNat}) (s : ZS floor low) : Prop :=
  start ≤ s.val.base.toNat ∧ s.val.base.toNat ≤ r.val.toNat

section

variable {H : Type} {m : Type → Type} {R E : Type} [Monad m] [LawfulMonad m] [Consume H m R E]
  {floor : Option Nat} {low : Nat} (b : USize)

theorem afterStep_sim (slice : ByteSlice) (h : slice.stop < USize.size) (start : USize)
    (start' : Nat) (es : ix slice.start start = start') (hb : slice.start ≤ b.toNat)
    (hbs : b = start) (hstart hstart') (r : {next : USize // start.toNat ≤ next.toNat}) :
    SimP (BaseIs b) (StepPost slice.start) (boundMap slice.start (floor := floor) (low := low))
      (nextMapLt slice.start es (hbs ▸ hb))
      (BSmtLib.Lexer.Internal.afterStep (H := H) (m := m) (R := R) (E := E)
        (inputOf slice h) start hstart r)
      (Lexer.WRustPort.afterStep slice start' hstart' (nextMap slice.start es r)) := by
  unfold BSmtLib.Lexer.Internal.afterStep Lexer.WRustPort.afterStep
  have hr := r.property
  have hs : slice.start ≤ start.toNat := hbs ▸ hb
  refine SimP.dite (by subst es; simp only [nextMap, ix]; omega)
    (fun h1 _ => SimP.pure (fun s hs' => ⟨by rw [hs']; exact hb, by rw [hs', hbs]; omega⟩)
      (Subtype.ext rfl))
    fun _ _ => SimP.mono (fun _ h => h)
      (fun r' s hs' => ⟨by rw [hs']; have := r'.property; omega, by rw [hs']; exact Nat.le_refl _⟩)
      (lexNormal_sim b slice h start start' es hb hbs hstart hstart')

theorem lexStep_sim (slice : ByteSlice) (h : slice.stop < USize.size) (start : USize)
    (start' : Nat) (es : ix slice.start start = start') (hb : slice.start ≤ b.toNat)
    (hbs : b = start) (hstart hstart') (state : Lexer.LexerState) (tokenStart : Location)
    (base : USize) (hbase : b = base) (hpending hpending') :
    SimP (BaseIs b) (StepPost slice.start) (boundMap slice.start (floor := floor) (low := low))
      (nextMapLt slice.start es (hbs ▸ hb))
      (BSmtLib.Lexer.Internal.lexStep (H := H) (m := m) (R := R) (E := E)
        (inputOf slice h) start hstart state tokenStart base hpending)
      (Lexer.WRustPort.lexStep slice start' hstart' state tokenStart (ix slice.start base)
        hpending') := by
  have hbs' : b.toNat ≤ start.toNat := hbs ▸ Nat.le_refl _
  have hlt : start.toNat < slice.stop := by
    have := hstart
    rw [inputOf_stop] at this
    exact this
  unfold BSmtLib.Lexer.Internal.lexStep Lexer.WRustPort.lexStep
  cases state <;> dsimp only
  case normal =>
    exact SimP.mono (fun _ h => h)
      (fun r s hs => ⟨by rw [hs]; have := r.property; subst hbs; omega,
        by rw [hs]; exact Nat.le_refl _⟩)
      (lexNormal_sim b slice h start start' es hb hbs hstart hstart')
  case numeralOrDecimal =>
    exact SimP.bind (lexNumeralOrDecimal_sim b slice h start start' es tokenStart base hbase hb
      hbs' _ _) fun r => afterStep_sim b slice h start start' es hb hbs hstart hstart' r
  case fraction =>
    exact SimP.bind (lexFractionFrom_sim b slice h start start' es tokenStart base hbase hb
      hbs' _ _) fun r => afterStep_sim b slice h start start' es hb hbs hstart hstart' r
  case baseSelection =>
    exact SimP.bind (lexBaseSelection_sim b slice h start start' es hstart tokenStart hb
      hbs' _ _) fun r => afterStep_sim b slice h start start' es hb hbs hstart hstart' r
  case hexadecimal =>
    exact SimP.bind (lexDigitRun_sim b slice h start start' es _ tokenStart base hbase hb
      hbs' _ _) fun r => afterStep_sim b slice h start start' es hb hbs hstart hstart' r
  case binary =>
    exact SimP.bind (lexDigitRun_sim b slice h start start' es _ tokenStart base hbase hb
      hbs' _ _) fun r => afterStep_sim b slice h start start' es hb hbs hstart hstart' r
  case stringLiteral =>
    exact SimP.bind (lexStringLiteral_sim b slice h start start' es tokenStart base hbase hb
      hbs' _ _) fun r => afterStep_sim b slice h start start' es hb hbs hstart hstart' r
  case stringLiteralDoubleQuote =>
    exact SimP.bind (lexStringLiteral_sim b slice h start start' es tokenStart base hbase hb
      hbs' _ _) fun r => afterStep_sim b slice h start start' es hb hbs hstart hstart' r
  case stringLiteralBackslashEscape =>
    exact SimP.bind (lexStringLiteral_sim b slice h start start' es tokenStart base hbase hb
      hbs' _ _) fun r => afterStep_sim b slice h start start' es hb hbs hstart hstart' r
  case simpleSymbol =>
    exact SimP.bind (lexSimpleSymbol_sim b slice h start start' es tokenStart base hbase hb
      hbs' _ _) fun r => afterStep_sim b slice h start start' es hb hbs hstart hstart' r
  case quotedSymbol =>
    exact SimP.bind (lexQuotedSymbol_sim b slice h start start' es tokenStart base hbase hb
      _ _ _ start start' rfl es hbs' _ _ _ _) fun r =>
        afterStep_sim b slice h start start' es hb hbs hstart hstart' r
  case keyword =>
    exact SimP.bind (lexKeyword_sim b slice h start start' es tokenStart base hbase hb
      hbs' _ _) fun r => afterStep_sim b slice h start start' es hb hbs hstart hstart' r
  case comment =>
    exact SimP.bind (lexComment_sim b slice h start start' es _ _ tokenStart base hbase hb
      hbs' _ _) fun r => afterStep_sim b slice h start start' es hb hbs hstart hstart' r
  case whitespace =>
    exact SimP.bind (lexWhitespace_sim b slice h start start' es tokenStart base hbase hb
      _ _ _ start start' rfl es hbs' _ _ _ _) fun r =>
        afterStep_sim b slice h start start' es hb hbs hstart hstart' r
  case quotedSymbolClosed =>
    exact SimP.bind (lexQuotedSymbolClosed_sim b slice h start start' es tokenStart base hbase
      hb hbs' hlt _ _) fun r => afterStep_sim b slice h start start' es hb hbs hstart hstart' r

end

end BSmtLib.Proofs.X1BatchInCoreLexer
