import BSmtLib.Proofs.X2ContentsLexer.Whitespace

/-!
# The steps per state of the library's lexer and of the lexer with the content buffer

Each step of the library's lexer that lexes on a token in progress, from a position `start`
of the input over a slice, is simulated by the step of the lexer with the content buffer from
the index of `start`. The steps read the slice at positions at or after `start`, which the
lemmas of `Positions` relate to indices, and do not change the base. The loops of strings,
quoted symbols and whitespace are simulated by induction on the bytes left after the position
they go on from.
-/

namespace BSmtLib.Proofs.X2ContentsLexer

open BSmtLib.Proofs.Simulation

/-! ## Positions and indices -/

section

variable {slice : ByteSlice} {h : slice.stop < USize.size}

/-- A position at or after the start of the slice is below its end if its index is below the
size of the slice. -/
theorem lt_stop_iff {p : USize} (hp : slice.start ≤ p.toNat) :
    p < (inputOf slice h).stop ↔ ix slice.start p < slice.size := by
  rw [USize.lt_iff_toNat_lt, inputOf_stop]
  have : slice.size = slice.stop - slice.start := rfl
  simp only [ix]
  omega

/-- A position at or after the start of the slice is the end of the input if its index is the
size of the slice. -/
theorem eq_stop_iff {p : USize} (hp : slice.start ≤ p.toNat) :
    p = (inputOf slice h).stop ↔ ix slice.start p = slice.size := by
  rw [← USize.toNat_inj, inputOf_stop]
  have : slice.size = slice.stop - slice.start := rfl
  have := slice.start_le_stop
  simp only [ix]
  omega

/-- The index of the end of the input is the size of the slice. -/
theorem ix_stop : ix slice.start (inputOf slice h).stop = slice.size := by
  simp only [ix, inputOf_stop]
  rfl

theorem get_eq (p : USize) (hp : slice.start ≤ p.toNat) :
    (inputOf slice h).get p = Lexer.Slice.get slice (ix slice.start p) := by
  unfold Lexer.Input.get Lexer.Slice.get
  rw [get?_eq p hp]

theorem borrow_eq (p q : USize) (hp : slice.start ≤ p.toNat) (hq : slice.start ≤ q.toNat) :
    Lexer.Content.borrow (inputOf slice h) p q =
      Lexer.Slice.borrow slice (ix slice.start p) (ix slice.start q) := by
  unfold Lexer.Content.borrow Lexer.Slice.borrow
  simp only [inputOf_bytes, start_add_ix hp, start_add_ix hq]

/-- The position after one with a byte has the index after its index. -/
theorem ix_add_one {p : USize} (hp : slice.start ≤ p.toNat)
    (hlt : p.toNat < (inputOf slice h).stop.toNat) :
    ix slice.start (p + 1) = ix slice.start p + 1 := by
  rw [ix, ix, Lexer.toNat_add_one_of_lt hlt]
  omega

theorem runEnd_ix {p : USize} {p' : Nat} (ep : ix slice.start p = p')
    (hp : slice.start ≤ p.toNat) (mask : UInt8) :
    slice.start ≤ (Lexer.runEnd (inputOf slice h) p mask).toNat ∧
      ix slice.start (Lexer.runEnd (inputOf slice h) p mask) =
        Lexer.Slice.runEnd slice p' mask := by
  subst ep
  exact runEnd_eq p hp mask

theorem runEndAll_ix {p : USize} {p' : Nat} (ep : ix slice.start p = p')
    (hp : slice.start ≤ p.toNat) (mask : UInt8) :
    slice.start ≤ (Lexer.runEndAll (inputOf slice h) p mask).toNat ∧
      ix slice.start (Lexer.runEndAll (inputOf slice h) p mask) =
        Lexer.Slice.runEndAll slice p' mask := by
  subst ep
  exact runEndAll_eq p hp mask

end

/-- The position a step returned, for the index the step of the lexer with the content buffer
returns. -/
def nextMap (s0 : Nat) {lo : USize} {lo' : Nat} (e : ix s0 lo = lo')
    (r : {next : USize // lo.toNat ≤ next.toNat}) : {next : Nat // lo' ≤ next} :=
  ⟨ix s0 r.val, by subst e; have := r.property; simp only [ix]; omega⟩

/-! ## The helpers, with the indices of the second lexer given by equations -/

section

variable {H : Type} {m : Type → Type} {R E : Type} [Monad m] [LawfulMonad m] [Consume H m R E]
  {floor : Option Nat} {low : Nat} (b : USize)

omit [Consume H m R E] in
theorem extendContent_sim' (slice : ByteSlice) (h : slice.stop < USize.size)
    (p q : USize) (p' q' : Nat) (ep : ix slice.start p = p') (eq : ix slice.start q = q')
    (hp : slice.start ≤ p.toNat) (hq : slice.start ≤ q.toNat) :
    SimP (BaseIs b) (fun _ => BaseIs b) (boundMap slice.start) id
      (BSmtLib.Lexer.Internal.extendContent (H := H) (m := m) (R := R) (E := E) (floor := floor)
        (low := low) (inputOf slice h) p q)
      (Lexer.X2Contents.extendContent slice p' q') := by
  subst ep eq
  exact extendContent_sim b slice h p q hp hq

omit [Consume H m R E] in
theorem markLineFeedAt_sim' (start : Nat) (position : USize) (position' : Nat)
    (ep : ix start position = position') (hb : start ≤ b.toNat)
    (hp : b.toNat ≤ position.toNat) :
    SimP (BaseIs b) (fun _ => BaseIs b) (boundMap start) id
      (BSmtLib.Lexer.Internal.markLineFeedAt (H := H) (m := m) (R := R) (E := E) (floor := floor)
        (low := low) position)
      (Lexer.X2Contents.markLineFeedAt position') := by
  subst ep
  exact markLineFeedAt_sim start b position hb hp

omit [Consume H m R E] in
theorem failAt_sim' {α β : Type} (start : Nat) (ψ : α → β) (kind : LexicalErrorKind)
    (position : USize) (position' : Nat) (ep : ix start position = position')
    (hb : start ≤ b.toNat) (hp : b.toNat < position.toNat) (Q : α → ZS floor low → Prop) :
    SimP (BaseIs b) Q (boundMap start) ψ
      (BSmtLib.Lexer.Internal.failAt (H := H) (m := m) (R := R) (E := E) kind position)
      (Lexer.X2Contents.failAt kind position') := by
  subst ep
  exact failAt_sim start ψ b kind position hb hp Q

omit [Consume H m R E] in
theorem expectDelimiter_sim' (start : Nat) (next : UInt8) (position : USize) (position' : Nat)
    (ep : ix start position = position') (hb : start ≤ b.toNat) (hp : b.toNat ≤ position.toNat)
    (hno : position.toNat + 1 < USize.size) :
    SimP (BaseIs b) (fun _ => BaseIs b) (boundMap start) id
      (BSmtLib.Lexer.Internal.expectDelimiter (H := H) (m := m) (R := R) (E := E)
        (floor := floor) (low := low) next position)
      (Lexer.X2Contents.expectDelimiter next position') := by
  subst ep
  exact expectDelimiter_sim start b next position hb hp hno

/-- The end of a token at a byte, at an index given by an equation. -/
theorem endMap_mkAtByte (start : Nat) (p : USize) (p' : Nat) (ep : ix start p = p') :
    endMap start (Lexer.TokenEnd.mkAtByte p) = Lexer.Slice.TokenEnd.mkAtByte p' := by
  subst ep
  rfl


theorem sinkStored_sim' (start : Nat) (ty : TokenCategory) (hty : ty ≠ .endOfFile)
    (te : BSmtLib.Lexer.TokenEnd) (te' : Lexer.Slice.TokenEnd) (ete : endMap start te = te')
    (s : Location) (base : USize) (hb : start ≤ base.toNat)
    (hp : base.toNat ≤ te.position.toNat) (h h') :
    SimP (BaseIs b) (fun _ => BaseIs b) (boundMap start (floor := floor) (low := low)) id
      (BSmtLib.Lexer.Internal.sinkStored (H := H) (m := m) (R := R) (E := E) ty hty te s base h)
      (Lexer.X2Contents.sinkStored ty hty te' s (ix start base) h') := by
  subst ete
  exact sinkStored_sim start b ty hty te s base hb hp h h'

theorem finishDecimal_sim' (start : Nat) (te : BSmtLib.Lexer.TokenEnd) (te' : Lexer.Slice.TokenEnd)
    (ete : endMap start te = te') (next next' : Option UInt8) (en : next = next') (s : Location)
    (base : USize) (ok : EndOk start b base te) (h h') :
    SimP (BaseIs b) (fun _ => BaseIs b) (boundMap start (floor := floor) (low := low)) id
      (BSmtLib.Lexer.Internal.finishDecimal (H := H) (m := m) (R := R) (E := E) te next s base h)
      (Lexer.X2Contents.finishDecimal te' next' s (ix start base) h') := by
  subst ete en
  exact finishDecimal_sim start b te next s base ok h h'

theorem finishNumeral_sim' (start : Nat) (te : BSmtLib.Lexer.TokenEnd) (te' : Lexer.Slice.TokenEnd)
    (ete : endMap start te = te') (s : Location) (base : USize) (ok : EndOk start b base te)
    (h h') :
    SimP (BaseIs b) (fun _ => BaseIs b) (boundMap start (floor := floor) (low := low)) id
      (BSmtLib.Lexer.Internal.finishNumeral (H := H) (m := m) (R := R) (E := E) te s base h)
      (Lexer.X2Contents.finishNumeral te' s (ix start base) h') := by
  subst ete
  exact finishNumeral_sim start b te s base ok h h'

theorem finishDigitRun_sim' (start : Nat) (run : Lexer.DigitRun) (hrun hrun')
    (te : BSmtLib.Lexer.TokenEnd) (te' : Lexer.Slice.TokenEnd) (ete : endMap start te = te')
    (next next' : Option UInt8) (en : next = next') (s : Location) (base : USize)
    (ok : EndOk start b base te) (h h') :
    SimP (BaseIs b) (fun _ => BaseIs b) (boundMap start (floor := floor) (low := low)) id
      (BSmtLib.Lexer.Internal.finishDigitRun (H := H) (m := m) (R := R) (E := E) run hrun te next
        s base h)
      (Lexer.X2Contents.finishDigitRun run hrun' te' next' s (ix start base) h') := by
  subst ete en
  exact finishDigitRun_sim start b run hrun hrun' te next s base ok h h'

theorem finishSimpleSymbol_sim' (start : Nat) (te : BSmtLib.Lexer.TokenEnd)
    (te' : Lexer.Slice.TokenEnd) (ete : endMap start te = te') (s : Location) (base : USize)
    (ok : EndOk start b base te) (h h') :
    SimP (BaseIs b) (fun _ => BaseIs b) (boundMap start (floor := floor) (low := low)) id
      (BSmtLib.Lexer.Internal.finishSimpleSymbol (H := H) (m := m) (R := R) (E := E) te s base h)
      (Lexer.X2Contents.finishSimpleSymbol te' s (ix start base) h') := by
  subst ete
  exact finishSimpleSymbol_sim start b te s base ok h h'

theorem finishKeyword_sim' (start : Nat) (te : BSmtLib.Lexer.TokenEnd) (te' : Lexer.Slice.TokenEnd)
    (ete : endMap start te = te') (next next' : Option UInt8) (en : next = next') (s : Location)
    (base : USize) (ok : EndOk start b base te) (h h') :
    SimP (BaseIs b) (fun _ => BaseIs b) (boundMap start (floor := floor) (low := low)) id
      (BSmtLib.Lexer.Internal.finishKeyword (H := H) (m := m) (R := R) (E := E) te next s base h)
      (Lexer.X2Contents.finishKeyword te' next' s (ix start base) h') := by
  subst ete en
  exact finishKeyword_sim start b te next s base ok h h'

theorem finishStringLiteral_sim' (start : Nat) (te : BSmtLib.Lexer.TokenEnd)
    (te' : Lexer.Slice.TokenEnd) (ete : endMap start te = te') (s : Location) (base : USize)
    (ok : EndOk start b base te) (h h') :
    SimP (BaseIs b) (fun _ => BaseIs b) (boundMap start (floor := floor) (low := low)) id
      (BSmtLib.Lexer.Internal.finishStringLiteral (H := H) (m := m) (R := R) (E := E) te s base h)
      (Lexer.X2Contents.finishStringLiteral te' s (ix start base) h') := by
  subst ete
  exact finishStringLiteral_sim start b te s base ok h h'

theorem finishWhitespace_sim' (start : Nat) (te : BSmtLib.Lexer.TokenEnd)
    (te' : Lexer.Slice.TokenEnd) (ete : endMap start te = te') (s : Location) (base : USize)
    (ok : EndOk start b base te) (h h') :
    SimP (BaseIs b) (fun _ => BaseIs b) (boundMap start (floor := floor) (low := low)) id
      (BSmtLib.Lexer.Internal.finishWhitespace (H := H) (m := m) (R := R) (E := E) te s base h)
      (Lexer.X2Contents.finishWhitespace te' s (ix start base) h') := by
  subst ete
  exact finishWhitespace_sim start b te s base ok h h'

/-- What a finishing step needs of a token end at the byte at `p`, which is in the slice. -/
theorem endOk_mkAtByte {slice : ByteSlice} {h : slice.stop < USize.size} {p : USize}
    (hb : slice.start ≤ b.toNat) (hbp : b.toNat ≤ p.toNat)
    (hlt : p.toNat < (inputOf slice h).stop.toNat) :
    EndOk slice.start b b (Lexer.TokenEnd.mkAtByte p) := by
  rw [inputOf_stop] at hlt
  exact ⟨hb, hb, hbp, hbp, by simp only [Lexer.TokenEnd.mkAtByte]; omega⟩

end

/-! ## The steps -/

section

variable {H : Type} {m : Type → Type} {R E : Type} [Monad m] [LawfulMonad m] [Consume H m R E]
  {floor : Option Nat} {low : Nat} (b : USize)

theorem lexFractionFrom_sim (slice : ByteSlice) (h : slice.stop < USize.size) (start : USize)
    (start' : Nat) (es : ix slice.start start = start') (tokenStart : Location) (base : USize)
    (hbase : b = base) (hb : slice.start ≤ b.toNat) (hbs : b.toNat ≤ start.toNat) (hh hh') :
    SimP (BaseIs b) (fun _ => BaseIs b) (boundMap slice.start (floor := floor) (low := low))
      (nextMap slice.start es)
      (BSmtLib.Lexer.Internal.lexFractionFrom (H := H) (m := m) (R := R) (E := E)
        (inputOf slice h) start tokenStart base hh)
      (Lexer.X2Contents.lexFractionFrom slice start' tokenStart (ix slice.start base) hh') := by
  subst hbase
  unfold BSmtLib.Lexer.Internal.lexFractionFrom Lexer.X2Contents.lexFractionFrom
  have hle := Lexer.le_runEnd (inputOf slice h) start Lexer.RUN_DIGIT
  obtain ⟨hr1, hr2⟩ := runEnd_ix (h := h) es (by omega) Lexer.RUN_DIGIT
  refine SimP.seq (extendContent_sim' b slice h start _ start' _ es hr2 (by omega) hr1)
    fun _ => ?_
  dsimp only
  refine SimP.ite ((lt_stop_iff hr1).trans (by rw [hr2])) (fun hlt => ?_) fun _ => ?_
  · have hlt' := USize.lt_iff_toNat_lt.mp hlt
    refine SimP.seq (finishDecimal_sim' b slice.start _ _ (endMap_mkAtByte _ _ _ hr2) _ _
      (by rw [get_eq _ hr1, hr2]) _ _ (endOk_mkAtByte b hb (by omega) hlt') _ _) fun _ => ?_
    refine SimP.seq (setNormal_sim slice.start b) fun _ => ?_
    exact SimP.pure (fun _ h => h) (Subtype.ext hr2)
  · refine SimP.seq (setTokenState_sim slice.start b _ _ _ _) fun _ => ?_
    exact SimP.pure (fun _ h => h) (Subtype.ext hr2)

theorem lexDigitRun_sim (slice : ByteSlice) (h : slice.stop < USize.size) (start : USize)
    (start' : Nat) (es : ix slice.start start = start') (run : Lexer.DigitRun) (hrun hrun')
    (tokenStart : Location) (base : USize) (hbase : b = base) (hb : slice.start ≤ b.toNat)
    (hbs : b.toNat ≤ start.toNat) (hh hh') :
    SimP (BaseIs b) (fun _ => BaseIs b) (boundMap slice.start (floor := floor) (low := low))
      (nextMap slice.start es)
      (BSmtLib.Lexer.Internal.lexDigitRun (H := H) (m := m) (R := R) (E := E)
        (inputOf slice h) start run hrun tokenStart base hh)
      (Lexer.X2Contents.lexDigitRun slice start' run hrun' tokenStart (ix slice.start base)
        hh') := by
  subst hbase
  unfold BSmtLib.Lexer.Internal.lexDigitRun Lexer.X2Contents.lexDigitRun
  have hle := Lexer.le_runEnd (inputOf slice h) start run.flag
  obtain ⟨hr1, hr2⟩ := runEnd_ix (h := h) es (by omega) run.flag
  refine SimP.seq (extendContent_sim' b slice h start _ start' _ es hr2 (by omega) hr1)
    fun _ => ?_
  dsimp only
  refine SimP.ite ((lt_stop_iff hr1).trans (by rw [hr2])) (fun hlt => ?_) fun _ => ?_
  · have hlt' := USize.lt_iff_toNat_lt.mp hlt
    refine SimP.seq (finishDigitRun_sim' b slice.start _ _ _ _ _ (endMap_mkAtByte _ _ _ hr2) _ _
      (by rw [get_eq _ hr1, hr2]) _ _ (endOk_mkAtByte b hb (by omega) hlt') _ _) fun _ => ?_
    refine SimP.seq (setNormal_sim slice.start b) fun _ => ?_
    exact SimP.pure (fun _ h => h) (Subtype.ext hr2)
  · exact SimP.pure (fun _ h => h) (Subtype.ext hr2)

theorem lexSimpleSymbol_sim (slice : ByteSlice) (h : slice.stop < USize.size) (start : USize)
    (start' : Nat) (es : ix slice.start start = start') (tokenStart : Location) (base : USize)
    (hbase : b = base) (hb : slice.start ≤ b.toNat) (hbs : b.toNat ≤ start.toNat) (hh hh') :
    SimP (BaseIs b) (fun _ => BaseIs b) (boundMap slice.start (floor := floor) (low := low))
      (nextMap slice.start es)
      (BSmtLib.Lexer.Internal.lexSimpleSymbol (H := H) (m := m) (R := R) (E := E)
        (inputOf slice h) start tokenStart base hh)
      (Lexer.X2Contents.lexSimpleSymbol slice start' tokenStart (ix slice.start base) hh') := by
  subst hbase
  unfold BSmtLib.Lexer.Internal.lexSimpleSymbol Lexer.X2Contents.lexSimpleSymbol
  have hle := Lexer.le_runEnd (inputOf slice h) start Lexer.RUN_SIMPLE_SYMBOL
  obtain ⟨hr1, hr2⟩ := runEnd_ix (h := h) es (by omega) Lexer.RUN_SIMPLE_SYMBOL
  refine SimP.seq (extendContent_sim' b slice h start _ start' _ es hr2 (by omega) hr1)
    fun _ => ?_
  dsimp only
  refine SimP.ite ((lt_stop_iff hr1).trans (by rw [hr2])) (fun hlt => ?_) fun _ => ?_
  · have hlt' := USize.lt_iff_toNat_lt.mp hlt
    have hst := (inputOf_stop (h := h)) ▸ hlt'
    refine SimP.seq (SimP.congr_g (by rw [get_eq _ hr1, hr2])
      (expectDelimiter_sim' b slice.start _ _ _ hr2 hb (by omega) (by omega))) fun _ => ?_
    refine SimP.seq (finishSimpleSymbol_sim' b slice.start _ _ (endMap_mkAtByte _ _ _ hr2) _ _
      (endOk_mkAtByte b hb (by omega) hlt') _ _) fun _ => ?_
    refine SimP.seq (setNormal_sim slice.start b) fun _ => ?_
    exact SimP.pure (fun _ h => h) (Subtype.ext hr2)
  · exact SimP.pure (fun _ h => h) (Subtype.ext hr2)

theorem lexKeyword_sim (slice : ByteSlice) (h : slice.stop < USize.size) (start : USize)
    (start' : Nat) (es : ix slice.start start = start') (tokenStart : Location) (base : USize)
    (hbase : b = base) (hb : slice.start ≤ b.toNat) (hbs : b.toNat ≤ start.toNat) (hh hh') :
    SimP (BaseIs b) (fun _ => BaseIs b) (boundMap slice.start (floor := floor) (low := low))
      (nextMap slice.start es)
      (BSmtLib.Lexer.Internal.lexKeyword (H := H) (m := m) (R := R) (E := E)
        (inputOf slice h) start tokenStart base hh)
      (Lexer.X2Contents.lexKeyword slice start' tokenStart (ix slice.start base) hh') := by
  subst hbase
  unfold BSmtLib.Lexer.Internal.lexKeyword Lexer.X2Contents.lexKeyword
  have hle := Lexer.le_runEnd (inputOf slice h) start Lexer.RUN_SIMPLE_SYMBOL
  obtain ⟨hr1, hr2⟩ := runEnd_ix (h := h) es (by omega) Lexer.RUN_SIMPLE_SYMBOL
  refine SimP.seq (extendContent_sim' b slice h start _ start' _ es hr2 (by omega) hr1)
    fun _ => ?_
  dsimp only
  refine SimP.ite ((lt_stop_iff hr1).trans (by rw [hr2])) (fun hlt => ?_) fun _ => ?_
  · have hlt' := USize.lt_iff_toNat_lt.mp hlt
    refine SimP.seq (finishKeyword_sim' b slice.start _ _ (endMap_mkAtByte _ _ _ hr2) _ _
      (by rw [get_eq _ hr1, hr2]) _ _ (endOk_mkAtByte b hb (by omega) hlt') _ _) fun _ => ?_
    refine SimP.seq (setNormal_sim slice.start b) fun _ => ?_
    exact SimP.pure (fun _ h => h) (Subtype.ext hr2)
  · exact SimP.pure (fun _ h => h) (Subtype.ext hr2)

theorem lexQuotedSymbolClosed_sim (slice : ByteSlice) (h : slice.stop < USize.size)
    (start : USize) (start' : Nat) (es : ix slice.start start = start') (tokenStart : Location)
    (base : USize) (hbase : b = base) (hb : slice.start ≤ b.toNat) (hbs : b.toNat ≤ start.toNat)
    (hstart : start.toNat < slice.stop) (hh hh') :
    SimP (BaseIs b) (fun _ => BaseIs b) (boundMap slice.start (floor := floor) (low := low))
      (nextMap slice.start es)
      (BSmtLib.Lexer.Internal.lexQuotedSymbolClosed (H := H) (m := m) (R := R) (E := E)
        (inputOf slice h) start tokenStart base hh)
      (Lexer.X2Contents.lexQuotedSymbolClosed slice start' tokenStart (ix slice.start base)
        hh') := by
  subst hbase
  unfold BSmtLib.Lexer.Internal.lexQuotedSymbolClosed Lexer.X2Contents.lexQuotedSymbolClosed
  refine SimP.seq (SimP.congr_g (by rw [get_eq _ (by omega), es])
    (expectDelimiter_sim' b slice.start _ _ _ es hb (by omega) (by omega))) fun _ => ?_
  refine SimP.seq (sinkStored_sim' b slice.start _ _ _ _ (endMap_mkAtByte _ _ _ es) _ _ hb
    hbs _ _) fun _ => ?_
  refine SimP.seq (setNormal_sim slice.start b) fun _ => ?_
  exact SimP.pure (fun _ h => h) (Subtype.ext es)

omit [Consume H m R E] in
theorem lexBaseSelection_sim (slice : ByteSlice) (h : slice.stop < USize.size) (start : USize)
    (start' : Nat) (es : ix slice.start start = start') (hstart) (tokenStart : Location)
    (hb : slice.start ≤ b.toNat) (hbs : b.toNat ≤ start.toNat) (hh hh') :
    SimP (BaseIs b) (fun _ => BaseIs b) (boundMap slice.start (floor := floor) (low := low))
      (nextMap slice.start es)
      (BSmtLib.Lexer.Internal.lexBaseSelection (H := H) (m := m) (R := R) (E := E)
        (inputOf slice h) start hstart tokenStart hh)
      (Lexer.X2Contents.lexBaseSelection slice start' tokenStart hh') := by
  unfold BSmtLib.Lexer.Internal.lexBaseSelection Lexer.X2Contents.lexBaseSelection
  have e1 := ix_add_one (h := h) (p := start) (by omega) hstart
  have e1' : ix slice.start (start + 1) = start' + 1 := by rw [e1, es]
  have hn := Lexer.toNat_add_one_of_lt hstart
  have eg : (inputOf slice h).get start = Lexer.Slice.get slice start' := by
    rw [get_eq _ (by omega), es]
  dsimp only
  rw [eg]
  refine SimP.ite Iff.rfl (fun _ => ?_) fun _ => ?_
  · refine SimP.seq (setTokenState_sim slice.start b _ _ _ _) fun _ => ?_
    exact SimP.pure (fun _ h => h) (Subtype.ext e1')
  refine SimP.ite Iff.rfl (fun _ => ?_) fun _ => ?_
  · refine SimP.seq (setTokenState_sim slice.start b _ _ _ _) fun _ => ?_
    exact SimP.pure (fun _ h => h) (Subtype.ext e1')
  · refine SimP.seq (failAt_sim' b slice.start id _ _ _ e1' hb (by omega) _) fun _ => ?_
    exact SimP.pure (fun _ h => h) (Subtype.ext e1')

omit [Consume H m R E] [LawfulMonad m] in
/-- A step from a state that is never reached is simulated by any step. -/
theorem SimP.of_false {start : Nat} {α β : Type} {Q : α → ZS floor low → Prop} {ψ : α → β}
    {f : BSmtLib.Lexer.LexM H m R E floor low α} {g : Lexer.X2Contents.LexM H m R E floor low β} :
    SimP (fun _ => False) Q (boundMap start) ψ f g :=
  fun _ hs => absurd hs id

theorem consumes_sim (start : Nat) :
    SimP (BaseIs b) (fun _ => BaseIs b) (boundMap start (floor := floor) (low := low)) id
      (BSmtLib.Lexer.Internal.consumesWhitespaceAndComments (H := H) (m := m) (R := R) (E := E))
      (Lexer.X2Contents.consumesWhitespaceAndComments) := by
  unfold BSmtLib.Lexer.Internal.consumesWhitespaceAndComments
    Lexer.X2Contents.consumesWhitespaceAndComments
  exact SimP.pure (fun _ h => h) rfl

theorem lexComment_sim (slice : ByteSlice) (h : slice.stop < USize.size) (start : USize)
    (start' : Nat) (es : ix slice.start start = start') (hs hs') (tokenStart : Location)
    (base : USize) (hbase : b = base) (hb : slice.start ≤ b.toNat) (hbs : b.toNat ≤ start.toNat)
    (hh hh') :
    SimP (BaseIs b) (fun _ => BaseIs b) (boundMap slice.start (floor := floor) (low := low))
      (nextMap slice.start es)
      (BSmtLib.Lexer.Internal.lexComment (H := H) (m := m) (R := R) (E := E)
        (inputOf slice h) start hs tokenStart base hh)
      (Lexer.X2Contents.lexComment slice start' hs' tokenStart (ix slice.start base) hh') := by
  subst hbase
  have hle := Lexer.le_runEnd (inputOf slice h) start Lexer.RUN_COMMENT_PLAIN
  obtain ⟨hr1, hr2⟩ := runEnd_ix (h := h) es (by omega) Lexer.RUN_COMMENT_PLAIN
  have hg := (get?_eq (h := h) _ hr1).trans (congrArg (Lexer.Slice.get? slice) hr2)
  unfold Lexer.X2Contents.lexComment
  dsimp only
  split
  · rename_i hc'
    unfold BSmtLib.Lexer.Internal.lexComment
    dsimp only
    split
    · refine SimP.bind (consumes_sim b slice.start) fun cons => ?_
      dsimp only [id]
      refine SimP.ite Iff.rfl (fun _ => ?_) fun _ => ?_
      · refine SimP.seq (extendContent_sim' b slice h start _ start' _ es ix_stop
          (by omega) (by simp only [inputOf_stop]; have := slice.start_le_stop; omega))
          fun _ => ?_
        exact SimP.pure (fun _ h => h) (Subtype.ext (by simp only [nextMap]; exact ix_stop))
      · exact SimP.pure (fun _ h => h) (Subtype.ext (by simp only [nextMap]; exact ix_stop))
    · rename_i c hc
      rw [hc, hc'] at hg; cases hg
  · rename_i c hc'
    unfold BSmtLib.Lexer.Internal.lexComment
    dsimp only
    split
    · rename_i hc
      rw [hc, hc'] at hg; cases hg
    rename_i c'' hc
    obtain rfl : c'' = c := Option.some.inj (hc.symm.trans (hg.trans hc'))
    have hlt := Lexer.Input.lt_stop_of_get? hc
    have e1 := ix_add_one (h := h) hr1 hlt
    rw [hr2] at e1
    have hst := (inputOf_stop (h := h)) ▸ hlt
    have hn := Lexer.toNat_add_one_of_lt hlt
    refine SimP.ite Iff.rfl (fun _ => ?_) fun _ => ?_
    all_goals first
      | refine SimP.seq (markLineFeedAt_sim' b slice.start _ _ hr2 hb (by omega)) fun _ => ?_
      | skip
    all_goals
      refine SimP.bind (consumes_sim b slice.start) fun cons => ?_
      dsimp only [id]
      refine SimP.ite Iff.rfl (fun _ => ?_) fun _ => ?_
      · refine SimP.seq (extendContent_sim' b slice h start _ start' _ es e1
          (by omega) (by omega)) fun _ => ?_
        refine SimP.seq (sinkStored_sim' b slice.start _ _ _ _ (endMap_mkAtByte _ _ _ e1)
          _ _ hb (by simp only [Lexer.TokenEnd.mkAtByte]; omega) _ _) fun _ => ?_
        refine SimP.seq (setNormal_sim slice.start b) fun _ => ?_
        exact SimP.pure (fun _ h => h) (Subtype.ext (by simp only [nextMap]; exact e1))
      · refine SimP.seq (setNormal_sim slice.start b) fun _ => ?_
        exact SimP.pure (fun _ h => h) (Subtype.ext (by simp only [nextMap]; exact e1))


omit [LawfulMonad m] [Consume H m R E] in
/-- The position after one with a position after it has the index after its index. -/
theorem ix_add_one_of_lt_size {s0 : Nat} {p : USize} (hp : s0 ≤ p.toNat)
    (hlt : p.toNat + 1 < USize.size) : ix s0 (p + 1) = ix s0 p + 1 := by
  rw [ix, ix, USize.toNat_add, USize.toNat_one, Nat.mod_eq_of_lt hlt]
  omega

theorem lexNumeralOrDecimal_sim (slice : ByteSlice) (h : slice.stop < USize.size)
    (start : USize) (start' : Nat) (es : ix slice.start start = start') (tokenStart : Location)
    (base : USize) (hbase : b = base) (hb : slice.start ≤ b.toNat) (hbs : b.toNat ≤ start.toNat)
    (hh hh') :
    SimP (BaseIs b) (fun _ => BaseIs b) (boundMap slice.start (floor := floor) (low := low))
      (nextMap slice.start es)
      (BSmtLib.Lexer.Internal.lexNumeralOrDecimal (H := H) (m := m) (R := R) (E := E)
        (inputOf slice h) start tokenStart base hh)
      (Lexer.X2Contents.lexNumeralOrDecimal slice start' tokenStart (ix slice.start base)
        hh') := by
  subst hbase
  unfold BSmtLib.Lexer.Internal.lexNumeralOrDecimal Lexer.X2Contents.lexNumeralOrDecimal
  have hle := Lexer.le_runEnd (inputOf slice h) start Lexer.RUN_DIGIT
  obtain ⟨hr1, hr2⟩ := runEnd_ix (h := h) es (by omega) Lexer.RUN_DIGIT
  have hg := (get?_eq (h := h) _ hr1).trans (congrArg (Lexer.Slice.get? slice) hr2)
  refine getCore_bind slice.start b fun c _ => ?_
  dsimp only
  have hgt : (Lexer.runEnd (inputOf slice h) start Lexer.RUN_DIGIT > start) ↔
      (Lexer.Slice.runEnd slice start' Lexer.RUN_DIGIT > start') := by
    rw [gt_iff_lt, USize.lt_iff_toNat_lt, gt_iff_lt, ← hr2, ← es]
    simp only [ix]
    omega
  refine SimP.ite (by simp only [Bool.and_eq_true, decide_eq_true_eq, hgt]; exact Iff.rfl)
    (fun hz => ?_) fun _ => ?_
  · have hz' : start.toNat < (Lexer.runEnd (inputOf slice h) start Lexer.RUN_DIGIT).toNat := by
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hz
      exact USize.lt_iff_toNat_lt.mp hz.1
    have hsz := USize.toNat_lt_size (Lexer.runEnd (inputOf slice h) start Lexer.RUN_DIGIT)
    have e1 : ix slice.start (start + 1) = start' + 1 := by
      rw [ix_add_one_of_lt_size (s0 := slice.start) (p := start) (by omega) (by omega), es]
    have hn : (start + 1).toNat = start.toNat + 1 := by
      exact Lexer.toNat_add_one_of_lt hz'
    exact SimP.bind (failAt_sim' b slice.start id _ _ _ e1 hb (by omega) (fun _ _ => False))
      fun _ => SimP.of_false
  refine SimP.seq (extendContent_sim' b slice h start _ start' _ es hr2 (by omega) hr1)
    fun _ => ?_
  split
  · rename_i next hc
    have hx : Lexer.Slice.get? slice (Lexer.Slice.runEnd slice start' Lexer.RUN_DIGIT) =
        some next := hg ▸ hc
    rw [hx]
    dsimp only
    have hlt := Lexer.Input.lt_stop_of_get? hc
    have e1 := ix_add_one (h := h) hr1 hlt
    rw [hr2] at e1
    have hn := Lexer.toNat_add_one_of_lt hlt
    have hst := (inputOf_stop (h := h)) ▸ hlt
    refine SimP.ite Iff.rfl (fun _ => ?_) fun _ => ?_
    · refine SimP.seq (pushContent_sim slice.start b _) fun _ => ?_
      refine SimP.bind (lexFractionFrom_sim b slice h _ _ e1 tokenStart b rfl hb (by omega) _ _)
        fun r => ?_
      obtain ⟨e, he⟩ := r
      dsimp only [nextMap]
      exact SimP.pure (fun _ h => h) rfl
    · refine SimP.seq (expectDelimiter_sim' b slice.start _ _ _ hr2 hb (by omega) (by omega))
        fun _ => ?_
      refine SimP.seq (finishNumeral_sim' b slice.start _ _ (endMap_mkAtByte _ _ _ hr2) _ _
        (endOk_mkAtByte b hb (by omega) hlt) _ _) fun _ => ?_
      refine SimP.seq (setNormal_sim slice.start b) fun _ => ?_
      exact SimP.pure (fun _ h => h) (Subtype.ext hr2)
  · rename_i hc
    have hx : Lexer.Slice.get? slice (Lexer.Slice.runEnd slice start' Lexer.RUN_DIGIT) =
        none := hg ▸ hc
    rw [hx]
    dsimp only
    exact SimP.pure (fun _ h => h) (Subtype.ext hr2)

/-- The option attached, for an option with a value. -/
theorem attach_of_eq {α : Type} {o : Option α} {a : α} (h : o = some a) :
    o.attach = some ⟨a, h⟩ := by
  subst h
  rfl

/-- The option attached, for an option without a value. -/
theorem attach_of_eq_none {α : Type} {o : Option α} (h : o = none) : o.attach = none := by
  subst h
  rfl

theorem lexWhitespace_sim (slice : ByteSlice) (h : slice.stop < USize.size) (origin : USize)
    (origin' : Nat) (eo : ix slice.start origin = origin') (tokenStart : Location) (base : USize)
    (hbase : b = base) (hb : slice.start ≤ b.toNat) (hh hh') :
    ∀ k (start : USize) (start' : Nat), slice.stop - start.toNat = k →
      ix slice.start start = start' → b.toNat ≤ start.toNat → ∀ horigin horigin' hs hs',
      SimP (BaseIs b) (fun _ => BaseIs b) (boundMap slice.start (floor := floor) (low := low))
        (nextMap slice.start eo)
        (BSmtLib.Lexer.Internal.lexWhitespace (H := H) (m := m) (R := R) (E := E)
          (inputOf slice h) start origin horigin hs tokenStart base hh)
        (Lexer.X2Contents.lexWhitespace slice start' origin' horigin' hs' tokenStart
          (ix slice.start base) hh') := by
  subst hbase
  intro k
  induction k using Nat.strongRecOn with
  | ind k ih =>
  intro start start' hk es hbs horigin horigin' hs hs'
  have hle := Lexer.le_runEnd (inputOf slice h) start Lexer.RUN_NON_LF_WHITESPACE
  obtain ⟨hr1, hr2⟩ := runEnd_ix (h := h) es (by omega) Lexer.RUN_NON_LF_WHITESPACE
  have hg := (get?_eq (h := h) _ hr1).trans (congrArg (Lexer.Slice.get? slice) hr2)
  rw [Lexer.X2Contents.lexWhitespace]
  dsimp only
  split
  · rename_i c hc'
    rw [BSmtLib.Lexer.Internal.lexWhitespace]
    dsimp only
    split
    · rename_i c'' hc
      obtain rfl : c'' = c := Option.some.inj (hc.symm.trans (hg.trans hc'))
      have hlt := Lexer.Input.lt_stop_of_get? hc
      have e1 := ix_add_one (h := h) hr1 hlt
      rw [hr2] at e1
      have hn := Lexer.toNat_add_one_of_lt hlt
      have hst := (inputOf_stop (h := h)) ▸ hlt
      refine SimP.ite Iff.rfl (fun _ => ?_) fun _ => ?_
      · refine SimP.seq (markLineFeedAt_sim' b slice.start _ _ hr2 hb (by omega)) fun _ => ?_
        refine SimP.seq (extendContent_sim' b slice h start _ start' _ es e1 (by omega)
          (by omega)) fun _ => ?_
        exact ih _ (by omega) _ _ rfl e1 (by omega) _ _ _ _
      · refine SimP.seq (extendContent_sim' b slice h start _ start' _ es hr2 (by omega) hr1)
          fun _ => ?_
        refine SimP.seq (finishWhitespace_sim' b slice.start _ _ (endMap_mkAtByte _ _ _ hr2) _ _
          (endOk_mkAtByte b hb (by omega) hlt) _ _) fun _ => ?_
        refine SimP.seq (setNormal_sim slice.start b) fun _ => ?_
        exact SimP.pure (fun _ h => h) (Subtype.ext hr2)
    · rename_i hc
      rw [hc, hc'] at hg; cases hg
  · rename_i hc'
    rw [BSmtLib.Lexer.Internal.lexWhitespace]
    dsimp only
    split
    · rename_i c hc
      rw [hc, hc'] at hg; cases hg
    · refine SimP.seq (extendContent_sim' b slice h start _ start' _ es ix_stop (by omega)
        (by simp only [inputOf_stop]; have := slice.start_le_stop; omega)) fun _ => ?_
      exact SimP.pure (fun _ h => h) (Subtype.ext ix_stop)

theorem lexQuotedSymbol_sim (slice : ByteSlice) (h : slice.stop < USize.size) (origin : USize)
    (origin' : Nat) (eo : ix slice.start origin = origin') (tokenStart : Location) (base : USize)
    (hbase : b = base) (hb : slice.start ≤ b.toNat) (hh hh') :
    ∀ k (consumed : USize) (consumed' : Nat), slice.stop - consumed.toNat = k →
      ix slice.start consumed = consumed' → b.toNat ≤ consumed.toNat →
      ∀ horigin horigin' hs hs',
      SimP (BaseIs b) (fun _ => BaseIs b) (boundMap slice.start (floor := floor) (low := low))
        (nextMap slice.start eo)
        (BSmtLib.Lexer.Internal.lexQuotedSymbol (H := H) (m := m) (R := R) (E := E)
          (inputOf slice h) consumed origin horigin hs tokenStart base hh)
        (Lexer.X2Contents.lexQuotedSymbol slice consumed' origin' horigin' hs' tokenStart
          (ix slice.start base) hh') := by
  subst hbase
  intro k
  induction k using Nat.strongRecOn with
  | ind k ih =>
  intro start start' hk es hbs horigin horigin' hs hs'
  have hle := Lexer.le_runEnd (inputOf slice h) start Lexer.RUN_QUOTED_PLAIN
  obtain ⟨hr1, hr2⟩ := runEnd_ix (h := h) es (by omega) Lexer.RUN_QUOTED_PLAIN
  have hg := (get?_eq (h := h) _ hr1).trans (congrArg (Lexer.Slice.get? slice) hr2)
  rw [Lexer.X2Contents.lexQuotedSymbol]
  dsimp only
  split
  · rename_i c hc'
    rw [BSmtLib.Lexer.Internal.lexQuotedSymbol]
    dsimp only
    split
    · rename_i c'' hc
      obtain rfl : c'' = c := Option.some.inj (hc.symm.trans (hg.trans hc'))
      have hlt := Lexer.Input.lt_stop_of_get? hc
      have e1 := ix_add_one (h := h) hr1 hlt
      rw [hr2] at e1
      have hn := Lexer.toNat_add_one_of_lt hlt
      have hst := (inputOf_stop (h := h)) ▸ hlt
      refine SimP.ite Iff.rfl (fun _ => ?_) fun _ => ?_
      · refine SimP.seq (extendContent_sim' b slice h start _ start' _ es hr2 (by omega) hr1)
          fun _ => ?_
        have hg1 := (get?_eq (h := h) _ (by omega)).trans (congrArg (Lexer.Slice.get? slice) e1)
        cases hn1 : (inputOf slice h).get?
            (Lexer.runEnd (inputOf slice h) start Lexer.RUN_QUOTED_PLAIN + 1) with
        | some next =>
          rw [hn1] at hg1
          rw [← hg1]
          dsimp only
          have hlt1 := Lexer.Input.lt_stop_of_get? hn1
          have hst1 := (inputOf_stop (h := h)) ▸ hlt1
          refine SimP.seq (expectDelimiter_sim' b slice.start _ _ _ e1 hb (by omega)
            (by omega)) fun _ => ?_
          refine SimP.seq (sinkStored_sim' b slice.start _ _ _ _ (endMap_mkAtByte _ _ _ e1) _ _ hb
            (by simp only [Lexer.TokenEnd.mkAtByte]; omega) _ _) fun _ => ?_
          refine SimP.seq (setNormal_sim slice.start b) fun _ => ?_
          exact SimP.pure (fun _ h => h) (Subtype.ext e1)
        | none =>
          rw [hn1] at hg1
          rw [← hg1]
          dsimp only
          refine SimP.seq (setTokenState_sim slice.start b _ _ _ _) fun _ => ?_
          exact SimP.pure (fun _ h => h) (Subtype.ext e1)
      refine SimP.ite Iff.rfl (fun _ => ?_) fun _ => ?_
      · exact failAt_sim' b slice.start _ _ _ _ e1 hb (by omega) _
      refine SimP.ite Iff.rfl (fun _ => ?_) fun _ => ?_
      · refine SimP.seq (markLineFeedAt_sim' b slice.start _ _ hr2 hb (by omega)) fun _ => ?_
        refine SimP.seq (extendContent_sim' b slice h start _ start' _ es e1 (by omega)
          (by omega)) fun _ => ?_
        exact ih _ (by omega) _ _ rfl e1 (by omega) _ _ _ _
      · exact failAt_sim' b slice.start _ _ _ _ e1 hb (by omega) _
    · rename_i hc
      rw [hc, hc'] at hg; cases hg
  · rename_i hc'
    rw [BSmtLib.Lexer.Internal.lexQuotedSymbol]
    dsimp only
    split
    · rename_i c hc
      rw [hc, hc'] at hg; cases hg
    · refine SimP.seq (extendContent_sim' b slice h start _ start' _ es ix_stop (by omega)
        (by simp only [inputOf_stop]; have := slice.start_le_stop; omega)) fun _ => ?_
      exact SimP.pure (fun _ h => h) (Subtype.ext ix_stop)

omit [LawfulMonad m] [Consume H m R E] in
/-- A branch of the first lexer, by cases on its condition. -/
theorem SimP.ite_left {start : Nat} {α β : Type} {Q : α → ZS floor low → Prop} {ψ : α → β}
    {P : ZS floor low → Prop} {c : Prop} [Decidable c]
    {f₁ f₂ : BSmtLib.Lexer.LexM H m R E floor low α} {g : Lexer.X2Contents.LexM H m R E floor low β}
    (h₁ : c → SimP P Q (boundMap start) ψ f₁ g) (h₂ : ¬c → SimP P Q (boundMap start) ψ f₂ g) :
    SimP P Q (boundMap start) ψ (if c then f₁ else f₂) g := by
  by_cases hc : c
  · simp only [hc, ↓reduceIte]; exact h₁ hc
  · simp only [hc, ↓reduceIte]; exact h₂ hc

omit [LawfulMonad m] [Consume H m R E] in
theorem runEnd_ix3 {slice : ByteSlice} {h : slice.stop < USize.size} {p : USize} {p' : Nat}
    (ep : ix slice.start p = p') (hp : slice.start ≤ p.toNat) (mask : UInt8) :
    p.toNat ≤ (Lexer.runEnd (inputOf slice h) p mask).toNat ∧
      slice.start ≤ (Lexer.runEnd (inputOf slice h) p mask).toNat ∧
      ix slice.start (Lexer.runEnd (inputOf slice h) p mask) = Lexer.Slice.runEnd slice p' mask :=
  ⟨Lexer.le_runEnd _ _ _, runEnd_ix ep hp mask⟩

set_option hygiene false in
/-- The run of a string literal after its start, from the position `cz` with the index `cz'`
(`ecz`), which is at or after the base (`hbz`) and the start of the slice (`hsz`). -/
local macro "string_rest" : tactic => `(tactic| (
  obtain ⟨hle, hr1, hr2⟩ := runEnd_ix3 (h := h) ecz hsz Lexer.RUN_STRING_PLAIN
  have hg := (get?_eq (h := h) _ hr1).trans (congrArg (Lexer.Slice.get? slice) hr2)
  split
  · rename_i c hc
    have hlt := Lexer.Input.lt_stop_of_get? hc
    have e1 := ix_add_one (h := h) hr1 hlt
    rw [hr2] at e1
    have hn := Lexer.toNat_add_one_of_lt hlt
    have hst := (inputOf_stop (h := h)) ▸ hlt
    refine SimP.ite_left (fun h10 => ?_) fun h10 => ?_
    · split
      · rename_i c' hc'
        obtain rfl : c' = c := Option.some.inj (hc'.symm.trans (hg.symm.trans hc))
        simp only [h10, ↓reduceIte]
        refine SimP.seq (markLineFeedAt_sim' b slice.start _ _ hr2 hb (by omega)) fun _ => ?_
        refine SimP.seq (extendContent_sim' b slice h _ _ _ _ ecz e1 (by omega)
          (by omega)) fun _ => ?_
        exact ih _ (by omega) _ _ rfl e1 (by omega) _ _
      · rename_i hc'
        rw [hc, hc'] at hg; cases hg
    refine SimP.ite_left (fun h34 => ?_) fun h34 => ?_
    · split
      · rename_i c' hc'
        obtain rfl : c' = c := Option.some.inj (hc'.symm.trans (hg.symm.trans hc))
        simp only [h10, h34, ↓reduceIte]
        refine SimP.seq (extendContent_sim' b slice h _ _ _ _ ecz hr2 (by omega) hr1)
          fun _ => ?_
        refine SimP.seq (setTokenState_sim slice.start b _ _ _ _) fun _ => ?_
        exact ih _ (by omega) _ _ rfl e1 (by omega) _ _
      · rename_i hc'
        rw [hc, hc'] at hg; cases hg
    · split
      · rename_i c' hc'
        obtain rfl : c' = c := Option.some.inj (hc'.symm.trans (hg.symm.trans hc))
        simp only [h10, h34, ↓reduceIte]
        exact failAt_sim' b slice.start _ _ _ _ e1 hb (by omega) _
      · rename_i hc'
        rw [hc, hc'] at hg; cases hg
  · rename_i hc
    split
    · rename_i c' hc'
      rw [hc, hc'] at hg; cases hg
    · refine SimP.seq (extendContent_sim' b slice h _ _ _ _ ecz ix_stop (by omega)
        (by simp only [inputOf_stop]; have := slice.start_le_stop; omega)) fun _ => ?_
      exact SimP.pure (fun _ h => h) (Subtype.ext ix_stop)))

theorem lexStringLiteralFrom_sim (slice : ByteSlice) (h : slice.stop < USize.size)
    (origin : USize) (origin' : Nat) (eo : ix slice.start origin = origin')
    (tokenStart : Location) (base : USize) (hbase : b = base) (hb : slice.start ≤ b.toNat)
    (hh hh') :
    ∀ k (consumed : USize) (consumed' : Nat), slice.stop - consumed.toNat = k →
      ix slice.start consumed = consumed' → b.toNat ≤ consumed.toNat → ∀ horigin horigin',
      SimP (BaseIs b) (fun _ => BaseIs b) (boundMap slice.start (floor := floor) (low := low))
        (nextMap slice.start eo)
        (BSmtLib.Lexer.Internal.lexStringLiteralFrom (H := H) (m := m) (R := R) (E := E)
          (inputOf slice h) consumed origin horigin tokenStart base hh)
        (Lexer.X2Contents.lexStringLiteralFrom slice consumed' origin' horigin' tokenStart
          (ix slice.start base) hh') := by
  subst hbase
  intro k
  induction k using Nat.strongRecOn with
  | ind k ih =>
  intro start start' hk es hbs horigin horigin'
  have hg0 := (get?_eq (h := h) start (by omega)).trans (congrArg (Lexer.Slice.get? slice) es)
  rw [BSmtLib.Lexer.Internal.lexStringLiteralFrom, Lexer.X2Contents.lexStringLiteralFrom]
  dsimp only
  split
  · rename_i first hfirst _
    have hX : Lexer.Slice.get? slice start' = some first := hg0 ▸ hfirst
    rw [attach_of_eq hX]
    try dsimp only
    refine getCore_bind slice.start b fun c _ => ?_
    try dsimp only
    have hlt := Lexer.Input.lt_stop_of_get? hfirst
    have hst := (inputOf_stop (h := h)) ▸ hlt
    refine SimP.ite Iff.rfl (fun _ => ?_) fun _ => ?_
    · refine SimP.ite Iff.rfl (fun _ => ?_) fun _ => ?_
      · refine SimP.seq (expectDelimiter_sim' b slice.start _ _ _ es hb hbs (by omega))
          fun _ => ?_
        refine SimP.seq (finishStringLiteral_sim' b slice.start _ _ (endMap_mkAtByte _ _ _ es) _ _
          (endOk_mkAtByte b hb hbs hlt) _ _) fun _ => ?_
        refine SimP.seq (setNormal_sim slice.start b) fun _ => ?_
        exact SimP.pure (fun _ h => h) (Subtype.ext es)
      · have ecz : ix slice.start (start + 1) = start' + 1 := by
          rw [ix_add_one (h := h) (by omega) hlt, es]
        have hn := Lexer.toNat_add_one_of_lt hlt
        have hsz : slice.start ≤ (start + 1).toNat := by omega
        refine SimP.seq (pushContent_sim slice.start b _) fun _ => ?_
        refine SimP.seq (setTokenState_sim slice.start b _ _ _ _) fun _ => ?_
        string_rest
    · have ecz := es
      have hsz : slice.start ≤ start.toNat := by omega
      string_rest
  · rename_i hnone
    rcases Option.eq_none_or_eq_some (Lexer.Slice.get? slice start') with hX | ⟨first', hX⟩
    · rw [attach_of_eq_none hX]
      try dsimp only
      exact SimP.pure (fun _ h => h) (Subtype.ext es)
    · exact absurd (hg0.trans hX) (fun hs => hnone first' hs (attach_of_eq hs))

omit [LawfulMonad m] [Consume H m R E] in
theorem runEndAll_ix3 {slice : ByteSlice} {h : slice.stop < USize.size} {p : USize} {p' : Nat}
    (ep : ix slice.start p = p') (hp : slice.start ≤ p.toNat) (mask : UInt8) :
    p.toNat ≤ (Lexer.runEndAll (inputOf slice h) p mask).toNat ∧
      slice.start ≤ (Lexer.runEndAll (inputOf slice h) p mask).toNat ∧
      ix slice.start (Lexer.runEndAll (inputOf slice h) p mask) =
        Lexer.Slice.runEndAll slice p' mask :=
  ⟨Lexer.le_runEndAll _ _ _, runEndAll_ix ep hp mask⟩

set_option hygiene false in
/-- The end of a run of a string literal in the legacy mode, once it is known whether the byte
that ended the run is added to the content. -/
local macro "legacy_tail" : tactic => `(tactic| (
  refine SimP.bind (SimP.pure (Q := fun _ => BaseIs b) (ψ := id) (fun _ h => h) rfl)
    fun add => ?_
  dsimp only [id]
  refine SimP.seq (extendContent_sim' b slice h _ _ _ _ ecz hr2 (by omega) hr1) fun _ => ?_
  refine SimP.ite Iff.rfl (fun _ => ?_) fun _ => ?_
  · refine SimP.seq (pushContent_sim slice.start b _) fun _ => ?_
    exact ih _ (by omega) _ _ rfl e1 (by omega) _ _
  · exact ih _ (by omega) _ _ rfl e1 (by omega) _ _))

set_option hygiene false in
/-- The run of a string literal in the legacy mode after its start, from the position `cz` with
the index `cz'` (`ecz`), which is at or after the base (`hbz`) and the start of the slice
(`hsz`). -/
local macro "legacy_rest" : tactic => `(tactic| (
  try dsimp only
  obtain ⟨hle, hr1, hr2⟩ :=
    runEndAll_ix3 (h := h) ecz hsz (Lexer.RUN_STRING_PLAIN ||| Lexer.RUN_QUOTED_PLAIN)
  have hg := (get?_eq (h := h) _ hr1).trans (congrArg (Lexer.Slice.get? slice) hr2)
  split
  · rename_i c hc _
    have hX := hg ▸ hc
    rw [attach_of_eq hX]
    try dsimp only
    have hlt := Lexer.Input.lt_stop_of_get? hc
    have e1 := ix_add_one (h := h) hr1 hlt
    rw [hr2] at e1
    have hn := Lexer.toNat_add_one_of_lt hlt
    have hst := (inputOf_stop (h := h)) ▸ hlt
    refine SimP.ite Iff.rfl (fun _ => ?_) fun _ => ?_
    · refine SimP.seq (markLineFeedAt_sim' b slice.start _ _ hr2 hb (by omega)) fun _ => ?_
      legacy_tail
    refine SimP.ite Iff.rfl (fun _ => ?_) fun _ => ?_
    · refine SimP.seq (setTokenState_sim slice.start b _ _ _ _) fun _ => ?_
      legacy_tail
    refine SimP.ite Iff.rfl (fun _ => ?_) fun _ => ?_
    · refine SimP.seq (setTokenState_sim slice.start b _ _ _ _) fun _ => ?_
      legacy_tail
    refine SimP.ite Iff.rfl (fun _ => ?_) fun _ => ?_
    · legacy_tail
    · exact SimP.bind (failAt_sim' b slice.start id _ _ _ e1 hb (by omega) (fun _ _ => False))
        fun _ => SimP.of_false
  · rename_i hnone
    rcases Option.eq_none_or_eq_some
      (Lexer.Slice.get? slice (Lexer.Slice.runEndAll slice _
        (Lexer.RUN_STRING_PLAIN ||| Lexer.RUN_QUOTED_PLAIN))) with hX | ⟨c', hX⟩
    · rw [attach_of_eq_none hX]
      try dsimp only
      refine SimP.seq (extendContent_sim' b slice h _ _ _ _ ecz ix_stop (by omega)
        (by simp only [inputOf_stop]; have := slice.start_le_stop; omega)) fun _ => ?_
      exact SimP.pure (fun _ h => h) (Subtype.ext ix_stop)
    · exact absurd (hg.trans hX) (fun hs => hnone c' hs (attach_of_eq hs))))

theorem lexStringLiteralLegacy_sim (slice : ByteSlice) (h : slice.stop < USize.size)
    (origin : USize) (origin' : Nat) (eo : ix slice.start origin = origin')
    (tokenStart : Location) (base : USize) (hbase : b = base) (hb : slice.start ≤ b.toNat)
    (hh hh') :
    ∀ k (consumed : USize) (consumed' : Nat), slice.stop - consumed.toNat = k →
      ix slice.start consumed = consumed' → b.toNat ≤ consumed.toNat → ∀ horigin horigin',
      SimP (BaseIs b) (fun _ => BaseIs b) (boundMap slice.start (floor := floor) (low := low))
        (nextMap slice.start eo)
        (BSmtLib.Lexer.Internal.lexStringLiteralLegacy (H := H) (m := m) (R := R) (E := E)
          (inputOf slice h) consumed origin horigin tokenStart base hh)
        (Lexer.X2Contents.lexStringLiteralLegacy slice consumed' origin' horigin' tokenStart
          (ix slice.start base) hh') := by
  subst hbase
  intro k
  induction k using Nat.strongRecOn with
  | ind k ih =>
  intro start start' hk es hbs horigin horigin'
  have hg0 := (get?_eq (h := h) start (by omega)).trans (congrArg (Lexer.Slice.get? slice) es)
  rw [BSmtLib.Lexer.Internal.lexStringLiteralLegacy, Lexer.X2Contents.lexStringLiteralLegacy]
  dsimp only
  split
  · rename_i first hfirst _
    have hX : Lexer.Slice.get? slice start' = some first := hg0 ▸ hfirst
    rw [attach_of_eq hX]
    try dsimp only
    refine getCore_bind slice.start b fun c _ => ?_
    dsimp only [coreMap]
    have hlt := Lexer.Input.lt_stop_of_get? hfirst
    have hst := (inputOf_stop (h := h)) ▸ hlt
    have hsz0 : slice.start ≤ start.toNat := by omega
    cases hs : c.state
    case stringLiteralDoubleQuote =>
      try dsimp only
      refine SimP.seq (expectDelimiter_sim' b slice.start _ _ _ es hb hbs (by omega))
        fun _ => ?_
      refine SimP.seq (finishStringLiteral_sim' b slice.start _ _ (endMap_mkAtByte _ _ _ es) _ _
        (endOk_mkAtByte b hb hbs hlt) _ _) fun _ => ?_
      refine SimP.seq (setNormal_sim slice.start b) fun _ => ?_
      exact SimP.pure (fun _ h => h) (Subtype.ext es)
    case stringLiteralBackslashEscape =>
      try dsimp only
      refine SimP.ite Iff.rfl (fun _ => ?_) fun _ => ?_
      · have ecz : ix slice.start (start + 1) = start' + 1 := by
          rw [ix_add_one (h := h) (by omega) hlt, es]
        have hn := Lexer.toNat_add_one_of_lt hlt
        have hsz : slice.start ≤ (start + 1).toNat := by omega
        refine SimP.seq (pushContent_sim slice.start b _) fun _ => ?_
        refine SimP.seq (setTokenState_sim slice.start b _ _ _ _) fun _ => ?_
        legacy_rest
      · have ecz := es
        have hsz := hsz0
        refine SimP.seq (pushContent_sim slice.start b _) fun _ => ?_
        refine SimP.seq (setTokenState_sim slice.start b _ _ _ _) fun _ => ?_
        legacy_rest
    all_goals
      have ecz := es
      have hsz := hsz0
      legacy_rest
  · rename_i hnone
    rcases Option.eq_none_or_eq_some (Lexer.Slice.get? slice start') with hX | ⟨first', hX⟩
    · rw [attach_of_eq_none hX]
      try dsimp only
      exact SimP.pure (fun _ h => h) (Subtype.ext es)
    · exact absurd (hg0.trans hX) (fun hs => hnone first' hs (attach_of_eq hs))

theorem lexStringLiteral_sim (slice : ByteSlice) (h : slice.stop < USize.size) (start : USize)
    (start' : Nat) (es : ix slice.start start = start') (tokenStart : Location) (base : USize)
    (hbase : b = base) (hb : slice.start ≤ b.toNat) (hbs : b.toNat ≤ start.toNat) (hh hh') :
    SimP (BaseIs b) (fun _ => BaseIs b) (boundMap slice.start (floor := floor) (low := low))
      (nextMap slice.start es)
      (BSmtLib.Lexer.Internal.lexStringLiteral (H := H) (m := m) (R := R) (E := E)
        (inputOf slice h) start tokenStart base hh)
      (Lexer.X2Contents.lexStringLiteral slice start' tokenStart (ix slice.start base) hh') := by
  unfold BSmtLib.Lexer.Internal.lexStringLiteral Lexer.X2Contents.lexStringLiteral
  refine getCore_bind slice.start b fun c _ => ?_
  refine SimP.ite Iff.rfl (fun _ => ?_) fun _ => ?_
  · exact lexStringLiteralLegacy_sim b slice h start start' es tokenStart base hbase hb hh hh' _
      start start' rfl es hbs _ _
  · exact lexStringLiteralFrom_sim b slice h start start' es tokenStart base hbase hb hh hh' _
      start start' rfl es hbs _ _

end

end BSmtLib.Proofs.X2ContentsLexer
