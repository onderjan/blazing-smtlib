module

public import BSmtLib.Facts.Proofs.Lexer.X1BatchInCoreLexer.Batch
import all BSmtLib.Lexer
import all BSmtLib.Lexer.Internal.WRustPort

@[expose] public section

/-!
# The whitespace run of the normal state, in both lexers
-/

namespace BSmtLib.Facts.Proofs.Lexer.X1BatchInCoreLexer.Whitespace

open BSmtLib.Facts.Proofs.Lexer.Simulation.Steps
open BSmtLib.Facts.Proofs.Lexer.X1BatchInCoreLexer.Batch
open BSmtLib.Facts.Proofs.Lexer.X1BatchInCoreLexer.Core
open BSmtLib.Facts.Proofs.Lexer.X1BatchInCoreLexer.Positions

section

variable {H : Type} {m : Type → Type} {R E : Type} [Monad m] [LawfulMonad m] [Token.Consume H R E]
  [∀ batch, Token.ConsumeFrom H (Token.BatchCursor batch) m]
  {floor : Option Nat} {low : Nat} (b : USize)

/-- The position after the run and the batch, for those after its index. -/
def wsMap (start : Nat) {offset : Nat} {base index : USize} (hb : start ≤ base.toNat)
    (hi : base.toNat ≤ index.toNat)
    (r : {next : USize × Token.TokenBatch //
      index.toNat < next.1.toNat ∧ BSmtLib.Lexer.Internal.Held floor offset base next.1 next.2}) :
    {next : Nat × Token.TokenBatch //
      ix start index < next.1 ∧
        Lexer.Internal.WRustPort.Held floor offset (ix start base) next.1 next.2} :=
  ⟨(ix start r.val.1, r.val.2), by have := r.property.1; simp only [ix]; omega,
    by rw [← sub_toNat_ix hb (by have := r.property.1; omega)]; exact r.property.2.1,
    r.property.2.2⟩

/-- What the whitespace run leaves: the base where the run goes on, and the end of the slice
`e` where it reaches the end of the slice and there is nothing to go on with. -/
def WsPost {α : Type} (b e : USize) (r : Option α) (c : ZS floor low) : Prop :=
  (r.isSome → BaseIs b c) ∧ (r.isNone → BaseIs e c)

theorem startWhitespaceFrom_sim (slice : ByteSlice) (h : slice.stop < USize.size)
    (offset : Nat) (base index : USize) (s : Span.Location) (hb : slice.start ≤ base.toNat)
    (hbase : b = base) (hbi : base.toNat ≤ index.toNat) :
    ∀ k (batch : Token.TokenBatch) (e : USize) (e' : Nat), slice.stop - e.toNat = k →
      ix slice.start e = e' → index.toNat ≤ e.toNat → ∀ hframe hframe' hstart hstart' hend
      hend' hrun hrun' hbatch hbatch',
      SimP (BaseIs b) (WsPost b (inputOf slice h).stop)
        (boundMap slice.start (floor := floor) (low := low))
        (Option.map (wsMap slice.start hb hbi))
        (BSmtLib.Lexer.Internal.startWhitespaceFrom (H := H) (m := m) (R := R) (E := E)
          (inputOf slice h) offset base index e s batch hframe hstart hend hrun hbatch)
        (Lexer.Internal.WRustPort.startWhitespaceFrom slice offset (ix slice.start base)
          (ix slice.start index) e' s batch hframe' hstart' hend' hrun' hbatch') := by
  intro k
  induction k using Nat.strongRecOn with
  | ind k ih =>
  intro batch e e' hk he hie hframe hframe' hstart hstart' hend hend' hrun hrun' hbatch hbatch'
  subst he
  rw [BSmtLib.Lexer.Internal.startWhitespaceFrom, Lexer.Internal.WRustPort.startWhitespaceFrom]
  dsimp only
  have hse : slice.start ≤ e.toNat := by omega
  obtain ⟨hr1, hr2⟩ := runEnd_eq (h := h) e hse Lexer.CharClass.RUN_NON_LF_WHITESPACE
  have hg := get?_eq (h := h) _ hr1
  rw [hr2] at hg
  subst hbase
  have hle := Lexer.CharClass.le_runEnd (inputOf slice h) e Lexer.CharClass.RUN_NON_LF_WHITESPACE
  have hstopz : (inputOf slice h).stop.toNat = slice.stop := inputOf_stop
  have hsz : slice.size = slice.stop - slice.start := rfl
  split
  · rename_i c hc
    have hx := hg ▸ hc
    have hlt := Lexer.CharClass.Input.lt_stop_of_get? hc
    rw [inputOf_stop] at hlt
    have e1 := Lexer.CharClass.toNat_add_one_of_lt (bound := (inputOf slice h).stop)
      (Lexer.CharClass.Input.lt_stop_of_get? hc)
    split
    · rename_i hnl
      split
      · rename_i c' hc'
        obtain rfl : c' = c := Option.some.inj (hc'.symm.trans hx)
        split
        · refine SimP.seq (SimP.congr_g ?_ (markLineFeedAt_sim (H := H) (m := m) (R := R)
            (E := E) (floor := floor) (low := low) slice.start b
            (Lexer.CharClass.runEnd (inputOf slice h) e Lexer.CharClass.RUN_NON_LF_WHITESPACE)
                (by omega)
            (by omega))) fun _ => ?_
          · exact congrArg _ hr2
          exact ih (slice.stop -
              (Lexer.CharClass.runEnd (inputOf slice h) e Lexer.CharClass.RUN_NON_LF_WHITESPACE +
                  1).toNat)
            (by omega) batch _ _ rfl (by simp only [ix, idx] at hr2 ⊢; omega) (by omega)
            _ _ _ _ _ _ _ _ _ _
        · exact absurd hnl ‹_›
      · exact absurd (hx.symm.trans ‹_›) (by simp)
    · rename_i hnl
      split
      · rename_i c' hc'
        obtain rfl : c' = c := Option.some.inj (hc'.symm.trans hx)
        split
        · exact absurd ‹_› hnl
        · have hlt' : index.toNat <
              (Lexer.CharClass.runEnd (inputOf slice h) e
                  Lexer.CharClass.RUN_NON_LF_WHITESPACE).toNat :=
            BSmtLib.Lexer.Internal.lt_whitespaceRunEnd hend.2.1 hrun hc hnl
          refine SimP.seq (pushBorrowed_sim' (H := H) (m := m) (R := R) (E := E)
            (floor := floor) (low := low) b slice batch offset b .whitespace index
            (Lexer.CharClass.runEnd (inputOf slice h) e Lexer.CharClass.RUN_NON_LF_WHITESPACE) s
            (Lexer.CharClass.runEnd (inputOf slice h) e Lexer.CharClass.RUN_NON_LF_WHITESPACE) _ _
                _ _ rfl rfl hr2 hr2
            (by omega) (by omega) ⟨hb, by omega⟩ _ _ _ _ _ _ _ _) fun x => ?_
          obtain ⟨bt, hbt⟩ := x
          dsimp only
          refine SimP.pure (fun _ hs => ⟨fun _ => hs, fun h => by simp at h⟩) ?_
          simp only [Option.map_some]
          congr 1
          apply Subtype.ext
          simp only [wsMap]
          exact Prod.ext hr2 rfl
      · exact absurd (hx.symm.trans ‹_›) (by simp)
  · rename_i hc
    have hx := hg ▸ hc
    split
    · exact absurd (hx.symm.trans ‹_›) (by simp)
    · have hge := BSmtLib.Lexer.Internal.stop_le_of_get?_none hc
      have hst : ix slice.start (inputOf slice h).stop = slice.size := by
        simp only [ix, hstopz, hsz]
      refine SimP.seq (SimP.congr_g ?_ (extendContent_sim (H := H) (m := m) (R := R) (E := E)
        (floor := floor) (low := low) b slice h index (inputOf slice h).stop (by omega)
        (by omega))) fun _ => ?_
      · rw [hst]
      exact SimP.bind (leavePending_sim' (H := H) (m := m) (R := R) (E := E)
        (floor := floor) (low := low) slice.start b .whitespace s offset b
        (inputOf slice h).stop batch _ _ rfl hst ⟨hb, by omega⟩ _ _ _ _ _ _ _ _) fun _ =>
          SimP.pure (fun _ hs => ⟨fun h => by simp at h, fun _ => hs⟩) rfl

omit [Token.Consume H R E] [∀ batch, Token.ConsumeFrom H (Token.BatchCursor batch) m] in
/-- `startToken`, with the indices of the second lexer given by equations. -/
theorem startToken_sim' (start : Nat) (offset : Nat) (base position : USize) (base' position' : Nat)
    (eb : ix start base = base') (ep : ix start position = position')
    (hb : start ≤ base.toNat) (hp : base.toNat ≤ position.toNat)
    (hframe : BSmtLib.Lexer.Internal.Frame floor low offset)
    (hframe' : Lexer.Internal.WRustPort.Frame floor low offset) :
    SimP (BaseIs b) (fun _ => BaseIs b) (boundMap start)
      (fun r => ⟨r.val, by rw [r.property, ← eb, ← ep, sub_toNat_ix hb hp]⟩)
      (BSmtLib.Lexer.Internal.startToken (H := H) (m := m) (R := R) (E := E) offset base position
        hframe)
      (Lexer.Internal.WRustPort.startToken offset base' position' hframe') := by
  subst eb ep
  exact startToken_sim start b offset base position hb hp hframe hframe'

theorem startWhitespace_sim (slice : ByteSlice) (h : slice.stop < USize.size)
    (offset : Nat) (base index : USize) (base' index' : Nat) (eb : ix slice.start base = base')
    (ei : ix slice.start index = index') (hb : slice.start ≤ base.toNat) (hbase : b = base)
    (hbi : base.toNat ≤ index.toNat) (batch : Token.TokenBatch) (hrun hrun' hframe hframe' hindex
      hindex' hbatch hbatch') :
    SimP (BaseIs b) (WsPost b (inputOf slice h).stop)
      (boundMap slice.start (floor := floor) (low := low))
      (fun r => eb ▸ ei ▸ Option.map (wsMap slice.start hb hbi) r)
      (BSmtLib.Lexer.Internal.startWhitespace (H := H) (m := m) (R := R) (E := E)
        (inputOf slice h) offset base index batch hrun hframe hindex hbatch)
      (Lexer.Internal.WRustPort.startWhitespace slice offset base' index' batch hrun' hframe'
          hindex'
        hbatch') := by
  subst eb ei
  unfold BSmtLib.Lexer.Internal.startWhitespace Lexer.Internal.WRustPort.startWhitespace
  refine SimP.seq (startToken_sim' (H := H) (m := m) (R := R) (E := E) b slice.start offset base
    index _ _ rfl rfl hb hbi hframe hframe') fun x => ?_
  obtain ⟨s, hs⟩ := x
  dsimp only
  exact startWhitespaceFrom_sim b slice h offset base index s hb hbase hbi _ batch index _ rfl rfl
    (Nat.le_refl _) _ _ _ _ _ _ _ _ _ _

end

end BSmtLib.Facts.Proofs.Lexer.X1BatchInCoreLexer.Whitespace
