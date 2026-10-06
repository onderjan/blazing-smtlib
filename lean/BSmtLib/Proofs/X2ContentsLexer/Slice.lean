import BSmtLib.Proofs.X2ContentsLexer.Step
import BSmtLib.Proofs.X2ContentsLexer.Outer

/-!
# The loop over a slice of the library's lexer and of the lexer with the content buffer

`lexSliceRun`, the loop of the steps up to the first stop of the consumer, is simulated exactly
under `coreMap` of the start of the slice, by induction on the bytes left and on whether a
lexical error was met: each step is simulated by `lexStep_sim` from the position of the lexer's
base, and after it the base is between the start of the slice and the position returned, so that
moving the offset on to that position is the same in both lexers (`coreMap_advance`).

`lexSliceFrom`, the loop over the stops of the consumer, goes back after a stop to the position
`input.start + resumed`, where the lexer with the content buffer goes back to the index `resumed`.
Where it goes on lexing, `resumed` is below the size of the slice, so the two agree under
`coreMap`; where it returns, only the base can differ, which means nothing between the calls. So
the loop over a slice is coupled (`Couple`) from related states, as `Outer` relates them.
-/

namespace BSmtLib.Proofs.X2ContentsLexer

open BSmtLib.Proofs.Simulation

/-- How lexing a slice ended, for the lexer with the content buffer. -/
def exitMap {R E : Type} {floor : Option Nat} :
    BSmtLib.Lexer.Internal.SliceExit R E floor → Lexer.X2Contents.SliceExit R E floor
  | .done result => .done result
  | .stopped stop location after => .stopped stop location after

/-- Moving the offset on to a position, for moving it on to its index. -/
theorem coreMap_advance {start : Nat} {c : ZCore} {p : USize} (hb : start ≤ c.base.toNat)
    (hp : c.base.toNat ≤ p.toNat) :
    coreMap start (c.advance p) = (coreMap start c).advance (ix start p) := by
  simp only [coreMap, BSmtLib.Lexer.LexerCore.advance, Lexer.X2Contents.LexerCore.advance,
    BSmtLib.Lexer.LexerCore.offsetAt, Lexer.X2Contents.LexerCore.offsetAt, sub_toNat_ix hb hp]

section

variable {H : Type} {m : Type → Type} [Monad m] [LawfulMonad m] {ε : Type}

/-- A run of a step of the lexers' monad followed by a step of the consumer's monad, for a step
simulated from its state and continuations that agree on the results it relates. -/
theorem run_bind_simP {S T α β σ τ : Type} {P : S → Prop} {Q : α → S → Prop} {φ : S → T}
    {ψ : α → β} {f : M m H ε S α} {g : M m H ε T β} (hf : SimP P Q φ ψ f g) {s : S}
    (hs : P s) (Φ : σ × H → τ × H) (K : Except ε α × S → StateT H m σ)
    (K' : Except ε β × T → StateT H m τ)
    (hK : ∀ (x : Except ε α) (s' : S) (h' : H), (∀ a, x = .ok a → Q a s') →
      Φ <$> (K (x, s')).run h' = (K' (x.map ψ, φ s')).run h') (h : H) :
    Φ <$> ((f.run.run s) >>= K).run h = ((g.run.run (φ s)) >>= K').run h := by
  obtain ⟨y, h1, h2⟩ := hf s hs h
  simp only [StateT.run_bind]
  rw [show (f.run.run s).run h = runM f s h from rfl, h1,
    show (g.run.run (φ s)).run h = runM g (φ s) h from rfl, h2, map_bind, bind_map_left,
    bind_map_left]
  refine congrArg (y >>= ·) (funext fun x => ?_)
  obtain ⟨⟨⟨r, s'⟩, h'⟩, hgood⟩ := x
  exact hK r s' h' hgood

end

section

variable {H : Type} {m : Type → Type} {R E : Type} [Monad m] [LawfulMonad m] [Consume H m R E]
  {floor : Option Nat}

/-- What `lexSliceRun` measures its progress by: the bytes left, and whether no lexical error was
met yet. -/
def runMeasure (slice : ByteSlice) (position : USize)
    (fnResult : Except (BSmtLib.Lexer.Failure E) (ControlFlow R)) : Nat :=
  2 * (slice.stop - position.toNat) + match fnResult with | .ok _ => 1 | .error _ => 0

theorem lexSliceRun_exact (slice : ByteSlice) (h : slice.stop < USize.size) :
    ∀ n (position : USize) (fnResult : Except (BSmtLib.Lexer.Failure E) (ControlFlow R))
      (c : ZS floor 0), runMeasure slice position fnResult = n →
      slice.start ≤ position.toNat → (∀ v, fnResult = .ok v → c.val.base = position) →
      ∀ hh : H,
      (fun r => ((exitMap r.1.1, boundMap slice.start r.1.2), r.2)) <$>
        (BSmtLib.Lexer.Internal.lexSliceRun (m := m) (inputOf slice h) position fnResult
          c).run hh =
      (Lexer.X2Contents.lexSliceRun slice (ix slice.start position) fnResult
        (boundMap slice.start c)).run hh := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
  intro position fnResult c hn hpos hbase hh
  have hsz : slice.size = slice.stop - slice.start := rfl
  have hstopz : (inputOf slice h).stop.toNat = slice.stop := inputOf_stop
  rw [BSmtLib.Lexer.Internal.lexSliceRun.eq_def, Lexer.X2Contents.lexSliceRun.eq_def]
  dsimp only
  cases fnResult with
  | error e =>
    dsimp only
    rw [dite_eq_left (by simp), dite_eq_left (by simp)]
    refine run_bind_simP (flushBatch_sim slice.start c.val.base) rfl _ _ _ ?_ hh
    intro x s' h' _
    rcases x with ⟨⟨_ | _, location, stopAfter⟩⟩ | ⟨⟩ <;> simp [Except.map, exitMap]
  | ok v =>
  dsimp only
  by_cases hge : position ≥ (inputOf slice h).stop
  · have hge' : ix slice.start position ≥ slice.size := by
      simp only [ge_iff_le, USize.le_iff_toNat_le, hstopz] at hge
      simp only [ix]
      omega
    rw [dite_eq_left (by simp [hge]), dite_eq_left (by simp [hge'])]
    refine run_bind_simP (flushBatch_sim slice.start c.val.base) rfl _ _ _ ?_ hh
    intro x s' h' _
    rcases x with ⟨⟨_ | _, location, stopAfter⟩⟩ | ⟨⟩ <;> simp [Except.map, exitMap]
  have hlt : position.toNat < slice.stop := by
    simp only [ge_iff_le, USize.le_iff_toNat_le, hstopz, Nat.not_le] at hge
    exact hge
  have hge' : ¬ix slice.start position ≥ slice.size := by
    simp only [ix]
    omega
  rw [dite_eq_right (by simp [hge]),
    dite_eq_right (by simp [hge'])]
  have hb := hbase v rfl
  refine run_bind_simP (lexStep_sim c.val.base slice h position (ix slice.start position) rfl
    (hb ▸ hpos) hb _ _ c.val.state c.val.tokenStart c.val.base rfl _ _)
    (s := ⟨c.val, ⟨Nat.le_refl _, c.property.2⟩⟩) rfl _ _ _ ?_ hh
  intro x s' h' hq
  rcases x with interrupted | ⟨next, hnext⟩
  · rcases interrupted with ⟨_ | _, location, stopAfter⟩
    · refine ih _ ?_ position _ _ rfl hpos (fun _ e => by cases e) h'
      subst hn
      simp only [runMeasure]
      omega
    · simp [Except.map, exitMap]
      rfl
  · obtain ⟨hq1, hq2⟩ := hq _ rfl
    dsimp only at hq1 hq2 ⊢
    have e := ih _ ?_ next (.ok v) ⟨s'.val.advance next, s'.property.weaken.advance next⟩ rfl
      (by omega) (fun _ _ => rfl) h'
    · refine e.trans ?_
      congr 2
      exact Subtype.ext (coreMap_advance hq1 hq2)
    · subst hn
      simp only [runMeasure]
      omega

end

/-! ## The loop over the stops of the consumer, coupled -/

section

variable {H : Type} {m : Type → Type} [Monad m] [LawfulMonad m]

/-- Two runs of the consumer's monad that give a result and a lexer state, from the consumer
`h`, are the two sides of one run of pairs with equal results, related states and the same
consumer. -/
def CoupleAt {γ : Type} (A : StateT H m (γ × ZCore)) (B : StateT H m (γ × XCore)) (h : H) :
    Prop :=
  ∃ y : m {p : ((γ × ZCore) × H) × ((γ × XCore) × H) //
      p.1.1.1 = p.2.1.1 ∧ Rel p.1.1.2 p.2.1.2 ∧ p.1.2 = p.2.2},
    A.run h = (fun p => p.val.1) <$> y ∧ B.run h = (fun p => p.val.2) <$> y

theorem CoupleAt.pure {γ : Type} {r : γ} {c : ZCore} {x : XCore} (hx : Rel c x) (h : H) :
    CoupleAt (m := m) (Pure.pure (r, c)) (Pure.pure (r, x)) h :=
  ⟨Pure.pure ⟨(((r, c), h), ((r, x), h)), rfl, hx, rfl⟩, by simp, by simp⟩

/-- A run followed by continuations that are coupled, where the second run is the first one
mapped. -/
theorem CoupleAt.bind_exact {σ τ γ : Type} (A : StateT H m σ) (B : StateT H m τ) (Φ : σ → τ)
    (K : σ → StateT H m (γ × ZCore)) (K' : τ → StateT H m (γ × XCore)) (h : H)
    (hAB : B.run h = (fun r => (Φ r.1, r.2)) <$> A.run h)
    (hK : ∀ s h', CoupleAt (K s) (K' (Φ s)) h') :
    CoupleAt (A >>= K) (B >>= K') h := by
  obtain ⟨Y, hY⟩ := Classical.skolem.mp fun r : σ × H => hK r.1 r.2
  refine ⟨A.run h >>= Y, ?_, ?_⟩
  · rw [StateT.run_bind, map_bind]
    exact congrArg (A.run h >>= ·) (funext fun r => (hY r).1)
  · rw [StateT.run_bind, hAB, bind_map_left, map_bind]
    exact congrArg (A.run h >>= ·) (funext fun r => (hY r).2)

end

section

variable {H : Type} {m : Type → Type} {R E : Type} [Monad m] [LawfulMonad m] [Consume H m R E]

/-- The index of the position the loop goes back to after a stop below the end of the slice. -/
theorem ix_resumed {slice : ByteSlice} (h : slice.stop < USize.size) {resumed : Nat}
    (hr : resumed < slice.size) :
    ix slice.start ((inputOf slice h).start + USize.ofNat resumed) = resumed ∧
      slice.start ≤ ((inputOf slice h).start + USize.ofNat resumed).toNat := by
  have hsz : slice.size = slice.stop - slice.start := rfl
  have hst := slice.start_le_stop
  have hus : USize.size = 2 ^ System.Platform.numBits := USize.size_eq_two_pow
  have e : ((inputOf slice h).start + USize.ofNat resumed).toNat = slice.start + resumed := by
    rw [USize.toNat_add, inputOf_start, USize.toNat_ofNat', Nat.mod_eq_of_lt (a := resumed)
      (by omega), Nat.mod_eq_of_lt (by omega)]
  simp only [ix, e]
  omega

theorem lexSliceFrom_couple (slice : ByteSlice) (h : slice.stop < USize.size)
    (initialOffset : Nat) :
    ∀ k (floor : Nat) hfloor hfloor' (position : USize) (position' : Nat)
      (fnResult : Except (BSmtLib.Lexer.Failure E) (ControlFlow R)) (c : ZS (some floor) 0)
      (x : XS (some floor) 0),
      slice.size + 1 - (floor + 1 - initialOffset) = k →
      ix slice.start position = position' → boundMap slice.start c = x →
      slice.start ≤ position.toNat → (∀ v, fnResult = .ok v → c.val.base = position) →
      ∀ hh : H,
      CoupleAt
        (BSmtLib.Lexer.Internal.lexSliceFrom (m := m) (inputOf slice h) initialOffset floor
          hfloor position fnResult c)
        (Lexer.X2Contents.lexSliceFrom slice initialOffset floor hfloor' position' fnResult x)
        hh := by
  intro k
  induction k using Nat.strongRecOn with
  | ind k ih =>
  intro floor hfloor hfloor' position position' fnResult c x hk ep ex hpos hbase hh
  subst ep ex
  rw [BSmtLib.Lexer.Internal.lexSliceFrom.eq_def, Lexer.X2Contents.lexSliceFrom.eq_def]
  refine CoupleAt.bind_exact _ _ (fun r => (exitMap r.1, boundMap slice.start r.2)) _ _ hh
    ?_ fun s h' => ?_
  · rw [← lexSliceRun_exact slice h _ position fnResult c rfl hpos hbase hh]
  obtain ⟨exit, c'⟩ := s
  have hsz : slice.size = slice.stop - slice.start := rfl
  cases exit with
  | done result => exact CoupleAt.pure (rel_coreMap _ _) h'
  | stopped stop location after =>
    dsimp only [exitMap]
    cases stop with
    | finished result =>
      dsimp only
      exact CoupleAt.pure (by rfl) h'
    | relex =>
      dsimp only
      have hcond : location.offset - initialOffset <
          (inputOf slice h).stop.toNat - (inputOf slice h).start.toNat ↔
          location.offset - initialOffset < slice.size := by
        rw [inputOf_stop, inputOf_start]
        exact Iff.rfl
      by_cases hr : location.offset - initialOffset < slice.size
      · rw [dite_eq_left (hcond.mpr hr), dite_eq_left hr]
        obtain ⟨er, hs⟩ := ix_resumed h hr
        have er' : ((inputOf slice h).start + USize.ofNat (location.offset - initialOffset)).toNat -
            slice.start = location.offset - initialOffset := er
        have := after floor rfl
        exact ih _ (by omega) location.offset _ _ _ _ (.ok .continue) _ _ rfl er
          (Subtype.ext (by
            simp only [boundMap, coreMap, BSmtLib.Lexer.LexerCore.resumeAt,
              Lexer.X2Contents.LexerCore.resumeAt]
            rw [er'])) hs (fun _ _ => rfl) h'
      · rw [dite_eq_right (fun h => hr (hcond.mp h)), dite_eq_right hr]
        exact CoupleAt.pure (by rfl) h'

/-- The loop over a slice of the library's lexer and that of the lexer with the content buffer,
run from related states, are coupled. -/
theorem lexSliceInner_couple (slice : ByteSlice) (h : slice.stop < USize.size) :
    Couple Eq (BSmtLib.Lexer.Internal.lexSliceInner (H := H) (m := m) (R := R) (E := E)
      (inputOf slice h)) (Lexer.X2Contents.lexSliceInner slice) := by
  intro c x hx hh
  rw [eq_wb hx]
  have hst : ix slice.start (inputOf slice h).start = 0 := by
    simp only [ix, inputOf_start, Nat.sub_self]
  exact lexSliceFrom_couple slice h c.offset _ (c.offset - 1) _ _ _ 0 _ _ _ rfl hst
    (Subtype.ext (by
      simp only [boundMap, coreMap, inputOf_start, Nat.sub_self]
      rfl))
    (by rw [inputOf_start]; exact Nat.le_refl _) (fun _ _ => by rfl) hh

end

end BSmtLib.Proofs.X2ContentsLexer
