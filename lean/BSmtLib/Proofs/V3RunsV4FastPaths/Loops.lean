import BSmtLib.Proofs.V3RunsV4FastPaths.Tokens

/-!
# The loops of the lexer over runs with two idle steps

The lexer over runs' loop with one idle step agrees with the loop with another idle step when
each step of the first loop agrees with a step of the second followed by the first loop
(`loop3_agree`). And the lexer over runs passes over whitespace that the consumer does not take
one byte at a time, which the fast path takes in one go (`loop3_skip`).
-/

namespace BSmtLib.Proofs.Lexer.V3RunsV4FastPaths

open V1Naive V2Batched V3Runs V2BatchedV3Runs

section

variable {H : Type} {m : Type → Type} {R E : Type} [Monad m] [Consume H m R E]

/-- A step of the loop with `idleA` agrees with a step with `idleB` followed by the loop with
`idleA`. -/
def StepAgrees (idleA idleB : IdleStep H m R E) (recover : Location → StateT H m Unit)
    (sliceStart : Nat) (slice : ByteSlice) : Prop :=
  ∀ index committed core batch flow hfits (h : index < slice.size),
    erase <$> loop3 idleA recover sliceStart slice index committed core batch flow hfits =
      erase <$> (do
        let ⟨(outcome, core, batch, ⟨next, _⟩), hfits⟩ ←
          lexAt idleB recover sliceStart slice index h core batch hfits
        cont (loop3 idleA recover sliceStart slice) sliceStart slice committed flow outcome core
          batch next hfits)

theorem loop3_agree [LawfulMonad m] (idleA idleB : IdleStep H m R E)
    (recover : Location → StateT H m Unit) (sliceStart : Nat) (slice : ByteSlice)
    (hstep : StepAgrees idleA idleB recover sliceStart slice) :
    ∀ a committed, slice.size - committed = a → ∀ b index, slice.size - index = b →
      Agree (loop3 idleA recover sliceStart slice) (loop3 idleB recover sliceStart slice)
        index committed := by
  intro a
  refine Nat.strongRecOn a ?_
  intro a iha committed ha b
  refine Nat.strongRecOn b ?_
  intro b ihb index hb core batch flow hfits
  have hres : ∀ r, committed < r → r ≤ slice.size →
      Agree (loop3 idleA recover sliceStart slice) (loop3 idleB recover sliceStart slice) r r :=
    fun r h1 h2 => iha (slice.size - r) (by omega) r rfl _ r rfl
  by_cases h : index < slice.size
  · rw [hstep index committed core batch flow hfits h, loop3_lt _ _ _ _ _ _ _ _ _ hfits h,
      map_bind, map_bind]
    congr
    funext x
    obtain ⟨⟨outcome, core, batch, ⟨next, hn⟩⟩, hfits⟩ := x
    exact cont_agree _ _ _ _ _ _ _ _ _ _ _
      (ihb (slice.size - next) (by omega) next rfl) hres
  · rw [loop3_ge _ _ _ _ _ _ _ _ _ hfits h, loop3_ge _ _ _ _ _ _ _ _ _ hfits h]
    exact atEnd_agree _ _ _ _ _ _ _ _ _ hres

/-- A batch that fits an idle state fits it at any later location. -/
theorem fits_idle {core : Core} {batch : Array Lexeme} (hfits : Fits core batch)
    (location : Location) (hle : core.location.offset ≤ location.offset) :
    Fits { core with activity := .idle, location, startedBefore := trivial } batch :=
  hfits.mono (show core.frontier ≤ location.offset by have := core.frontier_le; omega)

/-- The loop from equal positions and states is the same, whatever the proofs that the batch
fits. -/
theorem loop3_congr {idle : IdleStep H m R E} {recover : Location → StateT H m Unit}
    {sliceStart : Nat} {slice : ByteSlice} {index index' committed : Nat} {core core' : Core}
    {batch : Array Lexeme} {flow : ControlFlow (Located R)} {h : Fits core batch}
    {h' : Fits core' batch} (ei : index = index') (e : core = core') :
    loop3 idle recover sliceStart slice index committed core batch flow h =
      loop3 idle recover sliceStart slice index' committed core' batch flow h' := by
  subst ei e
  rfl

/-- The lexer over runs passes over whitespace that the consumer does not take one byte at a
time. -/
theorem loop3_skip [LawfulMonad m] (recover : Location → StateT H m Unit) (sliceStart : Nat)
    (slice : ByteSlice) (committed : Nat) (batch : Array Lexeme) (flow : ControlFlow (Located R))
    (hws : Consume.consumesWhitespaceAndComments (H := H) = false) :
    ∀ n i, slice.size - i = n → i ≤ slice.size → ∀ core : Core, core.activity = .idle →
      ∀ hfits hfits',
      loop3 V3Runs.lexIdle recover sliceStart slice i committed core batch flow hfits =
        loop3 V3Runs.lexIdle recover sliceStart slice (runEnd slice isWhitespaceRun i) committed
          { core with
            activity := .idle
            location := afterColumns core.location (runEnd slice isWhitespaceRun i - i)
            startedBefore := trivial }
          batch flow hfits' := by
  intro n
  induction n with
  | zero =>
    intro i hn hi core hact hfits hfits'
    have hend : runEnd slice isWhitespaceRun i = i := by
      rw [runEnd]; simp only [show ¬ i < slice.size by omega, dite_false]
    refine loop3_congr hend.symm ?_
    obtain ⟨v, iv, loc, act, d, s⟩ := core
    simp only at hact
    subst hact
    rw [hend, Nat.sub_self, afterColumns_zero]
  | succ n ih =>
    intro i hn hi core hact hfits hfits'
    have hlt : i < slice.size := by omega
    by_cases hp : isWhitespaceRun slice[i] = true
    · have hend := runEnd_succ slice isWhitespaceRun i hlt hp
      have hnl : slice[i] ≠ 10 := isWhitespaceRun_ne _ hp
      have hle := le_runEnd slice isWhitespaceRun (i + 1)
      rw [loop3_lt _ _ _ _ _ _ _ _ _ _ hlt]
      simp only [lexAt, withEq, hact, V3Runs.lexIdle, startS, start_space _ _ _ _ hp, hws,
        Bool.false_eq_true, ite_false, pure_bind, cont_next]
      have hafter : core.location.offset < (core.location.afterByte slice[i]).offset := by
        rw [afterByte_offset]; omega
      rw [ih (i + 1) (by omega) (by omega)
        { core with
          activity := .idle, location := core.location.afterByte slice[i]
          startedBefore := trivial } rfl _
        (fits_idle hfits _ (show core.location.offset ≤
          (afterColumns (core.location.afterByte slice[i]) _).offset by
            rw [afterColumns_offset]; omega))]
      refine loop3_congr hend.symm ?_
      congr 1
      rw [afterColumns_afterByte _ _ hnl, hend]
      congr 1
      omega
    · have hend : runEnd slice isWhitespaceRun i = i := by
        rw [runEnd]; simp only [hlt, dite_true, hp]; rfl
      refine loop3_congr hend.symm ?_
      obtain ⟨v, iv, loc, act, d, s⟩ := core
      simp only at hact
      subst hact
      rw [hend, Nat.sub_self, afterColumns_zero]

end

end BSmtLib.Proofs.Lexer.V3RunsV4FastPaths
