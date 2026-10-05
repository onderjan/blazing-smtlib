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
  ∀ index committed core batch flow (h : index < slice.size),
    erase <$> loop3 idleA recover sliceStart slice index committed core batch flow =
      erase <$> (do
        let (outcome, core, batch, ⟨next, _⟩) ←
          lexAt idleB recover sliceStart slice index h core batch
        cont (loop3 idleA recover sliceStart slice) sliceStart slice committed flow outcome core
          batch next)

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
  intro b ihb index hb core batch flow
  have hres : ∀ r, committed < r → r ≤ slice.size →
      Agree (loop3 idleA recover sliceStart slice) (loop3 idleB recover sliceStart slice) r r :=
    fun r h1 h2 => iha (slice.size - r) (by omega) r rfl _ r rfl
  by_cases h : index < slice.size
  · rw [hstep index committed core batch flow h, loop3_lt _ _ _ _ _ _ _ _ _ h, map_bind,
      map_bind]
    congr
    funext x
    obtain ⟨outcome, core, batch, ⟨next, hn⟩⟩ := x
    exact cont_agree _ _ _ _ _ _ _ _ _ _
      (ihb (slice.size - next) (by omega) next rfl) hres
  · rw [loop3_ge _ _ _ _ _ _ _ _ _ h, loop3_ge _ _ _ _ _ _ _ _ _ h]
    exact atEnd_agree _ _ _ _ _ _ _ _ hres

/-- The lexer over runs passes over whitespace that the consumer does not take one byte at a
time. -/
theorem loop3_skip [LawfulMonad m] (recover : Location → StateT H m Unit) (sliceStart : Nat)
    (slice : ByteSlice) (committed : Nat) (batch : Array Lexeme) (flow : ControlFlow (Located R))
    (hws : Consume.consumesWhitespaceAndComments (H := H) = false) :
    ∀ n i, slice.size - i = n → i ≤ slice.size → ∀ core : Core, core.activity = .idle →
      loop3 V3Runs.lexIdle recover sliceStart slice i committed core batch flow =
        loop3 V3Runs.lexIdle recover sliceStart slice (runEnd slice isWhitespaceRun i) committed
          { core with
            location := afterColumns core.location (runEnd slice isWhitespaceRun i - i) }
          batch flow := by
  intro n
  induction n with
  | zero =>
    intro i hn hi core hact
    have hend : runEnd slice isWhitespaceRun i = i := by
      rw [runEnd]; simp only [show ¬ i < slice.size by omega, dite_false]
    rw [hend, Nat.sub_self, afterColumns_zero]
  | succ n ih =>
    intro i hn hi core hact
    have hlt : i < slice.size := by omega
    by_cases hp : isWhitespaceRun slice[i] = true
    · have hend := runEnd_succ slice isWhitespaceRun i hlt hp
      have hnl : slice[i] ≠ 10 := isWhitespaceRun_ne _ hp
      rw [loop3_lt _ _ _ _ _ _ _ _ _ hlt]
      simp only [lexAt, hact, V3Runs.lexIdle, start_space _ _ _ _ hp, hws, Bool.false_eq_true,
        ite_false, pure_bind, cont_next]
      rw [ih (i + 1) (by omega) (by omega) _ rfl, hend]
      have hle := le_runEnd slice isWhitespaceRun (i + 1)
      simp only [afterColumns_afterByte _ _ hnl]
      congr 3
      omega
    · have hend : runEnd slice isWhitespaceRun i = i := by
        rw [runEnd]; simp only [hlt, dite_true, hp]; rfl
      rw [hend, Nat.sub_self, afterColumns_zero]

end

end BSmtLib.Proofs.Lexer.V3RunsV4FastPaths
