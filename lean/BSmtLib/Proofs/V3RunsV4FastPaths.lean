import BSmtLib.Proofs.V3RunsV4FastPaths.Idle

/-!
# The lexer over runs and the lexer with fast paths are equal

`Lexer.V3Runs.lexSlice_eq_lexSlice_v4FastPaths`: for every consumer, in every lawful monad,
with or without recovery, the lexer over runs `V3Runs` and the lexer with fast paths
`V4FastPaths` lex a slice alike. Both are the lexer over runs' loop `V3Runs.lexSliceWith`, with
different idle steps; the two share every other operation.

The proof, in parts:

- `V3RunsV4FastPaths.Tokens`: what the lexer over runs makes of the tokens of the fast paths;
- `V3RunsV4FastPaths.Loops`: the loops with two idle steps agree when their steps do, and the
  lexer over runs passes over whitespace that the consumer does not take byte by byte;
- `V3RunsV4FastPaths.Idle`: the idle steps, followed by the loop, agree.

The idle steps themselves differ: the fast path passes over whitespace that the consumer does
not take in one go, where the lexer over runs passes over one byte and its loop over the rest;
and where a token fails, the two go on at different bytes, which a failure does not use.
-/

namespace BSmtLib.Proofs.Lexer

open V1Naive V2Batched V3Runs V2BatchedV3Runs V3RunsV4FastPaths

section

variable {H : Type} {m : Type → Type} {R E : Type} [Monad m] [Consume H m R E]

namespace V3RunsV4FastPaths

theorem stepAgrees [LawfulMonad m] (recover : Location → StateT H m Unit) (sliceStart : Nat)
    (slice : ByteSlice) :
    StepAgrees (R := R) (E := E) V3Runs.lexIdle V4FastPaths.lexIdle recover sliceStart slice := by
  intro index committed core batch flow h
  rw [loop3_lt _ _ _ _ _ _ _ _ _ h]
  simp only [lexAt]
  cases hact : core.activity with
  | idle => exact lexIdle_agrees recover sliceStart slice committed flow index h core batch
  | token p =>
    simp only [V3Runs.lexToken]
    generalize run (Consume.consumesWhitespaceAndComments (H := H)) slice p index core.location = r
    cases r with
    | tokenBefore l next _ inside =>
      simp only [bind_assoc, map_bind]
      refine congrArg (_ >>= ·) (funext fun x => ?_)
      obtain ⟨outcome, c, b⟩ := x
      cases outcome with
      | next =>
        simp only [bind_assoc, pure_bind, ← map_bind]
        exact lexIdle_agrees recover sliceStart slice committed flow next inside c b
      | finished located => rfl
      | stopped stop => rfl
      | failed failure => rfl
    | _ => rfl
  | recovered =>
    simp only [bind_assoc, map_bind]
    refine congrArg (_ >>= ·) (funext fun _ => ?_)
    simp only [← map_bind]
    exact lexIdle_agrees recover sliceStart slice committed flow index h _ batch
  | skipping skip =>
    simp only
    cases hs : scan (core.version == .v2_0) skip core.depth slice[index] with
    | before =>
      simp only [show (Scanned.before == Scanned.before) = true from rfl, ite_true, bind_assoc,
        map_bind]
      refine congrArg (_ >>= ·) (funext fun _ => ?_)
      simp only [← map_bind]
      exact lexIdle_agrees recover sliceStart slice committed flow index h _ batch
    | skip skip' depth =>
      simp only [show (Scanned.skip skip' depth == Scanned.before) = false from rfl,
        Bool.false_eq_true, ite_false]
    | after =>
      simp only [show (Scanned.after == Scanned.before) = false from rfl, Bool.false_eq_true,
        ite_false]
  | discarding => rfl
  | ended => rfl

theorem lexFrom_agree [LawfulMonad m] (recover : Location → StateT H m Unit) (sliceStart : Nat)
    (slice : ByteSlice) (core : Core) :
    erase <$> V3Runs.lexFrom V3Runs.lexIdle recover sliceStart slice 0 0 core #[] .continue =
      erase <$> V3Runs.lexFrom V4FastPaths.lexIdle recover sliceStart slice 0 0 core #[]
        (.continue : ControlFlow (Located R)) :=
  loop3_agree _ _ recover sliceStart slice (stepAgrees recover sliceStart slice) _ 0 rfl _ 0 rfl
    core #[] .continue

end V3RunsV4FastPaths

/-- The lexer over runs and the lexer with fast paths lex a slice alike, for every consumer. -/
theorem V3Runs.lexSlice_eq_lexSlice_v4FastPaths [LawfulMonad m] {recovery : Recovery}
    [LexRecovery recovery H m] (self : V1Naive.Lexer H recovery) (slice : ByteSlice) :
    V3Runs.lexSlice (R := R) self slice = V4FastPaths.lexSlice self slice := by
  obtain ⟨handler, core⟩ := self
  simp only [V3Runs.lexSlice, V4FastPaths.lexSlice, V3Runs.lexSliceWith]
  have hloop := fun (c : Core) => V3RunsV4FastPaths.lexFrom_agree (R := R) (E := E)
    (LexRecovery.recover (H := H) (m := m) recovery) c.location.offset slice c
  cases recovery with
  | recovering =>
    simp only [show (Recovery.recovering == Recovery.recovering) = true from rfl]
    rw [lexSliceStep3_eq, lexSliceStep3_eq]
    rw [funext (sliceTail_recovering hloop _)]
  | failFast =>
    simp only [show (Recovery.failFast == Recovery.recovering) = false from rfl]
    have h : eraseLex <$> V3Runs.lexSliceStep (H := H) (m := m) (R := R) (E := E)
          V3Runs.lexIdle false (LexRecovery.abandon .failFast) (LexRecovery.recover .failFast)
          slice core =
        eraseLex <$> V3Runs.lexSliceStep V4FastPaths.lexIdle false
          (LexRecovery.abandon .failFast) (LexRecovery.recover .failFast) slice core := by
      rw [lexSliceStep3_eq, lexSliceStep3_eq, map_bind, map_bind]
      refine congrArg (_ >>= ·) (funext fun c => ?_)
      exact sliceTail_failFast hloop _ c
    have h' := congrArg (fun x => StateT.run x handler) h
    simp only [StateT.run_map] at h'
    refine V2BatchedV3Runs.bind_map_agree _ ?_ ?_ ?_ h' <;>
      (intro a; obtain ⟨⟨res, c⟩, hh⟩ := a; cases res <;> rfl)

end

end BSmtLib.Proofs.Lexer
