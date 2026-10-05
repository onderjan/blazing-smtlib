import BSmtLib.Proofs.V2BatchedV3Runs.Token

/-!
# A step of each lexer

Each step of the batched lexer's loop agrees with a step of the lexer over runs followed by the
batched lexer's loop (`stepAgrees`): with no token in progress (`lexStart_agrees`), the
batched lexer starts the token at the byte and lexes it byte by byte, which by `loop2_token` is
what the lexer over runs' `V3Runs.lexIdle` does in one go; with a token in progress
(`lexToken_agrees`), likewise from the byte on; skipping and discarding are the same step.
-/

namespace BSmtLib.Proofs.Lexer.V2BatchedV3Runs

open V1Naive V2Batched V3Runs

section

variable {H : Type} {m : Type → Type} {R E : Type} [Monad m] [Consume H m R E]

theorem lexStart_agrees [LawfulMonad m] (recover : Location → StateT H m Unit)
    (sliceStart : Nat) (slice : ByteSlice) (committed : Nat) (flow : ControlFlow (Located R))
    (i : Nat) (hi : i < slice.size) (core : Core) (batch : Array Lexeme) :
    erase <$> (do
      let (outcome, core, batch) ← V2Batched.lexStart sliceStart core batch slice[i]
      cont (loop2 recover sliceStart slice) sliceStart slice committed flow outcome core batch
        (i + 1)) =
    erase <$> (do
      let (outcome, core, batch, ⟨next, _⟩) ← V3Runs.lexIdle sliceStart slice i hi core batch
      cont (loop2 recover sliceStart slice) sliceStart slice committed flow outcome core batch
        next) := by
  simp only [V2Batched.lexStart, V3Runs.lexIdle]
  cases hs : start core.version (Consume.consumesWhitespaceAndComments (H := H)) core.location
      slice[i] with
  | idle => simp only [pure_bind]
  | token l => simp only [bind_assoc, pure_bind]
  | error failure => simp only [pure_bind]
  | pending p =>
    simp only [pure_bind, cont_next]
    rw [loop2_token recover sliceStart slice committed flow batch _ (i + 1) rfl (by omega) p _ rfl]
    simp only
    generalize hr : run (Consume.consumesWhitespaceAndComments (H := H)) slice p (i + 1)
      (core.location.afterByte slice[i]) = r
    cases r with
    | pending p' location => simp only [expand, pure_bind, cont_next]
    | idle next location _ => simp only [expand, pure_bind, cont_next]
    | tokenWith l next _ => simp only [expand, bind_assoc, pure_bind]
    | tokenBefore l next _ inside =>
      simp only [expand, bind_assoc, pure_bind]
      conv => lhs; rw [emit_bind]
      conv => rhs; rw [emit_bind]
      simp only [map_bind]
      refine congrArg (_ >>= ·) (funext fun x => ?_)
      obtain ⟨outcome, c, b⟩ := x
      cases outcome with
      | next =>
        simp only [cont_next]
        rw [loop2_lt _ _ _ _ _ _ _ _ inside]
        simp only [V2Batched.lexByte, fixCore]
      | finished located =>
        simp only [cont_finished]
        rw [loop2_lt _ _ _ _ _ _ _ _ inside]
        simp only [V2Batched.lexByte, fixCore, pure_bind, cont_next]
      | stopped stop => rw [cont_stopped]
      | failed failure => exact cont_failed _ _ _ _ _ _ rfl _ _ _
    | error failure =>
      simp only [expand, pure_bind]
      refine cont_failed _ _ _ _ _ _ ?_ _ _ _
      rfl

theorem lexToken_agrees [LawfulMonad m] (recover : Location → StateT H m Unit)
    (sliceStart : Nat) (slice : ByteSlice) (committed : Nat) (flow : ControlFlow (Located R))
    (i : Nat) (hi : i < slice.size) (p : Pending) (core : Core) (hact : core.activity = .token p)
    (batch : Array Lexeme) :
    erase <$> loop2 recover sliceStart slice i committed core batch flow =
    erase <$> (do
      let (outcome, core, batch, ⟨next, _⟩) ←
        V3Runs.lexToken V3Runs.lexIdle sliceStart slice i hi core batch p
      cont (loop2 recover sliceStart slice) sliceStart slice committed flow outcome core batch
        next) := by
  rw [loop2_token recover sliceStart slice committed flow batch _ i rfl (by omega) p core hact]
  simp only [V3Runs.lexToken]
  generalize run (Consume.consumesWhitespaceAndComments (H := H)) slice p i core.location = r
  cases r with
  | pending p' location => simp only [expand, pure_bind, cont_next]
  | idle next location _ => simp only [expand, pure_bind, cont_next]
  | tokenWith l next _ => simp only [expand, bind_assoc, pure_bind]
  | tokenBefore l next _ inside =>
    simp only [expand, bind_assoc, map_bind]
    refine congrArg (_ >>= ·) (funext fun x => ?_)
    obtain ⟨outcome, c, b⟩ := x
    cases outcome with
    | next =>
      simp only [bind_assoc, pure_bind, ← map_bind]
      exact lexStart_agrees recover sliceStart slice committed flow next inside c b
    | finished located => simp only [pure_bind]
    | stopped stop => simp only [pure_bind]
    | failed failure => simp only [pure_bind]
  | error failure =>
    simp only [expand, pure_bind]
    exact cont_failed _ _ _ _ _ _ rfl _ _ _

theorem stepAgrees [LawfulMonad m] (recover : Location → StateT H m Unit) (sliceStart : Nat)
    (slice : ByteSlice) : StepAgrees (R := R) (E := E) recover sliceStart slice := by
  intro index committed core batch flow h
  simp only [lexAt]
  cases hact : core.activity with
  | idle =>
    rw [loop2_lt _ _ _ _ _ _ _ _ h]
    simp only [V2Batched.lexByte, hact]
    exact lexStart_agrees recover sliceStart slice committed flow index h core batch
  | token p =>
    exact lexToken_agrees recover sliceStart slice committed flow index h p core hact batch
  | recovered =>
    rw [loop2_lt _ _ _ _ _ _ _ _ h]
    simp only [V2Batched.lexByte, hact, bind_assoc, map_bind]
    refine congrArg (_ >>= ·) (funext fun _ => ?_)
    simp only [← map_bind]
    exact lexStart_agrees recover sliceStart slice committed flow index h _ batch
  | skipping skip =>
    rw [loop2_lt _ _ _ _ _ _ _ _ h]
    cases hs : scan (core.version == .v2_0) skip core.depth slice[index] with
    | before =>
      simp only [V2Batched.lexByte, hact, hs,
        show (Scanned.before == Scanned.before) = true from rfl, ite_true, bind_assoc, map_bind]
      refine congrArg (_ >>= ·) (funext fun _ => ?_)
      simp only [← map_bind]
      exact lexStart_agrees recover sliceStart slice committed flow index h _ batch
    | skip skip' depth =>
      simp only [hs, show (Scanned.skip skip' depth == Scanned.before) = false from rfl,
        Bool.false_eq_true, ite_false, bind_assoc, pure_bind]
    | after =>
      simp only [hs, show (Scanned.after == Scanned.before) = false from rfl,
        Bool.false_eq_true, ite_false, bind_assoc, pure_bind]
  | discarding =>
    rw [loop2_lt _ _ _ _ _ _ _ _ h]
    simp only [bind_assoc, pure_bind]
  | ended =>
    rw [loop2_lt _ _ _ _ _ _ _ _ h]
    simp only [bind_assoc, pure_bind]

end

end BSmtLib.Proofs.Lexer.V2BatchedV3Runs
