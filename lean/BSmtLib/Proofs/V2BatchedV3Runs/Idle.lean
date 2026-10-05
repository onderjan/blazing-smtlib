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
    (i : Nat) (hi : i < slice.size) (core : Core) (batch : Array Lexeme)
    (hfits : Fits core batch) :
    erase <$> (do
      let ⟨(outcome, core, batch), hfits⟩ ←
        V2Batched.lexStart sliceStart core batch slice[i] hfits
      cont (loop2 recover sliceStart slice) sliceStart slice committed flow outcome core batch
        (i + 1) hfits) =
    erase <$> (do
      let ⟨(outcome, core, batch, ⟨next, _⟩), hfits⟩ ←
        V3Runs.lexIdle sliceStart slice i hi core batch hfits
      cont (loop2 recover sliceStart slice) sliceStart slice committed flow outcome core batch
        next hfits) := by
  simp only [V2Batched.lexStart, V3Runs.lexIdle]
  cases hs : start core.version (Consume.consumesWhitespaceAndComments (H := H)) core.location
      slice[i] with
  | idle => simp only [startS, hs, pure_bind]
  | token l =>
    simp only [startS, hs, bind_assoc]
    refine congrArg (erase <$> ·) (congrArg (_ >>= ·) (funext fun x => ?_))
    obtain ⟨⟨o, c, b⟩, hf, hfix⟩ := x
    simp only [pure_bind]
  | error failure => simp only [startS, hs, pure_bind]
  | pending p =>
    simp only [startS, hs, pure_bind, cont_next]
    rw [loop2_token recover sliceStart slice committed flow batch _ (i + 1) rfl (by omega) p _ rfl
      _ (runS (Consume.consumesWhitespaceAndComments (H := H)) slice p (i + 1)
        (core.location.afterByte slice[i])).1
      (runS (Consume.consumesWhitespaceAndComments (H := H)) slice p (i + 1)
        (core.location.afterByte slice[i])).2 rfl]
    generalize runS (Consume.consumesWhitespaceAndComments (H := H)) slice p (i + 1)
      (core.location.afterByte slice[i]) = x
    obtain ⟨r, hr⟩ := x
    cases r with
    | pending p' location => simp only [expand, pure_bind, cont_next]
    | idle next location _ => simp only [expand, pure_bind, cont_next]
    | tokenWith l next _ =>
      simp only [expand, expandWith, bind_assoc]
      refine congrArg (erase <$> ·) (congrArg (_ >>= ·) (funext fun x => ?_))
      obtain ⟨⟨o, c, b⟩, hf, hfix⟩ := x
      simp only [pure_bind]
    | tokenBefore l next _ inside =>
      simp only [expand, expandBefore, bind_assoc, map_bind]
      refine congrArg (_ >>= ·) (funext fun x => ?_)
      obtain ⟨⟨outcome, c, b⟩, hf, hfix⟩ := x
      cases outcome with
      | next =>
        have hidle : c.activity = .idle := congrArg Core.activity hfix
        simp only [pure_bind, cont_next]
        rw [loop2_lt _ _ _ _ _ _ _ _ _ inside]
        simp only [V2Batched.lexByte, withEq, hidle]
      | finished located =>
        have hdisc : c.activity = .discarding := congrArg Core.activity hfix
        simp only [pure_bind, cont_finished]
        rw [loop2_lt _ _ _ _ _ _ _ _ _ inside]
        simp only [V2Batched.lexByte, withEq, hdisc, pure_bind, cont_next]
      | stopped stop => simp only [pure_bind]; rw [cont_stopped]
      | failed failure =>
        simp only [pure_bind]
        exact cont_failed _ _ _ _ _ _ rfl _ _ _ _ _
    | error failure =>
      simp only [expand, pure_bind]
      refine cont_failed _ _ _ _ _ _ ?_ _ _ _ _ _
      rfl

theorem lexToken_agrees [LawfulMonad m] (recover : Location → StateT H m Unit)
    (sliceStart : Nat) (slice : ByteSlice) (committed : Nat) (flow : ControlFlow (Located R))
    (i : Nat) (hi : i < slice.size) (p : Pending) (core : Core) (hact : core.activity = .token p)
    (batch : Array Lexeme) (hfits : Fits core batch) :
    erase <$> loop2 recover sliceStart slice i committed core batch flow hfits =
    erase <$> (do
      let ⟨(outcome, core, batch, ⟨next, _⟩), hfits⟩ ←
        V3Runs.lexToken V3Runs.lexIdle sliceStart slice i hi core batch p hact hfits
      cont (loop2 recover sliceStart slice) sliceStart slice committed flow outcome core batch
        next hfits) := by
  rw [loop2_token recover sliceStart slice committed flow batch _ i rfl (by omega) p core hact
    hfits (runS (Consume.consumesWhitespaceAndComments (H := H)) slice p i core.location).1
    (runS (Consume.consumesWhitespaceAndComments (H := H)) slice p i core.location).2 rfl]
  simp only [V3Runs.lexToken]
  generalize runS (Consume.consumesWhitespaceAndComments (H := H)) slice p i core.location = x
  obtain ⟨r, hr⟩ := x
  cases r with
  | pending p' location => simp only [expand, pure_bind, cont_next]
  | idle next location _ => simp only [expand, pure_bind, cont_next]
  | tokenWith l next _ =>
    simp only [expand, expandWith, bind_assoc]
    refine congrArg (erase <$> ·) (congrArg (_ >>= ·) (funext fun x => ?_))
    obtain ⟨⟨o, c, b⟩, hf, hfix⟩ := x
    simp only [pure_bind]
  | tokenBefore l next _ inside =>
    simp only [expand, expandBefore, bind_assoc, map_bind]
    refine congrArg (_ >>= ·) (funext fun x => ?_)
    obtain ⟨⟨outcome, c, b⟩, hf, hfix⟩ := x
    cases outcome with
    | next =>
      simp only [bind_assoc, pure_bind, ← map_bind]
      exact lexStart_agrees recover sliceStart slice committed flow next inside c b hf
    | finished located => simp only [pure_bind]
    | stopped stop => simp only [pure_bind]
    | failed failure => simp only [pure_bind]
  | error failure =>
    simp only [expand, pure_bind]
    exact cont_failed _ _ _ _ _ _ rfl _ _ _ _ _

theorem stepAgrees [LawfulMonad m] (recover : Location → StateT H m Unit) (sliceStart : Nat)
    (slice : ByteSlice) : StepAgrees (R := R) (E := E) recover sliceStart slice := by
  intro index committed core batch flow hfits h
  cases hact : core.activity with
  | idle =>
    rw [loop2_lt _ _ _ _ _ _ _ _ _ h]
    simp only [lexAt, V2Batched.lexByte, withEq, hact]
    exact lexStart_agrees recover sliceStart slice committed flow index h core batch hfits
  | token p =>
    simp only [lexAt, withEq, hact]
    exact lexToken_agrees recover sliceStart slice committed flow index h p core hact batch hfits
  | recovered =>
    rw [loop2_lt _ _ _ _ _ _ _ _ _ h]
    simp only [lexAt, V2Batched.lexByte, withEq, hact, bind_assoc, map_bind]
    refine congrArg (_ >>= ·) (funext fun _ => ?_)
    simp only [← map_bind]
    exact lexStart_agrees recover sliceStart slice committed flow index h _ batch _
  | skipping skip =>
    rw [loop2_lt _ _ _ _ _ _ _ _ _ h]
    cases hs : scan (core.version == .v2_0) skip core.depth slice[index] with
    | before =>
      simp only [lexAt, V2Batched.lexByte, withEq, hact, hs,
        show (Scanned.before == Scanned.before) = true from rfl, ite_true, bind_assoc, map_bind]
      refine congrArg (_ >>= ·) (funext fun _ => ?_)
      simp only [← map_bind]
      exact lexStart_agrees recover sliceStart slice committed flow index h _ batch _
    | skip skip' depth =>
      simp only [lexAt, V2Batched.lexByte, withEq, hact, hs,
        show (Scanned.skip skip' depth == Scanned.before) = false from rfl,
        Bool.false_eq_true, ite_false, pure_bind]
    | after =>
      simp only [lexAt, V2Batched.lexByte, withEq, hact, hs,
        show (Scanned.after == Scanned.before) = false from rfl,
        Bool.false_eq_true, ite_false, bind_assoc, pure_bind]
  | discarding =>
    rw [loop2_lt _ _ _ _ _ _ _ _ _ h]
    simp only [lexAt, V2Batched.lexByte, withEq, hact, pure_bind]
  | ended =>
    rw [loop2_lt _ _ _ _ _ _ _ _ _ h]
    simp only [lexAt, V2Batched.lexByte, withEq, hact, pure_bind]

end

end BSmtLib.Proofs.Lexer.V2BatchedV3Runs
