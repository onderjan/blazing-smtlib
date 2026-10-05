import BSmtLib.Proofs.V2BatchedV3Runs.Idle

/-!
# The batched lexer and the lexer over runs are equal

`Lexer.V2Batched.lexSlice_eq_lexSlice_v3Runs`: for every consumer, in every lawful monad, with
or without recovery, the batched lexer `V2Batched` and the lexer over runs `V3Runs` lex a slice
alike: the same calls of the consumer in the same order, the same result and the same lexer
after it. The two share every other operation.

The proof, in parts:

- `V2BatchedV3Runs.Bytes`: the bytes and locations of a run;
- `V2BatchedV3Runs.Loops`: the loops over a slice agree when their steps do;
- `V2BatchedV3Runs.Steps`: what a hand-over leaves of the state, what the loops do after a step,
  and how the batched lexer steps over a run;
- `V2BatchedV3Runs.Byte`: the batched lexer at a byte of a token;
- `V2BatchedV3Runs.RunEq`: the lexer over runs, byte by byte;
- `V2BatchedV3Runs.Token`: the batched lexer over a token in progress;
- `V2BatchedV3Runs.Idle`: a step of each lexer.

Inside a slice the two agree only up to `erase`: where a token fails, the lexer over runs keeps
its state from the start of the token. A failed lexing of a slice overwrites the location and
the activity of a recovering lexer, and gives back no lexer that stops at its first error, so
the calls are equal.
-/

namespace BSmtLib.Proofs.Lexer

open V1Naive V2Batched V3Runs V2BatchedV3Runs

section

variable {H : Type} {m : Type → Type} {R E : Type} [Monad m] [Consume H m R E]

namespace V2BatchedV3Runs

theorem lexFrom_agree [LawfulMonad m] (recover : Location → StateT H m Unit) (sliceStart : Nat)
    (slice : ByteSlice) (core : Core) :
    erase <$> V2Batched.lexFrom recover sliceStart slice 0 0 core #[] .continue =
      erase <$> V3Runs.lexFrom V3Runs.lexIdle recover sliceStart slice 0 0 core #[]
        (.continue : ControlFlow (Located R)) :=
  loop2_agree_loop3 recover sliceStart slice (stepAgrees recover sliceStart slice) _ 0 rfl _ 0 rfl
    core #[] .continue

/-- A continuation that does not depend on what `erase` forgets. -/
theorem bind_erase [LawfulMonad m] {α β : Type}
    {x y : StateT H m (Except (Failure E) α × Core)}
    (k : Except (Failure E) α × Core → StateT H m β) (hk : ∀ r, k r = k (erase r))
    (h : erase <$> x = erase <$> y) : x >>= k = y >>= k := by
  calc x >>= k = x >>= (fun r => k (erase r)) := by
        congr 1; funext r; exact hk r
    _ = (erase <$> x) >>= k := by rw [bind_map_left]
    _ = (erase <$> y) >>= k := by rw [h]
    _ = y >>= k := by
        rw [bind_map_left]; congr 1; funext r; exact (hk r).symm

theorem failCall_blank (abandon : Location → StateT H m Unit) (failure : Failure E)
    (atEnd : Bool) {c₁ c₂ : Core} (h : blank c₁ = blank c₂) :
    failCall true abandon failure atEnd c₁ = failCall true abandon failure atEnd c₂ := by
  obtain ⟨v₁, i₁, l₁, a₁, d₁⟩ := c₁
  obtain ⟨v₂, i₂, l₂, a₂, d₂⟩ := c₂
  simp only [blank, Core.mk.injEq] at h
  obtain ⟨rfl, rfl, -, -, rfl⟩ := h
  rfl

/-- A result of the lexing of a slice with the location and activity of the state forgotten if
it is an error. -/
def eraseLex {α : Type} : Except (LexError E) α × Core → Except (LexError E) α × Core
  | (.ok a, core) => (.ok a, core)
  | (.error err, core) => (.error err, blank core)

/-- What the lexing of a slice does after the loop over it, with or without recovery. -/
def afterLoop (recovers : Bool) (abandon : Location → StateT H m Unit)
    (r : Except (Failure E) (ControlFlow (Located R)) × Core) :
    StateT H m (Except (LexError E) (ControlFlow (Located R)) × Core) :=
  match r.1 with
  | .ok flow => pure (.ok flow, r.2)
  | .error failure => do
    let r' ← failCall recovers abandon failure false r.2
    pure (.error r'.1, r'.2)

/-- What the lexing of a slice does first: a recovery that is due. -/
def beforeLoop (recover : Location → StateT H m Unit) (core : Core) : StateT H m Core :=
  match core.activity with
  | .recovered => do
    recover core.location
    pure { core with activity := .idle }
  | _ => pure core

/-- The lexing of a slice after `beforeLoop`, with the loop `loop`. -/
def sliceTail (loop : Core → StateT H m (Except (Failure E) (ControlFlow (Located R)) × Core))
    (recovers : Bool) (abandon : Location → StateT H m Unit) (core : Core) :
    StateT H m (Except (LexError E) (ControlFlow (Located R)) × Core) :=
  match core.activity with
  | .ended => pure (.ok .continue, core)
  | _ => loop core >>= afterLoop recovers abandon

theorem lexSliceStep2_eq [LawfulMonad m] (recovers : Bool)
    (abandon recover : Location → StateT H m Unit)
    (slice : ByteSlice) (core : Core) :
    V2Batched.lexSliceStep (R := R) recovers abandon recover slice core =
      beforeLoop recover core >>= sliceTail
        (fun c => V2Batched.lexFrom recover c.location.offset slice 0 0 c #[] .continue)
        recovers abandon := by
  cases hact : core.activity <;>
    simp only [V2Batched.lexSliceStep, beforeLoop, hact, bind_assoc, pure_bind, sliceTail] <;> rfl

theorem lexSliceStep3_eq [LawfulMonad m] (idle : IdleStep H m R E) (recovers : Bool)
    (abandon recover : Location → StateT H m Unit)
    (slice : ByteSlice) (core : Core) :
    V3Runs.lexSliceStep idle recovers abandon recover slice core =
      beforeLoop recover core >>= sliceTail
        (fun c => V3Runs.lexFrom idle recover c.location.offset slice 0 0 c #[] .continue)
        recovers abandon := by
  cases hact : core.activity <;>
    simp only [V3Runs.lexSliceStep, beforeLoop, hact, bind_assoc, pure_bind, sliceTail] <;> rfl

omit [Consume H m R E] in
theorem sliceTail_recovering [LawfulMonad m]
    {loopA loopB : Core → StateT H m (Except (Failure E) (ControlFlow (Located R)) × Core)}
    (h : ∀ c, erase <$> loopA c = erase <$> loopB c) (abandon : Location → StateT H m Unit)
    (core : Core) :
    sliceTail loopA true abandon core = sliceTail loopB true abandon core := by
  unfold sliceTail
  split
  · rfl
  · refine bind_erase _ ?_ (h core)
    intro r
    obtain ⟨res, c⟩ := r
    cases res with
    | ok flow => rfl
    | error failure =>
      simp only [afterLoop, erase]
      rw [failCall_blank abandon failure false (c₁ := blank c) (c₂ := c) rfl]

omit [Consume H m R E] in
theorem sliceTail_failFast [LawfulMonad m]
    {loopA loopB : Core → StateT H m (Except (Failure E) (ControlFlow (Located R)) × Core)}
    (h : ∀ c, erase <$> loopA c = erase <$> loopB c) (abandon : Location → StateT H m Unit)
    (core : Core) :
    eraseLex <$> sliceTail loopA false abandon core =
      eraseLex <$> sliceTail loopB false abandon core := by
  unfold sliceTail
  split
  · rfl
  · simp only [map_bind]
    refine bind_erase _ ?_ (h core)
    intro r
    obtain ⟨res, c⟩ := r
    cases res with
    | ok flow => rfl
    | error failure => simp [afterLoop, erase, failCall, eraseLex, blank]

/-- With recovery, the lexing of a slice is the same in both lexers. -/
theorem lexSliceStep_recovering [LawfulMonad m] (abandon recover : Location → StateT H m Unit)
    (slice : ByteSlice) (core : Core) :
    V2Batched.lexSliceStep (R := R) true abandon recover slice core =
      V3Runs.lexSliceStep V3Runs.lexIdle true abandon recover slice core := by
  rw [lexSliceStep2_eq, lexSliceStep3_eq]
  refine congrArg (_ >>= ·) (funext fun c => ?_)
  exact sliceTail_recovering (fun c => lexFrom_agree recover _ slice c) abandon c

/-- Without recovery, the lexing of a slice is the same in both lexers up to `eraseLex`. -/
theorem lexSliceStep_failFast [LawfulMonad m] (abandon recover : Location → StateT H m Unit)
    (slice : ByteSlice) (core : Core) :
    eraseLex <$> V2Batched.lexSliceStep (R := R) false abandon recover slice core =
      eraseLex <$> V3Runs.lexSliceStep V3Runs.lexIdle false abandon recover slice core := by
  rw [lexSliceStep2_eq, lexSliceStep3_eq, map_bind, map_bind]
  refine congrArg (_ >>= ·) (funext fun c => ?_)
  exact sliceTail_failFast (fun c => lexFrom_agree recover _ slice c) abandon c

/-- Two continuations that agree on what `g` keeps, after two computations that agree on it. -/
theorem bind_map_agree [LawfulMonad m] {α β : Type} {x y : m α} (g : α → α) {F G : α → m β}
    (hF : ∀ a, F a = F (g a)) (hG : ∀ a, G a = G (g a)) (hFG : ∀ a, F (g a) = G (g a))
    (h : g <$> x = g <$> y) : x >>= F = y >>= G := by
  calc x >>= F = x >>= (fun a => F (g a)) := by congr 1; funext a; exact hF a
    _ = (g <$> x) >>= F := by rw [bind_map_left]
    _ = (g <$> y) >>= F := by rw [h]
    _ = y >>= (fun a => G (g a)) := by rw [bind_map_left]; congr 1; funext a; exact hFG a
    _ = y >>= G := by congr 1; funext a; exact (hG a).symm

end V2BatchedV3Runs

/-- The batched lexer and the lexer over runs lex a slice alike, for every consumer. -/
theorem V2Batched.lexSlice_eq_lexSlice_v3Runs [LawfulMonad m] {recovery : Recovery}
    [LexRecovery recovery H m] (self : V1Naive.Lexer H recovery) (slice : ByteSlice) :
    V2Batched.lexSlice (R := R) self slice = V3Runs.lexSlice self slice := by
  obtain ⟨handler, core⟩ := self
  simp only [V2Batched.lexSlice, V3Runs.lexSlice, V3Runs.lexSliceWith]
  cases recovery with
  | recovering =>
    simp only [show (Recovery.recovering == Recovery.recovering) = true from rfl]
    rw [V2BatchedV3Runs.lexSliceStep_recovering]
    rfl
  | failFast =>
    simp only [show (Recovery.failFast == Recovery.recovering) = false from rfl]
    have h := congrArg (fun x => StateT.run x handler)
      (V2BatchedV3Runs.lexSliceStep_failFast (R := R) (LexRecovery.abandon .failFast)
        (LexRecovery.recover .failFast) slice core)
    simp only [StateT.run_map] at h
    refine V2BatchedV3Runs.bind_map_agree _ ?_ ?_ ?_ h <;>
      (intro a; obtain ⟨⟨res, c⟩, hh⟩ := a; cases res <;> rfl)

end

end BSmtLib.Proofs.Lexer
