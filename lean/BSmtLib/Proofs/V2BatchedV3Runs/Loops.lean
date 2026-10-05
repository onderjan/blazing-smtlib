import BSmtLib.Proofs.Lexer.V3Runs

/-!
# The loops over a slice

The batched lexer and the lexer over runs loop over a slice in the same way: a step at a byte,
then what the outcome of the step leaves to do (`cont`), and at the end of the slice the batch
is handed over (`atEnd`). Only the step differs. The two loops agree when each step of the
batched lexer agrees with a step of the lexer over runs followed by the batched lexer's loop
(`loop2_agree_loop3`).

They agree up to `erase`: where the lexer over runs fails inside a token, it gives back its
state from the start of the token, and the batched lexer its state at the failing byte. The two
differ only in the location and the activity, which a failed lexing of a slice overwrites or
drops.
-/

namespace BSmtLib.Proofs.Lexer.V2BatchedV3Runs

open V1Naive V2Batched V3Runs

section
variable {H : Type} {m : Type → Type} {R E : Type} [Monad m] [Consume H m R E]

/-- A loop over a slice, from a lexer state that the batch fits. -/
abbrev Loop (H : Type) (m : Type → Type) (R E : Type) :=
  Nat → Nat → (core : Core) → (batch : Array Lexeme) → ControlFlow (Located R) →
    Fits core batch → StateT H m (Except (Failure E) (ControlFlow (Located R)) × Core)

/-- What the loops do after the outcome of a step, going on at `next`. -/
def cont (loop : Loop H m R E) (sliceStart : Nat) (slice : ByteSlice) (committed : Nat)
    (flow : ControlFlow (Located R)) (outcome : Outcome R E) (core : Core) (batch : Array Lexeme)
    (next : Nat) (hfits : Fits core batch) :
    StateT H m (Except (Failure E) (ControlFlow (Located R)) × Core) := do
  match ← settle outcome core batch flow hfits with
  | .proceed core batch flow hfits => loop next committed core batch flow hfits
  | .fail failure core => return (.error failure, core)
  | .stop stop core flow =>
    match withEq (resumption stop flow) with
    | ⟨.error failure, _⟩ => return (.error failure, core)
    | ⟨.ok (location, activity, flow), hres⟩ =>
      let resumed := location.offset - sliceStart
      if committed < resumed ∧ resumed ≤ slice.size then
        loop resumed resumed
          { core with location, activity, startedBefore := resumption_startsBefore hres } #[] flow
          (fits_empty _)
      else
        return (.error { cause := .internal .stoppedBeforeStart, location }, core)

/-- The batched lexer's loop. -/
def loop2 (recover : Location → StateT H m Unit) (sliceStart : Nat) (slice : ByteSlice) :
    Loop H m R E :=
  fun index committed core batch flow hfits =>
    V2Batched.lexFrom recover sliceStart slice index committed core batch flow hfits

theorem loop2_lt (recover : Location → StateT H m Unit) (sliceStart : Nat) (slice : ByteSlice)
    (index committed : Nat) (core : Core) (batch : Array Lexeme) (flow : ControlFlow (Located R))
    (hfits : Fits core batch) (h : index < slice.size) :
    loop2 recover sliceStart slice index committed core batch flow hfits = (do
      let ⟨(outcome, core, batch), hfits⟩ ←
        V2Batched.lexByte recover sliceStart core batch slice[index] hfits
      cont (loop2 recover sliceStart slice) sliceStart slice committed flow outcome core batch
        (index + 1) hfits) := by
  simp only [loop2]
  rw [V2Batched.lexFrom]
  simp only [h, dite_true, cont]
  rfl

/-- The lexer over runs' loop, with the idle step `idle`. -/
def loop3 (idle : IdleStep H m R E) (recover : Location → StateT H m Unit) (sliceStart : Nat)
    (slice : ByteSlice) : Loop H m R E :=
  fun index committed core batch flow hfits =>
    V3Runs.lexFrom idle recover sliceStart slice index committed core batch flow hfits

theorem loop3_lt (idle : IdleStep H m R E) (recover : Location → StateT H m Unit)
    (sliceStart : Nat) (slice : ByteSlice)
    (index committed : Nat) (core : Core) (batch : Array Lexeme) (flow : ControlFlow (Located R))
    (hfits : Fits core batch) (h : index < slice.size) :
    loop3 idle recover sliceStart slice index committed core batch flow hfits = (do
      let ⟨(outcome, core, batch, ⟨next, _⟩), hfits⟩ ←
        lexAt idle recover sliceStart slice index h core batch hfits
      cont (loop3 idle recover sliceStart slice) sliceStart slice committed flow outcome core batch
        next hfits) := by
  simp only [loop3]
  rw [V3Runs.lexFrom]
  simp only [h, dite_true, cont]
  rfl

/-- The loops at the end of the slice. -/
def atEnd (loop : Loop H m R E) (sliceStart : Nat) (slice : ByteSlice) (committed : Nat)
    (core : Core) (batch : Array Lexeme) (flow : ControlFlow (Located R))
    (hfits : Fits core batch) :
    StateT H m (Except (Failure E) (ControlFlow (Located R)) × Core) := do
  match ← settleEnd core batch flow hfits with
  | .proceed core _ flow _ => return (.ok flow, core)
  | .fail failure core => return (.error failure, core)
  | .stop stop core flow =>
    match withEq (resumption stop flow) with
    | ⟨.error failure, _⟩ => return (.error failure, core)
    | ⟨.ok (location, activity, flow), hres⟩ =>
      let resumed := location.offset - sliceStart
      if committed < resumed ∧ resumed ≤ slice.size then
        loop resumed resumed
          { core with location, activity, startedBefore := resumption_startsBefore hres } #[] flow
          (fits_empty _)
      else
        return (.error { cause := .internal .stoppedBeforeStart, location }, core)

theorem loop2_ge (recover : Location → StateT H m Unit) (sliceStart : Nat) (slice : ByteSlice)
    (index committed : Nat) (core : Core) (batch : Array Lexeme) (flow : ControlFlow (Located R))
    (hfits : Fits core batch) (h : ¬ index < slice.size) :
    loop2 recover sliceStart slice index committed core batch flow hfits =
      atEnd (loop2 recover sliceStart slice) sliceStart slice committed core batch flow hfits := by
  simp only [loop2]
  rw [V2Batched.lexFrom]
  simp only [h, dite_false, atEnd]
  rfl

theorem loop3_ge (idle : IdleStep H m R E) (recover : Location → StateT H m Unit)
    (sliceStart : Nat) (slice : ByteSlice)
    (index committed : Nat) (core : Core) (batch : Array Lexeme) (flow : ControlFlow (Located R))
    (hfits : Fits core batch) (h : ¬ index < slice.size) :
    loop3 idle recover sliceStart slice index committed core batch flow hfits =
      atEnd (loop3 idle recover sliceStart slice) sliceStart slice committed core batch flow
        hfits := by
  simp only [loop3]
  rw [V3Runs.lexFrom]
  simp only [h, dite_false, atEnd]
  rfl

omit [Monad m] [Consume H m R E] in
/-- A loop from equal states is the same, whatever the proofs that the batch fits. -/
theorem loop_congr (loop : Loop H m R E) {index committed : Nat} {core core' : Core}
    {batch : Array Lexeme} {flow : ControlFlow (Located R)} {h : Fits core batch}
    {h' : Fits core' batch} (e : core = core') :
    loop index committed core batch flow h = loop index committed core' batch flow h' := by
  subst e
  rfl

/-- The core with its location and activity forgotten. -/
def blank (core : Core) : Core :=
  { core with location := Location.initial, activity := .idle, startedBefore := trivial }

/-- A result with the location and activity of the core forgotten if it is an error. -/
def erase {α : Type} : Except (Failure E) α × Core → Except (Failure E) α × Core
  | (.ok a, core) => (.ok a, core)
  | (.error failure, core) => (.error failure, blank core)

/-- Two loops agree up to `erase`. -/
def Agree (loopA loopB : Loop H m R E) (index committed : Nat) : Prop :=
  ∀ core batch flow hfits, erase <$> loopA index committed core batch flow hfits =
    erase <$> loopB index committed core batch flow hfits

theorem cont_agree [LawfulMonad m] (loopA loopB : Loop H m R E) (sliceStart : Nat)
    (slice : ByteSlice) (committed : Nat) (flow : ControlFlow (Located R)) (outcome : Outcome R E)
    (core : Core) (batch : Array Lexeme) (next : Nat) (hfits : Fits core batch)
    (hnext : Agree loopA loopB next committed)
    (hres : ∀ r, committed < r → r ≤ slice.size → Agree loopA loopB r r) :
    erase <$> cont loopA sliceStart slice committed flow outcome core batch next hfits =
      erase <$> cont loopB sliceStart slice committed flow outcome core batch next hfits := by
  simp only [cont, map_bind]
  congr
  funext x
  match x with
  | .proceed core batch flow hfits => exact hnext core batch flow hfits
  | .fail failure core => rfl
  | .stop stop core flow =>
    simp only
    split
    · rfl
    · split
      · rename_i h
        exact hres _ h.1 h.2 _ _ _ _
      · rfl

theorem atEnd_agree [LawfulMonad m] (loopA loopB : Loop H m R E) (sliceStart : Nat)
    (slice : ByteSlice) (committed : Nat) (core : Core) (batch : Array Lexeme)
    (flow : ControlFlow (Located R)) (hfits : Fits core batch)
    (hres : ∀ r, committed < r → r ≤ slice.size → Agree loopA loopB r r) :
    erase <$> atEnd loopA sliceStart slice committed core batch flow hfits =
      erase <$> atEnd loopB sliceStart slice committed core batch flow hfits := by
  simp only [atEnd, map_bind]
  congr
  funext x
  match x with
  | .proceed core batch flow _ => rfl
  | .fail failure core => rfl
  | .stop stop core flow =>
    simp only
    split
    · rfl
    · split
      · rename_i h
        exact hres _ h.1 h.2 _ _ _ _
      · rfl

/-- The step of the batched lexer's loop at a byte agrees with the step of the lexer over runs
with the batched lexer's loop after it. -/
def StepAgrees (recover : Location → StateT H m Unit) (sliceStart : Nat) (slice : ByteSlice) :
    Prop :=
  ∀ index committed core batch flow hfits (h : index < slice.size),
    erase <$> loop2 recover sliceStart slice index committed core batch flow hfits =
      erase <$> (do
        let ⟨(outcome, core, batch, ⟨next, _⟩), hfits⟩ ←
          lexAt V3Runs.lexIdle recover sliceStart slice index h core batch hfits
        cont (loop2 recover sliceStart slice) sliceStart slice committed flow outcome core batch
          next hfits)

theorem loop2_agree_loop3 [LawfulMonad m] (recover : Location → StateT H m Unit)
    (sliceStart : Nat) (slice : ByteSlice) (hstep : StepAgrees recover sliceStart slice) :
    ∀ a committed, slice.size - committed = a → ∀ b index, slice.size - index = b →
      Agree (loop2 recover sliceStart slice) (loop3 V3Runs.lexIdle recover sliceStart slice)
        index committed := by
  intro a
  refine Nat.strongRecOn a ?_
  intro a iha committed ha b
  refine Nat.strongRecOn b ?_
  intro b ihb index hb core batch flow hfits
  have hres : ∀ r, committed < r → r ≤ slice.size →
      Agree (loop2 recover sliceStart slice) (loop3 V3Runs.lexIdle recover sliceStart slice) r r :=
    fun r h1 h2 => iha (slice.size - r) (by omega) r rfl _ r rfl
  by_cases h : index < slice.size
  · rw [hstep index committed core batch flow hfits h, loop3_lt _ _ _ _ _ _ _ _ _ hfits h,
      map_bind, map_bind]
    congr
    funext x
    obtain ⟨⟨outcome, core, batch, ⟨next, hn⟩⟩, hfits⟩ := x
    exact cont_agree _ _ _ _ _ _ _ _ _ _ _
      (ihb (slice.size - next) (by omega) next rfl) hres
  · rw [loop2_ge _ _ _ _ _ _ _ _ hfits h, loop3_ge _ _ _ _ _ _ _ _ _ hfits h]
    exact atEnd_agree _ _ _ _ _ _ _ _ _ hres

end
end BSmtLib.Proofs.Lexer.V2BatchedV3Runs
