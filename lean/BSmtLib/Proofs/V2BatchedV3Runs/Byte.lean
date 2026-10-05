import BSmtLib.Proofs.V2BatchedV3Runs.Steps

/-!
# A byte in a token

What the batched lexer does at one byte of a token in progress, stated as what the lexer over
runs makes of its result (`expand`). `byteRan` is the result of the naive lexer's step
`advance` at the byte, in the form of the lexer over runs' `V3Runs.Ran`, with the run going on
after the byte if the token does.
-/

namespace BSmtLib.Proofs.Lexer.V2BatchedV3Runs

open V1Naive V2Batched V3Runs

/-- The naive lexer's step at the byte at `j` of the token `q` at `location`, in the form of the
lexer over runs, which goes on with the run after the byte if the token does. -/
def byteRan (whitespace : Bool) (slice : ByteSlice) (q : Pending) (j : Nat) (h : j < slice.size)
    (location : Location) : Ran slice.size j :=
  match advance whitespace q location slice[j] with
  | .pending q' => (run whitespace slice q' (j + 1) (location.afterByte slice[j])).lift (by omega)
  | .idle => .idle (j + 1) (location.afterByte slice[j]) (by omega)
  | .tokenWith l => .tokenWith l (j + 1) (by omega)
  | .tokenBefore l => .tokenBefore l j (Nat.le_refl _) h
  | .error failure => .error failure

/-- The token `q` at `location` from the byte at `j` on: the naive lexer's step at the byte, or,
at the end of the slice, the token left in progress. -/
def runOrPending (whitespace : Bool) (slice : ByteSlice) (q : Pending) (j : Nat)
    (location : Location) : Ran slice.size j :=
  if h : j < slice.size then byteRan whitespace slice q j h location else .pending q location

section

variable {H : Type} {m : Type → Type} {R E : Type} [Monad m] [Consume H m R E]

/--
What the batched lexer's loop does after a token in progress in `core` was lexed by the lexer
over runs to `ran`. Where the token ends before a byte, the byte is lexed at once with no token
in progress, as both lexers do.
-/
def expand (recover : Location → StateT H m Unit) (sliceStart : Nat) (slice : ByteSlice)
    (committed : Nat) (flow : ControlFlow (Located R)) (core : Core) (batch : Array Lexeme)
    {i : Nat} : Ran slice.size i →
      StateT H m (Except (Failure E) (ControlFlow (Located R)) × Core)
  | .pending p location =>
    loop2 recover sliceStart slice slice.size committed
      { core with activity := .token p, location } batch flow
  | .idle next location _ =>
    loop2 recover sliceStart slice next committed { core with activity := .idle, location } batch
      flow
  | .tokenWith l next _ => do
    let (outcome, core, batch) ←
      emit sliceStart { core with activity := .idle, location := l.end } batch l
    cont (loop2 recover sliceStart slice) sliceStart slice committed flow outcome core batch next
  | .tokenBefore l next _ inside => do
    let (outcome, core, batch) ←
      emit sliceStart { core with activity := .idle, location := l.end } batch l
    match outcome with
    | .next => do
      let (outcome, core, batch) ← V2Batched.lexStart sliceStart core batch slice[next]
      cont (loop2 recover sliceStart slice) sliceStart slice committed flow outcome core batch
        (next + 1)
    | .finished located =>
      cont (loop2 recover sliceStart slice) sliceStart slice committed flow (.finished located)
        { core with location := core.location.afterByte slice[next] } batch (next + 1)
    | outcome =>
      cont (loop2 recover sliceStart slice) sliceStart slice committed flow outcome core batch
        (next + 1)
  | .error failure =>
    cont (loop2 recover sliceStart slice) sliceStart slice committed flow
      (.failed { cause := .lexical failure.error, location := failure.location }) core batch 0

theorem expand_lift (recover : Location → StateT H m Unit) (sliceStart : Nat) (slice : ByteSlice)
    (committed : Nat) (flow : ControlFlow (Located R)) (core : Core) (batch : Array Lexeme)
    {i i' : Nat} (h : i ≤ i') (r : Ran slice.size i') :
    expand recover sliceStart slice committed flow core batch (r.lift h) =
      expand recover sliceStart slice committed flow core batch r := by
  cases r <;> rfl

theorem expand_blank [LawfulMonad m] (recover : Location → StateT H m Unit) (sliceStart : Nat)
    (slice : ByteSlice) (committed : Nat) (flow : ControlFlow (Located R)) {c₁ c₂ : Core}
    (hb : blank c₁ = blank c₂) (batch : Array Lexeme) {i : Nat} (r : Ran slice.size i) :
    erase <$> expand recover sliceStart slice committed flow c₁ batch r =
      erase <$> expand recover sliceStart slice committed flow c₂ batch r := by
  cases r with
  | pending p location => simp only [expand, blank_eq hb]
  | idle next location _ => simp only [expand, blank_eq hb]
  | tokenWith l next _ => simp only [expand, blank_eq hb]
  | tokenBefore l next _ _ => simp only [expand, blank_eq hb]
  | error failure => exact cont_failed _ _ _ _ _ _ hb _ _ _

/-! ## The naive lexer's step -/

/-- A token that ends with the byte ends after it. -/
theorem advance_tokenWith {whitespace : Bool} {p : Pending} {location : Location} {c : UInt8}
    {l : Lexeme} (h : advance whitespace p location c = .tokenWith l) :
    l.end = location.afterByte c := by
  rcases p with ⟨mode, start, content⟩
  cases mode <;> simp only [advance, legacyStringByte] at h <;>
    (repeat' split at h) <;> simp_all <;> (subst h; rfl)

/-- A token that ends before the byte ends at it. -/
theorem advance_tokenBefore {whitespace : Bool} {p : Pending} {location : Location} {c : UInt8}
    {l : Lexeme} (h : advance whitespace p location c = .tokenBefore l) :
    l.end = location := by
  rcases p with ⟨mode, start, content⟩
  cases mode <;> simp only [advance, legacyStringByte] at h <;>
    (repeat' split at h) <;> simp_all <;> (subst h; rfl)

/--
The batched lexer's loop at a byte of a token in progress does what the lexer over runs makes
of the naive lexer's step at the byte, given that from the next byte on it does what the lexer
over runs makes of the rest of the token.
-/
theorem loop2_byte [LawfulMonad m] (recover : Location → StateT H m Unit) (sliceStart : Nat)
    (slice : ByteSlice) (committed : Nat) (flow : ControlFlow (Located R)) (batch : Array Lexeme)
    (j : Nat) (hj : j < slice.size) (q : Pending) (core : Core) (hact : core.activity = .token q)
    (ih : ∀ (q' : Pending) (core' : Core), core'.activity = .token q' →
      erase <$> loop2 recover sliceStart slice (j + 1) committed core' batch flow =
        erase <$> expand recover sliceStart slice committed flow core' batch
          (run (Consume.consumesWhitespaceAndComments (H := H)) slice q' (j + 1)
            core'.location)) :
    erase <$> loop2 recover sliceStart slice j committed core batch flow =
      erase <$> expand recover sliceStart slice committed flow core batch
        (byteRan (Consume.consumesWhitespaceAndComments (H := H)) slice q j hj
          core.location) := by
  rw [loop2_lt _ _ _ _ _ _ _ _ hj]
  unfold byteRan
  cases hadv : advance (Consume.consumesWhitespaceAndComments (H := H)) q core.location
      slice[j] with
  | pending q' =>
    simp only [V2Batched.lexByte, hact, hadv, pure_bind, cont_next, expand_lift]
    rw [ih q' _ rfl]
    refine expand_blank (H := H) (m := m) (R := R) (E := E) _ _ _ _ _ ?_ _ _
    rfl
  | idle =>
    simp only [V2Batched.lexByte, hact, hadv, pure_bind, cont_next, expand]
  | tokenWith l =>
    simp only [V2Batched.lexByte, hact, hadv, expand, advance_tokenWith hadv]
  | tokenBefore l =>
    have hl := advance_tokenBefore hadv
    simp only [V2Batched.lexByte, hact, hadv, bind_assoc, expand]
    rw [hl]
    conv => lhs; rw [emit_bind]
    conv => rhs; rw [emit_bind]
    refine congrArg (fun x => erase <$> x) ?_
    refine congrArg (_ >>= ·) (funext fun r => ?_)
    obtain ⟨outcome, c, b⟩ := r
    cases outcome <;> simp [fixCore]
  | error failure =>
    simp only [V2Batched.lexByte, hact, hadv, pure_bind, expand]
    exact cont_failed _ _ _ _ _ _ rfl _ _ _

end

end BSmtLib.Proofs.Lexer.V2BatchedV3Runs
