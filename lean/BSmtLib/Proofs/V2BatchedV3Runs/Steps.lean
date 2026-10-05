import BSmtLib.Proofs.V2BatchedV3Runs.Bytes
import BSmtLib.Proofs.V2BatchedV3Runs.Loops

/-!
# Steps of the batched lexer

Facts about the steps that the batched lexer and the lexer over runs share: what a hand-over
(`V2Batched.emit`) leaves of the lexer state, what the loops do after each kind of outcome
(`cont`), and how the batched lexer steps over a run of bytes that a token takes as they are
(`loop2_steps`).
-/

namespace BSmtLib.Proofs.Lexer.V2BatchedV3Runs

open V1Naive V2Batched V3Runs

section

variable {H : Type} {m : Type → Type} {R E : Type} [Monad m] [Consume H m R E]

/-! ## Hand-overs -/

/-- The state a hand-over gives back, as far as it is known from the state handed in: the
location stays, and so does the activity, unless the consumer finished on a token alone. -/
def fixCore (core : Core) (outcome : Outcome R E) (after : Core) : Core :=
  { after with
    location := core.location
    activity := match outcome with
      | .finished _ => .discarding
      | _ => core.activity }

theorem flush_eq [LawfulMonad m] (core : Core) (batch : Array Lexeme) :
    flush (H := H) (m := m) (R := R) (E := E) core batch =
      (fun r => (r.1, { core with
        version := r.2.version
        depth := r.2.foldConsumedCategories core.depth depthAfter })) <$>
        handOverCursor (BatchCursor.new core.version (toTokenBatch batch)) := by
  simp only [flush, map_eq_pure_bind]

theorem emit_eq [LawfulMonad m] (sliceStart : Nat) (core : Core) (batch : Array Lexeme)
    (l : Lexeme) :
    emit (H := H) (m := m) (R := R) (E := E) sliceStart core batch l =
      (fun r => (r.1, fixCore core r.1 r.2.1, r.2.2)) <$> emit sliceStart core batch l := by
  unfold emit
  split
  · rw [flush_eq, bind_map_left, map_bind]
    refine congrArg (_ >>= ·) (funext fun x => ?_)
    obtain ⟨stop, cursor⟩ := x
    cases stop with
    | some stop => simp [fixCore]
    | none =>
      simp only [handOverAt, handOver, bind_assoc, pure_bind, map_bind]
      refine congrArg (_ >>= ·) (funext fun y => ?_)
      obtain ⟨answer, cursor', _⟩ := y
      cases answer with
      | ok flow => cases flow <;> simp [fixCore]
      | error err => simp [fixCore]
  · simp only
    split
    · simp [fixCore]
    · rw [flush_eq, bind_map_left, map_bind]
      refine congrArg (_ >>= ·) (funext fun x => ?_)
      obtain ⟨stop, cursor⟩ := x
      cases stop <;> simp [fixCore]

theorem emit_bind [LawfulMonad m] {β : Type} (sliceStart : Nat) (core : Core)
    (batch : Array Lexeme) (l : Lexeme) (k : Outcome R E × Core × Array Lexeme → StateT H m β) :
    (emit sliceStart core batch l >>= k) =
      (emit sliceStart core batch l >>= fun r => k (r.1, fixCore core r.1 r.2.1, r.2.2)) := by
  conv => lhs; rw [emit_eq]
  rw [bind_map_left]

/-! ## After a step -/

theorem cont_next [LawfulMonad m] (loop : Loop H m R E) (sliceStart : Nat) (slice : ByteSlice)
    (committed : Nat) (flow : ControlFlow (Located R)) (core : Core) (batch : Array Lexeme)
    (next : Nat) :
    cont loop sliceStart slice committed flow .next core batch next =
      loop next committed core batch flow := by
  simp [cont, settle]

theorem cont_finished [LawfulMonad m] (loop : Loop H m R E) (sliceStart : Nat)
    (slice : ByteSlice) (committed : Nat) (flow : ControlFlow (Located R)) (located : Located R)
    (core : Core) (batch : Array Lexeme) (next : Nat) :
    cont loop sliceStart slice committed flow (.finished located) core batch next =
      loop next committed core batch (.break located) := by
  simp [cont, settle]

theorem cont_stopped [LawfulMonad m] (loop : Loop H m R E) (sliceStart : Nat) (slice : ByteSlice)
    (committed : Nat) (flow : ControlFlow (Located R)) (stop : Stop R E) (core : Core)
    (batch : Array Lexeme) (next next' : Nat) :
    cont loop sliceStart slice committed flow (.stopped stop) core batch next =
      cont loop sliceStart slice committed flow (.stopped stop) core batch next' := by
  simp [cont, settle]

theorem blank_eq {c₁ c₂ : Core} (h : blank c₁ = blank c₂) (location : Location)
    (activity : Activity) :
    { c₁ with location, activity } = { c₂ with location, activity } := by
  obtain ⟨v₁, i₁, l₁, a₁, d₁⟩ := c₁
  obtain ⟨v₂, i₂, l₂, a₂, d₂⟩ := c₂
  simp only [blank, Core.mk.injEq] at h ⊢
  simp_all

theorem blank_with {c₁ c₂ : Core} (h : blank c₁ = blank c₂) (version : Version) (depth : Nat) :
    blank { c₁ with version, depth } = blank { c₂ with version, depth } := by
  obtain ⟨v₁, i₁, l₁, a₁, d₁⟩ := c₁
  obtain ⟨v₂, i₂, l₂, a₂, d₂⟩ := c₂
  simp only [blank, Core.mk.injEq] at h ⊢
  simp_all

theorem blank_version {c₁ c₂ : Core} (h : blank c₁ = blank c₂) : c₁.version = c₂.version := by
  have := congrArg Core.version h
  exact this

theorem blank_depth {c₁ c₂ : Core} (h : blank c₁ = blank c₂) : c₁.depth = c₂.depth := by
  have := congrArg Core.depth h
  exact this

/-- After a failure, the loops do not depend on where they go on, nor, up to `erase`, on the
location and the activity of the state. -/
theorem cont_failed [LawfulMonad m] (loop : Loop H m R E) (sliceStart : Nat) (slice : ByteSlice)
    (committed : Nat) (flow : ControlFlow (Located R)) (failure : Failure E) {c₁ c₂ : Core}
    (h : blank c₁ = blank c₂) (batch : Array Lexeme) (next₁ next₂ : Nat) :
    erase <$> cont loop sliceStart slice committed flow (.failed failure) c₁ batch next₁ =
      erase <$> cont loop sliceStart slice committed flow (.failed failure) c₂ batch next₂ := by
  simp only [cont, settle, flush_eq, bind_map_left, bind_assoc, pure_bind, map_bind,
    blank_version h, blank_depth h]
  refine congrArg (_ >>= ·) (funext fun x => ?_)
  obtain ⟨stop, cursor⟩ := x
  cases stop with
  | none => simp [erase, blank_with h]
  | some stop =>
    simp only
    split
    · simp [erase, blank_with h]
    · split
      · rw [blank_eq (blank_with h _ _)]
      · simp [erase, blank_with h]

/-! ## Runs of bytes -/

/-- The batched lexer's step at a byte in a token, as the naive lexer's step `advance` has it go
on. -/
theorem loop2_pending [LawfulMonad m] (recover : Location → StateT H m Unit) (sliceStart : Nat)
    (slice : ByteSlice) (committed : Nat) (batch : Array Lexeme) (flow : ControlFlow (Located R))
    (i : Nat) (hi : i < slice.size) (p p' : Pending) (core : Core) (hact : core.activity = .token p)
    (hadv : advance (Consume.consumesWhitespaceAndComments (H := H)) p core.location slice[i] =
      .pending p') :
    loop2 recover sliceStart slice i committed core batch flow =
      loop2 recover sliceStart slice (i + 1) committed
        { core with activity := .token p', location := core.location.afterByte slice[i] } batch
        flow := by
  rw [loop2_lt _ _ _ _ _ _ _ _ hi]
  simp only [V2Batched.lexByte, hact, hadv, pure_bind]
  exact cont_next _ _ _ _ _ _ _ _

/--
The batched lexer steps over a run of bytes that a token takes as they are, as the lexer over
runs takes them in one go: the bytes that pass `pred` extend the content of a token in the mode
`mode` and are not line feeds.
-/
theorem loop2_steps [LawfulMonad m] (recover : Location → StateT H m Unit) (sliceStart : Nat)
    (slice : ByteSlice) (committed : Nat) (batch : Array Lexeme) (flow : ControlFlow (Located R))
    (pred : UInt8 → Bool) (mode : Mode)
    (hstep : ∀ (q : Pending) location c, q.mode = mode → pred c = true →
      advance (Consume.consumesWhitespaceAndComments (H := H)) q location c =
        .pending { q with content := q.content.push c })
    (hnl : ∀ c, pred c = true → c ≠ 10) :
    ∀ n i, slice.size - i = n → i ≤ slice.size → ∀ (p : Pending) (core : Core),
      p.mode = mode → core.activity = .token p →
      loop2 recover sliceStart slice i committed core batch flow =
        loop2 recover sliceStart slice (runEnd slice pred i) committed
          { core with
            activity :=
              .token { p with content := p.content ++ bytesOf slice i (runEnd slice pred i) }
            location := afterColumns core.location (runEnd slice pred i - i) } batch flow := by
  intro n
  induction n with
  | zero =>
    intro i hn hi p core hm hact
    have hend : runEnd slice pred i = i := by
      rw [runEnd]; simp only [show ¬ i < slice.size by omega, dite_false]
    rw [hend, bytesOf_self slice i hi, ByteArray.append_empty, Nat.sub_self, afterColumns_zero]
    obtain ⟨v, iv, loc, act, d⟩ := core
    simp only at hact
    subst hact
    rfl
  | succ n ih =>
    intro i hn hi p core hm hact
    have hlt : i < slice.size := by omega
    by_cases hp : pred slice[i] = true
    · have hend : runEnd slice pred i = runEnd slice pred (i + 1) := by
        rw [runEnd]; simp only [hlt, dite_true, hp, ite_true]
      have hle := le_runEnd slice pred (i + 1)
      rw [loop2_pending recover sliceStart slice committed batch flow i hlt p _ core hact
        (hstep p core.location slice[i] hm hp)]
      rw [ih (i + 1) (by omega) (by omega) { p with content := p.content.push slice[i] } _ hm rfl,
        hend]
      simp only [
        push_append_bytesOf p.content slice hlt (by omega)
          (runEnd_le slice pred (i + 1) (by omega)),
        afterColumns_afterByte core.location slice[i] (hnl _ hp)]
      congr 3
      omega
    · have hend : runEnd slice pred i = i := by
        rw [runEnd]; simp only [hlt, dite_true, hp]; rfl
      rw [hend, bytesOf_self slice i hi, ByteArray.append_empty, Nat.sub_self, afterColumns_zero]
      obtain ⟨v, iv, loc, act, d⟩ := core
      simp only at hact
      subst hact
      rfl

end

end BSmtLib.Proofs.Lexer.V2BatchedV3Runs
