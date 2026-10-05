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

theorem flush_eq [LawfulMonad m] (core : Core) (batch : Array Lexeme) (h : Ordered 0 batch.toList) :
    flush (H := H) (m := m) (R := R) (E := E) core batch h =
      (fun r => (r.1, { core with
        version := r.2.version
        depth := r.2.foldConsumedCategories core.depth depthAfter })) <$>
        handOverCursor (BatchCursor.new core.version (toTokenBatch batch h)) := by
  simp only [flush, map_eq_pure_bind]

/-- What a hand-over gives back from the state `core`. -/
abbrev EmitResult (R E : Type) (core : Core) :=
  {r : Outcome R E × Core × Array Lexeme // Fits r.2.1 r.2.2 ∧ r.2.1 = fixCore core r.1 r.2.1}

/-- What a hand-over gave back, with its state written as `fixCore` gives it. -/
def fixResult (core : Core) (r : EmitResult R E core) : EmitResult R E core :=
  ⟨(r.1.1, fixCore core r.1.1 r.1.2.1, r.1.2.2), r.2.2 ▸ r.2.1,
    (fixCore_fixCore core r.1.1 r.1.2.1).symm⟩

theorem fixResult_eq (core : Core) (r : EmitResult R E core) : fixResult core r = r := by
  obtain ⟨⟨o, c, b⟩, hf, hfix⟩ := r
  apply Subtype.ext
  simp only [fixResult]
  rw [← hfix]

theorem emit_bind {β : Type} (sliceStart : Nat) (core : Core) (batch : Array Lexeme) (l : Lexeme)
    (h : Ordered 0 batch.toList) (hstart : lastEnd 0 batch.toList ≤ l.start.offset)
    (hl : l.Valid) (hend : l.end.offset ≤ core.frontier)
    (k : EmitResult R E core → StateT H m β) :
    (emit sliceStart core batch l h hstart hl hend >>= k) =
      (emit sliceStart core batch l h hstart hl hend >>= fun r => k (fixResult core r)) := by
  simp only [fixResult_eq]

/-- Hand-overs of equal lexemes from equal states, followed by continuations that agree on each
result, are the same, whatever the proofs. -/
theorem emit_bind_congr {β : Type} {sliceStart : Nat} {c₁ c₂ : Core} (e : c₁ = c₂)
    {batch : Array Lexeme} {l₁ l₂ : Lexeme} (el : l₁ = l₂) {h : Ordered 0 batch.toList}
    {hstart₁ : lastEnd 0 batch.toList ≤ l₁.start.offset}
    {hstart₂ : lastEnd 0 batch.toList ≤ l₂.start.offset} {hl₁ : l₁.Valid} {hl₂ : l₂.Valid}
    {hend₁ : l₁.end.offset ≤ c₁.frontier} {hend₂ : l₂.end.offset ≤ c₂.frontier}
    {k₁ : EmitResult R E c₁ → StateT H m β} {k₂ : EmitResult R E c₂ → StateT H m β}
    (hk : ∀ o c b hf₁ hx₁ hf₂ hx₂,
      k₁ ⟨(o, c, b), hf₁, hx₁⟩ = k₂ ⟨(o, c, b), hf₂, hx₂⟩) :
    (emit sliceStart c₁ batch l₁ h hstart₁ hl₁ hend₁ >>= k₁) =
      (emit sliceStart c₂ batch l₂ h hstart₂ hl₂ hend₂ >>= k₂) := by
  subst e el
  refine congrArg (_ >>= ·) (funext fun r => ?_)
  obtain ⟨⟨o, c, b⟩, hf, hx⟩ := r
  exact hk o c b hf hx hf hx

/-! ## After a step -/

theorem cont_next [LawfulMonad m] (loop : Loop H m R E) (sliceStart : Nat) (slice : ByteSlice)
    (committed : Nat) (flow : ControlFlow (Located R)) (core : Core) (batch : Array Lexeme)
    (next : Nat) (hfits : Fits core batch) :
    cont loop sliceStart slice committed flow .next core batch next hfits =
      loop next committed core batch flow hfits := by
  simp [cont, settle]

theorem cont_finished [LawfulMonad m] (loop : Loop H m R E) (sliceStart : Nat)
    (slice : ByteSlice) (committed : Nat) (flow : ControlFlow (Located R)) (located : Located R)
    (core : Core) (batch : Array Lexeme) (next : Nat) (hfits : Fits core batch) :
    cont loop sliceStart slice committed flow (.finished located) core batch next hfits =
      loop next committed core batch (.break located) hfits := by
  simp [cont, settle]

theorem cont_stopped [LawfulMonad m] (loop : Loop H m R E) (sliceStart : Nat) (slice : ByteSlice)
    (committed : Nat) (flow : ControlFlow (Located R)) (stop : Stop R E) (core : Core)
    (batch : Array Lexeme) (next next' : Nat) (hfits hfits' : Fits core batch) :
    cont loop sliceStart slice committed flow (.stopped stop) core batch next hfits =
      cont loop sliceStart slice committed flow (.stopped stop) core batch next' hfits' := by
  simp [cont, settle]

theorem blank_eq {c₁ c₂ : Core} (h : blank c₁ = blank c₂) (location : Location)
    (activity : Activity) (hs : activity.StartsBefore location) :
    { c₁ with location, activity, startedBefore := hs } =
      { c₂ with location, activity, startedBefore := hs } := by
  obtain ⟨v₁, i₁, l₁, a₁, d₁, s₁⟩ := c₁
  obtain ⟨v₂, i₂, l₂, a₂, d₂, s₂⟩ := c₂
  simp only [blank, Core.mk.injEq] at h ⊢
  simp_all

theorem blank_with {c₁ c₂ : Core} (h : blank c₁ = blank c₂) (version : Version) (depth : Nat) :
    blank { c₁ with version, depth } = blank { c₂ with version, depth } := by
  obtain ⟨v₁, i₁, l₁, a₁, d₁, s₁⟩ := c₁
  obtain ⟨v₂, i₂, l₂, a₂, d₂, s₂⟩ := c₂
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
    (h : blank c₁ = blank c₂) (batch : Array Lexeme) (next₁ next₂ : Nat)
    (h₁ : Fits c₁ batch) (h₂ : Fits c₂ batch) :
    erase <$> cont loop sliceStart slice committed flow (.failed failure) c₁ batch next₁ h₁ =
      erase <$> cont loop sliceStart slice committed flow (.failed failure) c₂ batch next₂ h₂ := by
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
      · exact congrArg (erase <$> ·) (loop_congr loop (blank_eq (blank_with h _ _) _ _ _))
      · simp [erase, blank_with h]

/-! ## Runs of bytes -/

/-- The loop from equal states is the same, whatever the proofs that the batch fits. -/
theorem loop2_congr {recover : Location → StateT H m Unit} {sliceStart : Nat} {slice : ByteSlice}
    {index committed : Nat} {core core' : Core} {batch : Array Lexeme}
    {flow : ControlFlow (Located R)} {h : Fits core batch} {h' : Fits core' batch}
    (e : core = core') :
    loop2 recover sliceStart slice index committed core batch flow h =
      loop2 recover sliceStart slice index committed core' batch flow h' := by
  subst e
  rfl

/-- The batched lexer's step at a byte in a token, as the naive lexer's step `advance` has it go
on. -/
theorem loop2_pending [LawfulMonad m] (recover : Location → StateT H m Unit) (sliceStart : Nat)
    (slice : ByteSlice) (committed : Nat) (batch : Array Lexeme) (flow : ControlFlow (Located R))
    (i : Nat) (hi : i < slice.size) (p p' : Pending) (core : Core) (hact : core.activity = .token p)
    (hfits : Fits core batch)
    (hadv : advance (Consume.consumesWhitespaceAndComments (H := H)) p core.location slice[i] =
      .pending p')
    (hs : (Activity.token p').StartsBefore (core.location.afterByte slice[i]))
    (hfits' : Fits
      { core with
        activity := .token p', location := core.location.afterByte slice[i], startedBefore := hs }
      batch) :
    loop2 recover sliceStart slice i committed core batch flow hfits =
      loop2 recover sliceStart slice (i + 1) committed
        { core with
          activity := .token p', location := core.location.afterByte slice[i], startedBefore := hs }
        batch flow hfits' := by
  rw [loop2_lt _ _ _ _ _ _ _ _ _ hi]
  simp only [V2Batched.lexByte, withEq, hact, advanceS, hadv, pure_bind]
  exact cont_next _ _ _ _ _ _ _ _ _

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
      p.mode = mode → (hact : core.activity = .token p) → (hfits : Fits core batch) →
      ∀ hs hfits',
      loop2 recover sliceStart slice i committed core batch flow hfits =
        loop2 recover sliceStart slice (runEnd slice pred i) committed
          { core with
            activity :=
              .token { p with content := p.content ++ bytesOf slice i (runEnd slice pred i) }
            location := afterColumns core.location (runEnd slice pred i - i)
            startedBefore := hs } batch flow hfits' := by
  intro n
  induction n with
  | zero =>
    intro i hn hi p core hm hact hfits hs hfits'
    have hend : runEnd slice pred i = i := by
      rw [runEnd]; simp only [show ¬ i < slice.size by omega, dite_false]
    revert hs hfits'
    rw [hend, bytesOf_self slice i hi, ByteArray.append_empty, Nat.sub_self, afterColumns_zero]
    intro hs hfits'
    obtain ⟨v, iv, loc, act, d, s⟩ := core
    simp only at hact
    subst hact
    rfl
  | succ n ih =>
    intro i hn hi p core hm hact hfits hs hfits'
    have hlt : i < slice.size := by omega
    have hp : p.start.offset < core.location.offset := core.started hact
    have hfront : core.frontier = p.start.offset := by unfold Core.frontier; rw [hact]
    by_cases hpr : pred slice[i] = true
    · have hend : runEnd slice pred i = runEnd slice pred (i + 1) := by
        rw [runEnd]; simp only [hlt, dite_true, hpr, ite_true]
      have hle := le_runEnd slice pred (i + 1)
      have hs1 : (Activity.token { p with content := p.content.push slice[i] }).StartsBefore
          (core.location.afterByte slice[i]) := by
        show p.start.offset < (core.location.afterByte slice[i]).offset
        rw [afterByte_offset]; omega
      rw [loop2_pending recover sliceStart slice committed batch flow i hlt p _ core hact hfits
        (hstep p core.location slice[i] hm hpr) hs1
        (hfits.mono (Nat.le_of_eq hfront))]
      rw [ih (i + 1) (by omega) (by omega) { p with content := p.content.push slice[i] } _ hm rfl
        _ ?hs2 ?hf2]
      case hs2 =>
        show p.start.offset < (afterColumns _ _).offset
        simp only [afterColumns_offset, afterByte_offset]; omega
      case hf2 => exact hfits.mono (Nat.le_of_eq hfront)
      revert hs hfits'
      rw [hend]
      intro hs hfits'
      apply loop2_congr
      have e : runEnd slice pred (i + 1) - (i + 1) + 1 = runEnd slice pred (i + 1) - i := by omega
      simp only [
        push_append_bytesOf p.content slice hlt (by omega)
          (runEnd_le slice pred (i + 1) (by omega)),
        afterColumns_afterByte core.location slice[i] (hnl _ hpr), e]
    · have hend : runEnd slice pred i = i := by
        rw [runEnd]; simp only [hlt, dite_true, hpr]; rfl
      revert hs hfits'
      rw [hend, bytesOf_self slice i hi, ByteArray.append_empty, Nat.sub_self, afterColumns_zero]
      intro hs hfits'
      obtain ⟨v, iv, loc, act, d, s⟩ := core
      simp only at hact
      subst hact
      rfl

end

end BSmtLib.Proofs.Lexer.V2BatchedV3Runs
