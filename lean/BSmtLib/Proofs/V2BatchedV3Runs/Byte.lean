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

theorem byteRan_spec (whitespace : Bool) (slice : ByteSlice) (q : Pending) (j : Nat)
    (h : j < slice.size) (location : Location) :
    (byteRan whitespace slice q j h location).Spec q location := by
  unfold byteRan
  split
  · rename_i q' hadv
    exact Ran.spec_lift (Ran.Spec.weaken (run_spec _ _ _ _ _) (advance_pending hadv)
      (by rw [afterByte_offset]; omega))
  · show location.offset ≤ (location.afterByte _).offset
    rw [afterByte_offset]; omega
  · rename_i l hadv
    exact ⟨(advance_tokenWith hadv).1, by rw [(advance_tokenWith hadv).2, afterByte_offset]; omega⟩
  · rename_i l hadv
    exact ⟨(advance_tokenBefore hadv).1, Nat.le_of_eq (by rw [(advance_tokenBefore hadv).2])⟩
  · trivial

/-- The token `q` at `location` from the byte at `j` on: the naive lexer's step at the byte, or,
at the end of the slice, the token left in progress. -/
def runOrPending (whitespace : Bool) (slice : ByteSlice) (q : Pending) (j : Nat)
    (location : Location) : Ran slice.size j :=
  if h : j < slice.size then byteRan whitespace slice q j h location else .pending q location

theorem runOrPending_spec (whitespace : Bool) (slice : ByteSlice) (q : Pending) (j : Nat)
    (location : Location) : (runOrPending whitespace slice q j location).Spec q location := by
  unfold runOrPending
  split
  · exact byteRan_spec _ _ _ _ _ _
  · exact ⟨rfl, Nat.le_refl _⟩

/-- The batch fits a state with the token in progress, so it ends at or before the start of
the token. -/
theorem Fits.le_start {core : Core} {batch : Array Lexeme} {p : Pending} (h : Fits core batch)
    (hact : core.activity = .token p) : lastEnd 0 batch.toList ≤ p.start.offset :=
  Nat.le_trans h.2 (Nat.le_of_eq (by unfold Core.frontier; rw [hact]))

section

variable {H : Type} {m : Type → Type} {R E : Type} [Monad m] [Consume H m R E]

/-- What the batched lexer's loop does after the token `l` ended with a byte, handed over from
the state `core`, going on at `next`. -/
def expandWith (recover : Location → StateT H m Unit) (sliceStart : Nat) (slice : ByteSlice)
    (committed : Nat) (flow : ControlFlow (Located R)) (core : Core) (batch : Array Lexeme)
    (l : Lexeme) (next : Nat) (h : Ordered 0 batch.toList)
    (hstart : lastEnd 0 batch.toList ≤ l.start.offset) (hl : l.Valid)
    (hend : l.end.offset ≤ core.frontier) :
    StateT H m (Except (Failure E) (ControlFlow (Located R)) × Core) := do
  let ⟨(outcome, core, batch), hfits, _⟩ ← emit sliceStart core batch l h hstart hl hend
  cont (loop2 recover sliceStart slice) sliceStart slice committed flow outcome core batch next
    hfits

/-- What the batched lexer's loop does after the token `l` ended before the byte at `next`,
handed over from the state `core`: it lexes the byte with no token in progress. -/
def expandBefore (recover : Location → StateT H m Unit) (sliceStart : Nat) (slice : ByteSlice)
    (committed : Nat) (flow : ControlFlow (Located R)) (core : Core) (batch : Array Lexeme)
    (l : Lexeme) (next : Nat) (inside : next < slice.size) (h : Ordered 0 batch.toList)
    (hstart : lastEnd 0 batch.toList ≤ l.start.offset) (hl : l.Valid)
    (hend : l.end.offset ≤ core.frontier) :
    StateT H m (Except (Failure E) (ControlFlow (Located R)) × Core) := do
  let ⟨(outcome, core, batch), hfits, _⟩ ← emit sliceStart core batch l h hstart hl hend
  match outcome with
  | .next => do
    let ⟨(outcome, core, batch), hfits⟩ ←
      V2Batched.lexStart sliceStart core batch slice[next] hfits
    cont (loop2 recover sliceStart slice) sliceStart slice committed flow outcome core batch
      (next + 1) hfits
  | .finished located =>
    cont (loop2 recover sliceStart slice) sliceStart slice committed flow (.finished located)
      { core with
        location := core.location.afterByte slice[next], activity := .discarding
        startedBefore := trivial } batch (next + 1)
      (hfits.mono (show core.frontier ≤ (core.location.afterByte slice[next]).offset by
        have := core.frontier_le
        rw [afterByte_offset]
        omega))
  | outcome =>
    cont (loop2 recover sliceStart slice) sliceStart slice committed flow outcome core batch
      (next + 1) hfits

/--
What the batched lexer's loop does after a token in progress in `core` was lexed by the lexer
over runs to `ran`. Where the token ends before a byte, the byte is lexed at once with no token
in progress, as both lexers do. The token `p` was lexed from `location` on, where the batch
ends.
-/
def expand (recover : Location → StateT H m Unit) (sliceStart : Nat) (slice : ByteSlice)
    (committed : Nat) (flow : ControlFlow (Located R)) (core : Core) (batch : Array Lexeme)
    (p : Pending) (location : Location) (hfits : Fits core batch)
    (hlast : lastEnd 0 batch.toList ≤ p.start.offset) (hstart : p.start.offset < location.offset)
    {i : Nat} : (r : Ran slice.size i) → r.Spec p location →
      StateT H m (Except (Failure E) (ControlFlow (Located R)) × Core)
  | .pending p' location', hr =>
    loop2 recover sliceStart slice slice.size committed
      { core with
        activity := .token p', location := location'
        startedBefore := show p'.start.offset < location'.offset by
          rw [hr.1]; exact Nat.lt_of_lt_of_le hstart hr.2 }
      batch flow ⟨hfits.1, show _ ≤ p'.start.offset by rw [hr.1]; exact hlast⟩
  | .idle next location' _, hr =>
    loop2 recover sliceStart slice next committed
      { core with activity := .idle, location := location', startedBefore := trivial } batch
      flow ⟨hfits.1, show _ ≤ location'.offset by
        have : location.offset ≤ location'.offset := hr
        omega⟩
  | .tokenWith l next _, hr =>
    expandWith recover sliceStart slice committed flow
      { core with activity := .idle, location := l.end, startedBefore := trivial } batch l next
      hfits.1 (by rw [hr.1]; exact hlast) (.inl (by rw [hr.1]; exact Nat.lt_trans hstart hr.2))
      (Nat.le_refl _)
  | .tokenBefore l next _ inside, hr =>
    expandBefore recover sliceStart slice committed flow
      { core with activity := .idle, location := l.end, startedBefore := trivial } batch l next
      inside hfits.1 (by rw [hr.1]; exact hlast)
      (.inl (by rw [hr.1]; exact Nat.lt_of_lt_of_le hstart hr.2)) (Nat.le_refl _)
  | .error failure, _ =>
    cont (loop2 recover sliceStart slice) sliceStart slice committed flow
      (.failed { cause := .lexical failure.error, location := failure.location }) core batch 0
      hfits

theorem expand_lift (recover : Location → StateT H m Unit) (sliceStart : Nat) (slice : ByteSlice)
    (committed : Nat) (flow : ControlFlow (Located R)) (core : Core) (batch : Array Lexeme)
    (p : Pending) (location : Location) (hfits : Fits core batch)
    (hlast : lastEnd 0 batch.toList ≤ p.start.offset) (hstart : p.start.offset < location.offset)
    {i i' : Nat} (h : i ≤ i') (r : Ran slice.size i') (hr' : (r.lift h).Spec p location)
    (hr : r.Spec p location) :
    expand recover sliceStart slice committed flow core batch p location hfits hlast hstart
        (r.lift h) hr' =
      expand recover sliceStart slice committed flow core batch p location hfits hlast hstart r
        hr := by
  cases r <;> rfl

theorem expand_blank [LawfulMonad m] (recover : Location → StateT H m Unit) (sliceStart : Nat)
    (slice : ByteSlice) (committed : Nat) (flow : ControlFlow (Located R)) {c₁ c₂ : Core}
    (hb : blank c₁ = blank c₂) (batch : Array Lexeme) (p : Pending) (location : Location)
    (h₁ : Fits c₁ batch) (h₂ : Fits c₂ batch) (hlast : lastEnd 0 batch.toList ≤ p.start.offset)
    (hstart : p.start.offset < location.offset) {i : Nat} (r : Ran slice.size i)
    (hr : r.Spec p location) :
    erase <$> expand recover sliceStart slice committed flow c₁ batch p location h₁ hlast hstart r
        hr =
      erase <$> expand recover sliceStart slice committed flow c₂ batch p location h₂ hlast hstart
        r hr := by
  cases r with
  | error failure => exact cont_failed _ _ _ _ _ _ hb _ _ _ _ _
  | _ =>
    obtain ⟨v₁, i₁, l₁, a₁, d₁, s₁⟩ := c₁
    obtain ⟨v₂, i₂, l₂, a₂, d₂, s₂⟩ := c₂
    simp only [blank, Core.mk.injEq] at hb
    obtain ⟨rfl, rfl, -, -, rfl⟩ := hb
    first | rfl | (simp only [expand]; congr)

/-- What the loop makes of the token lexed by the lexer over runs depends, up to `erase`, only
on the result of the run and on the state but its location and activity. -/
theorem expand_congr [LawfulMonad m] (recover : Location → StateT H m Unit) (sliceStart : Nat)
    (slice : ByteSlice) (committed : Nat) (flow : ControlFlow (Located R)) {c₁ c₂ : Core}
    (hb : blank c₁ = blank c₂) (batch : Array Lexeme) {p₁ p₂ : Pending}
    {location₁ location₂ : Location} (h₁ : Fits c₁ batch) (h₂ : Fits c₂ batch)
    (hlast₁ : lastEnd 0 batch.toList ≤ p₁.start.offset)
    (hlast₂ : lastEnd 0 batch.toList ≤ p₂.start.offset)
    (hstart₁ : p₁.start.offset < location₁.offset) (hstart₂ : p₂.start.offset < location₂.offset)
    {i : Nat} (r : Ran slice.size i) (hr₁ : r.Spec p₁ location₁) (hr₂ : r.Spec p₂ location₂) :
    erase <$> expand recover sliceStart slice committed flow c₁ batch p₁ location₁ h₁ hlast₁
        hstart₁ r hr₁ =
      erase <$> expand recover sliceStart slice committed flow c₂ batch p₂ location₂ h₂ hlast₂
        hstart₂ r hr₂ := by
  cases r with
  | error failure => exact cont_failed _ _ _ _ _ _ hb _ _ _ _ _
  | _ =>
    obtain ⟨v₁, i₁, l₁, a₁, d₁, s₁⟩ := c₁
    obtain ⟨v₂, i₂, l₂, a₂, d₂, s₂⟩ := c₂
    simp only [blank, Core.mk.injEq] at hb
    obtain ⟨rfl, rfl, -, -, rfl⟩ := hb
    rfl

/--
The batched lexer's loop at a byte of a token in progress does what the lexer over runs makes
of the naive lexer's step at the byte, given that from the next byte on it does what the lexer
over runs makes of the rest of the token.
-/
theorem loop2_byte [LawfulMonad m] (recover : Location → StateT H m Unit) (sliceStart : Nat)
    (slice : ByteSlice) (committed : Nat) (flow : ControlFlow (Located R)) (batch : Array Lexeme)
    (j : Nat) (hj : j < slice.size) (q : Pending) (core : Core) (hact : core.activity = .token q)
    (hfits : Fits core batch)
    (ih : ∀ (q' : Pending) (core' : Core) (hact' : core'.activity = .token q')
      (hfits' : Fits core' batch) (r : Ran slice.size (j + 1)) (hr : r.Spec q' core'.location),
      r = run (Consume.consumesWhitespaceAndComments (H := H)) slice q' (j + 1) core'.location →
      erase <$> loop2 recover sliceStart slice (j + 1) committed core' batch flow hfits' =
        erase <$> expand recover sliceStart slice committed flow core' batch q' core'.location
          hfits' (Fits.le_start hfits' hact') (core'.started hact') r hr)
    (r : Ran slice.size j) (hr : r.Spec q core.location)
    (hr0 : r = byteRan (Consume.consumesWhitespaceAndComments (H := H)) slice q j hj
      core.location) :
    erase <$> loop2 recover sliceStart slice j committed core batch flow hfits =
      erase <$> expand recover sliceStart slice committed flow core batch q core.location hfits
        (Fits.le_start hfits hact) (core.started hact) r hr := by
  have hp : q.start.offset < core.location.offset := core.started hact
  have hlast := Fits.le_start hfits hact
  rw [loop2_lt _ _ _ _ _ _ _ _ _ hj]
  cases hadv : advance (Consume.consumesWhitespaceAndComments (H := H)) q core.location
      slice[j] with
  | pending q' =>
    have e : byteRan (Consume.consumesWhitespaceAndComments (H := H)) slice q j hj core.location =
        (run (Consume.consumesWhitespaceAndComments (H := H)) slice q' (j + 1)
          (core.location.afterByte slice[j])).lift (by omega) := by
      simp only [byteRan, hadv]
    rw [e] at hr0
    subst hr0
    have hq' : q'.start = q.start := advance_pending hadv
    have hafter : core.location.offset < (core.location.afterByte slice[j]).offset := by
      rw [afterByte_offset]; omega
    rw [expand_lift _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
      (Ran.Spec.weaken (run_spec _ _ _ _ _) hq' (Nat.le_of_lt hafter))]
    simp only [V2Batched.lexByte, withEq, hact, advanceS, hadv, pure_bind, cont_next]
    rw [ih q' _ rfl _ _ (run_spec _ _ _ _ _) rfl]
    refine expand_congr (H := H) (m := m) (R := R) (E := E) _ _ _ _ _ ?_ _ _ _ _ _ _ _ _ _ _
    rfl
  | idle =>
    have e : byteRan (Consume.consumesWhitespaceAndComments (H := H)) slice q j hj core.location =
        .idle (j + 1) (core.location.afterByte slice[j]) (by omega) := by
      simp only [byteRan, hadv]
    rw [e] at hr0
    subst hr0
    simp only [V2Batched.lexByte, withEq, hact, advanceS, hadv, pure_bind, cont_next, expand]
  | tokenWith l =>
    have e : byteRan (Consume.consumesWhitespaceAndComments (H := H)) slice q j hj core.location =
        .tokenWith l (j + 1) (by omega) := by
      simp only [byteRan, hadv]
    rw [e] at hr0
    subst hr0
    have hl := (advance_tokenWith hadv).2
    obtain ⟨cat, content, start, «end»⟩ := l
    simp only at hl
    subst hl
    simp only [V2Batched.lexByte, withEq, hact, advanceS, hadv, expand, expandWith, bind_assoc]
    refine congrArg (erase <$> ·) (congrArg (_ >>= ·) (funext fun x => ?_))
    obtain ⟨⟨o, c, b⟩, hf, hfix⟩ := x
    simp only [pure_bind]
  | tokenBefore l =>
    have e : byteRan (Consume.consumesWhitespaceAndComments (H := H)) slice q j hj core.location =
        .tokenBefore l j (Nat.le_refl _) hj := by
      simp only [byteRan, hadv]
    rw [e] at hr0
    subst hr0
    have hl := (advance_tokenBefore hadv).2
    obtain ⟨cat, content, start, «end»⟩ := l
    simp only at hl
    subst hl
    simp only [V2Batched.lexByte, withEq, hact, advanceS, hadv, bind_assoc, expand,
      expandBefore]
    refine congrArg (erase <$> ·) (congrArg (_ >>= ·) (funext fun x => ?_))
    obtain ⟨⟨o, c, b⟩, hf, hfix⟩ := x
    cases o
    all_goals simp only [pure_bind]
    case finished =>
      have hloc : c.location = core.location := (congrArg Core.location hfix :)
      obtain ⟨v, i, loc, a, d, s⟩ := c
      simp only at hloc
      subst hloc
      rfl
  | error failure =>
    have e : byteRan (Consume.consumesWhitespaceAndComments (H := H)) slice q j hj core.location =
        .error failure := by
      simp only [byteRan, hadv]
    rw [e] at hr0
    subst hr0
    simp only [V2Batched.lexByte, withEq, hact, advanceS, hadv, pure_bind, expand]
    exact cont_failed _ _ _ _ _ _ rfl _ _ _ _ _

end

end BSmtLib.Proofs.Lexer.V2BatchedV3Runs
