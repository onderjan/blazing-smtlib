import BSmtLib.Proofs.Lexer.WRustPort
import BSmtLib.Proofs.Lexer.X1BatchInCore
import BSmtLib.Proofs.WRustPortX1BatchInCore.Relation
import BSmtLib.Proofs.WRustPortX1BatchInCore.Batch

/-!
# The states of the Rust port and of the lexer with the batch in its state

The two lexer states have the same fields. They correspond (`CoreRel`) when each field is the
same in both but the batch, where the batches agree (`Agree`); and the Rust port's batch is
below its capacity, as a full batch is handed over at once. The helpers of the two lexers that
read and change the state are simulated here, by `SimR` with the states related by `CoreRel`
(`SR`), and an interruption thrown from related states (`LSim`).

Batches without tokens agree whatever their arrays of contents. Inside a slice, the arrays of
contents of the two lexers' batches are the slice's, which the tokens of the slice borrow from:
the batches the loop of the normal state takes from the states must have the same one. A
simulation that is `strict` keeps this, also where it is interrupted (`ErS`); at the end of the
input the Rust port's batch is a fresh one, and the simulation there is not strict. The helpers
that do not change the batches keep any fact `Bx` of them. The helpers that throw nothing are
simulated whatever relates the states an interruption is thrown from (`ESim`); `ErZ` adds to
`ErS` that the Rust port's batch has no tokens, as where the consumer stops in a hand-over.

Inside the loop of the normal state, the Rust port keeps the line and the line start in locals
(`WRustPort.FastState`), where the lexer with the batch in its state reads them from its state;
the locals are those of the state wherever the Rust port reads them. `SRL l ls` adds to `SR`
that the Rust port's line and line start are `l` and `ls`, which the helpers that do not change
the line keep.
-/

namespace BSmtLib.Proofs.WRustPortX1BatchInCore

open BSmtLib.Proofs.Simulation (M runM)
open BSmtLib.Lexer (BATCH_CAPACITY Interrupted)

abbrev WCore := BSmtLib.Proofs.Lexer.WRustPort.LexerCore
abbrev XCore := BSmtLib.Proofs.Lexer.X1BatchInCore.LexerCore

/-- The two lexer states have the same fields but for the version and the batch. -/
structure SameBut (w : WCore) (x : XCore) : Prop where
  initialVersion : w.initialVersion = x.initialVersion
  state : w.state = x.state
  discard : w.discard = x.discard
  recovers : w.recovers = x.recovers
  consumedDepth : w.consumedDepth = x.consumedDepth
  lexedDepth : w.lexedDepth = x.lexedDepth
  recoveryState : w.recoveryState = x.recoveryState
  tokenStart : w.tokenStart = x.tokenStart
  tokenContent : w.tokenContent = x.tokenContent
  offset : w.offset = x.offset
  base : w.base = x.base
  line : w.line = x.line
  lineStart : w.lineStart = x.lineStart

/-- The two lexer states correspond: the same fields, but for the batches, which agree; and the
Rust port's batch is below its capacity. -/
structure CoreRel (w : WCore) (x : XCore) : Prop extends SameBut w x where
  version : w.version = x.version
  batch : Agree w.batch x.batch
  capacity : w.batch.len < BATCH_CAPACITY

/-- The bounded state of the Rust port. -/
abbrev WS (floor : Option Nat) (low : Nat) := {c : WCore // c.Bound floor low}

/-- The bounded state of the lexer with the batch in its state. -/
abbrev XS (floor : Option Nat) (low : Nat) := {c : XCore // c.Bound floor low}

/-- The bounded states correspond. -/
abbrev SR {floor : Option Nat} {low : Nat} (s : WS floor low) (t : XS floor low) : Prop :=
  CoreRel s.val t.val

/-- The bounded states correspond, and the Rust port's line and line start are `l` and `ls`. -/
abbrev SRL {floor : Option Nat} {low : Nat} (l ls : Nat) (s : WS floor low) (t : XS floor low) :
    Prop :=
  SR s t ∧ s.val.line = l ∧ s.val.lineStart = ls

/-- `SRL`, and the fact `Bx` of the two states' batches. -/
abbrev SRLx {floor : Option Nat} {low : Nat} (l ls : Nat) (Bx : TokenBatch → TokenBatch → Prop)
    (s : WS floor low) (t : XS floor low) : Prop :=
  SRL l ls s t ∧ Bx s.val.batch t.val.batch

/-- Where the simulation is strict, the two batches have the same array of contents. -/
abbrev BytesEq (strict : Bool) (b c : TokenBatch) : Prop :=
  strict = true → b.bytes = c.bytes

/-- The states an interruption is thrown from correspond, with the same arrays of contents of
the batches where the simulation is strict. -/
abbrev ErS (strict : Bool) {floor : Option Nat} {low : Nat} (s : WS floor low)
    (t : XS floor low) : Prop :=
  SR s t ∧ BytesEq strict s.val.batch t.val.batch

/-- `ErS`, and the Rust port's batch has no tokens: the states a stop of the consumer is thrown
from in a hand-over. -/
abbrev ErZ (strict : Bool) {floor : Option Nat} {low : Nat} (s : WS floor low)
    (t : XS floor low) : Prop :=
  ErS strict s t ∧ s.val.batch.len = 0

/-- `SR`, and the same arrays of contents of the batches where the simulation is strict. -/
abbrev SRb (strict : Bool) {floor : Option Nat} {low : Nat} (s : WS floor low)
    (t : XS floor low) : Prop :=
  SR s t ∧ BytesEq strict s.val.batch t.val.batch

/-- `SRL`, and the same arrays of contents of the batches where the simulation is strict. -/
abbrev SRLb (strict : Bool) {floor : Option Nat} {low : Nat} (l ls : Nat) (s : WS floor low)
    (t : XS floor low) : Prop :=
  SRLx l ls (BytesEq strict) s t

theorem SRL.sr {floor : Option Nat} {low : Nat} {l ls : Nat} {s : WS floor low}
    {t : XS floor low} (h : SRL l ls s t) : SR s t :=
  h.1

theorem sr_srl {floor : Option Nat} {low : Nat} {s : WS floor low} {t : XS floor low}
    (h : SR s t) : SRL s.val.line s.val.lineStart s t :=
  ⟨h, rfl, rfl⟩

/-- An empty batch is below the capacity. -/
theorem zero_lt_capacity : 0 < BATCH_CAPACITY := by decide

/-- Batches that agree and are below the capacity, with the rest of the states. -/
theorem coreRel_with_batch {w : WCore} {x : XCore} (h : CoreRel w x) {b c : TokenBatch}
    (hbc : Agree b c) (hcap : b.len < BATCH_CAPACITY) (e e') :
    CoreRel { w with batch := b, batchEnded := e } { x with batch := c, batchEnded := e' } :=
  { h with batch := hbc, capacity := hcap }

/-- Shows `SameBut` of two states from `SameBut` of states they are made from by changing other
fields, with the equations of the changed fields in the context. -/
macro "same_but " h:term : tactic =>
  `(tactic| (
    have hh := $h
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _⟩ := hh
    constructor <;> assumption))

section

variable {H : Type} {m : Type → Type} {R E : Type} [Monad m] [LawfulMonad m]
  {floor : Option Nat} {low : Nat} {strict : Bool}

/-- A step of the Rust port simulated by one of the lexer with the batch in its state, with an
interruption thrown from states with `ErS strict`. -/
abbrev LSim (strict : Bool) {α β : Type} (P : WS floor low → XS floor low → Prop)
    (Q : α → β → WS floor low → XS floor low → Prop)
    (f : Lexer.WRustPort.LexM H m R E floor low α)
    (g : Lexer.X1BatchInCore.LexM H m R E floor low β) : Prop :=
  SimR (ErS strict) P Q f g

/-- A step of the Rust port simulated by one of the lexer with the batch in its state, with an
interruption thrown from states with `Er`. -/
abbrev ESim (Er : WS floor low → XS floor low → Prop) {α β : Type}
    (P : WS floor low → XS floor low → Prop) (Q : α → β → WS floor low → XS floor low → Prop)
    (f : Lexer.WRustPort.LexM H m R E floor low α)
    (g : Lexer.X1BatchInCore.LexM H m R E floor low β) : Prop :=
  SimR Er P Q f g

/-- From states that correspond, with any line and line start of the Rust port. -/
theorem LSim.of_srl {α β : Type} {Bx : TokenBatch → TokenBatch → Prop}
    {Q : α → β → WS floor low → XS floor low → Prop}
    {f : Lexer.WRustPort.LexM H m R E floor low α}
    {g : Lexer.X1BatchInCore.LexM H m R E floor low β}
    (h : ∀ l ls, LSim strict (SRLx l ls Bx) Q f g) :
    LSim strict (fun s t => SR s t ∧ Bx s.val.batch t.val.batch) Q f g :=
  SimR.intro fun s t hst => SimR.pre (fun _ _ h' => by
    obtain ⟨⟨h', hb⟩, rfl, rfl⟩ := h'
    exact ⟨sr_srl h', hb⟩) (h s.val.line s.val.lineStart)

variable [Consume H m R E] {Er : WS floor low → XS floor low → Prop}

omit [Consume H m R E] in
theorem getCore_sim (P : WS floor low → XS floor low → Prop) :
    SimR (m := m) (H := H) (ε := Interrupted R E floor) Er P
      (fun a b s t => P s t ∧ a = s.val ∧ b = t.val)
      Lexer.WRustPort.getCore Lexer.X1BatchInCore.getCore := by
  unfold Lexer.WRustPort.getCore Lexer.X1BatchInCore.getCore
  exact SimR.bind (SimR.get (Q := fun a b s t => P s t ∧ a = s ∧ b = t) fun _ _ h => ⟨h, rfl, rfl⟩)
    fun a b => SimR.pure fun _ _ h => ⟨h.1, by rw [h.2.1], by rw [h.2.2]⟩

omit [Consume H m R E] in
/-- A step after reading the two states, which correspond. -/
theorem getCore_bind {α β : Type} {P : WS floor low → XS floor low → Prop}
    {Q : α → β → WS floor low → XS floor low → Prop}
    {k : WCore → Lexer.WRustPort.LexM H m R E floor low α}
    {k' : XCore → Lexer.X1BatchInCore.LexM H m R E floor low β}
    (hk : ∀ w x, SimR Er (fun s t => P s t ∧ s.val = w ∧ t.val = x) Q (k w) (k' x)) :
    SimR Er P Q (Lexer.WRustPort.getCore >>= k) (Lexer.X1BatchInCore.getCore >>= k') :=
  SimR.bind (getCore_sim P) fun w x =>
    SimR.pre (fun _ _ h => ⟨h.1, h.2.1.symm, h.2.2.symm⟩) (hk w x)

omit [Consume H m R E] in
/-- A step after reading the two states, which keeps the precondition. -/
theorem getCore_bind_P {α β : Type} {P : WS floor low → XS floor low → Prop}
    {Q : α → β → WS floor low → XS floor low → Prop}
    {k : WCore → Lexer.WRustPort.LexM H m R E floor low α}
    {k' : XCore → Lexer.X1BatchInCore.LexM H m R E floor low β}
    (hk : ∀ s t, P s t → SimR Er P Q (k s.val) (k' t.val)) :
    SimR Er P Q (Lexer.WRustPort.getCore >>= k) (Lexer.X1BatchInCore.getCore >>= k') :=
  getCore_bind fun w x => SimR.intro fun s t h => by
    obtain ⟨hP, hw, hx⟩ := h
    subst hw hx
    exact SimR.pre (fun s' t' h' => by rw [h'.2.1, h'.2.2]; exact hP) (hk s t hP)

omit [Consume H m R E] in
theorem failWith_bind {α β : Type} (kind : LexicalErrorKind) (position failure : Nat)
    (k : α → Lexer.X1BatchInCore.LexM H m R E floor low β) :
    (Lexer.X1BatchInCore.failWith kind position failure >>= k) =
      Lexer.X1BatchInCore.failWith kind position failure := by
  unfold Lexer.X1BatchInCore.failWith
  simp only [bind_assoc, throw_bind]

omit [Consume H m R E] in
theorem failAt_bind {α β : Type} (kind : LexicalErrorKind) (position : Nat)
    (k : α → Lexer.X1BatchInCore.LexM H m R E floor low β) :
    (Lexer.X1BatchInCore.failAt kind position >>= k) =
      Lexer.X1BatchInCore.failAt kind position :=
  failWith_bind _ _ _ k

omit [Consume H m R E] in
theorem fail_bind {α β : Type} (kind : LexicalErrorKind) (tokenEnd : Lexer.Slice.TokenEnd)
    (k : α → Lexer.X1BatchInCore.LexM H m R E floor low β) :
    (Lexer.X1BatchInCore.fail kind tokenEnd >>= k) = Lexer.X1BatchInCore.fail kind tokenEnd :=
  failWith_bind _ _ _ k

omit [Consume H m R E] in
/-- A step after reading the Rust port's state, which the other lexer does not read. -/
theorem getCore_bind_left {α β : Type} {P : WS floor low → XS floor low → Prop}
    {Q : α → β → WS floor low → XS floor low → Prop}
    {k : WCore → Lexer.WRustPort.LexM H m R E floor low α}
    {g : Lexer.X1BatchInCore.LexM H m R E floor low β}
    (hk : ∀ s t, P s t → SimR Er (fun s' t' => s' = s ∧ t' = t) Q (k s.val) g) :
    SimR Er P Q (Lexer.WRustPort.getCore >>= k) g := by
  unfold Lexer.WRustPort.getCore
  simp only [bind_assoc, pure_bind]
  exact SimR.get_bind_left hk

omit [Consume H m R E] in
/-- A step after reading the state of the lexer with the batch in its state, which the Rust port
does not read. -/
theorem getCore_bind_right {α β : Type} {P : WS floor low → XS floor low → Prop}
    {Q : α → β → WS floor low → XS floor low → Prop}
    {f : Lexer.WRustPort.LexM H m R E floor low α}
    {k : XCore → Lexer.X1BatchInCore.LexM H m R E floor low β}
    (hk : ∀ s t, P s t → SimR Er (fun s' t' => s' = s ∧ t' = t) Q f (k t.val)) :
    SimR Er P Q f (Lexer.X1BatchInCore.getCore >>= k) := by
  unfold Lexer.X1BatchInCore.getCore
  simp only [bind_assoc, pure_bind]
  exact SimR.get_bind_right hk

omit [Consume H m R E] in
theorem modifyCore_sim {f : WCore → WCore} {g : XCore → XCore}
    {hf : ∀ c, c.Bound floor low → (f c).Bound floor low}
    {hg : ∀ c, c.Bound floor low → (g c).Bound floor low}
    (P : WS floor low → XS floor low → Prop) (Q : Unit → Unit → WS floor low → XS floor low → Prop)
    (e : ∀ s t, P s t → Q () () ⟨f s.val, hf s.val s.property⟩ ⟨g t.val, hg t.val t.property⟩) :
    SimR (m := m) (H := H) (ε := Interrupted R E floor) Er P Q
      (Lexer.WRustPort.modifyCore f hf) (Lexer.X1BatchInCore.modifyCore g hg) := by
  unfold Lexer.WRustPort.modifyCore Lexer.X1BatchInCore.modifyCore
  exact SimR.modify e

omit [Consume H m R E] in
theorem modifyBound_sim
    {f : (c : WCore) → c.Bound floor low → {c' : WCore // c'.Bound floor low}}
    {g : (c : XCore) → c.Bound floor low → {c' : XCore // c'.Bound floor low}}
    (P : WS floor low → XS floor low → Prop) (Q : Unit → Unit → WS floor low → XS floor low → Prop)
    (e : ∀ s t, P s t → Q () () (f s.val s.property) (g t.val t.property)) :
    SimR (m := m) (H := H) (ε := Interrupted R E floor) Er P Q
      (Lexer.WRustPort.modifyBound f) (Lexer.X1BatchInCore.modifyBound g) := by
  unfold Lexer.WRustPort.modifyBound Lexer.X1BatchInCore.modifyBound
  exact SimR.modify e

omit [Consume H m R E] in
theorem setNormal_sim (l ls : Nat) (Bx : TokenBatch → TokenBatch → Prop) :
    ESim (H := H) (m := m) (R := R) (E := E) (floor := floor) (low := low) Er
      (SRLx l ls Bx) (fun _ _ => SRLx l ls Bx) Lexer.WRustPort.setNormal
      Lexer.X1BatchInCore.setNormal :=
  modifyCore_sim _ _ fun _ _ h => ⟨⟨{ h.1.1 with state := rfl }, h.1.2⟩, h.2⟩

omit [Consume H m R E] in
theorem setTokenState_sim (l ls : Nat) (Bx : TokenBatch → TokenBatch → Prop)
    (state : Lexer.LexerState) (start : Location)
    (h : Lexer.WRustPort.Started floor low start)
    (h' : Lexer.X1BatchInCore.Started floor low start) :
    ESim (H := H) (m := m) (R := R) (E := E) (floor := floor) (low := low) Er
      (SRLx l ls Bx) (fun _ _ => SRLx l ls Bx)
      (Lexer.WRustPort.setTokenState state start h)
      (Lexer.X1BatchInCore.setTokenState state start h') :=
  modifyBound_sim _ _ fun _ _ h => ⟨⟨{ h.1.1 with state := rfl, tokenStart := rfl }, h.1.2⟩, h.2⟩

omit [Consume H m R E] in
theorem modifyContent_sim (l ls : Nat) (Bx : TokenBatch → TokenBatch → Prop)
    (f : ByteArray → ByteArray) :
    ESim (H := H) (m := m) (R := R) (E := E) (floor := floor) (low := low) Er
      (SRLx l ls Bx) (fun _ _ => SRLx l ls Bx) (Lexer.WRustPort.modifyContent f)
      (Lexer.X1BatchInCore.modifyContent f) :=
  modifyCore_sim _ _ fun _ _ h =>
    ⟨⟨{ h.1.1 with tokenContent := congrArg f h.1.1.tokenContent }, h.1.2⟩, h.2⟩

omit [Consume H m R E] in
theorem extendContentFrom_sim (l ls : Nat) (Bx : TokenBatch → TokenBatch → Prop)
    (bytes : ByteSlice) :
    ESim (H := H) (m := m) (R := R) (E := E) (floor := floor) (low := low) Er
      (SRLx l ls Bx) (fun _ _ => SRLx l ls Bx) (Lexer.WRustPort.extendContentFrom bytes)
      (Lexer.X1BatchInCore.extendContentFrom bytes) :=
  modifyContent_sim l ls Bx _

omit [Consume H m R E] in
theorem extendContent_sim (l ls : Nat) (Bx : TokenBatch → TokenBatch → Prop) (input : ByteSlice)
    (start stop : Nat) :
    ESim (H := H) (m := m) (R := R) (E := E) (floor := floor) (low := low) Er
      (SRLx l ls Bx) (fun _ _ => SRLx l ls Bx) (Lexer.WRustPort.extendContent input start stop)
      (Lexer.X1BatchInCore.extendContent input start stop) := by
  unfold Lexer.WRustPort.extendContent Lexer.X1BatchInCore.extendContent
  exact extendContentFrom_sim l ls Bx _

omit [Consume H m R E] in
theorem pushContent_sim (l ls : Nat) (Bx : TokenBatch → TokenBatch → Prop) (c : UInt8) :
    ESim (H := H) (m := m) (R := R) (E := E) (floor := floor) (low := low) Er
      (SRLx l ls Bx) (fun _ _ => SRLx l ls Bx) (Lexer.WRustPort.pushContent c)
      (Lexer.X1BatchInCore.pushContent c) :=
  modifyContent_sim l ls Bx _

omit [Consume H m R E] in
theorem startToken_sim (l ls : Nat) (Bx : TokenBatch → TokenBatch → Prop) (offset : Nat)
    (base position : Nat) (hframe : Lexer.WRustPort.Frame floor low offset)
    (hframe' : Lexer.X1BatchInCore.Frame floor low offset) :
    ESim (H := H) (m := m) (R := R) (E := E) (floor := floor) (low := low) Er
      (SRLx l ls Bx)
      (fun a b s t => a.val = b.val ∧ SRLx l ls Bx s t)
      (Lexer.WRustPort.startToken offset base position hframe)
      (Lexer.X1BatchInCore.startToken offset base position hframe') := by
  unfold Lexer.WRustPort.startToken Lexer.X1BatchInCore.startToken
  refine getCore_bind_P fun s₀ t₀ h₀ => ?_
  obtain ⟨⟨hst, hl, hls⟩, hz⟩ := h₀
  refine SimR.seq (P' := SRLx l ls Bx) (modifyCore_sim _ _ fun s t h => ?_) ?_
  · obtain ⟨⟨h, hl', hls'⟩, hz'⟩ := h
    exact ⟨⟨{ h with tokenStart := by simp only [hst.line, hst.lineStart], state := rfl }, hl',
      hls'⟩, hz'⟩
  refine SimR.seq (P' := SRLx l ls Bx) (modifyContent_sim l ls Bx _) ?_
  exact SimR.pure fun s t h => ⟨by simp only [hst.line, hst.lineStart], h⟩

omit [Consume H m R E] in
theorem markLineFeedAt_sim (Bx : TokenBatch → TokenBatch → Prop) (position : Nat) :
    ESim (H := H) (m := m) (R := R) (E := E) (floor := floor) (low := low) Er
      (fun s t => SR s t ∧ Bx s.val.batch t.val.batch)
      (fun _ _ s t => SR s t ∧ Bx s.val.batch t.val.batch)
      (Lexer.WRustPort.markLineFeedAt position) (Lexer.X1BatchInCore.markLineFeedAt position) :=
  modifyCore_sim _ _ fun _ _ h => ⟨{ h.1 with
    line := by simp [h.1.line]
    lineStart := by
      simp only [Lexer.WRustPort.LexerCore.offsetAt, Lexer.X1BatchInCore.LexerCore.offsetAt,
        h.1.offset, h.1.base] }, h.2⟩

omit [Consume H m R E] in
/-- The error of the Rust port, thrown, and the failure of the lexer with the batch in its
state. -/
theorem errorWith_sim {α β : Type} (l ls : Nat) (kind : LexicalErrorKind)
    (position failure : Nat) (Q : α → β → WS floor low → XS floor low → Prop) :
    LSim strict (H := H) (m := m) (R := R) (E := E) (SRLb strict l ls) Q
      (Lexer.WRustPort.errorWith kind position failure >>= fun e => throw e)
      (Lexer.X1BatchInCore.failWith kind position failure) := by
  unfold Lexer.WRustPort.errorWith Lexer.X1BatchInCore.failWith
  simp only [bind_assoc, pure_bind]
  refine getCore_bind_P fun s₀ t₀ h₀ => ?_
  refine SimR.throw ?_ fun s t h => ⟨h.1.1, h.2⟩
  have hst := h₀.1.1
  simp only [Lexer.WRustPort.LexerCore.locationAt, Lexer.X1BatchInCore.LexerCore.locationAt,
    Lexer.WRustPort.LexerCore.offsetAt, Lexer.X1BatchInCore.LexerCore.offsetAt, hst.offset,
    hst.base, hst.line, hst.lineStart, hst.tokenStart]

omit [Consume H m R E] in
theorem errorAt_sim {α β : Type} (l ls : Nat) (kind : LexicalErrorKind) (position : Nat)
    (Q : α → β → WS floor low → XS floor low → Prop) :
    LSim strict (H := H) (m := m) (R := R) (E := E) (SRLb strict l ls) Q
      (Lexer.WRustPort.errorAt kind position >>= fun e => throw e)
      (Lexer.X1BatchInCore.failAt kind position) :=
  errorWith_sim l ls kind _ _ Q

omit [Consume H m R E] in
theorem error_sim {α β : Type} (l ls : Nat) (kind : LexicalErrorKind)
    (tokenEnd : Lexer.Slice.TokenEnd) (Q : α → β → WS floor low → XS floor low → Prop) :
    LSim strict (H := H) (m := m) (R := R) (E := E) (SRLb strict l ls) Q
      (Lexer.WRustPort.error kind tokenEnd >>= fun e => throw e)
      (Lexer.X1BatchInCore.fail kind tokenEnd) :=
  errorWith_sim l ls kind _ _ Q

omit [Consume H m R E] in
/-- `error_sim` from states whose batches have no tokens, which the error is thrown from. -/
theorem error_simZ {α β : Type} (l ls : Nat) (kind : LexicalErrorKind)
    (tokenEnd : Lexer.Slice.TokenEnd) (Q : α → β → WS floor low → XS floor low → Prop) :
    SimR (m := m) (H := H) (ε := Interrupted R E floor) (ErZ strict)
      (fun s t => SRLb strict l ls s t ∧ s.val.batch.len = 0) Q
      (Lexer.WRustPort.error kind tokenEnd >>= fun e => throw e)
      (Lexer.X1BatchInCore.fail kind tokenEnd) := by
  unfold Lexer.WRustPort.error Lexer.X1BatchInCore.fail Lexer.WRustPort.errorWith
    Lexer.X1BatchInCore.failWith
  simp only [bind_assoc, pure_bind]
  refine getCore_bind_P fun s₀ t₀ h₀ => ?_
  refine SimR.throw ?_ fun s t h => ⟨⟨h.1.1.1, h.1.2⟩, h.2⟩
  have hst := h₀.1.1.1
  simp only [Lexer.WRustPort.LexerCore.locationAt, Lexer.X1BatchInCore.LexerCore.locationAt,
    Lexer.WRustPort.LexerCore.offsetAt, Lexer.X1BatchInCore.LexerCore.offsetAt, hst.offset,
    hst.base, hst.line, hst.lineStart, hst.tokenStart]

omit [Consume H m R E] in
theorem expectDelimiter_sim (l ls : Nat) (next : UInt8) (position : Nat) :
    LSim strict (H := H) (m := m) (R := R) (E := E) (floor := floor) (low := low)
      (SRLb strict l ls) (fun _ _ => SRLb strict l ls)
      (Lexer.WRustPort.expectDelimiter next position)
      (Lexer.X1BatchInCore.expectDelimiter next position) := by
  unfold Lexer.WRustPort.expectDelimiter Lexer.X1BatchInCore.expectDelimiter
  by_cases hd : Lexer.isDelimiter next = true
  · simp only [hd, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    exact SimR.pure fun _ _ h => h
  · simp only [hd, Bool.not_false, ↓reduceIte, Bool.false_eq_true]
    exact errorAt_sim l ls _ _ _

omit [Consume H m R E] in
theorem locationFrom_sim (l ls : Nat) (Bx : TokenBatch → TokenBatch → Prop)
    (base position : Nat) :
    ESim (H := H) (m := m) (R := R) (E := E) (floor := floor) (low := low) Er
      (SRLx l ls Bx) (fun a b s t => a.val = b.val ∧ SRLx l ls Bx s t)
      (Lexer.WRustPort.locationFrom base position)
      (Lexer.X1BatchInCore.locationFrom base position) := by
  unfold Lexer.WRustPort.locationFrom Lexer.X1BatchInCore.locationFrom
  refine getCore_bind_P fun s₀ t₀ h₀ => ?_
  refine SimR.pure fun s t h => ⟨?_, h⟩
  simp only [h₀.1.1.line, h₀.1.1.lineStart]

end

end BSmtLib.Proofs.WRustPortX1BatchInCore
