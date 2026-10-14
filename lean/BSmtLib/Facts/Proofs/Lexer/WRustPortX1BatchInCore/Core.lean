module

public import BSmtLib.Lexer.Internal.WRustPort
public import BSmtLib.Facts.Proofs.Lexer.Simulation
import all BSmtLib.Lexer
import all BSmtLib.Lexer.Helpers
import all BSmtLib.Lexer.Internal.WRustPort

@[expose] public section

/-!
# The lexer states of two runs of the Rust port's code

The Rust port `WRustPort` and the lexer with the batch in its state `X1BatchInCore` run the same
code over different operations (`WRustPort.Ops`), from lexer states of the same type. The two
states of such runs correspond (`CoreRel`) when each field is the same in both but the batch,
where the batches agree (`Agree`); and the batch is below its capacity, as a full batch is
handed over at once. The helpers of the code that do not use the operations are simulated here,
by `SimR` with the states related by `CoreRel` (`SR`), and an interruption thrown from related
states (`LSim`).

Batches without tokens agree whatever their arrays of contents. Inside a slice, the arrays of
contents of the two batches are the slice's, which the tokens of the slice borrow from: the
batches the loop of the normal state takes from the states must have the same one. A simulation
that is `strict` keeps this, also where it is interrupted (`ErS`); at the end of the input it is
not strict. The helpers that do not change the batches keep any fact `Bx` of them. The helpers
that throw nothing are simulated whatever relates the states an interruption is thrown from
(`ESim`); `ErZ` adds to `ErS` that the first batch has no tokens, as where the consumer stops in
a hand-over.

Inside the loop of the normal state, the operations may keep the line and the line start in
locals (`WRustPort.Ops.Locals`); `SRL l ls` adds to `SR` that the line and the line start are
`l` and `ls`, which the helpers that do not change the line keep.
-/

namespace BSmtLib.Facts.Proofs.Lexer.WRustPortX1BatchInCore.Core

open BSmtLib.Lexer (BATCH_CAPACITY Interrupted)
open BSmtLib.Facts.Proofs.Lexer.Simulation.Batch BSmtLib.Facts.Proofs.Lexer.Simulation.Relation
open BSmtLib.Lexer.Error

/-- The lexer state of the Rust port's code. -/
abbrev _root_.BSmtLib.Facts.Proofs.Lexer.WRustPortX1BatchInCore.Core :=
    Lexer.Internal.WRustPort.LexerCore

/-- The two lexer states have the same fields but for the version and the batch. -/
structure SameBut (w x : Core) : Prop where
  initialVersion : w.initialVersion = x.initialVersion
  state : w.state = x.state
  discardedFrom : w.discardedFrom = x.discardedFrom
  holding : w.holding = x.holding
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
first batch is below its capacity. -/
structure CoreRel (w x : Core) : Prop extends SameBut w x where
  version : w.version = x.version
  batch : Agree w.batch x.batch
  capacity : w.batch.len < BATCH_CAPACITY

/-- The bounded lexer state. -/
abbrev St (floor : Option Nat) (low : Nat) := {c : Core // c.Bound floor low}

section

variable {floor : Option Nat} {low : Nat}

/-- The bounded states correspond. -/
abbrev SR (s t : St floor low) : Prop :=
  CoreRel s.val t.val

/-- The bounded states correspond, and their line and line start are `l` and `ls`. -/
abbrev SRL (l ls : Nat) (s t : St floor low) : Prop :=
  SR s t ∧ s.val.line = l ∧ s.val.lineStart = ls

/-- `SRL`, and the fact `Bx` of the two states' batches. -/
abbrev SRLx (l ls : Nat) (Bx : Token.TokenBatch → Token.TokenBatch → Prop)
    (s t : St floor low) : Prop :=
  SRL l ls s t ∧ Bx s.val.batch t.val.batch

/-- Where the simulation is strict, the two batches have the same array of contents. -/
abbrev BytesEq (strict : Bool) (b c : Token.TokenBatch) : Prop :=
  strict = true → b.bytes = c.bytes

/-- The states an interruption is thrown from correspond, with the same arrays of contents of
the batches where the simulation is strict. -/
abbrev ErS (strict : Bool) (s t : St floor low) : Prop :=
  SR s t ∧ BytesEq strict s.val.batch t.val.batch

/-- `ErS`, and the first batch has no tokens: the states a stop of the consumer is thrown from in
a hand-over. -/
abbrev ErZ (strict : Bool) (s t : St floor low) : Prop :=
  ErS strict s t ∧ s.val.batch.len = 0

/-- `SR`, and the same arrays of contents of the batches where the simulation is strict. -/
abbrev SRb (strict : Bool) (s t : St floor low) : Prop :=
  SR s t ∧ BytesEq strict s.val.batch t.val.batch

/-- `SRL`, and the same arrays of contents of the batches where the simulation is strict. -/
abbrev SRLb (strict : Bool) (l ls : Nat) (s t : St floor low) : Prop :=
  SRLx l ls (BytesEq strict) s t

/-- `SRLb`, and the first batch has no tokens. -/
abbrev SRLbZ (strict : Bool) (l ls : Nat) (s t : St floor low) : Prop :=
  SRLb strict l ls s t ∧ s.val.batch.len = 0

/-- The first batch has no tokens. -/
abbrev NoTokens (b _ : Token.TokenBatch) : Prop :=
  b.len = 0

/-- The two states correspond with the line and line start `l` and `ls`, and their batches have
no tokens. -/
abbrev SRE (l ls : Nat) (s t : St floor low) : Prop :=
  SRLx l ls NoTokens s t

/-- `SRE`, and the same arrays of contents of the batches where the simulation is strict. -/
abbrev SREb (strict : Bool) (l ls : Nat) (s t : St floor low) : Prop :=
  SRE l ls s t ∧ BytesEq strict s.val.batch t.val.batch

/-- The two states correspond and their batches have no tokens. -/
abbrev SR0 (s t : St floor low) : Prop :=
  SR s t ∧ s.val.batch.len = 0

end

/-- The batches held by the two loops of the normal state agree, with the same array of
contents, and are below the capacity. -/
structure HR (b b' : Token.TokenBatch) : Prop where
  agree : Agree b b'
  bytes : b.bytes = b'.bytes
  capacity : b.len < BATCH_CAPACITY

/-- What a push gives back: batches held by the loops, and the two states with batches without
tokens. -/
abbrev PushQ {floor : Option Nat} {low : Nat} (l ls : Nat) {α β : Type} (val : α → Token.TokenBatch)
    (val' : β → Token.TokenBatch) (a : α) (b : β) (s t : St floor low) : Prop :=
  HR (val a) (val' b) ∧ SRE l ls s t

theorem sr_srl {floor : Option Nat} {low : Nat} {s t : St floor low} (h : SR s t) :
    SRL s.val.line s.val.lineStart s t :=
  ⟨h, rfl, rfl⟩

/-- An empty batch is below the capacity. -/
theorem zero_lt_capacity : 0 < BATCH_CAPACITY := by decide

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

/-- A step simulated by another, with an interruption thrown from states with `ErS strict`. -/
abbrev LSim (strict : Bool) {α β : Type} (P : St floor low → St floor low → Prop)
    (Q : α → β → St floor low → St floor low → Prop)
    (f : Lexer.Internal.WRustPort.LexM H m R E floor low α)
    (g : Lexer.Internal.WRustPort.LexM H m R E floor low β) : Prop :=
  SimR (ErS strict) P Q f g

/-- A step simulated by another, with an interruption thrown from states with `Er`. -/
abbrev ESim (Er : St floor low → St floor low → Prop) {α β : Type}
    (P : St floor low → St floor low → Prop) (Q : α → β → St floor low → St floor low → Prop)
    (f : Lexer.Internal.WRustPort.LexM H m R E floor low α)
    (g : Lexer.Internal.WRustPort.LexM H m R E floor low β) : Prop :=
  SimR Er P Q f g

/-- From states that correspond, with any line and line start. -/
theorem SimR.of_srl {α β : Type} {Er : St floor low → St floor low → Prop}
    {Bx : Token.TokenBatch → Token.TokenBatch → Prop}
    {Q : α → β → St floor low → St floor low → Prop}
    {f : Lexer.Internal.WRustPort.LexM H m R E floor low α}
    {g : Lexer.Internal.WRustPort.LexM H m R E floor low β}
    (h : ∀ l ls, ESim Er (SRLx l ls Bx) Q f g) :
    ESim Er (fun s t => SR s t ∧ Bx s.val.batch t.val.batch) Q f g :=
  SimR.intro fun s _ _ => SimR.pre (fun _ _ h' => by
    obtain ⟨⟨h', hb⟩, rfl, rfl⟩ := h'
    exact ⟨sr_srl h', hb⟩) (h s.val.line s.val.lineStart)

/-- From states whose batches have no tokens, with any line and line start. -/
theorem SimR.of_sre {α β : Type} {Er : St floor low → St floor low → Prop}
    {Q : α → β → St floor low → St floor low → Prop}
    {f : Lexer.Internal.WRustPort.LexM H m R E floor low α}
    {g : Lexer.Internal.WRustPort.LexM H m R E floor low β}
    (h : ∀ l ls, ESim Er (SRE l ls) Q f g) : ESim Er SR0 Q f g :=
  SimR.of_srl (Bx := NoTokens) h

variable {Er : St floor low → St floor low → Prop}

theorem getCore_sim (P : St floor low → St floor low → Prop) :
    SimR (m := m) (H := H) (ε := Interrupted R E floor) Er P
      (fun a b s t => P s t ∧ a = s.val ∧ b = t.val)
      Lexer.Internal.WRustPort.getCore Lexer.Internal.WRustPort.getCore := by
  unfold Lexer.Internal.WRustPort.getCore
  exact SimR.bind (SimR.get (Q := fun a b s t => P s t ∧ a = s ∧ b = t) fun _ _ h => ⟨h, rfl, rfl⟩)
    fun a b => SimR.pure fun _ _ h => ⟨h.1, by rw [h.2.1], by rw [h.2.2]⟩

/-- A step after reading the two states. -/
theorem getCore_bind {α β : Type} {P : St floor low → St floor low → Prop}
    {Q : α → β → St floor low → St floor low → Prop}
    {k : Core → Lexer.Internal.WRustPort.LexM H m R E floor low α}
    {k' : Core → Lexer.Internal.WRustPort.LexM H m R E floor low β}
    (hk : ∀ w x, SimR Er (fun s t => P s t ∧ s.val = w ∧ t.val = x) Q (k w) (k' x)) :
    SimR Er P Q (Lexer.Internal.WRustPort.getCore >>= k)
        (Lexer.Internal.WRustPort.getCore >>= k') :=
  SimR.bind (getCore_sim P) fun w x =>
    SimR.pre (fun _ _ h => ⟨h.1, h.2.1.symm, h.2.2.symm⟩) (hk w x)

/-- A step after reading the two states, which keeps the precondition. -/
theorem getCore_bind_P {α β : Type} {P : St floor low → St floor low → Prop}
    {Q : α → β → St floor low → St floor low → Prop}
    {k : Core → Lexer.Internal.WRustPort.LexM H m R E floor low α}
    {k' : Core → Lexer.Internal.WRustPort.LexM H m R E floor low β}
    (hk : ∀ s t, P s t → SimR Er P Q (k s.val) (k' t.val)) :
    SimR Er P Q (Lexer.Internal.WRustPort.getCore >>= k)
        (Lexer.Internal.WRustPort.getCore >>= k') :=
  getCore_bind fun w x => SimR.intro fun s t h => by
    obtain ⟨hP, hw, hx⟩ := h
    subst hw hx
    exact SimR.pre (fun s' t' h' => by rw [h'.2.1, h'.2.2]; exact hP) (hk s t hP)

/-- A step after reading the first state, which the second step does not read. -/
theorem getCore_bind_left {α β : Type} {P : St floor low → St floor low → Prop}
    {Q : α → β → St floor low → St floor low → Prop}
    {k : Core → Lexer.Internal.WRustPort.LexM H m R E floor low α}
    {g : Lexer.Internal.WRustPort.LexM H m R E floor low β}
    (hk : ∀ s t, P s t → SimR Er (fun s' t' => s' = s ∧ t' = t) Q (k s.val) g) :
    SimR Er P Q (Lexer.Internal.WRustPort.getCore >>= k) g := by
  unfold Lexer.Internal.WRustPort.getCore
  simp only [bind_assoc, pure_bind]
  exact SimR.get_bind_left hk

/-- A step after reading the second state, which the first step does not read. -/
theorem getCore_bind_right {α β : Type} {P : St floor low → St floor low → Prop}
    {Q : α → β → St floor low → St floor low → Prop}
    {f : Lexer.Internal.WRustPort.LexM H m R E floor low α}
    {k : Core → Lexer.Internal.WRustPort.LexM H m R E floor low β}
    (hk : ∀ s t, P s t → SimR Er (fun s' t' => s' = s ∧ t' = t) Q f (k t.val)) :
    SimR Er P Q f (Lexer.Internal.WRustPort.getCore >>= k) := by
  unfold Lexer.Internal.WRustPort.getCore
  simp only [bind_assoc, pure_bind]
  exact SimR.get_bind_right hk

theorem modifyCore_sim {f g : Core → Core}
    {hf : ∀ c, c.Bound floor low → (f c).Bound floor low}
    {hg : ∀ c, c.Bound floor low → (g c).Bound floor low}
    (P : St floor low → St floor low → Prop)
    (Q : Unit → Unit → St floor low → St floor low → Prop)
    (e : ∀ s t, P s t → Q () () ⟨f s.val, hf s.val s.property⟩ ⟨g t.val, hg t.val t.property⟩) :
    SimR (m := m) (H := H) (ε := Interrupted R E floor) Er P Q
      (Lexer.Internal.WRustPort.modifyCore f hf) (Lexer.Internal.WRustPort.modifyCore g hg) := by
  unfold Lexer.Internal.WRustPort.modifyCore
  exact SimR.modify e

theorem modifyBound_sim
    {f g : (c : Core) → c.Bound floor low → {c' : Core // c'.Bound floor low}}
    (P : St floor low → St floor low → Prop)
    (Q : Unit → Unit → St floor low → St floor low → Prop)
    (e : ∀ s t, P s t → Q () () (f s.val s.property) (g t.val t.property)) :
    SimR (m := m) (H := H) (ε := Interrupted R E floor) Er P Q
      (Lexer.Internal.WRustPort.modifyBound f) (Lexer.Internal.WRustPort.modifyBound g) := by
  unfold Lexer.Internal.WRustPort.modifyBound
  exact SimR.modify e

theorem modifyCore_bind_left {α β : Type} {P : St floor low → St floor low → Prop}
    {Q : α → β → St floor low → St floor low → Prop} {f : Core → Core} {hf}
    {k : PUnit → Lexer.Internal.WRustPort.LexM H m R E floor low α}
    {g : Lexer.Internal.WRustPort.LexM H m R E floor low β}
    (hk : ∀ s t, P s t →
      SimR Er (fun s' t' => s' = ⟨f s.val, hf s.val s.property⟩ ∧ t' = t) Q (k ⟨⟩) g) :
    SimR Er P Q (Lexer.Internal.WRustPort.modifyCore f hf >>= k) g := by
  unfold Lexer.Internal.WRustPort.modifyCore
  exact SimR.modify_bind_left hk

theorem modifyCore_bind_right {α β : Type} {P : St floor low → St floor low → Prop}
    {Q : α → β → St floor low → St floor low → Prop} {f : Core → Core} {hf}
    {k : Lexer.Internal.WRustPort.LexM H m R E floor low α}
    {g : PUnit → Lexer.Internal.WRustPort.LexM H m R E floor low β}
    (hk : ∀ s t, P s t →
      SimR Er (fun s' t' => s' = s ∧ t' = ⟨f t.val, hf t.val t.property⟩) Q k (g ⟨⟩)) :
    SimR Er P Q k (Lexer.Internal.WRustPort.modifyCore f hf >>= g) := by
  unfold Lexer.Internal.WRustPort.modifyCore
  exact SimR.modify_bind_right hk

theorem setNormal_sim (l ls : Nat) (Bx : Token.TokenBatch → Token.TokenBatch → Prop) :
    ESim (H := H) (m := m) (R := R) (E := E) (floor := floor) (low := low) Er
      (SRLx l ls Bx) (fun _ _ => SRLx l ls Bx) Lexer.Internal.WRustPort.setNormal
      Lexer.Internal.WRustPort.setNormal :=
  modifyCore_sim _ _ fun _ _ h => ⟨⟨{ h.1.1 with state := rfl }, h.1.2⟩, h.2⟩

theorem setTokenState_sim (l ls : Nat) (Bx : Token.TokenBatch → Token.TokenBatch → Prop)
    (state : Lexer.Helpers.LexerState) (start : Span.Location)
    (h h' : Lexer.Internal.WRustPort.Started floor low start) :
    ESim (H := H) (m := m) (R := R) (E := E) (floor := floor) (low := low) Er
      (SRLx l ls Bx) (fun _ _ => SRLx l ls Bx)
      (Lexer.Internal.WRustPort.setTokenState state start h)
      (Lexer.Internal.WRustPort.setTokenState state start h') :=
  modifyBound_sim _ _ fun _ _ h => ⟨⟨{ h.1.1 with state := rfl, tokenStart := rfl }, h.1.2⟩, h.2⟩

theorem modifyContent_sim (l ls : Nat) (Bx : Token.TokenBatch → Token.TokenBatch → Prop)
    (f : Lexer.Helpers.ContentBuffer → Lexer.Helpers.ContentBuffer) :
    ESim (H := H) (m := m) (R := R) (E := E) (floor := floor) (low := low) Er
      (SRLx l ls Bx) (fun _ _ => SRLx l ls Bx) (Lexer.Internal.WRustPort.modifyContent f)
      (Lexer.Internal.WRustPort.modifyContent f) :=
  modifyCore_sim _ _ fun _ _ h =>
    ⟨⟨{ h.1.1 with tokenContent := congrArg f h.1.1.tokenContent }, h.1.2⟩, h.2⟩

theorem extendContent_sim (l ls : Nat) (Bx : Token.TokenBatch → Token.TokenBatch → Prop)
    (input : ByteSlice)
    (start stop : Nat) :
    ESim (H := H) (m := m) (R := R) (E := E) (floor := floor) (low := low) Er
      (SRLx l ls Bx) (fun _ _ => SRLx l ls Bx) (Lexer.Internal.WRustPort.extendContent input start
          stop)
      (Lexer.Internal.WRustPort.extendContent input start stop) :=
  modifyContent_sim l ls Bx _

theorem pushContent_sim (l ls : Nat) (Bx : Token.TokenBatch → Token.TokenBatch → Prop) (c : UInt8) :
    ESim (H := H) (m := m) (R := R) (E := E) (floor := floor) (low := low) Er
      (SRLx l ls Bx) (fun _ _ => SRLx l ls Bx) (Lexer.Internal.WRustPort.pushContent c)
      (Lexer.Internal.WRustPort.pushContent c) :=
  modifyContent_sim l ls Bx _

/-- The start of a token, which empties the content buffer. -/
theorem startToken_sim (l ls : Nat) (Bx : Token.TokenBatch → Token.TokenBatch → Prop) (offset : Nat)
    (base position : Nat) (hframe hframe' : Lexer.Internal.WRustPort.Frame floor low offset) :
    ESim (H := H) (m := m) (R := R) (E := E) (floor := floor) (low := low) Er
      (SRLx l ls Bx)
      (fun a b s t => a.val = b.val ∧ SRLx l ls Bx s t ∧ s.val.tokenContent.len = 0)
      (Lexer.Internal.WRustPort.startToken offset base position hframe)
      (Lexer.Internal.WRustPort.startToken offset base position hframe') := by
  unfold Lexer.Internal.WRustPort.startToken
  refine getCore_bind_P fun s₀ t₀ h₀ => ?_
  obtain ⟨⟨hst, hl, hls⟩, hz⟩ := h₀
  refine SimR.seq (P' := SRLx l ls Bx) (modifyCore_sim _ _ fun s t h => ?_) ?_
  · obtain ⟨⟨h, hl', hls'⟩, hz'⟩ := h
    exact ⟨⟨{ h with tokenStart := by simp only [hst.line, hst.lineStart], state := rfl }, hl',
      hls'⟩, hz'⟩
  refine SimR.seq (P' := fun s t => SRLx l ls Bx s t ∧ s.val.tokenContent.len = 0)
    (modifyCore_sim _ _ fun s t h => ?_) ?_
  · obtain ⟨⟨h, hl', hls'⟩, hz'⟩ := h
    exact ⟨⟨⟨{ h with tokenContent := by rw [h.tokenContent] }, hl', hls'⟩, hz'⟩, rfl⟩
  exact SimR.pure fun s t h => ⟨by simp only [hst.line, hst.lineStart], h⟩

/-- `startToken_sim` without the content buffer. -/
theorem startToken_simx (l ls : Nat) (Bx : Token.TokenBatch → Token.TokenBatch → Prop)
    (offset : Nat)
    (base position : Nat) (hframe hframe' : Lexer.Internal.WRustPort.Frame floor low offset) :
    ESim (H := H) (m := m) (R := R) (E := E) (floor := floor) (low := low) Er
      (SRLx l ls Bx) (fun a b s t => a.val = b.val ∧ SRLx l ls Bx s t)
      (Lexer.Internal.WRustPort.startToken offset base position hframe)
      (Lexer.Internal.WRustPort.startToken offset base position hframe') :=
  SimR.post (fun _ _ _ _ h => ⟨h.1, h.2.1⟩) (startToken_sim l ls Bx offset base position _ _)

theorem markLineFeedAt_sim (Bx : Token.TokenBatch → Token.TokenBatch → Prop) (position : Nat) :
    ESim (H := H) (m := m) (R := R) (E := E) (floor := floor) (low := low) Er
      (fun s t => SR s t ∧ Bx s.val.batch t.val.batch)
      (fun _ _ s t => SR s t ∧ Bx s.val.batch t.val.batch)
      (Lexer.Internal.WRustPort.markLineFeedAt position)
          (Lexer.Internal.WRustPort.markLineFeedAt position) :=
  modifyCore_sim _ _ fun _ _ h => ⟨{ h.1 with
    line := by simp [h.1.line]
    lineStart := by
      simp only [Lexer.Internal.WRustPort.LexerCore.offsetAt, h.1.offset, h.1.base] }, h.2⟩

/-- `markLineFeedAt_sim` from states whose batches have no tokens. -/
theorem markLineFeedAt_sim0 (position : Nat) :
    ESim (H := H) (m := m) (R := R) (E := E) (floor := floor) (low := low) Er SR0
      (fun _ _ => SR0) (Lexer.Internal.WRustPort.markLineFeedAt position)
      (Lexer.Internal.WRustPort.markLineFeedAt position) :=
  markLineFeedAt_sim NoTokens position

/-- An error thrown from states that correspond is the same interruption. -/
theorem errorWith_sim {α β : Type} (l ls : Nat) (kind : LexicalErrorKind)
    (position failure : Nat) (Q : α → β → St floor low → St floor low → Prop) :
    LSim strict (H := H) (m := m) (R := R) (E := E) (SRLb strict l ls) Q
      (Lexer.Internal.WRustPort.errorWith kind position failure >>= fun e => throw e)
      (Lexer.Internal.WRustPort.errorWith kind position failure >>= fun e => throw e) := by
  unfold Lexer.Internal.WRustPort.errorWith
  simp only [bind_assoc, pure_bind]
  refine getCore_bind_P fun s₀ t₀ h₀ => ?_
  refine SimR.throw ?_ fun s t h => ⟨h.1.1, h.2⟩
  have hst := h₀.1.1
  simp only [Lexer.Internal.WRustPort.LexerCore.locationAt,
      Lexer.Internal.WRustPort.LexerCore.offsetAt, hst.offset,
    hst.base, hst.line, hst.lineStart, hst.tokenStart]

theorem errorAt_sim {α β : Type} (l ls : Nat) (kind : LexicalErrorKind) (position : Nat)
    (Q : α → β → St floor low → St floor low → Prop) :
    LSim strict (H := H) (m := m) (R := R) (E := E) (SRLb strict l ls) Q
      (Lexer.Internal.WRustPort.errorAt kind position >>= fun e => throw e)
      (Lexer.Internal.WRustPort.errorAt kind position >>= fun e => throw e) :=
  errorWith_sim l ls kind _ _ Q

theorem error_sim {α β : Type} (l ls : Nat) (kind : LexicalErrorKind)
    (tokenEnd : Lexer.Internal.WRustPort.Slice.TokenEnd)
    (Q : α → β → St floor low → St floor low → Prop) :
    LSim strict (H := H) (m := m) (R := R) (E := E) (SRLb strict l ls) Q
      (Lexer.Internal.WRustPort.error kind tokenEnd >>= fun e => throw e)
      (Lexer.Internal.WRustPort.error kind tokenEnd >>= fun e => throw e) :=
  errorWith_sim l ls kind _ _ Q

/-- `error_sim` from states whose first batch has no tokens, which the error is thrown from. -/
theorem error_simZ {α β : Type} (l ls : Nat) (kind : LexicalErrorKind)
    (tokenEnd : Lexer.Internal.WRustPort.Slice.TokenEnd)
    (Q : α → β → St floor low → St floor low → Prop) :
    SimR (m := m) (H := H) (ε := Interrupted R E floor) (ErZ strict) (SRLbZ strict l ls) Q
      (Lexer.Internal.WRustPort.error kind tokenEnd >>= fun e => throw e)
      (Lexer.Internal.WRustPort.error kind tokenEnd >>= fun e => throw e) := by
  unfold Lexer.Internal.WRustPort.error Lexer.Internal.WRustPort.errorWith
  simp only [bind_assoc, pure_bind]
  refine getCore_bind_P fun s₀ t₀ h₀ => ?_
  refine SimR.throw ?_ fun s t h => ⟨⟨h.1.1.1, h.1.2⟩, h.2⟩
  have hst := h₀.1.1.1
  simp only [Lexer.Internal.WRustPort.LexerCore.locationAt,
      Lexer.Internal.WRustPort.LexerCore.offsetAt, hst.offset,
    hst.base, hst.line, hst.lineStart, hst.tokenStart]

theorem expectDelimiter_sim (l ls : Nat) (next : UInt8) (position : Nat) :
    LSim strict (H := H) (m := m) (R := R) (E := E) (floor := floor) (low := low)
      (SRLb strict l ls) (fun _ _ => SRLb strict l ls)
      (Lexer.Internal.WRustPort.expectDelimiter next position)
      (Lexer.Internal.WRustPort.expectDelimiter next position) := by
  unfold Lexer.Internal.WRustPort.expectDelimiter
  by_cases hd : Lexer.Helpers.isDelimiter next = true
  · simp only [hd, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    exact SimR.pure fun _ _ h => h
  · simp only [hd, Bool.not_false, ↓reduceIte]
    exact errorAt_sim l ls _ _ _

theorem locationFrom_sim (l ls : Nat) (Bx : Token.TokenBatch → Token.TokenBatch → Prop)
    (base position : Nat) :
    ESim (H := H) (m := m) (R := R) (E := E) (floor := floor) (low := low) Er
      (SRLx l ls Bx) (fun a b s t => a.val = b.val ∧ SRLx l ls Bx s t)
      (Lexer.Internal.WRustPort.locationFrom base position)
      (Lexer.Internal.WRustPort.locationFrom base position) := by
  unfold Lexer.Internal.WRustPort.locationFrom
  refine getCore_bind_P fun s₀ t₀ h₀ => ?_
  refine SimR.pure fun s t h => ⟨?_, h⟩
  simp only [h₀.1.1.line, h₀.1.1.lineStart]

theorem leave_sim (l ls : Nat) (offset base position : Nat) (b b' : Token.TokenBatch) (hb : HR b b')
    (hframe hframe' hbatch hbatch') :
    LSim strict (H := H) (m := m) (R := R) (E := E) (floor := floor) (low := low) (SRL l ls)
      (fun _ _ => SRLb strict l ls) (Lexer.Internal.WRustPort.leave offset base position b hframe
          hbatch)
      (Lexer.Internal.WRustPort.leave offset base position b' hframe' hbatch') :=
  modifyBound_sim _ _ fun _ _ h => ⟨⟨{ h.1 with
    offset := rfl, base := rfl, state := rfl, batch := hb.agree, capacity := hb.capacity }, h.2⟩,
    fun _ => hb.bytes⟩

theorem leavePending_sim (l ls : Nat) (state : Lexer.Helpers.LexerState) (start : Span.Location)
    (offset base position : Nat) (b b' : Token.TokenBatch) (hb : HR b b')
    (hframe hframe' hbatch hbatch' hstart hstart' hfloor hfloor') :
    LSim strict (H := H) (m := m) (R := R) (E := E) (floor := floor) (low := low) (SRL l ls)
      (fun _ _ => SRLb strict l ls)
      (Lexer.Internal.WRustPort.leavePending state start offset base position b hframe hbatch
          hstart hfloor)
      (Lexer.Internal.WRustPort.leavePending state start offset base position b' hframe' hbatch'
          hstart'
        hfloor') :=
  modifyBound_sim _ _ fun _ _ h => ⟨⟨{ h.1 with
    offset := rfl, base := rfl, state := rfl, tokenStart := rfl, batch := hb.agree
    capacity := hb.capacity }, h.2⟩, fun _ => hb.bytes⟩

theorem storeUnfinishedSymbolRun_sim (l ls : Nat) (input : ByteSlice) (entry : UInt8)
    (offset base index after runEndAt : Nat) (b b' : Token.TokenBatch) (hb : HR b b')
    (hframe hframe' hindex hrun hbatch hbatch') :
    LSim strict (H := H) (m := m) (R := R) (E := E) (floor := floor) (low := low) (SRE l ls)
      (fun _ _ => SRLb strict l ls)
      (Lexer.Internal.WRustPort.storeUnfinishedSymbolRun input entry offset base index after
          runEndAt b
        hframe hindex hrun hbatch)
      (Lexer.Internal.WRustPort.storeUnfinishedSymbolRun input entry offset base index after
          runEndAt
        b' hframe' hindex hrun hbatch') := by
  unfold Lexer.Internal.WRustPort.storeUnfinishedSymbolRun
  refine SimR.bind (startToken_sim l ls _ offset base index hframe hframe') fun a a' => ?_
  obtain ⟨a, ha⟩ := a
  obtain ⟨a', ha'⟩ := a'
  refine SimR.of_fact' (Er := ErS strict) fun (e : a = a') => ?_
  subst e
  dsimp only
  refine SimR.ite Iff.rfl (fun _ => ?_) fun _ => ?_ <;>
  exact SimR.seq (SimR.pre (fun s t h => h.1) (extendContent_sim l ls _ _ _ _))
    (SimR.pre (fun s t h => h.1) (leavePending_sim l ls _ _ _ _ _ _ _ hb _ _ _ _ _ _ _ _))

end

end BSmtLib.Facts.Proofs.Lexer.WRustPortX1BatchInCore.Core
