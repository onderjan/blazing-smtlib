module

public import BSmtLib.Facts.Proofs.Lexer.X1BatchInCoreLexer.Positions
public import BSmtLib.Facts.Proofs.Lexer.Simulation
import all BSmtLib.Lexer
import all BSmtLib.Lexer.Internal.WRustPort

@[expose] public section

/-!
# The states of the library's lexer and of `X1BatchInCore`

The two lexer states have the same fields but for `base`, which the library's lexer keeps as a
position in the slice's array and `X1BatchInCore` as an index into the slice.
`coreMap start` maps the first to the second for a slice that starts at `start` in its array.
The helpers of the two lexers that read and change the state are simulated here.
-/

namespace BSmtLib.Facts.Proofs.Lexer.X1BatchInCoreLexer

/- The code of the Rust port runs over operations given as an instance argument; in this link it
runs over those of `X1BatchInCore`. -/
attribute [scoped instance] Lexer.Internal.X1BatchInCore.ops

end BSmtLib.Facts.Proofs.Lexer.X1BatchInCoreLexer

namespace BSmtLib.Facts.Proofs.Lexer.X1BatchInCoreLexer.Core

open BSmtLib.Facts.Proofs.Lexer.Simulation.Steps
open BSmtLib.Facts.Proofs.Lexer.X1BatchInCoreLexer.Positions BSmtLib.Lexer.Error

abbrev ZCore := BSmtLib.Lexer.LexerCore
abbrev XCore := Lexer.Internal.WRustPort.LexerCore

/-- The state of `X1BatchInCore` for that of the library's lexer, in a slice
that starts at `start` in its array. -/
def coreMap (start : Nat) (c : ZCore) : XCore :=
  { version := c.version, initialVersion := c.initialVersion, state := c.state
    discardedFrom := c.discardedFrom, holding := c.holding, recovers := c.recovers
    consumedDepth := c.consumedDepth
    lexedDepth := c.lexedDepth, recoveryState := c.recoveryState, tokenStart := c.tokenStart
    tokenContent := c.tokenContent, offset := c.offset, base := c.base.toNat - start
    line := c.line, lineStart := c.lineStart, batch := c.batch
    tokenStarted := c.tokenStarted, batchEnded := c.batchEnded }

/-- The bounded states, mapped. -/
def boundMap (start : Nat) {floor : Option Nat} {low : Nat}
    (c : {c : ZCore // c.Bound floor low}) : {c : XCore // c.Bound floor low} :=
  ⟨coreMap start c.val, c.property⟩

/-- The index of a position in the slice that starts at `start`. -/
abbrev ix (start : Nat) (p : USize) : Nat := p.toNat - start

theorem sub_toNat {b p : USize} (h : b.toNat ≤ p.toNat) : (p - b).toNat = p.toNat - b.toNat :=
  USize.toNat_sub_of_le _ _ (USize.le_iff_toNat_le.mpr h)

/-- The bytes from one position to a later one are as many as between their indices. -/
theorem sub_toNat_ix {start : Nat} {b p : USize} (hb : start ≤ b.toNat) (h : b.toNat ≤ p.toNat) :
    (p - b).toNat = ix start p - ix start b := by
  rw [sub_toNat h]
  simp only [ix]
  omega

/-- The bounded state of the library's lexer. -/
abbrev ZS (floor : Option Nat) (low : Nat) := {c : ZCore // c.Bound floor low}

/-- The bounded state of `X1BatchInCore`. -/
abbrev XS (floor : Option Nat) (low : Nat) := {c : XCore // c.Bound floor low}

/-- The state's base is `b`. -/
abbrev BaseIs {floor : Option Nat} {low : Nat} (b : USize) (c : ZS floor low) : Prop :=
  c.val.base = b

theorem coreMap_offsetAt {start : Nat} {c : ZCore} {p : USize} (hb : start ≤ c.base.toNat)
    (hp : c.base.toNat ≤ p.toNat) :
    (coreMap start c).offsetAt (ix start p) = c.offsetAt p := by
  simp only [Lexer.Internal.WRustPort.LexerCore.offsetAt, BSmtLib.Lexer.LexerCore.offsetAt, coreMap,
    sub_toNat_ix hb hp]

theorem coreMap_locationAt {start : Nat} {c : ZCore} {p : USize} (hb : start ≤ c.base.toNat)
    (hp : c.base.toNat ≤ p.toNat) :
    (coreMap start c).locationAt (ix start p) = c.locationAt p := by
  simp only [Lexer.Internal.WRustPort.LexerCore.locationAt, BSmtLib.Lexer.LexerCore.locationAt,
    coreMap_offsetAt hb hp]
  rfl

section

variable {H : Type} {m : Type → Type} {R E : Type} [Monad m] [Token.Consume H R E]
  [∀ batch, Token.ConsumeFrom H (Token.BatchCursor batch) m]
  {floor : Option Nat} {low : Nat}

/-! The operations of `X1BatchInCore`, as the Rust port's code calls
them: the locals of the loop of the normal state are empty, so that storing and loading them does
nothing. -/

theorem storeLocals_eq (l : Unit) :
    (Lexer.Internal.WRustPort.Ops.storeLocals (H := H) (m := m) (R := R) (E := E) (floor := floor)
      (low := low) l) = pure () :=
  rfl

theorem loadLocals_eq :
    (Lexer.Internal.WRustPort.Ops.loadLocals (H := H) (m := m) (R := R) (E := E) (floor := floor)
      (low := low) : Lexer.Internal.WRustPort.LexM H m R E floor low Unit) = pure () :=
  rfl

omit [∀ batch, Token.ConsumeFrom H (Token.BatchCursor batch) m] in
/-- Whether the consumer takes whitespace and comments, read by the library's lexer. -/
theorem consumes_eq_lexer :
    BSmtLib.Lexer.Internal.consumesWhitespaceAndComments (H := H) (m := m) (R := R) (E := E)
      (floor := floor) (low := low) = pure (Token.Consume.isConcrete (H := H)) :=
  (rfl)

omit [∀ batch, Token.ConsumeFrom H (Token.BatchCursor batch) m] in
/-- Whether the consumer takes whitespace and comments, read by the Rust port. -/
theorem consumes_eq_x1 :
    Lexer.Internal.WRustPort.consumesWhitespaceAndComments (H := H) (m := m) (R := R) (E := E)
      (floor := floor) (low := low) = pure (Token.Consume.isConcrete (H := H)) :=
  (rfl)

/-! The operations of the batch, as the Rust port's code calls them, are those of the lexer with
the batch kept in its state. -/

theorem pushFast_eq :
    @Lexer.Internal.WRustPort.Ops.pushFast H m R E Lexer.Internal.X1BatchInCore.ops floor low =
      @Lexer.Internal.X1BatchInCore.pushFast H m R E _ _ _ floor low :=
  rfl

theorem flushHeld_eq :
    @Lexer.Internal.WRustPort.Ops.flushHeld H m R E Lexer.Internal.X1BatchInCore.ops floor low =
      @Lexer.Internal.X1BatchInCore.flushHeld H m R E _ _ _ floor low :=
  rfl

theorem flushBatch_eq :
    @Lexer.Internal.WRustPort.Ops.flushBatch H m R E Lexer.Internal.X1BatchInCore.ops floor low =
      @Lexer.Internal.X1BatchInCore.flushBatch H m R E _ _ _ floor low :=
  rfl

theorem sinkStoredAt_eq :
    @Lexer.Internal.WRustPort.Ops.sinkStoredAt H m R E Lexer.Internal.X1BatchInCore.ops floor low =
      @Lexer.Internal.X1BatchInCore.handOverStored H m R E _ _ _ floor low :=
  rfl

theorem sinkEof_eq :
    @Lexer.Internal.WRustPort.Ops.sinkEof H m R E Lexer.Internal.X1BatchInCore.ops low =
      @Lexer.Internal.X1BatchInCore.handOverEof H m R E _ _ _ low :=
  rfl

theorem eofBatch_eq (c : XCore) :
    @Lexer.Internal.WRustPort.Ops.eofBatch H m R E Lexer.Internal.X1BatchInCore.ops c =
        ⟨c.batch, c.batchEnded⟩ :=
  rfl

theorem sliceStorage_eq (batch : Token.TokenBatch) :
    @Lexer.Internal.WRustPort.Ops.sliceStorage H m R E Lexer.Internal.X1BatchInCore.ops batch =
        batch :=
  rfl

end

section

variable {H : Type} {m : Type → Type} {R E : Type} [Monad m] [LawfulMonad m]
  {floor : Option Nat} {low : Nat} (start : Nat)

theorem getCore_sim (P : ZS floor low → Prop) :
    SimP P (fun c s => P s ∧ c = s.val) (boundMap start) (coreMap start)
      (BSmtLib.Lexer.Internal.getCore (H := H) (m := m) (R := R) (E := E))
      (Lexer.Internal.WRustPort.getCore) := by
  unfold BSmtLib.Lexer.Internal.getCore Lexer.Internal.WRustPort.getCore
  exact SimP.bind (SimP.get (Q := fun a s => P s ∧ a = s) fun s hs => ⟨hs, rfl⟩)
    fun a => SimP.pure (fun s hs => ⟨hs.1, by rw [hs.2]⟩) rfl

theorem modifyCore_sim {f : ZCore → ZCore} {g : XCore → XCore}
    {hf : ∀ c, c.Bound floor low → (f c).Bound floor low}
    {hg : ∀ c, c.Bound floor low → (g c).Bound floor low}
    (P : ZS floor low → Prop) (Q : Unit → ZS floor low → Prop)
    (e : ∀ c, P c → g (coreMap start c.val) = coreMap start (f c.val))
    (hq : ∀ c, P c → Q () ⟨f c.val, hf c.val c.property⟩) :
    SimP P Q (boundMap start) id
      (BSmtLib.Lexer.Internal.modifyCore (H := H) (m := m) (R := R) (E := E) f hf)
      (Lexer.Internal.WRustPort.modifyCore g hg) := by
  unfold BSmtLib.Lexer.Internal.modifyCore Lexer.Internal.WRustPort.modifyCore
  exact SimP.modify (fun c hc => Subtype.ext (e c hc)) hq

theorem modifyBound_sim
    {f : (c : ZCore) → c.Bound floor low → {c' : ZCore // c'.Bound floor low}}
    {g : (c : XCore) → c.Bound floor low → {c' : XCore // c'.Bound floor low}}
    (P : ZS floor low → Prop) (Q : Unit → ZS floor low → Prop)
    (e : ∀ c, P c → (g (coreMap start c.val) c.property).val = coreMap start (f c.val c.property))
    (hq : ∀ c, P c → Q () (f c.val c.property)) :
    SimP P Q (boundMap start) id
      (BSmtLib.Lexer.Internal.modifyBound (H := H) (m := m) (R := R) (E := E) f)
      (Lexer.Internal.WRustPort.modifyBound g) := by
  unfold BSmtLib.Lexer.Internal.modifyBound Lexer.Internal.WRustPort.modifyBound
  exact SimP.modify (fun c hc => Subtype.ext (e c hc)) hq

theorem setNormal_sim (b : USize) :
    SimP (BaseIs b) (fun _ => BaseIs b) (boundMap start) id
      (BSmtLib.Lexer.Internal.setNormal (H := H) (m := m) (R := R) (E := E) (floor := floor)
        (low := low))
      Lexer.Internal.WRustPort.setNormal :=
  modifyCore_sim start _ _ (fun _ _ => rfl) fun _ hc => hc

theorem setTokenState_sim (b : USize) (state : Lexer.Helpers.LexerState) (s : Span.Location)
    (h : BSmtLib.Lexer.Internal.Started floor low s)
    (h' : Lexer.Internal.WRustPort.Started floor low s) :
    SimP (BaseIs b) (fun _ => BaseIs b) (boundMap start) id
      (BSmtLib.Lexer.Internal.setTokenState (H := H) (m := m) (R := R) (E := E) state s h)
      (Lexer.Internal.WRustPort.setTokenState state s h') :=
  modifyBound_sim start _ _ (fun _ _ => rfl) fun _ hc => hc

theorem modifyContent_sim (b : USize) (f : Lexer.Helpers.ContentBuffer →
    Lexer.Helpers.ContentBuffer) :
    SimP (BaseIs b) (fun _ => BaseIs b) (boundMap start) id
      (BSmtLib.Lexer.Internal.modifyContent (H := H) (m := m) (R := R) (E := E) (floor := floor)
        (low := low) f)
      (Lexer.Internal.WRustPort.modifyContent f) :=
  modifyCore_sim start _ _ (fun _ _ => rfl) fun _ hc => hc

theorem pushContent_sim (b : USize) (x : UInt8) :
    SimP (BaseIs b) (fun _ => BaseIs b) (boundMap start) id
      (BSmtLib.Lexer.Internal.pushContent (H := H) (m := m) (R := R) (E := E) (floor := floor)
        (low := low) x)
      (Lexer.Internal.WRustPort.pushContent x) :=
  modifyContent_sim start b _

theorem extendContent_sim (b : USize) (slice : ByteSlice) (h : slice.stop < USize.size)
    (p q : USize) (hp : slice.start ≤ p.toNat) (hq : slice.start ≤ q.toNat) :
    SimP (BaseIs b) (fun _ => BaseIs b) (boundMap slice.start) id
      (BSmtLib.Lexer.Internal.extendContent (H := H) (m := m) (R := R) (E := E) (floor := floor)
        (low := low) (inputOf slice h) p q)
      (Lexer.Internal.WRustPort.extendContent slice (ix slice.start p) (ix slice.start q)) := by
  unfold BSmtLib.Lexer.Internal.extendContent Lexer.Internal.WRustPort.extendContent
  have ep : slice.start + ix slice.start p = p.toNat := by simp only [ix]; omega
  have eq : slice.start + ix slice.start q = q.toNat := by simp only [ix]; omega
  rw [ep, eq]
  exact modifyContent_sim _ b _

theorem startToken_sim (b : USize) (offset : Nat) (base position : USize)
    (hb : start ≤ base.toNat) (hp : base.toNat ≤ position.toNat)
    (hframe : BSmtLib.Lexer.Internal.Frame floor low offset)
    (hframe' : Lexer.Internal.WRustPort.Frame floor low offset) :
    SimP (BaseIs b) (fun _ => BaseIs b) (boundMap start)
      (fun r => ⟨r.val, by rw [r.property, sub_toNat_ix hb hp]⟩)
      (BSmtLib.Lexer.Internal.startToken (H := H) (m := m) (R := R) (E := E) offset base position
        hframe)
      (Lexer.Internal.WRustPort.startToken offset (ix start base) (ix start position) hframe') := by
  unfold BSmtLib.Lexer.Internal.startToken Lexer.Internal.WRustPort.startToken
  refine SimP.bind (getCore_sim start _) fun c => ?_
  refine SimP.bind (modifyCore_sim start _ (fun _ s => BaseIs b s ∧ c = c) ?_ ?_) fun _ => ?_
  · intro s hs
    simp only [coreMap, sub_toNat_ix hb hp]
  · intro s hs
    exact ⟨hs.1, rfl⟩
  refine SimP.bind (SimP.mono (fun s hs => hs.1) (fun _ _ h => h) (modifyContent_sim start b _))
    fun _ => SimP.pure (fun _ h => h) ?_
  simp only [coreMap, sub_toNat_ix hb hp]

theorem markLineFeedAt_sim (b : USize) (position : USize) (hb : start ≤ b.toNat)
    (hp : b.toNat ≤ position.toNat) :
    SimP (BaseIs b) (fun _ => BaseIs b) (boundMap start) id
      (BSmtLib.Lexer.Internal.markLineFeedAt (H := H) (m := m) (R := R) (E := E) (floor := floor)
        (low := low) position)
      (Lexer.Internal.WRustPort.markLineFeedAt (ix start position)) := by
  unfold BSmtLib.Lexer.Internal.markLineFeedAt Lexer.Internal.WRustPort.markLineFeedAt
  refine modifyCore_sim start _ _ (fun c hc => ?_) fun _ hc => hc
  have hc' : c.val.base = b := hc
  have e := coreMap_offsetAt (start := start) (c := c.val) (p := position) (by rw [hc']; exact hb)
    (by rw [hc']; exact hp)
  simp only [coreMap] at e ⊢
  rw [e]

/- The library's lexer throws its errors where they are found (`failWith`); the Rust port forms
them as values and its callers throw them (`throw (← errorWith ..)`). -/
theorem failWith_sim {α β : Type} (ψ : α → β) (b : USize) (kind : LexicalErrorKind)
    (position failure : USize) (hb : start ≤ b.toNat) (hp : b.toNat ≤ position.toNat)
    (hf : b.toNat ≤ failure.toNat) (Q : α → ZS floor low → Prop) :
    SimP (BaseIs b) Q (boundMap start) ψ
      (BSmtLib.Lexer.Internal.failWith (H := H) (m := m) (R := R) (E := E) kind position failure)
      (do throw (← Lexer.Internal.WRustPort.errorWith kind (ix start position) (ix start failure)))
          := by
  unfold BSmtLib.Lexer.Internal.failWith Lexer.Internal.WRustPort.errorWith
  simp only [bind_assoc, pure_bind]
  refine SimP.bind (getCore_sim start _) fun c => ?_
  intro s hs h
  have hc : c.base = b := by rw [hs.2]; exact hs.1
  refine SimP.throw_eq (P := fun s => BaseIs b s ∧ c = s.val) ?_ s hs h
  simp only [coreMap_locationAt (start := start) (c := c) (by rw [hc]; exact hb)
      (by rw [hc]; exact hp),
    coreMap_locationAt (start := start) (c := c) (by rw [hc]; exact hb) (by rw [hc]; exact hf)]
  rfl

theorem failAt_sim {α β : Type} (ψ : α → β) (b : USize) (kind : LexicalErrorKind)
    (position : USize) (hb : start ≤ b.toNat) (hp : b.toNat < position.toNat)
    (Q : α → ZS floor low → Prop) :
    SimP (BaseIs b) Q (boundMap start) ψ
      (BSmtLib.Lexer.Internal.failAt (H := H) (m := m) (R := R) (E := E) kind position)
      (do throw (← Lexer.Internal.WRustPort.errorAt kind (ix start position))) := by
  unfold BSmtLib.Lexer.Internal.failAt Lexer.Internal.WRustPort.errorAt
  have e : (position - 1).toNat = position.toNat - 1 :=
    by have := sub_toNat (p := position) (b := 1) (by simp; omega); simpa using this
  have e' : ix start position - 1 = ix start (position - 1) := by simp only [ix, e]; omega
  rw [e']
  exact failWith_sim start ψ b kind position (position - 1) hb (Nat.le_of_lt hp)
    (by rw [e]; omega) Q

/-- The token end of `X1BatchInCore` for that of the library's
lexer. -/
def endMap (start : Nat) (te : Lexer.Helpers.TokenEnd) : Lexer.Internal.WRustPort.Slice.TokenEnd :=
  { position := ix start te.position, atByte := te.atByte }

theorem fail_sim {α β : Type} (ψ : α → β) (b : USize) (kind : LexicalErrorKind)
    (te : Lexer.Helpers.TokenEnd) (hb : start ≤ b.toNat) (hp : b.toNat ≤ te.position.toNat)
    (hno : te.position.toNat + 1 < USize.size) (Q : α → ZS floor low → Prop) :
    SimP (BaseIs b) Q (boundMap start) ψ
      (BSmtLib.Lexer.Internal.fail (H := H) (m := m) (R := R) (E := E) kind te)
      (do throw (← Lexer.Internal.WRustPort.error kind (endMap start te))) := by
  obtain ⟨pos, atByte⟩ := te
  unfold BSmtLib.Lexer.Internal.fail Lexer.Internal.WRustPort.error
  simp only [endMap] at hp hno ⊢
  have e1 : (pos + 1).toNat = pos.toNat + 1 := by
    rw [USize.toNat_add, USize.toNat_one, Nat.mod_eq_of_lt hno]
  cases atByte with
  | true =>
    have e' : ix start pos + 1 = ix start (pos + 1) := by simp only [ix, e1]; omega
    simp only [ite_true, e']
    exact failWith_sim start ψ b kind _ pos hb (by rw [e1]; omega) hp Q
  | false =>
    simp only [Bool.false_eq_true, ite_false, Nat.add_zero]
    have e0 : pos + 0 = pos := by simp
    rw [e0]
    exact failWith_sim start ψ b kind pos pos hb hp hp Q

theorem expectDelimiter_sim (b : USize) (next : UInt8) (position : USize)
    (hb : start ≤ b.toNat) (hp : b.toNat ≤ position.toNat)
    (hno : position.toNat + 1 < USize.size) :
    SimP (BaseIs b) (fun _ => BaseIs b) (boundMap start) id
      (BSmtLib.Lexer.Internal.expectDelimiter (H := H) (m := m) (R := R) (E := E)
        (floor := floor) (low := low) next position)
      (Lexer.Internal.WRustPort.expectDelimiter next (ix start position)) := by
  unfold BSmtLib.Lexer.Internal.expectDelimiter Lexer.Internal.WRustPort.expectDelimiter
  have e : (position + 1).toNat = position.toNat + 1 := by
    rw [USize.toNat_add, USize.toNat_one, Nat.mod_eq_of_lt hno]
  have e' : ix start position + 1 = ix start (position + 1) := by simp only [ix, e]; omega
  rw [e']
  cases Lexer.Helpers.isDelimiter next
  · exact failAt_sim start id b _ _ hb (by rw [e]; omega) _
  · exact SimP.pure (fun _ h => h) rfl


/-- An error followed by more steps: the library's lexer's error is thrown before them, and so is
the Rust port's. -/
theorem fail_bind_sim {α β γ δ : Type} (ψ : γ → δ) (b : USize) (kind : LexicalErrorKind)
    (te : Lexer.Helpers.TokenEnd) (hb : start ≤ b.toNat) (hp : b.toNat ≤ te.position.toNat)
    (hno : te.position.toNat + 1 < USize.size) (Q : γ → ZS floor low → Prop)
    (k : α → BSmtLib.Lexer.LexM H m R E floor low γ)
    (k' : β → Lexer.Internal.WRustPort.LexM H m R E floor low δ) :
    SimP (BaseIs b) Q (boundMap start) ψ
      (BSmtLib.Lexer.Internal.fail (H := H) (m := m) (R := R) (E := E) kind te >>= k)
      (Lexer.Internal.WRustPort.error kind (endMap start te) >>= fun e => throw e >>= k') := by
  have e1 : (BSmtLib.Lexer.Internal.fail (H := H) (m := m) (R := R) (E := E) kind te >>= k) =
      BSmtLib.Lexer.Internal.fail kind te := by
    unfold BSmtLib.Lexer.Internal.fail BSmtLib.Lexer.Internal.failWith
    simp only [bind_assoc, throw_bind]
  simp only [throw_bind]
  rw [e1]
  exact fail_sim start ψ b kind te hb hp hno Q

/-- An error at a position followed by more steps. -/
theorem failAt_bind_sim {α β γ δ : Type} (ψ : γ → δ) (b : USize) (kind : LexicalErrorKind)
    (position : USize) (hb : start ≤ b.toNat) (hp : b.toNat < position.toNat)
    (Q : γ → ZS floor low → Prop)
    (k : α → BSmtLib.Lexer.LexM H m R E floor low γ)
    (k' : β → Lexer.Internal.WRustPort.LexM H m R E floor low δ) :
    SimP (BaseIs b) Q (boundMap start) ψ
      (BSmtLib.Lexer.Internal.failAt (H := H) (m := m) (R := R) (E := E) kind position >>= k)
      (Lexer.Internal.WRustPort.errorAt kind (ix start position) >>= fun e => throw e >>= k') := by
  have e1 : (BSmtLib.Lexer.Internal.failAt (H := H) (m := m) (R := R) (E := E) kind position >>=
      k) = BSmtLib.Lexer.Internal.failAt kind position := by
    unfold BSmtLib.Lexer.Internal.failAt BSmtLib.Lexer.Internal.failWith
    simp only [bind_assoc, throw_bind]
  simp only [throw_bind]
  rw [e1]
  exact failAt_sim start ψ b kind position hb hp Q

end

end BSmtLib.Facts.Proofs.Lexer.X1BatchInCoreLexer.Core
