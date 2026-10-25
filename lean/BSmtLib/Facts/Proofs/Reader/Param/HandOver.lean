module

public import BSmtLib.Facts.Proofs.Reader.Param.Walk
import all BSmtLib.Lexer

@[expose] public section

/-!
# The handover to the two consumers

The lexer's steps that do not hand anything over are related on the two consumers by the walk
alone. Those that hand a batch over call the consumer: where the two calls on the same cursor are
related as the link says (`Calls`), the lexer acts on their answers alike, and the two handovers
are related (`Calls.handOver_sim`); the walk needs only that (`Consumers`). Here are the lemmas
for the helpers of the lexer's state and for the handover (`flushCursor`, `handOver`,
`flushBatch`, `handOverStored`, `handOverEof`).
-/

open BSmtLib.Lexer.Cursor (LexerCursor)

namespace BSmtLib.Facts.Proofs.Reader.Param.HandOver

open BSmtLib.Lexer
open BSmtLib.Lexer.Cursor.LexerCursor.Internal (remaining)
open BSmtLib.Lexer.Internal (BATCH_CAPACITY Stop Interrupted Failure LexerCore InnerM StepM LexM)
open BSmtLib.Facts.Proofs.Reader.Param.Basic

section

variable {H₁ H₂ : Type} {m₁ m₂ : Type → Type} [Monad m₁] [Monad m₂] {R₁ R₂ E₁ E₂ : Type}
  [Token.Consume H₁ R₁ E₁] [Token.Consume H₂ R₂ E₂]

/-- The two consumers' calls on the same cursor are related as the link says: the same answer,
with results and errors related, and the same cursor given back. Both take whitespace and
comments, or neither does. -/
structure Calls [∀ b, Token.ConsumeFrom H₁ (LexerCursor b) m₁]
    [∀ b, Token.ConsumeFrom H₂ (LexerCursor b) m₂]
    (L : Link H₁ m₁ R₁ E₁ H₂ m₂ R₂ E₂) : Prop where
  concrete : Token.Consume.isConcrete (H := H₁) = Token.Consume.isConcrete (H := H₂)
  consume {b : Token.BatchTag} (cursor : LexerCursor b) (h : cursor.HasNext) :
    L.rc.rel (fun a b => ERel L.re (FlowRel L.rr) a.1 b.1 ∧ a.2 = b.2)
      (Token.ConsumeFrom.consume cursor h) (Token.ConsumeFrom.consume cursor h)

/-- The lexer's handovers of the same batch to the two consumers are related as the link says:
the same values, or related interruptions. Both take whitespace and comments, or neither
does. -/
structure Consumers [∀ b, Token.ConsumeFrom H₁ (LexerCursor b) m₁]
    [∀ b, Token.ConsumeFrom H₂ (LexerCursor b) m₂]
    (L : Link H₁ m₁ R₁ E₁ H₂ m₂ R₂ E₂) : Prop where
  concrete : Token.Consume.isConcrete (H := H₁) = Token.Consume.isConcrete (H := H₂)
  handOver {floor : Option Nat} {low : Nat} (batch : Token.Internal.TokenBatch)
      (bytesAfter : ByteArray)
    (hfloor : ∀ p, floor = some p → batch.EndsAfter p) :
    LSim L (· = ·) (Internal.handOver (H := H₁) (floor := floor)
        (low := low) batch bytesAfter hfloor)
      (Internal.handOver (H := H₂) batch bytesAfter hfloor)

end

section State

variable {H₁ H₂ : Type} {m₁ m₂ : Type → Type} [Monad m₁] [Monad m₂] {R₁ R₂ E₁ E₂ : Type}
  {L : Link H₁ m₁ R₁ E₁ H₂ m₂ R₂ E₂} {floor : Option Nat} {low : Nat}

/-! ## The helpers of the lexer's state -/

theorem getCore_sim : LSim L (· = ·) (Internal.getCore (floor := floor) (low := low))
    Internal.getCore := by
  unfold Internal.getCore; lsim

theorem modifyCore_sim (f : LexerCore → LexerCore) (h) :
    LSim L (· = ·) (Internal.modifyCore (floor := floor) (low := low) f h)
        (Internal.modifyCore f h) := by
  unfold Internal.modifyCore; lsim

theorem modifyBound_sim (f) :
    LSim L (· = ·) (Internal.modifyBound (floor := floor) (low := low) f)
        (Internal.modifyBound f) := by
  unfold Internal.modifyBound; lsim

theorem setNormal_sim : LSim L (· = ·) (Internal.setNormal (floor := floor) (low := low))
    Internal.setNormal := by
  unfold Internal.setNormal; lsim

theorem setTokenState_sim (state start h) :
    LSim L (· = ·) (Internal.setTokenState (floor := floor) (low := low) state start h)
      (Internal.setTokenState state start h) := by
  unfold Internal.setTokenState; lsim

theorem modifyContent_sim (f) :
    LSim L (· = ·) (Internal.modifyContent (floor := floor) (low := low) f)
        (Internal.modifyContent f) := by
  unfold Internal.modifyContent; lsim

theorem extendContent_sim (input start stop) :
    LSim L (· = ·) (Internal.extendContent (floor := floor) (low := low) input start stop)
      (Internal.extendContent input start stop) := by
  unfold Internal.extendContent; lsim

theorem pushContent_sim (c) :
    LSim L (· = ·) (Internal.pushContent (floor := floor) (low := low) c)
        (Internal.pushContent c) := by
  unfold Internal.pushContent; lsim

theorem startToken_sim (offset base position hframe) :
    LSim L (· = ·) (Internal.startToken (floor := floor) (low := low) offset base position hframe)
      (Internal.startToken offset base position hframe) := by
  unfold Internal.startToken; lsim

theorem markLineFeedAt_sim (position) :
    LSim L (· = ·) (Internal.markLineFeedAt (floor := floor) (low := low) position)
      (Internal.markLineFeedAt position) := by
  unfold Internal.markLineFeedAt; lsim

theorem failWith_sim {α : Type} (kind position failure) :
    LSim L (· = ·) (Internal.failWith (floor := floor) (low := low) (α := α) kind position failure)
      (Internal.failWith kind position failure) := by
  unfold Internal.failWith; lsim

theorem failAt_sim {α : Type} (kind position) :
    LSim L (· = ·) (Internal.failAt (floor := floor) (low := low) (α := α) kind position)
      (Internal.failAt kind position) := by
  unfold Internal.failAt; lsim

theorem fail_sim {α : Type} (kind tokenEnd) :
    LSim L (· = ·) (Internal.fail (floor := floor) (low := low) (α := α) kind tokenEnd)
      (Internal.fail kind tokenEnd) := by
  unfold Internal.fail; lsim

theorem expectDelimiter_sim (next position) :
    LSim L (· = ·) (Internal.expectDelimiter (floor := floor) (low := low) next position)
      (Internal.expectDelimiter next position) := by
  unfold Internal.expectDelimiter; lsim

theorem storeSpent_sim (spent) :
    LSim L (· = ·) (Internal.storeSpent (floor := floor) (low := low) spent)
        (Internal.storeSpent spent) := by
  unfold Internal.storeSpent; lsim

theorem takeBatch_sim : LSim L (· = ·) (Internal.takeBatch (floor := floor) (low := low))
    Internal.takeBatch := by
  unfold Internal.takeBatch; lsim

theorem locationFrom_sim (base position) :
    LSim L (· = ·) (Internal.locationFrom (floor := floor) (low := low) base position)
      (Internal.locationFrom base position) := by
  unfold Internal.locationFrom; lsim

end State
section Consumer

variable {H₁ H₂ : Type} {m₁ m₂ : Type → Type} [Monad m₁] [Monad m₂] {R₁ R₂ E₁ E₂ : Type}
  [Token.Consume H₁ R₁ E₁] [Token.Consume H₂ R₂ E₂] [∀ b, Token.ConsumeFrom H₁
      (LexerCursor b) m₁]
  [∀ b, Token.ConsumeFrom H₂ (LexerCursor b) m₂]
  {L : Link H₁ m₁ R₁ E₁ H₂ m₂ R₂ E₂} {floor : Option Nat} {low : Nat}

/-! ## The handover -/

theorem callConsumer_sim (hc : Calls L) {b : Token.BatchTag} (cursor : LexerCursor b)
    (h : cursor.HasNext) :
    LSim L (fun a b => ERel L.re (FlowRel L.rr) a.1 b.1 ∧ a.2 = b.2)
      (Internal.callConsumer (floor := floor) (low := low) cursor h)
          (Internal.callConsumer cursor h) :=
  XSim.lift (SSim.lift (hc.consume cursor h))

/-- What the handover of a cursor gives: related stops, if any, and the same cursor. -/
abbrev FlushRel (L : Link H₁ m₁ R₁ E₁ H₂ m₂ R₂ E₂) {b : Token.BatchTag} :
    Option (Interrupted R₁ E₁ floor) × LexerCursor b →
      Option (Interrupted R₂ E₂ floor) × LexerCursor b → Prop :=
  fun a b => ORel (IRel L.rr L.re) a.1 b.1 ∧ a.2 = b.2

theorem flushCursor_sim (hc : Calls L) {b : Token.BatchTag} :
    ∀ (n : Nat) (cursor : LexerCursor b) (hfloor), remaining cursor < n →
      LSim L (FlushRel L) (Internal.flushCursor (floor := floor) (low := low) cursor hfloor)
        (Internal.flushCursor cursor hfloor)
  | 0, _, _, hn => absurd hn (Nat.not_lt_zero _)
  | n + 1, cursor, hfloor, hn => by
    rw [Internal.flushCursor.eq_1, Internal.flushCursor.eq_1]
    refine XSim.dite (fun h => ?_) (fun _ => XSim.pure ⟨trivial, rfl⟩)
    refine XSim.bind_eq getCore_sim fun core => ?_
    refine XSim.ite (fun _ => XSim.pure ⟨⟨rfl, rfl, rfl⟩, rfl⟩) (fun _ => ?_)
    refine XSim.bind (callConsumer_sim hc cursor h) ?_
    rintro ⟨r₁, next, consumed⟩ ⟨r₂, next', consumed'⟩ ⟨hr, he⟩
    cases he
    dsimp only
    match r₁, r₂, hr with
    | .error e₁, .error e₂, he =>
      refine XSim.ite (fun _ => ?_) (fun _ => XSim.pure ⟨⟨rfl, rfl, he⟩, rfl⟩)
      refine XSim.bind_eq ?_ fun _ => XSim.pure ⟨⟨rfl, rfl, he⟩, rfl⟩
      lsim
    | .ok flow₁, .ok flow₂, hf =>
      dsimp only
      refine XSim.ite (fun _ => ?_) (fun _ => ?_)
      · refine XSim.pure ⟨⟨rfl, rfl, ?_⟩, rfl⟩
        match flow₁, flow₂, hf with
        | .continue, .continue, _ => exact trivial
        | .break r₁, .break r₂, hf => exact hf
      · match flow₁, flow₂, hf with
        | .continue, .continue, _ =>
          dsimp only
          refine XSim.ite (fun _ => XSim.pure ⟨⟨rfl, rfl, trivial⟩, rfl⟩) (fun _ => ?_)
          refine flushCursor_sim hc n _ _ ?_
          rw [Lexer.Cursor.LexerCursor.remaining_resetConsumed]
          exact Nat.lt_of_lt_of_le consumed.remaining_lt (Nat.le_of_lt_succ hn)
        | .break r₁, .break r₂, hf =>
          dsimp only
          exact XSim.dite (fun _ => XSim.pure ⟨⟨rfl, rfl, rfl⟩, rfl⟩)
            (fun _ => XSim.pure ⟨⟨rfl, rfl, hf⟩, rfl⟩)
theorem Calls.handOver_sim (hc : Calls L) (batch bytesAfter hfloor) :
    LSim L (· = ·) (Internal.handOver (floor := floor) (low := low) batch bytesAfter hfloor)
      (Internal.handOver batch bytesAfter hfloor) := by
  unfold Internal.handOver
  refine XSim.bind_eq getCore_sim fun core => ?_
  refine XSim.bind (flushCursor_sim hc _ _ _ (Nat.lt_succ_self _)) ?_
  rintro ⟨stop₁, cursor⟩ ⟨stop₂, cursor'⟩ ⟨hs, he⟩
  cases he
  dsimp only
  refine XSim.bind_eq getCore_sim fun core' => ?_
  match stop₁, stop₂, hs with
  | none, none, _ => lsim
  | some i₁, some i₂, hi =>
    lsim

/-- Consumers whose calls are related have related handovers. -/
theorem Consumers.ofCalls (hc : Calls L) : Consumers L :=
  ⟨hc.concrete, fun batch bytesAfter hfloor => Calls.handOver_sim hc batch bytesAfter hfloor⟩

theorem handOver_sim (hc : Consumers L) (batch bytesAfter hfloor) :
    LSim L (· = ·) (Internal.handOver (floor := floor) (low := low) batch bytesAfter hfloor)
      (Internal.handOver batch bytesAfter hfloor) :=
  hc.handOver batch bytesAfter hfloor

theorem flushBatch_sim (hc : Consumers L) :
    LSim L (· = ·) (Internal.flushBatch (floor := floor) (low := low)) Internal.flushBatch := by
  unfold Internal.flushBatch; lsim

theorem handOverStored_sim (hc : Consumers L) (ty start «end» hend hfloor) :
    LSim L (· = ·) (Internal.handOverStored (floor := floor)
        (low := low) ty start «end» hend hfloor)
      (Internal.handOverStored ty start «end» hend hfloor) := by
  unfold Internal.handOverStored; lsim

theorem handOverEof_sim (hc : Consumers L) (location) :
    LSim L (· = ·) (Internal.handOverEof (low := low) location)
        (Internal.handOverEof location) := by
  unfold Internal.handOverEof; lsim

end Consumer

/-! ## Consumers with the same handovers -/

section Same

variable {H₁ H₂ : Type} {m₁ m₂ : Type → Type} [Monad m₁] [Monad m₂] {R₁ R₂ E₁ E₂ : Type}
  [Token.Consume H₁ R₁ E₁] [Token.Consume H₂ R₂ E₂] {L : Link H₁ m₁ R₁ E₁ H₂ m₂ R₂ E₂}

/-- The relation of the handovers holds for a second consumer whose handovers are those of
another one on its type. -/
theorem Consumers.ofEq₂ {inst₁ : ∀ b, Token.ConsumeFrom H₁ (LexerCursor b) m₁}
    {inst₂ inst₂' : ∀ b, Token.ConsumeFrom H₂ (LexerCursor b) m₂}
    (he : ∀ (floor : Option Nat) (low : Nat) (batch : Token.Internal.TokenBatch)
    (bytesAfter : ByteArray)
      (hfloor : ∀ p, floor = some p → batch.EndsAfter p),
      @Internal.handOver H₂ m₂ R₂ E₂ _ _ inst₂ floor low batch bytesAfter hfloor =
        @Internal.handOver H₂ m₂ R₂ E₂ _ _ inst₂' floor low batch bytesAfter hfloor)
    (hc : @Consumers H₁ H₂ m₁ m₂ _ _ R₁ R₂ E₁ E₂ _ _ inst₁ inst₂' L) :
    @Consumers H₁ H₂ m₁ m₂ _ _ R₁ R₂ E₁ E₂ _ _ inst₁ inst₂ L :=
  @Consumers.mk H₁ H₂ m₁ m₂ _ _ R₁ R₂ E₁ E₂ _ _ inst₁ inst₂ L hc.concrete
    fun {floor low} batch bytesAfter hfloor => by
      rw [he]; exact @Consumers.handOver H₁ H₂ m₁ m₂ _ _ R₁ R₂ E₁ E₂ _ _ inst₁ inst₂' L hc floor
        low batch bytesAfter hfloor

/-- The relation of the handovers holds for a first consumer whose handovers are those of
another one on its type. -/
theorem Consumers.ofEq₁ {inst₁ inst₁' : ∀ b, Token.ConsumeFrom H₁ (LexerCursor b) m₁}
    {inst₂ : ∀ b, Token.ConsumeFrom H₂ (LexerCursor b) m₂}
    (he : ∀ (floor : Option Nat) (low : Nat) (batch : Token.Internal.TokenBatch)
    (bytesAfter : ByteArray)
      (hfloor : ∀ p, floor = some p → batch.EndsAfter p),
      @Internal.handOver H₁ m₁ R₁ E₁ _ _ inst₁ floor low batch bytesAfter hfloor =
        @Internal.handOver H₁ m₁ R₁ E₁ _ _ inst₁' floor low batch bytesAfter hfloor)
    (hc : @Consumers H₁ H₂ m₁ m₂ _ _ R₁ R₂ E₁ E₂ _ _ inst₁' inst₂ L) :
    @Consumers H₁ H₂ m₁ m₂ _ _ R₁ R₂ E₁ E₂ _ _ inst₁ inst₂ L :=
  @Consumers.mk H₁ H₂ m₁ m₂ _ _ R₁ R₂ E₁ E₂ _ _ inst₁ inst₂ L hc.concrete
    fun {floor low} batch bytesAfter hfloor => by
      rw [he]; exact @Consumers.handOver H₁ H₂ m₁ m₂ _ _ R₁ R₂ E₁ E₂ _ _ inst₁' inst₂ L hc floor
        low batch bytesAfter hfloor

end Same

end BSmtLib.Facts.Proofs.Reader.Param.HandOver
