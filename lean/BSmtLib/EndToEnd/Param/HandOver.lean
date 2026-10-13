import BSmtLib.EndToEnd.Param.Walk

/-!
# The handover to the two consumers

The lexer's steps that do not hand anything over are related on the two consumers by the walk
alone. Those that hand a batch over call the consumer: the two calls are related as the link
says (`Consumers`), and the lexer acts on their answers alike. Here are the lemmas for the
helpers of the lexer's state and for the handover (`flushCursor`, `handOver`, `flushBatch`,
`handOverStored`, `handOverEof`).
-/

namespace BSmtLib.EndToEnd.Param

open BSmtLib.Lexer BSmtLib.Lexer.Internal

section

variable {H₁ H₂ : Type} {m₁ m₂ : Type → Type} [Monad m₁] [Monad m₂] {R₁ R₂ E₁ E₂ : Type}
  [Consume H₁ R₁ E₁] [Consume H₂ R₂ E₂]

/-- The two consumers' calls on the same cursor are related as the link says: the same answer,
with results and errors related, and the same cursor given back. Both take whitespace and
comments, or neither does. -/
structure Consumers [∀ b, ConsumeFrom H₁ (BatchCursor b) m₁]
    [∀ b, ConsumeFrom H₂ (BatchCursor b) m₂] (L : Link H₁ m₁ R₁ E₁ H₂ m₂ R₂ E₂) : Prop where
  concrete : Consume.isConcrete (H := H₁) = Consume.isConcrete (H := H₂)
  consume {b : BatchTag} (cursor : BatchCursor b) (h : cursor.HasNext) :
    L.rc.rel (fun a b => ERel L.re (FlowRel L.rr) a.1 b.1 ∧ a.2 = b.2)
      (ConsumeFrom.consume cursor h) (ConsumeFrom.consume cursor h)

end

section State

variable {H₁ H₂ : Type} {m₁ m₂ : Type → Type} [Monad m₁] [Monad m₂] {R₁ R₂ E₁ E₂ : Type}
  {L : Link H₁ m₁ R₁ E₁ H₂ m₂ R₂ E₂} {floor : Option Nat} {low : Nat}

/-! ## The helpers of the lexer's state -/

theorem getCore_sim : LSim L (· = ·) (getCore (floor := floor) (low := low)) getCore := by
  unfold getCore; lsim

theorem modifyCore_sim (f : LexerCore → LexerCore) (h) :
    LSim L (· = ·) (modifyCore (floor := floor) (low := low) f h) (modifyCore f h) := by
  unfold modifyCore; lsim

theorem modifyBound_sim (f) :
    LSim L (· = ·) (modifyBound (floor := floor) (low := low) f) (modifyBound f) := by
  unfold modifyBound; lsim

theorem setNormal_sim : LSim L (· = ·) (setNormal (floor := floor) (low := low)) setNormal := by
  unfold setNormal; lsim

theorem setTokenState_sim (state start h) :
    LSim L (· = ·) (setTokenState (floor := floor) (low := low) state start h)
      (setTokenState state start h) := by
  unfold setTokenState; lsim

theorem modifyContent_sim (f) :
    LSim L (· = ·) (modifyContent (floor := floor) (low := low) f) (modifyContent f) := by
  unfold modifyContent; lsim

theorem extendContent_sim (input start stop) :
    LSim L (· = ·) (extendContent (floor := floor) (low := low) input start stop)
      (extendContent input start stop) := by
  unfold extendContent; lsim

theorem pushContent_sim (c) :
    LSim L (· = ·) (pushContent (floor := floor) (low := low) c) (pushContent c) := by
  unfold pushContent; lsim

theorem startToken_sim (offset base position hframe) :
    LSim L (· = ·) (startToken (floor := floor) (low := low) offset base position hframe)
      (startToken offset base position hframe) := by
  unfold startToken; lsim

theorem markLineFeedAt_sim (position) :
    LSim L (· = ·) (markLineFeedAt (floor := floor) (low := low) position)
      (markLineFeedAt position) := by
  unfold markLineFeedAt; lsim

theorem failWith_sim {α : Type} (kind position failure) :
    LSim L (· = ·) (failWith (floor := floor) (low := low) (α := α) kind position failure)
      (failWith kind position failure) := by
  unfold failWith; lsim

theorem failAt_sim {α : Type} (kind position) :
    LSim L (· = ·) (failAt (floor := floor) (low := low) (α := α) kind position)
      (failAt kind position) := by
  unfold failAt; lsim

theorem fail_sim {α : Type} (kind tokenEnd) :
    LSim L (· = ·) (fail (floor := floor) (low := low) (α := α) kind tokenEnd)
      (fail kind tokenEnd) := by
  unfold fail; lsim

theorem expectDelimiter_sim (next position) :
    LSim L (· = ·) (expectDelimiter (floor := floor) (low := low) next position)
      (expectDelimiter next position) := by
  unfold expectDelimiter; lsim

theorem storeSpent_sim (spent) :
    LSim L (· = ·) (storeSpent (floor := floor) (low := low) spent) (storeSpent spent) := by
  unfold storeSpent; lsim

theorem takeBatch_sim : LSim L (· = ·) (takeBatch (floor := floor) (low := low)) takeBatch := by
  unfold takeBatch; lsim

theorem locationFrom_sim (base position) :
    LSim L (· = ·) (locationFrom (floor := floor) (low := low) base position)
      (locationFrom base position) := by
  unfold locationFrom; lsim

end State
section Consumer

variable {H₁ H₂ : Type} {m₁ m₂ : Type → Type} [Monad m₁] [Monad m₂] {R₁ R₂ E₁ E₂ : Type}
  [Consume H₁ R₁ E₁] [Consume H₂ R₂ E₂] [∀ b, ConsumeFrom H₁ (BatchCursor b) m₁]
  [∀ b, ConsumeFrom H₂ (BatchCursor b) m₂]
  {L : Link H₁ m₁ R₁ E₁ H₂ m₂ R₂ E₂} {floor : Option Nat} {low : Nat}

/-! ## The handover -/

theorem callConsumer_sim (hc : Consumers L) {b : BatchTag} (cursor : BatchCursor b)
    (h : cursor.HasNext) :
    LSim L (fun a b => ERel L.re (FlowRel L.rr) a.1 b.1 ∧ a.2 = b.2)
      (callConsumer (floor := floor) (low := low) cursor h) (callConsumer cursor h) :=
  XSim.lift (SSim.lift (hc.consume cursor h))

/-- What the handover of a cursor gives: related stops, if any, and the same cursor. -/
abbrev FlushRel (L : Link H₁ m₁ R₁ E₁ H₂ m₂ R₂ E₂) {b : BatchTag} :
    Option (Interrupted R₁ E₁ floor) × BatchCursor b →
      Option (Interrupted R₂ E₂ floor) × BatchCursor b → Prop :=
  fun a b => ORel (IRel L.rr L.re) a.1 b.1 ∧ a.2 = b.2

theorem flushCursor_sim (hc : Consumers L) {b : BatchTag} :
    ∀ (n : Nat) (cursor : BatchCursor b) (hfloor), cursor.remaining < n →
      LSim L (FlushRel L) (flushCursor (floor := floor) (low := low) cursor hfloor)
        (flushCursor cursor hfloor)
  | 0, _, _, hn => absurd hn (Nat.not_lt_zero _)
  | n + 1, cursor, hfloor, hn => by
    rw [flushCursor.eq_1, flushCursor.eq_1]
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
          rw [BatchCursor.remaining_resetConsumed]
          exact Nat.lt_of_lt_of_le consumed.remaining_lt (Nat.le_of_lt_succ hn)
        | .break r₁, .break r₂, hf =>
          dsimp only
          exact XSim.dite (fun _ => XSim.pure ⟨⟨rfl, rfl, rfl⟩, rfl⟩)
            (fun _ => XSim.pure ⟨⟨rfl, rfl, hf⟩, rfl⟩)
theorem handOver_sim (hc : Consumers L) (batch bytesAfter hfloor) :
    LSim L (· = ·) (handOver (floor := floor) (low := low) batch bytesAfter hfloor)
      (handOver batch bytesAfter hfloor) := by
  unfold handOver
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

theorem flushBatch_sim (hc : Consumers L) :
    LSim L (· = ·) (flushBatch (floor := floor) (low := low)) flushBatch := by
  unfold flushBatch; lsim

theorem handOverStored_sim (hc : Consumers L) (ty start «end» hend hfloor) :
    LSim L (· = ·) (handOverStored (floor := floor) (low := low) ty start «end» hend hfloor)
      (handOverStored ty start «end» hend hfloor) := by
  unfold handOverStored; lsim

theorem handOverEof_sim (hc : Consumers L) (location) :
    LSim L (· = ·) (handOverEof (low := low) location) (handOverEof location) := by
  unfold handOverEof; lsim

end Consumer

end BSmtLib.EndToEnd.Param
