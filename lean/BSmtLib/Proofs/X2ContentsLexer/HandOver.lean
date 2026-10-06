import BSmtLib.Proofs.X2ContentsLexer.Core

/-!
# The hand-overs of the library's lexer and of the lexer with the content buffer

The hand-overs to the consumer read no position: they are simulated from every state with any
base, which they keep.
-/

namespace BSmtLib.Proofs.X2ContentsLexer

open BSmtLib.Proofs.Simulation

section

variable {H : Type} {m : Type → Type} {R E : Type} [Monad m] [LawfulMonad m] [Consume H m R E]
  {floor : Option Nat} {low : Nat} (start : Nat) (b : USize)

theorem callConsumer_sim {g : BatchTag} (cursor : BatchCursor g) (h : cursor.HasNext) :
    SimP (BaseIs b) (fun _ => BaseIs b) (boundMap start (floor := floor) (low := low)) id
      (BSmtLib.Lexer.Internal.callConsumer (H := H) (m := m) (R := R) (E := E) cursor h)
      (Lexer.X2Contents.callConsumer cursor h) := by
  unfold BSmtLib.Lexer.Internal.callConsumer Lexer.X2Contents.callConsumer
  exact SimP.lift (fun _ => by simp) fun _ _ h => h

theorem flushCursor_sim {g : BatchTag} : ∀ n (cursor : BatchCursor g), cursor.remaining = n →
    ∀ hfloor hfloor',
    SimP (BaseIs b) (fun _ => BaseIs b) (boundMap start (floor := floor) (low := low)) id
      (BSmtLib.Lexer.Internal.flushCursor (H := H) (m := m) (R := R) (E := E) cursor hfloor)
      (Lexer.X2Contents.flushCursor cursor hfloor') := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
  intro cursor hn hfloor hfloor'
  rw [BSmtLib.Lexer.Internal.flushCursor, Lexer.X2Contents.flushCursor]
  refine SimP.dite Iff.rfl (fun hc _ => ?_) fun _ _ => SimP.pure (fun _ h => h) rfl
  refine SimP.bind (callConsumer_sim start b cursor hc) fun x => ?_
  obtain ⟨result, next, consumed⟩ := x
  dsimp only [id]
  cases result with
  | ok flow =>
    cases flow with
    | «continue» =>
      refine SimP.ite Iff.rfl (fun _ => SimP.pure (fun _ h => h) rfl) fun _ => ?_
      exact ih _ (by rw [← hn, BatchCursor.remaining_resetConsumed]; exact consumed.remaining_lt)
        _ rfl _ _
    | «break» r => exact SimP.pure (fun _ h => h) rfl
  | error err => exact SimP.pure (fun _ h => h) rfl

omit [Consume H m R E] in
/-- Reading the state, under the base. -/
theorem getCore_simB :
    SimP (BaseIs b) (fun c s => BaseIs b s ∧ c = s.val) (boundMap start (floor := floor)
      (low := low)) (coreMap start)
      (BSmtLib.Lexer.Internal.getCore (H := H) (m := m) (R := R) (E := E))
      (Lexer.X2Contents.getCore) :=
  getCore_sim start _

omit [Consume H m R E] in
/-- A step that keeps the base, after reading the state. -/
theorem getCore_bind {α β : Type} {ψ : α → β}
    {k : ZCore → BSmtLib.Lexer.LexM H m R E floor low α}
    {k' : XCore → Lexer.X2Contents.LexM H m R E floor low β} {Q : α → ZS floor low → Prop}
    (hk : ∀ c, c.base = b → SimP (BaseIs b) Q (boundMap start) ψ (k c) (k' (coreMap start c))) :
    SimP (BaseIs b) Q (boundMap start) ψ
      (BSmtLib.Lexer.Internal.getCore >>= k) (Lexer.X2Contents.getCore >>= k') := by
  refine SimP.bind (getCore_simB start b) fun c => ?_
  intro s hs h
  exact hk c (by rw [hs.2]; exact hs.1) s hs.1 h

omit [Consume H m R E] in
theorem storeSpent_sim (spent : TokenBatch) :
    SimP (BaseIs b) (fun _ => BaseIs b) (boundMap start (floor := floor) (low := low)) id
      (BSmtLib.Lexer.Internal.storeSpent (H := H) (m := m) (R := R) (E := E) spent)
      (Lexer.X2Contents.storeSpent spent) :=
  modifyBound_sim start _ _ (fun _ _ => rfl) fun _ hc => hc

/-- Takes the steps of the hand-overs that read the state, change it without a position, branch
and end, as long as they are the same on both sides. -/
local macro "sim_auto" : tactic => `(tactic| repeat (first
    | (refine getCore_bind _ _ fun _ _ => ?_)
    | (refine SimP.seq (modifyCore_sim _ _ _ (fun _ _ => by rfl) fun _ hc => hc) fun _ => ?_)
    | (refine SimP.seq (storeSpent_sim _ _ _) fun _ => ?_)
    | (refine SimP.ite Iff.rfl (fun _ => ?_) fun _ => ?_)
    | (exact SimP.pure (fun _ h => h) rfl)
    | (exact SimP.throw _)
    | (refine SimP.seq (SimP.throw (ψ := id) _) fun _ => ?_)
    | (exact modifyCore_sim _ _ _ (fun _ _ => by rfl) fun _ hc => hc)
    | (exact storeSpent_sim _ _ _)))

theorem handOver_sim (batch : TokenBatch) (bytesAfter : ByteArray) (hfloor hfloor') :
    SimP (BaseIs b) (fun _ => BaseIs b) (boundMap start (floor := floor) (low := low)) id
      (BSmtLib.Lexer.Internal.handOver (H := H) (m := m) (R := R) (E := E) batch bytesAfter
        hfloor)
      (Lexer.X2Contents.handOver batch bytesAfter hfloor') := by
  unfold BSmtLib.Lexer.Internal.handOver Lexer.X2Contents.handOver
  refine getCore_bind start b fun c _ => ?_
  refine SimP.bind (flushCursor_sim start b _ _ rfl _ _) fun x => ?_
  obtain ⟨stop, cursor⟩ := x
  cases stop <;> dsimp only [id] <;> sim_auto

omit [Consume H m R E] in
theorem takeBatch_sim :
    SimP (BaseIs b) (fun _ => BaseIs b) (boundMap start (floor := floor) (low := low)) id
      (BSmtLib.Lexer.Internal.takeBatch (H := H) (m := m) (R := R) (E := E))
      (Lexer.X2Contents.takeBatch) := by
  unfold BSmtLib.Lexer.Internal.takeBatch Lexer.X2Contents.takeBatch
  exact SimP.modifyGet (fun _ _ => rfl) fun _ hc => hc

theorem flushBatch_sim :
    SimP (BaseIs b) (fun _ => BaseIs b) (boundMap start (floor := floor) (low := low)) id
      (BSmtLib.Lexer.Internal.flushBatch (H := H) (m := m) (R := R) (E := E))
      (Lexer.X2Contents.flushBatch) := by
  unfold BSmtLib.Lexer.Internal.flushBatch Lexer.X2Contents.flushBatch
  refine getCore_bind start b fun c _ => ?_
  refine SimP.ite Iff.rfl (fun _ => SimP.pure (fun _ h => h) rfl) fun _ => ?_
  refine SimP.bind (takeBatch_sim start b) fun x => ?_
  obtain ⟨batch, hbatch⟩ := x
  exact SimP.bind (handOver_sim start b _ _ _ _) fun _ => storeSpent_sim start b _

theorem handOverStored_sim (ty : TokenCategory) (hty : ty ≠ .endOfFile) (s e : Location)
    (hend : s.offset < e.offset) (hfloor hfloor') :
    SimP (BaseIs b) (fun _ => BaseIs b) (boundMap start (floor := floor) (low := low)) id
      (BSmtLib.Lexer.Internal.handOverStored (H := H) (m := m) (R := R) (E := E) ty hty s e hend
        hfloor)
      (Lexer.X2Contents.handOverStored ty hty s e hend hfloor') := by
  unfold BSmtLib.Lexer.Internal.handOverStored Lexer.X2Contents.handOverStored
  refine SimP.bind (flushBatch_sim start b) fun _ => ?_
  refine SimP.bind (takeBatch_sim start b) fun x => ?_
  obtain ⟨batch, hbatch⟩ := x
  refine getCore_bind start b fun c _ => ?_
  exact SimP.bind (handOver_sim start b _ _ _ _) fun _ => storeSpent_sim start b _

theorem handOverEof_sim (location : Location) {low : Nat} :
    SimP (BaseIs b) (fun _ => BaseIs b) (boundMap start (floor := none) (low := low)) id
      (BSmtLib.Lexer.Internal.handOverEof (H := H) (m := m) (R := R) (E := E) location)
      (Lexer.X2Contents.handOverEof location) := by
  unfold BSmtLib.Lexer.Internal.handOverEof Lexer.X2Contents.handOverEof
  refine SimP.bind (flushBatch_sim start b) fun _ => ?_
  refine SimP.bind (takeBatch_sim start b) fun x => ?_
  obtain ⟨batch, hbatch⟩ := x
  refine getCore_bind start b fun c _ => ?_
  exact SimP.bind (handOver_sim start b _ _ _ _) fun _ => storeSpent_sim start b _

end

end BSmtLib.Proofs.X2ContentsLexer
