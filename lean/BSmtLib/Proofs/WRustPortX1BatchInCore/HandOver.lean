import BSmtLib.Proofs.WRustPortX1BatchInCore.Core
import BSmtLib.Proofs.Lexer.X1BatchInCore

/-!
# The hand-overs

The Rust port hands a batch over in a cursor (`flushCursor`) and acts on a stop of the consumer
inside its loop over the cursor: it sets the version after every call of the consumer, and the
depths and throws the stop where the consumer stopped. The lexer with the batch in its state
returns the stop and the cursor from its loop and acts on them after it (`handOver`): the
depths, the version, and the batch put back into its state before the stop is thrown. The two
are simulated as a whole (`flushCursor_sim`): the version the Rust port sets last is that of
the cursor the loop ends with, which the other sets once. A stop is thrown from states whose
batches have no tokens (`ErZ`).
-/

namespace BSmtLib.Proofs.WRustPortX1BatchInCore

open BSmtLib.Lexer.Internal (intoBatch)
open BSmtLib.Proofs.Simulation
open BSmtLib.Lexer (BATCH_CAPACITY Interrupted)

section

variable {H : Type} {m : Type → Type} {R E : Type} [Monad m] [LawfulMonad m] [Consume H m R E]
  {floor : Option Nat} {low : Nat} {strict : Bool} {Er : St floor low → St floor low → Prop}
  {g g' : BatchTag}

theorem callConsumer_sim (hc : ConsumesAlike H m R E) (P : St floor low → St floor low → Prop)
    (c : BatchCursor g) (d : BatchCursor g') (hcd : CursorAgree c d) (h : c.HasNext)
    (h' : d.HasNext) :
    SimR Er P (fun a b s t => P s t ∧ a.1 = b.1 ∧ CursorAgree a.2.val b.2.val)
      (Lexer.WRustPort.callConsumer (H := H) (m := m) (R := R) (E := E) c h)
      (Lexer.WRustPort.callConsumer d h') := by
  unfold Lexer.WRustPort.callConsumer
  exact SimR.lift (Rab := fun a b => a.1 = b.1 ∧ CursorAgree a.2.val b.2.val)
    (fun s => by
      obtain ⟨y, h1, h2⟩ := hc c d h h' hcd s
      exact ⟨(fun z => ⟨((z.val.1, z.val.2.2), (z.val.2.1, z.val.2.2)), z.property, rfl⟩) <$> y,
        by rw [h1, Functor.map_map], by rw [h2, Functor.map_map]⟩)
    fun _ _ _ _ hst hab => ⟨hst, hab⟩

/-- What the lexer with the batch in its state does after its loop over the cursor. -/
def handOverTail (bytesAfter : ByteArray) :
    Option (Interrupted R E floor) × BatchCursor g →
      Lexer.WRustPort.LexM H m R E floor low TokenBatch :=
  fun (stop, cursor) => do
  if (← Lexer.WRustPort.getCore).recovers then
    match stop with
    | some _ =>
      Lexer.WRustPort.modifyCore fun c =>
        let consumedDepth := cursor.foldConsumedCategories c.consumedDepth fun depth category =>
          match category with
          | .parenOpen => depth + 1
          | .parenClose => depth - 1
          | _ => depth
        { c with consumedDepth, lexedDepth := consumedDepth }
    | none =>
      Lexer.WRustPort.modifyCore fun c => { c with consumedDepth := c.lexedDepth }
  Lexer.WRustPort.modifyCore fun c => { c with version := cursor.version }
  let spent : TokenBatch := { intoBatch cursor with bytes := bytesAfter }
  if let some interrupted := stop then
    Lexer.X1BatchInCore.storeSpent spent
    throw interrupted
  return spent

omit [LawfulMonad m] in
theorem handOver_eq (batch : TokenBatch) (bytesAfter : ByteArray) (hfloor) :
    Lexer.X1BatchInCore.handOver (H := H) (m := m) (R := R) (E := E) (floor := floor) (low := low)
      batch bytesAfter hfloor =
      Lexer.WRustPort.getCore >>= fun c =>
        Lexer.X1BatchInCore.flushCursor (BatchCursor.new c.version batch)
          (fun p hp => BatchCursor.endsAfter_new (hfloor p hp) _) >>= handOverTail bytesAfter := by
  unfold Lexer.X1BatchInCore.handOver handOverTail
  rfl

/-- What the loops over a cursor keep of the two states: the same fields but for the version
and the batch; the Rust port's version is that of its cursor, as it sets it after every call of
the consumer; the batches are those before the loop; the Rust port's line and line start are `l`
and `ls`. -/
structure FlushRel (l ls : Nat) (Bw Bx : TokenBatch) (c : BatchCursor g) (s : St floor low)
    (t : St floor low) : Prop where
  same : SameBut s.val t.val
  version : s.val.version = c.version
  batchW : s.val.batch = Bw
  batchX : t.val.batch = Bx
  line : s.val.line = l
  lineStart : s.val.lineStart = ls

/-- What the hand-overs keep of the two states: `FlushRel` with the version the same, and the
batch given back, which is that of the cursor with the array of contents `bytesAfter`. -/
structure FlushedRel (l ls : Nat) (Bw Bx : TokenBatch) (s : St floor low)
    (t : St floor low) : Prop where
  same : SameBut s.val t.val
  version : s.val.version = t.val.version
  batchW : s.val.batch = Bw
  batchX : t.val.batch = Bx
  line : s.val.line = l
  lineStart : s.val.lineStart = ls

/-- The depths after a stop of the consumer, counted over the tokens it consumed. -/
def stopDepth (cursor : BatchCursor g) (depth : Nat) : Nat :=
  cursor.foldConsumedCategories depth fun depth category =>
    match category with
    | .parenOpen => depth + 1
    | .parenClose => depth - 1
    | _ => depth

omit [Consume H m R E] in
theorem storeSpent_bind_right {α β : Type} {P : St floor low → St floor low → Prop}
    {Q : α → β → St floor low → St floor low → Prop} (spent : TokenBatch)
    {k : Lexer.WRustPort.LexM H m R E floor low α}
    {g : PUnit → Lexer.WRustPort.LexM H m R E floor low β}
    (hk : ∀ s t, P s t → SimR Er (fun s' t' => s' = s ∧ t'.val = { t.val with
      batch := spent.clear t.val.offset
      batchEnded := Nat.le_of_eq (TokenBatch.lastEnd_clear _ _) }) Q k (g ⟨⟩)) :
    SimR Er P Q k (Lexer.X1BatchInCore.storeSpent spent >>= g) := by
  unfold Lexer.X1BatchInCore.storeSpent Lexer.WRustPort.modifyBound
  exact SimR.modify_bind_right fun s t hst => SimR.pre
    (fun s' t' h => ⟨h.1, by rw [h.2]⟩) (hk s t hst)

omit [Monad m] [LawfulMonad m] [Consume H m R E] in
/-- Interruptions with the same result and location are the same. -/
theorem interrupted_eq {i j : Interrupted R E floor} (h1 : i.result = j.result)
    (h2 : i.location = j.location) : i = j := by
  cases i
  cases j
  cases h1
  cases h2
  rfl

omit [Consume H m R E] in
/-- A stop of the consumer: the Rust port sets the depths and throws the stop; the lexer with
the batch in its state sets the depths and the version, and puts the batch back before it throws
the stop. -/
theorem stop_sim {α : Type} (bytesAfter : ByteArray) (i i' : Interrupted R E floor) (hi : i = i')
    (cur : BatchCursor g) (cur' : BatchCursor g') (hag : CursorAgree cur cur') (sW : Core)
    (t : St floor low) (hsame : SameBut sW t.val) (hversion : sW.version = cur.version)
    (hlen : sW.batch.len = 0) (hbytes : strict = true → sW.batch.bytes = bytesAfter)
    (Q : α → TokenBatch → St floor low → St floor low → Prop) (hd) :
    SimR (ErZ strict) (fun s' t' => s'.val = sW ∧ t' = t) Q
      (Lexer.WRustPort.getCore (H := H) (m := m) (R := R) (E := E) >>= fun lift =>
        if lift.recovers = true then
          Lexer.WRustPort.modifyCore (fun c => { c with
            consumedDepth := stopDepth cur c.consumedDepth
            lexedDepth := stopDepth cur c.consumedDepth }) hd >>= fun _ => throw i
        else throw i)
      (handOverTail bytesAfter (some i', cur')) := by
  unfold handOverTail
  dsimp only
  refine getCore_bind fun w' x' => ?_
  refine SimR.intro fun s₀ t₀ h₀ => ?_
  obtain ⟨⟨hs₀, ht₀⟩, hw, hx⟩ := h₀
  subst ht₀
  subst hw hx
  rw [← hs₀] at hsame hversion hlen hbytes
  refine SimR.pre (P := fun s t => s = s₀ ∧ t = t₀) (fun s t h => h.2) ?_
  simp only [throw_bind]
  have hfin : ∀ (w : Core) (x : Core), SameBut w x → w.version = cur.version →
      w.batch.len = 0 → (strict = true → w.batch.bytes = bytesAfter) → ∀ hb hb',
      CoreRel w { x with
        version := cur'.version
        batch := ({ intoBatch cur' with bytes := bytesAfter } : TokenBatch).clear x.offset
        tokenStarted := hb
        batchEnded := hb' } ∧ (strict = true → w.batch.bytes = bytesAfter) := by
    intro w x hs hv hl hby _ _
    refine ⟨?_, hby⟩
    exact { toSameBut := by same_but hs
            version := by rw [hv, hag.version]
            batch := agree_of_len_zero hl rfl
            capacity := by rw [hl]; decide }
  by_cases hr : s₀.val.recovers = true
  · have hr' : t₀.val.recovers = true := hsame.recovers ▸ hr
    rw [ite_eq_left hr, ite_eq_left hr']
    refine SimR.bind (modifyCore_sim _ (fun _ _ s t => s.val.consumedDepth = t.val.consumedDepth ∧
      SameBut s.val t.val ∧ s.val.version = cur.version ∧ s.val.batch.len = 0 ∧
      (strict = true → s.val.batch.bytes = bytesAfter)) ?_) fun _ _ => ?_
    · intro s t h
      obtain ⟨rfl, rfl⟩ := h
      have e : stopDepth cur s.val.consumedDepth = stopDepth cur' t.val.consumedDepth := by
        unfold stopDepth
        rw [hsame.consumedDepth]
        exact hag.foldConsumedCategories _ _
      exact ⟨e, by same_but hsame, hversion, hlen, hbytes⟩
    refine modifyCore_bind_right fun s t h => ?_
    refine storeSpent_bind_right _ fun s' t' h' => ?_
    refine SimR.throw hi fun s'' t'' h'' => ?_
    obtain ⟨rfl, ht'⟩ := h''
    obtain ⟨rfl, rfl⟩ := h'
    obtain ⟨-, hs, hv, hl, hby⟩ := h
    have e : t'' = ⟨_, t''.property⟩ := rfl
    rw [e]
    simp only [ht']
    exact ⟨hfin _ _ hs hv hl hby _ _, hl⟩
  · have hr' : ¬t₀.val.recovers = true := hsame.recovers ▸ hr
    rw [ite_eq_right hr, ite_eq_right hr']
    refine modifyCore_bind_right fun s t h => ?_
    refine storeSpent_bind_right _ fun s' t' h' => ?_
    refine SimR.throw hi fun s'' t'' h'' => ?_
    obtain ⟨rfl, ht'⟩ := h''
    obtain ⟨rfl, rfl⟩ := h'
    obtain ⟨rfl, rfl⟩ := h
    have e : t'' = ⟨_, t''.property⟩ := rfl
    rw [e]
    simp only [ht']
    exact ⟨hfin _ _ hsame hversion hlen hbytes _ _, hlen⟩

omit [Consume H m R E] in
/-- The end of the loop over a cursor that is empty: the Rust port sets the depths; the lexer
with the batch in its state sets the depths and the version, and gives the batch back. -/
theorem finish_sim (l ls : Nat) (Bw Bx : TokenBatch) (bytesAfter : ByteArray)
    (cur : BatchCursor g) (cur' : BatchCursor g') (hag : CursorAgree cur cur') (hd) :
    SimR Er (FlushRel l ls Bw Bx cur)
      (fun _ spent s t => FlushedRel l ls Bw Bx s t ∧
        spent = { intoBatch cur' with bytes := bytesAfter })
      (Lexer.WRustPort.getCore (H := H) (m := m) (R := R) (E := E) (floor := floor) (low := low)
        >>= fun lift =>
        if lift.recovers = true then
          Lexer.WRustPort.modifyCore (fun c => { c with consumedDepth := c.lexedDepth }) hd
        else pure ())
      (handOverTail bytesAfter (none, cur')) := by
  unfold handOverTail
  dsimp only
  refine getCore_bind fun w x => ?_
  refine SimR.intro fun s₀ t₀ h₀ => ?_
  obtain ⟨hrel, hw, hx⟩ := h₀
  subst hw hx
  refine SimR.pre (P := fun s t => s = s₀ ∧ t = t₀) (fun s t h => h.2) ?_
  have hfin : ∀ (w : Core) (x : Core), SameBut w x → w.version = cur.version → ∀ hb hb',
      SameBut w { x with version := cur'.version, tokenStarted := hb, batchEnded := hb' } ∧
        w.version = cur'.version := fun w x hs hv _ _ =>
    ⟨by same_but hs, by rw [hv, hag.version]⟩
  by_cases hr : s₀.val.recovers = true
  · have hr' : t₀.val.recovers = true := hrel.same.recovers ▸ hr
    rw [ite_eq_left hr, ite_eq_left hr']
    refine SimR.of_bind_pure_left (SimR.bind (modifyCore_sim _ (fun _ _ s t =>
      SameBut s.val t.val ∧ s.val.version = cur.version ∧ s.val.batch = Bw ∧ t.val.batch = Bx ∧
        s.val.line = l ∧ s.val.lineStart = ls) ?_) fun _ _ => ?_)
    · intro s t h
      obtain ⟨rfl, rfl⟩ := h
      have e : s.val.lexedDepth = t.val.lexedDepth := hrel.same.lexedDepth
      exact ⟨by same_but hrel.same, hrel.version, hrel.batchW, hrel.batchX, hrel.line,
        hrel.lineStart⟩
    refine modifyCore_bind_right fun s t h => ?_
    refine SimR.pure fun s' t' h' => ?_
    obtain ⟨rfl, rfl⟩ := h'
    obtain ⟨hs, hv, hbw, hbx, hl, hls⟩ := h
    have := hfin _ _ hs hv
    exact ⟨⟨(this _ _).1, by rw [hv, hag.version], hbw, hbx, hl, hls⟩, rfl⟩
  · have hr' : ¬t₀.val.recovers = true := hrel.same.recovers ▸ hr
    rw [ite_eq_right hr, ite_eq_right hr']
    refine SimR.of_bind_pure_left ?_
    rw [pure_bind]
    refine modifyCore_bind_right fun s t h => ?_
    refine SimR.pure fun s' t' h' => ?_
    obtain ⟨rfl, rfl⟩ := h'
    obtain ⟨rfl, rfl⟩ := h
    have := hfin _ _ hrel.same hrel.version
    exact ⟨⟨(this _ _).1, by rw [hrel.version, hag.version], hrel.batchW, hrel.batchX, hrel.line,
      hrel.lineStart⟩, rfl⟩

theorem flushCursor_sim (hcons : ConsumesAlike H m R E) (l ls : Nat) (Bw Bx : TokenBatch)
    (hBw : Bw.len = 0) (bytesAfter : ByteArray) (hbytes : strict = true → Bw.bytes = bytesAfter) :
    ∀ n (c : BatchCursor g) (d : BatchCursor g'), c.remaining = n → CursorAgree c d → ∀ hf hf',
    SimR (ErZ strict) (FlushRel l ls Bw Bx c)
      (fun _ spent s t => FlushedRel l ls Bw Bx s t ∧
        spent = { intoBatch d with bytes := bytesAfter })
      (Lexer.WRustPort.Rust.flushCursor (H := H) (m := m) (R := R) (E := E) (floor := floor)
        (low := low) c hf)
      (Lexer.X1BatchInCore.flushCursor d hf' >>= handOverTail bytesAfter) := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
  intro c d hn hcd hf hf'
  rw [Lexer.WRustPort.Rust.flushCursor, Lexer.X1BatchInCore.flushCursor]
  by_cases hc : c.HasNext
  · have hd : d.HasNext := hcd.hasNext_iff.mp hc
    rw [dite_eq_left_of_eq_true (eq_true hc), dite_eq_left_of_eq_true (eq_true hd), bind_assoc]
    refine SimR.bind (callConsumer_sim hcons _ c d hcd hc hd) fun a b => ?_
    obtain ⟨result, cursor', consumed⟩ := a
    obtain ⟨result', next, consumed'⟩ := b
    dsimp only
    refine SimR.of_fact (F := result = result' ∧ CursorAgree cursor' next) fun ⟨hres, hag⟩ => ?_
    subst hres
    refine modifyCore_bind_left fun s t hst => ?_
    have hsame : SameBut { s.val with version := cursor'.version } t.val := by same_but hst.same
    have hlen : s.val.batch.len = 0 := by rw [hst.batchW]; exact hBw
    have hby : strict = true → s.val.batch.bytes = bytesAfter := fun h => by
      rw [hst.batchW]; exact hbytes h
    have hloc : cursor'.consumedEndOf consumed = next.consumedEndOf consumed' :=
      hag.consumedEndOf consumed consumed'
    have hbatch : intoBatch next = intoBatch d := intoBatch_eq next d
    cases result with
    | ok flow =>
      cases flow with
      | «continue» =>
        dsimp only
        by_cases hr : cursor'.relexRequested = true
        · rw [ite_eq_left hr, ite_eq_left (hag.relex ▸ hr), pure_bind]
          refine SimR.pre ?_ (stop_sim bytesAfter _ _ ?_
            cursor' next hag _ t hsame rfl hlen hby _ _)
          · exact fun s' t' h => ⟨by rw [h.1], h.2⟩
          · exact interrupted_eq rfl hloc
        · rw [ite_eq_right hr, ite_eq_right (hag.relex ▸ hr)]
          have hlt : cursor'.resetConsumed.remaining < n := by
            rw [BatchCursor.remaining_resetConsumed, ← hn]
            exact consumed.remaining_lt
          refine SimR.mono (fun s' t' h => ?_) (fun _ _ _ _ h => ?_) (fun _ _ h => h)
            (ih _ hlt cursor'.resetConsumed next.resetConsumed rfl hag.resetConsumed _ _)
          · obtain ⟨rfl, rfl⟩ := h
            exact ⟨hsame, rfl, hst.batchW, hst.batchX, hst.line, hst.lineStart⟩
          · exact ⟨h.1, by rw [h.2, ← hbatch]; rfl⟩
      | «break» r =>
        dsimp only
        rw [pure_bind]
        refine SimR.pre ?_ (stop_sim bytesAfter _ _ ?_
          cursor' next hag _ t hsame rfl hlen hby _ _)
        · exact fun s' t' h => ⟨by rw [h.1], h.2⟩
        · exact interrupted_eq rfl hloc
    | error err =>
      dsimp only
      rw [pure_bind]
      refine SimR.pre ?_ (stop_sim bytesAfter _ _ ?_
        cursor' next hag _ t hsame rfl hlen hby _ _)
      · exact fun s' t' h => ⟨by rw [h.1], h.2⟩
      · exact interrupted_eq rfl hloc
  · have hd : ¬d.HasNext := fun h => hc (hcd.hasNext_iff.mpr h)
    rw [dite_eq_right_of_eq_false (eq_false hc), dite_eq_right_of_eq_false (eq_false hd), pure_bind]
    exact finish_sim l ls Bw Bx bytesAfter c d hcd _

end

end BSmtLib.Proofs.WRustPortX1BatchInCore
