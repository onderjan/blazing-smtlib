import BSmtLib.Proofs.WRustPortX1BatchInCore.Finish

/-!
# The batch held by the loop of the normal state

The loop of the normal state of both lexers holds the batch, appends the tokens of the fast path
(`pushFast`) and of the slow path (`pushBorrowed`) to it, hands it over when it is full
(`flushHeld`), and puts it back into the lexer state where the loop ends (`leave`,
`leavePending`). The batches the two loops hold agree, have the same array of contents (the
slice's) and are below the capacity (`HR`); while the loops hold them, the batches in the two
lexer states have no tokens (`SRE`).

The Rust port keeps the line and the line start in locals (`FastState`), which it stores back
and loads again around its slow path, and from which its fast path makes the spans; the other
lexer reads them from its state. The locals are the state's wherever the Rust port reads them:
`SRE l ls` with the locals `⟨l, ls⟩`.
-/

namespace BSmtLib.Proofs.WRustPortX1BatchInCore

open BSmtLib.Proofs.Simulation (M runM)
open BSmtLib.Lexer (BATCH_CAPACITY Interrupted)

/-- The batches held by the two loops agree, with the same array of contents, and are below the
capacity. -/
structure HR (b b' : TokenBatch) : Prop where
  agree : Agree b b'
  bytes : b.bytes = b'.bytes
  capacity : b.len < BATCH_CAPACITY

section

variable {H : Type} {m : Type → Type} {R E : Type} [Monad m] [LawfulMonad m] [Consume H m R E]
  {floor : Option Nat} {low : Nat} {strict : Bool}

omit [Consume H m R E] in
theorem leave_sim (l ls : Nat) (offset base position : Nat) (b b' : TokenBatch) (hb : HR b b')
    (hframe hframe' hbatch hbatch') :
    LSim strict (H := H) (m := m) (R := R) (E := E) (floor := floor) (low := low) (SRL l ls)
      (fun _ _ => SRLb strict l ls) (Lexer.WRustPort.leave offset base position b hframe hbatch)
      (Lexer.X1BatchInCore.leave offset base position b' hframe' hbatch') :=
  modifyBound_sim _ _ fun _ _ h => ⟨⟨{ h.1 with
    offset := rfl, base := rfl, state := rfl, batch := hb.agree, capacity := hb.capacity }, h.2⟩,
    fun _ => hb.bytes⟩

omit [Consume H m R E] in
theorem leavePending_sim (l ls : Nat) (state : Lexer.LexerState) (start : Location)
    (offset base position : Nat) (b b' : TokenBatch) (hb : HR b b')
    (hframe hframe' hbatch hbatch' hstart hstart' hfloor hfloor') :
    LSim strict (H := H) (m := m) (R := R) (E := E) (floor := floor) (low := low) (SRL l ls)
      (fun _ _ => SRLb strict l ls)
      (Lexer.WRustPort.leavePending state start offset base position b hframe hbatch hstart hfloor)
      (Lexer.X1BatchInCore.leavePending state start offset base position b' hframe' hbatch' hstart'
        hfloor') :=
  modifyBound_sim _ _ fun _ _ h => ⟨⟨{ h.1 with
    offset := rfl, base := rfl, state := rfl, tokenStart := rfl, batch := hb.agree
    capacity := hb.capacity }, h.2⟩, fun _ => hb.bytes⟩

omit [Consume H m R E] in
/-- The Rust port stores its locals back, which are the line and line start of its state. -/
theorem store_bind_left {α β : Type} {P : WS floor low → XS floor low → Prop}
    {Q : α → β → WS floor low → XS floor low → Prop} (locals : Lexer.WRustPort.FastState)
    {k : PUnit → Lexer.WRustPort.LexM H m R E floor low α}
    {g : Lexer.X1BatchInCore.LexM H m R E floor low β}
    (hP : ∀ s t, P s t → s.val.line = locals.line ∧ s.val.lineStart = locals.lineStart)
    (hk : LSim strict P Q (k ⟨⟩) g) :
    LSim strict P Q (locals.store >>= k) g := by
  unfold Lexer.WRustPort.FastState.store Lexer.WRustPort.modifyCore
  refine SimR.modify_bind_left fun s t h => SimR.pre (fun s' t' h' => ?_) hk
  obtain ⟨hs', ht'⟩ := h'
  have e : s' = s := Subtype.ext (by rw [hs', ← (hP s t h).1, ← (hP s t h).2])
  rw [e, ht']
  exact h

omit [Consume H m R E] in
/-- The Rust port loads its locals: the line and the line start of its state. -/
theorem load_bind_left {α β : Type} {P : WS floor low → XS floor low → Prop}
    {Q : α → β → WS floor low → XS floor low → Prop}
    {k : Lexer.WRustPort.FastState → Lexer.WRustPort.LexM H m R E floor low α}
    {g : Lexer.X1BatchInCore.LexM H m R E floor low β}
    (hk : ∀ s t, P s t → LSim strict (fun s' t' => s' = s ∧ t' = t) Q
      (k ⟨s.val.line, s.val.lineStart⟩) g) :
    LSim strict P Q (Lexer.WRustPort.FastState.load >>= k) g := by
  unfold Lexer.WRustPort.FastState.load
  simp only [bind_assoc, pure_bind]
  exact getCore_bind_left hk

/-- What a push gives back: batches held by the loops, and the two states with batches without
tokens. -/
abbrev PushQ (l ls : Nat) {α β : Type} (val : α → TokenBatch) (val' : β → TokenBatch) (a : α)
    (b : β) (s : WS floor low) (t : XS floor low) : Prop :=
  HR (val a) (val' b) ∧ SRE l ls s t

theorem pushFast_sim (hcons : ConsumesAlike H m R E) (l ls : Nat) (b b' : TokenBatch)
    (hb : HR b b') (locals : Lexer.WRustPort.FastState) (hl : locals.line = l)
    (hls : locals.lineStart = ls) (offset base : Nat) (ty : TokenCategory) (content : ByteSlice)
    (start «end» : Nat) (emit : Bool) (hty hstart hend hframe hframe' hbatch hbatch') :
    LSim strict (H := H) (m := m) (R := R) (E := E) (floor := floor) (low := low) (SRE l ls)
      (PushQ l ls (·.val) (·.val))
      (Lexer.WRustPort.pushFast b locals offset base ty content start «end» emit hty hstart hend
        hframe hbatch)
      (Lexer.X1BatchInCore.pushFast b' offset base ty content start «end» emit hty hstart hend
        hframe' hbatch') := by
  unfold Lexer.WRustPort.pushFast Lexer.X1BatchInCore.pushFast
  cases emit with
  | false =>
    simp only [Bool.false_eq_true, Bool.not_false, ↓reduceIte]
    split
    rename_i batch hlast hfrom heq
    have e : b = batch := congrArg Subtype.val heq
    subst e
    rw [ite_eq_right (by have := hb.capacity; simp; omega)]
    exact SimR.pure fun s t h => ⟨hb, h⟩
  | true =>
    simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    refine getCore_bind_right fun s t h => ?_
    have htl : t.val.line = locals.line := by rw [hl, ← h.1.2.1]; exact h.1.1.line.symm
    have htls : t.val.lineStart = locals.lineStart := by
      rw [hls, ← h.1.2.2]; exact h.1.1.lineStart.symm
    rw [htl, htls]
    split
    rename_i batch hlast hfrom heq
    have e : _ = batch := congrArg Subtype.val heq
    subst e
    have hpush := hb.agree.pushOnLine hb.bytes ty content.start content.stop locals.line
      locals.lineStart (offset + (start - base)) (offset + («end» - base)) hbatch.1
      (.inl (by omega)) hbatch'.1 (.inl (by omega))
    refine SimR.ite (by simp only [beq_iff_eq, hpush.len]) (fun _ => ?_) fun hne => ?_
    · refine SimR.bind (SimR.pre (fun s' t' h' => ?_) (flushHeld_sim hcons l ls _ _ hpush
        hb.bytes _ _ _)) fun x y => ?_
      · obtain ⟨rfl, rfl⟩ := h'
        exact h
      · obtain ⟨x, hx1, hx2⟩ := x
        obtain ⟨y, hy1, hy2⟩ := y
        exact SimR.pure fun s' t' h' => ⟨⟨h'.1, h'.2.1, by rw [h'.2.2.1]; exact zero_lt_capacity⟩,
          h'.2.2.2⟩
    · refine SimR.pure fun s' t' h' => ?_
      obtain ⟨rfl, rfl⟩ := h'
      refine ⟨⟨hpush, hb.bytes, ?_⟩, h⟩
      have := hb.capacity
      simp only [beq_iff_eq] at hne
      show b.len + 1 < BATCH_CAPACITY
      have : b.len + 1 ≠ BATCH_CAPACITY := hne
      omega

/-- `pushFast_sim` with the type and whether the token is emitted given by equations. -/
theorem pushFast_sim' (hcons : ConsumesAlike H m R E) (l ls : Nat) (b b' : TokenBatch)
    (hb : HR b b') (locals : Lexer.WRustPort.FastState) (hl : locals.line = l)
    (hls : locals.lineStart = ls) (offset base : Nat) (ty ty' : TokenCategory) (ety : ty = ty')
    (content : ByteSlice) (start «end» : Nat) (emit emit' : Bool) (eemit : emit = emit')
    (hty hty' hstart hend hframe hframe' hbatch hbatch') :
    LSim strict (H := H) (m := m) (R := R) (E := E) (floor := floor) (low := low) (SRE l ls)
      (PushQ l ls (·.val) (·.val))
      (Lexer.WRustPort.pushFast b locals offset base ty content start «end» emit hty hstart hend
        hframe hbatch)
      (Lexer.X1BatchInCore.pushFast b' offset base ty' content start «end» emit' hty' hstart hend
        hframe' hbatch') := by
  subst ety eemit
  exact pushFast_sim hcons l ls b b' hb locals hl hls offset base ty content start «end» emit _ _
    _ _ _ _ _

theorem pushBorrowed_sim (hcons : ConsumesAlike H m R E) (l ls : Nat) (b b' : TokenBatch)
    (hb : HR b b') (offset base : Nat) (ty : TokenCategory) (content : ByteSlice)
    (start : Location) (tokenEnd : Nat) (hty hafter hend hfloor hafter' hend' hfloor') :
    LSim strict (H := H) (m := m) (R := R) (E := E) (floor := floor) (low := low) (SRE l ls)
      (PushQ l ls (·.val) (·.val))
      (Lexer.WRustPort.pushBorrowed b offset base ty content start tokenEnd hty hafter hend hfloor)
      (Lexer.X1BatchInCore.pushBorrowed b' offset base ty content start tokenEnd hty hafter' hend'
        hfloor') := by
  unfold Lexer.WRustPort.pushBorrowed Lexer.X1BatchInCore.pushBorrowed
  refine getCore_bind_P fun s t h => ?_
  dsimp only
  rw [← h.1.1.line, ← h.1.1.lineStart]
  have hpush := hb.agree.pushLocated hb.bytes ty content.start content.stop start
    { offset := offset + (tokenEnd - base), line := s.val.line,
      column := offset + (tokenEnd - base) - s.val.lineStart } hafter (.inl hend) hafter'
      (.inl hend')
  refine SimR.ite (by simp only [beq_iff_eq, hpush.len]) (fun _ => ?_) fun hne => ?_
  · refine SimR.bind (flushHeld_sim hcons l ls _ _ hpush hb.bytes _ _ _) fun x y => ?_
    obtain ⟨x, hx1, hx2⟩ := x
    obtain ⟨y, hy1, hy2⟩ := y
    exact SimR.pure fun s' t' h' => ⟨⟨h'.1, h'.2.1, by rw [h'.2.2.1]; exact zero_lt_capacity⟩,
      h'.2.2.2⟩
  · refine SimR.pure fun s' t' h' => ?_
    refine ⟨⟨hpush, hb.bytes, ?_⟩, h'⟩
    have := hb.capacity
    simp only [beq_iff_eq] at hne
    show b.len + 1 < BATCH_CAPACITY
    have : b.len + 1 ≠ BATCH_CAPACITY := hne
    omega

end

end BSmtLib.Proofs.WRustPortX1BatchInCore
