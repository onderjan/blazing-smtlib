import BSmtLib.Proofs.WRustPortX1BatchInCore.Flush
import BSmtLib.Proofs.WRustPortX1BatchInCore.Ops

/-!
# The operations of the Rust port and of the lexer with the batch in its state

The operations of the Rust port (`WRustPort.Rust.ops`) and of the lexer with the batch in its
state (`X1BatchInCore.ops`) simulate each other (`opsSim_rust_x1BatchInCore`), for every consumer
that reads the cursors it is handed only below the length of their batches (`ConsumesAlike`).
The hand-overs are shown alike in `HandOver` and `Flush`; here the batch held by the loop of the
normal state and the locals of its fast path.

The Rust port keeps the line and the line start in locals (`FastState`), which it loads from
its state and stores back, and from which its fast path makes the spans; the other lexer has no
locals and reads its state. The locals are related at the line and the line start of the
states when they are those (`FastRel`): the Rust port's locals are the line and the line start
of its state wherever it reads them.
-/

namespace BSmtLib.Proofs.WRustPortX1BatchInCore

open BSmtLib.Proofs.Simulation
open BSmtLib.Lexer (BATCH_CAPACITY Interrupted)

/-- The Rust port's locals are the line and the line start; the other lexer has none. -/
def FastRel (a : Lexer.WRustPort.FastState) (_ : Unit) (l ls : Nat) : Prop :=
  a.line = l ∧ a.lineStart = ls

section

variable {H : Type} {m : Type → Type} {R E : Type} [Monad m] [LawfulMonad m] [Consume H m R E]
  {floor : Option Nat} {low : Nat} {strict : Bool} {Er : St floor low → St floor low → Prop}

omit [Consume H m R E] in
/-- The Rust port loads its locals: the line and the line start of its state. -/
theorem load_sim (l ls : Nat) (Bx : TokenBatch → TokenBatch → Prop) :
    SimR (m := m) (H := H) (ε := Interrupted R E floor) Er
      (SRLx (floor := floor) (low := low) l ls Bx)
      (fun a b s t => FastRel a b l ls ∧ SRLx l ls Bx s t)
      Lexer.WRustPort.FastState.load (pure ()) := by
  unfold Lexer.WRustPort.FastState.load
  refine SimR.of_bind_pure_right (getCore_bind_left fun s t h => ?_)
  rw [pure_bind]
  exact SimR.pure fun s' t' h' => by
    obtain ⟨rfl, rfl⟩ := h'
    exact ⟨⟨h.1.2.1, h.1.2.2⟩, h⟩

omit [Consume H m R E] in
/-- The Rust port stores its locals back, which are the line and line start of its state. -/
theorem store_sim (l ls : Nat) (Bx : TokenBatch → TokenBatch → Prop)
    (a : Lexer.WRustPort.FastState) (hab : FastRel a () l ls) :
    SimR (m := m) (H := H) (ε := Interrupted R E floor) Er
      (SRLx (floor := floor) (low := low) l ls Bx)
      (fun _ _ => SRLx l ls Bx) (a.store) (pure ()) := by
  unfold Lexer.WRustPort.FastState.store Lexer.WRustPort.modifyCore
  refine SimR.modifyGet_left fun s t h => ?_
  obtain ⟨⟨hst, hl, hls⟩, hx⟩ := h
  obtain ⟨hal, hals⟩ := hab
  dsimp only
  exact ⟨⟨{ hst with
    line := (by rw [hal, ← hl]; exact hst.line)
    lineStart := (by rw [hals, ← hls]; exact hst.lineStart) }, hal, hals⟩, hx⟩

theorem pushFast_sim (hcons : ConsumesAlike H m R E) (l ls : Nat) (b b' : TokenBatch)
    (hb : HR b b') (locals : Lexer.WRustPort.FastState) (hloc : FastRel locals () l ls)
    (input : ByteSlice) (offset base : Nat) (ty : TokenCategory)
    (contentStart contentStop start «end» : Nat) (emit : Bool)
    (hty hstart hend hframe hbatch hbatch') :
    LSim strict (H := H) (m := m) (R := R) (E := E) (floor := floor) (low := low) (SRE l ls)
      (PushQ l ls (·.val) (·.val))
      (Lexer.WRustPort.Rust.pushFast input b locals offset base ty contentStart contentStop start
        «end» emit hty hstart hend hframe hbatch)
      (Lexer.X1BatchInCore.pushFast input b' () offset base ty contentStart contentStop start
        «end» emit hty hstart hend hframe hbatch') := by
  obtain ⟨hl, hls⟩ := hloc
  unfold Lexer.WRustPort.Rust.pushFast Lexer.X1BatchInCore.pushFast
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
    have hpush := hb.agree.pushOnLine hb.bytes ty (input.start + contentStart)
      (input.start + contentStop) locals.line locals.lineStart (offset + (start - base))
      (offset + («end» - base)) hbatch.1 (.inl (by omega)) hbatch'.1 (.inl (by omega))
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

end

/-- The operations of the Rust port and of the lexer with the batch in its state simulate each
other, for every consumer that reads the cursors it is handed only below the length of their
batches. -/
theorem opsSim_rust_x1BatchInCore {H : Type} {m : Type → Type} {R E : Type} [Monad m]
    [LawfulMonad m] [Consume H m R E] (hcons : ConsumesAlike H m R E) :
    OpsSim (Lexer.WRustPort.Rust.ops (H := H) (m := m) (R := R) (E := E))
      Lexer.X1BatchInCore.ops FastRel where
  loadLocals l ls Bx := load_sim l ls Bx
  storeLocals l ls Bx a _ hab := store_sim l ls Bx a hab
  pushFast l ls b b' hb a _ ha input offset base ty cs ce start «end» emit hty hstart hend hframe
      hbatch hbatch' :=
    pushFast_sim hcons l ls b b' hb a ha input offset base ty cs ce start «end» emit hty hstart
      hend hframe hbatch hbatch'
  flushHeld l ls batch batch' hb hbytes origin hbatch hbatch' :=
    flushHeld_sim hcons l ls batch batch' hb hbytes origin hbatch hbatch'
  flushBatch l ls := flushBatch_simZ hcons l ls
  sinkStoredAt l ls ty start «end» hend hfloor := handOverStored_simZ hcons l ls ty start «end»
    hend hfloor
  sinkEof l ls location := handOverEof_simZ hcons l ls location
  eofBatch c c' hc hlen := ⟨rfl, by
    show c'.batch.len = 0
    rw [← hc.batch.len]
    exact hlen⟩

end BSmtLib.Proofs.WRustPortX1BatchInCore
