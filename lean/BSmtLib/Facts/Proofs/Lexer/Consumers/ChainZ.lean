module

public import BSmtLib.Facts.Proofs.Lexer.X1BatchInCoreLexer
public import BSmtLib.Facts.Proofs.Lexer.Consumers.ChainX1
import all BSmtLib.Lexer
import all BSmtLib.Lexer.Internal.WRustPort

@[expose] public section

/-!
# The library's lexer and `X1BatchInCore` with every consumer of the spec

The steps of the library's lexer and of `X1BatchInCore` on a slice that ends below `USize.size`,
from lexers with related states, give the same results and take the same tokens, also where they
hold different results (`step_fit`). A slice that does not end below `USize.size` the library's
lexer lexes in chunks (`lexChunks`), keeping the results it holds from them aside until the end
of the slice; `X1BatchInCore`, fed the chunks one after another by the adapter, holds each as it
comes (`chunks_rel`). So the library's lexer fed slices by the adapter does what `X1BatchInCore`
does fed their cut (`runInput_cut`): the two take the same tokens and stand alike, and are related
where they do not fail; where they fail, they may hold different results, and the adapter goes on
with a new lexer after a failed input. So the adapter makes of the library's lexer what it makes
of `X1BatchInCore` fed each input cut (`lexing_cut`).
-/

namespace BSmtLib.Facts.Proofs.Lexer.Consumers.ChainZ

open BSmtLib.Facts.Lexer.Adapters BSmtLib.Facts.Proofs.Lexer.Consumers.Alike
open BSmtLib.Facts.Proofs.Lexer.X1BatchInCoreLexer
open BSmtLib.Facts.Proofs.Lexer.X1BatchInCoreLexer.Handed
open BSmtLib.Facts.Proofs.Lexer.X1BatchInCoreLexer.Outer
open BSmtLib.Facts.Proofs.Lexer.X1BatchInCoreLexer.Top
open BSmtLib.Lexer.Recovery (FailFast)

section
variable {consumer : BSmtLibSpec.Lexer.Consumer}

theorem zrun_held {α : Type} (l : Lexer.lexOps.Lexer consumer)
    (f : BSmtLib.Lexer.Internal.InnerM (Answering consumer) AnswerM α) (t : List
        BSmtLibSpec.Lexer.Handed) :
    BSmtLib.Lexer.Internal.held ((BSmtLib.Lexer.Internal.run l f).run t).1.2 =
        BSmtLib.Lexer.Internal.held l := (rfl)

theorem xrun_held {α : Type} (x : X1BatchInCore.lexOps.Lexer consumer)
    (f : Lexer.Internal.WRustPort.InnerM (Answering consumer) AnswerM α)
    (t : List BSmtLibSpec.Lexer.Handed) :
    ((x.run f).run t).1.2.held = x.held := (rfl)

theorem zrun_bind {α β : Type} (l : Lexer.lexOps.Lexer consumer)
    (f : BSmtLib.Lexer.Internal.InnerM (Answering consumer) AnswerM α)
    (k : α → BSmtLib.Lexer.Internal.InnerM (Answering consumer) AnswerM β) :
    BSmtLib.Lexer.Internal.run l (f >>= k) = (BSmtLib.Lexer.Internal.run l f >>= fun p =>
        BSmtLib.Lexer.Internal.run p.2 (k p.1)) := (rfl)

theorem zrun_pure {α : Type} (l : Lexer.lexOps.Lexer consumer) (a : α) :
    BSmtLib.Lexer.Internal.run l (pure a : BSmtLib.Lexer.Internal.InnerM (Answering consumer)
        AnswerM α) =
        pure (a, l) := (rfl)

theorem xrun_withHeld {α : Type} (x : X1BatchInCore.lexOps.Lexer consumer)
    (d : Option (Span.Located consumer.Result))
    (f : Lexer.Internal.WRustPort.InnerM (Answering consumer) AnswerM α)
    (t : List BSmtLibSpec.Lexer.Handed) :
    (x.run f).run t =
      ((((({ x with held := d } : Lexer.Internal.WRustPort.Lexer _ FailFast).run f).run t).1.1,
        { ((({ x with held := d } : Lexer.Internal.WRustPort.Lexer _ FailFast).run f).run
            t).1.2 with
          held := x.held }),
        ((({ x with held := d } : Lexer.Internal.WRustPort.Lexer _ FailFast).run f).run t).2) :=
            (rfl)

/-- The library's lexer and `X1BatchInCore` with the same consumer and related states, whatever
results they hold. -/
def LooseRel (l : Lexer.lexOps.Lexer consumer) (x : X1BatchInCore.lexOps.Lexer consumer) :
    Prop :=
  x.handler = BSmtLib.Lexer.Internal.handler l ∧ Rel (BSmtLib.Lexer.Internal.core l) x.core

theorem LooseRel.of {l : Lexer.lexOps.Lexer consumer} {x : X1BatchInCore.lexOps.Lexer consumer}
    (h : LexerRel l x) : LooseRel l x := ⟨h.1, h.2.1⟩

theorem LexerRel.of {l : Lexer.lexOps.Lexer consumer} {x : X1BatchInCore.lexOps.Lexer consumer}
    (h : LooseRel l x) (hd : x.held = BSmtLib.Lexer.Internal.held l) : LexerRel l x :=
    ⟨h.1, h.2, hd⟩

/-- A call on a slice that ends below `USize.size`, on lexers with related states: the two give
the same result, take the same tokens, keep the results they hold and have related states. -/
theorem step_fit (l : Lexer.lexOps.Lexer consumer) (x : X1BatchInCore.lexOps.Lexer consumer)
    (h : LooseRel l x) (slice : ByteSlice) (hs : slice.stop < USize.size)
    (t : List BSmtLibSpec.Lexer.Handed) :
    ((Lexer.lexOps.lexSliceStep l slice).run t).1.1 =
        ((X1BatchInCore.lexOps.lexSliceStep x slice).run t).1.1 ∧
      LooseRel ((Lexer.lexOps.lexSliceStep l slice).run t).1.2
        ((X1BatchInCore.lexOps.lexSliceStep x slice).run t).1.2 ∧
      ((Lexer.lexOps.lexSliceStep l slice).run t).2 =
        ((X1BatchInCore.lexOps.lexSliceStep x slice).run t).2 := by
  have hc := run_lexSliceStep (m := AnswerM) (R := consumer.Result) (E := Option consumer.Error)
    (Lexer.Recovery.LexRecovery.abandon FailFast)
    (Lexer.Recovery.LexRecovery.recover FailFast) l
    { x with held := BSmtLib.Lexer.Internal.held l } (LexerRel.of h rfl) slice hs
  obtain ⟨⟨e1, e2⟩, e3⟩ := mcouple_answerM hc t
  simp only [X1BatchInCore.lexOps, Lexer.lexOps]
  rw [xrun_withHeld x (BSmtLib.Lexer.Internal.held l)]
  exact ⟨e1, ⟨e2.1, e2.2.1⟩, e3⟩

/-- `lexChunks` from `p`, on the library's lexer, lexes the chunk at `p` as a call on it does and
goes on from the next chunk, with the result held from it, if the call continues. -/
theorem run_lexChunks_lt (l : Lexer.lexOps.Lexer consumer) (s : BSmtLibSpec.Regex.Chars) (p : Nat)
    (hp : p < s.length) (acc : Option (Span.Located consumer.Result)) :
    BSmtLib.Lexer.Internal.run l (BSmtLib.Lexer.Internal.lexChunks
        (Lexer.Recovery.LexRecovery.abandon FailFast)
        (Lexer.Recovery.LexRecovery.recover FailFast) s.toByteArray.toByteSlice p
            acc) =
      (Lexer.lexOps.lexSliceStep l (Chunks.chunkAt s p).toByteArray.toByteSlice >>= fun q =>
        match q.1 with
        | .ok ch => BSmtLib.Lexer.Internal.run q.2
            (BSmtLib.Lexer.Internal.lexChunks (Lexer.Recovery.LexRecovery.abandon
                FailFast)
            (Lexer.Recovery.LexRecovery.recover FailFast) s.toByteArray.toByteSlice
            (p + BSmtLib.Lexer.Internal.CHUNK_SIZE) (ch.or acc))
        | .error err => pure (.error err, q.2)) := by
  have hp' : p < s.toByteArray.toByteSlice.size := by
    rw [Chunks.toByteSlice_size, List.size_toByteArray]; exact hp
  rw [BSmtLib.Lexer.Internal.lexChunks, dite_eq_left_of_eq_true (eq_true hp'), zrun_bind]
  have hfit : ∀ h, BSmtLib.Lexer.Internal.lexSliceFitting (H := Answering consumer) (m := AnswerM)
      (R := consumer.Result) (E := Option consumer.Error)
      (Lexer.Recovery.LexRecovery.abandon FailFast) (Lexer.Recovery.LexRecovery.recover FailFast)
      (s.toByteArray.toByteSlice.byteArray.extract (s.toByteArray.toByteSlice.start + p)
        (min (s.toByteArray.toByteSlice.start + p + BSmtLib.Lexer.Internal.CHUNK_SIZE)
          s.toByteArray.toByteSlice.stop)).toByteSlice h =
      BSmtLib.Lexer.Internal.lexSliceStep (Lexer.Recovery.LexRecovery.abandon FailFast)
          (Lexer.Recovery.LexRecovery.recover FailFast)
        (Chunks.chunkAt s p).toByteArray.toByteSlice := by
    rw [Chunks.chunk_eq s p]
    intro h
    unfold BSmtLib.Lexer.Internal.lexSliceStep
    rw [dite_eq_left_of_eq_true (eq_true h)]
  rw [hfit]
  refine congrArg (_ >>= ·) (funext fun q => ?_)
  obtain ⟨r, l'⟩ := q
  cases r <;> rfl

theorem runInput_cons (ops : LexOps) (lexer : ops.Lexer consumer) (ended : Bool)
    (slice : BSmtLibSpec.Regex.Chars) (slices : List BSmtLibSpec.Regex.Chars)
    (t : List BSmtLibSpec.Lexer.Handed) :
    (ops.runInput lexer ended (slice :: slices)).run t =
      match (ops.lexSliceStep lexer slice.toByteArray.toByteSlice).run t with
      | ((.ok held, lexer), t') =>
        (ops.runInput (ops.withHeld lexer (held.or (ops.held lexer))) ended slices).run t'
      | ((.error error, lexer), t') => ((.failed (failureOf error), lexer), t') := by
  simp only [LexOps.runInput, StateT.run_bind]
  rcases (ops.lexSliceStep lexer slice.toByteArray.toByteSlice).run t with ⟨⟨_ | _, _⟩, _⟩ <;> rfl

theorem run_lexChunks_ge (l : Lexer.lexOps.Lexer consumer) (s : BSmtLibSpec.Regex.Chars) (p : Nat)
    (hp : ¬ p < s.length) (acc : Option (Span.Located consumer.Result)) :
    BSmtLib.Lexer.Internal.run l (BSmtLib.Lexer.Internal.lexChunks
        (Lexer.Recovery.LexRecovery.abandon FailFast)
        (Lexer.Recovery.LexRecovery.recover FailFast) s.toByteArray.toByteSlice p
            acc) =
      pure (.ok acc, l) := by
  have hp' : ¬ p < s.toByteArray.toByteSlice.size := by
    rw [Chunks.toByteSlice_size, List.size_toByteArray]; exact hp
  rw [BSmtLib.Lexer.Internal.lexChunks, dite_eq_right_of_eq_false (eq_false hp')]
  rfl

/-- `lexChunks` from `p` on the library's lexer, and the calls of `X1BatchInCore` on the chunks
from `p` on, from lexers with related states, the second holding what the first holds after the
result held from the chunks before: the two give the same result, take the same tokens, and have
related states, the second holding then after the first's held result what the chunks gave. -/
theorem chunks_rel (s : BSmtLibSpec.Regex.Chars) (rest : List BSmtLibSpec.Regex.Chars)
    (ended : Bool)
    (p : Nat) :
    ∀ (acc : Option (Span.Located consumer.Result)) (l : Lexer.lexOps.Lexer consumer)
      (x : X1BatchInCore.lexOps.Lexer consumer) (t : List BSmtLibSpec.Lexer.Handed),
      LooseRel l x → x.held = acc.or (BSmtLib.Lexer.Internal.held l) →
      ∀ r (l' : Lexer.lexOps.Lexer consumer) t',
        (BSmtLib.Lexer.Internal.run l (BSmtLib.Lexer.Internal.lexChunks
            (Lexer.Recovery.LexRecovery.abandon FailFast)
          (Lexer.Recovery.LexRecovery.recover FailFast) s.toByteArray.toByteSlice p
              acc)).run t =
          ((r, l'), t') →
        ∃ x' : X1BatchInCore.lexOps.Lexer consumer, LooseRel l' x' ∧
          match r with
          | .ok h => x'.held = h.or (BSmtLib.Lexer.Internal.held l) ∧
              (X1BatchInCore.lexOps.runInput x ended (Chunks.chunksFrom s p ++ rest)).run t =
                (X1BatchInCore.lexOps.runInput x' ended rest).run t'
          | .error err =>
              (X1BatchInCore.lexOps.runInput x ended (Chunks.chunksFrom s p ++ rest)).run t =
                ((.failed (failureOf err), x'), t') := by
  fun_induction Chunks.chunksFrom s p with
  | case1 p hp ih =>
    intro acc l x t hL hd r l' t' hz
    rw [run_lexChunks_lt l s p hp acc, StateT.run_bind] at hz
    obtain ⟨e1, e2, e3⟩ := step_fit l x hL _ (Chunks.chunk_stop_lt s p) t
    have hzh : BSmtLib.Lexer.Internal.held ((Lexer.lexOps.lexSliceStep l
        (Chunks.chunkAt s p).toByteArray.toByteSlice).run t).1.2 = BSmtLib.Lexer.Internal.held l :=
            rfl
    have hxh : ((X1BatchInCore.lexOps.lexSliceStep x
        (Chunks.chunkAt s p).toByteArray.toByteSlice).run t).1.2.held = x.held := rfl
    rw [List.cons_append]
    rw [runInput_cons]
    generalize (Lexer.lexOps.lexSliceStep l (Chunks.chunkAt s p).toByteArray.toByteSlice).run t
      = A at e1 e2 e3 hz hzh
    generalize (X1BatchInCore.lexOps.lexSliceStep x
      (Chunks.chunkAt s p).toByteArray.toByteSlice).run t = B at e1 e2 e3 hxh ⊢
    obtain ⟨⟨ra, la⟩, ta⟩ := A
    obtain ⟨⟨rb, xb⟩, tb⟩ := B
    simp only at e1 e2 e3 hz hzh hxh
    subst e1 e3
    cases ra with
    | error err =>
      change ((Except.error err, la), ta) = ((r, l'), t') at hz
      obtain ⟨h12, h3⟩ := Prod.mk.inj hz
      obtain ⟨h1, h2⟩ := Prod.mk.inj h12
      subst h1 h2 h3
      exact ⟨xb, e2, rfl⟩
    | ok ch =>
      obtain ⟨x', h1, h2⟩ := ih (ch.or acc) la
        (X1BatchInCore.lexOps.withHeld xb (ch.or (X1BatchInCore.lexOps.held xb))) ta e2
        (by
          show ch.or xb.held = (ch.or acc).or (BSmtLib.Lexer.Internal.held la)
          rw [hxh, hd, hzh, Option.or_assoc])
        r l' t' hz
      refine ⟨x', h1, ?_⟩
      cases r with
      | ok h => exact ⟨h2.1.trans (by rw [hzh]), h2.2⟩
      | error err => exact h2
  | case2 p hp =>
    intro acc l x t hL hd r l' t' hz
    rw [run_lexChunks_ge l s p hp acc] at hz
    change ((Except.ok acc, l), t) = ((r, l'), t') at hz
    simp only [Prod.mk.injEq] at hz
    obtain ⟨⟨rfl, rfl⟩, rfl⟩ := hz
    refine ⟨x, hL, hd, ?_⟩
    rw [List.nil_append]

theorem runInput_nil_true (ops : LexOps) (lexer : ops.Lexer consumer)
    (t : List BSmtLibSpec.Lexer.Handed) :
    (ops.runInput lexer true []).run t =
      match (ops.lexEofStep lexer).run t with
      | ((.ok flow, lexer), t') =>
        match eofResult (ops.held lexer) flow with
        | some result =>
          ((.finished result.value (toLocation result.location), ops.withHeld lexer none), t')
        | none => ((.running, ops.withHeld lexer none), t')
      | ((.error error, lexer), t') => ((.failed (failureOf error), lexer), t') := by
  simp only [LexOps.runInput, ite_true, StateT.run_bind]
  rcases (ops.lexEofStep lexer).run t with ⟨⟨_ | flow, l⟩, t'⟩
  · rfl
  · show (match eofResult (ops.held l) flow with
        | some result => (pure (BSmtLibSpec.Lexer.Outcome.finished result.value
            (toLocation result.location), ops.withHeld l none) : AnswerM _)
        | none => pure (.running, ops.withHeld l none)).run t' = _
    dsimp only
    cases eofResult (ops.held l) flow <;> rfl

/-- A call of the library's lexer on a slice, and the calls of `X1BatchInCore` on its cut, from
related lexers: the two give the same result, take the same tokens and have related states, the
second holding then what the first holds after the call. -/
theorem slice_cut (s : BSmtLibSpec.Regex.Chars) (rest : List BSmtLibSpec.Regex.Chars) (ended : Bool)
    (l : Lexer.lexOps.Lexer consumer) (x : X1BatchInCore.lexOps.Lexer consumer)
    (t : List BSmtLibSpec.Lexer.Handed) (h : LexerRel l x) :
    ∀ r (l' : Lexer.lexOps.Lexer consumer) t',
      (Lexer.lexOps.lexSliceStep l s.toByteArray.toByteSlice).run t = ((r, l'), t') →
      ∃ x' : X1BatchInCore.lexOps.Lexer consumer, LooseRel l' x' ∧
        match r with
        | .ok h => x'.held = h.or (BSmtLib.Lexer.Internal.held l) ∧
            (X1BatchInCore.lexOps.runInput x ended (Chunks.cut s ++ rest)).run t =
              (X1BatchInCore.lexOps.runInput x' ended rest).run t'
        | .error err =>
            (X1BatchInCore.lexOps.runInput x ended (Chunks.cut s ++ rest)).run t =
              ((.failed (failureOf err), x'), t') := by
  intro r l' t' hz
  unfold Chunks.cut
  by_cases hs : s.length < USize.size
  · rw [ite_eq_left_of_eq_true _ _ (eq_true hs)]
    rw [List.singleton_append, runInput_cons]
    obtain ⟨e1, e2, e3⟩ := step_fit l x (LooseRel.of h) _ (stop_toByteSlice_lt hs) t
    have hxh : ((X1BatchInCore.lexOps.lexSliceStep x
        s.toByteArray.toByteSlice).run t).1.2.held = x.held := rfl
    generalize (X1BatchInCore.lexOps.lexSliceStep x s.toByteArray.toByteSlice).run t = B
      at e1 e2 e3 hxh ⊢
    rw [hz] at e1 e2 e3
    obtain ⟨⟨rb, xb⟩, tb⟩ := B
    simp only at e1 e2 e3 hxh
    subst e1 e3
    cases r with
    | error err => exact ⟨xb, e2, rfl⟩
    | ok d =>
      refine ⟨X1BatchInCore.lexOps.withHeld xb (d.or (X1BatchInCore.lexOps.held xb)), e2, ?_, rfl⟩
      show d.or xb.held = d.or (BSmtLib.Lexer.Internal.held l)
      rw [hxh, h.2.2]
  · rw [ite_eq_right_of_eq_false _ _ (eq_false hs)]
    have hs' : ¬ s.toByteArray.toByteSlice.stop < USize.size := by
      rw [Chunks.stop_toByteSlice, List.size_toByteArray]; exact hs
    have hz' : (BSmtLib.Lexer.Internal.run l (BSmtLib.Lexer.Internal.lexChunks
        (Lexer.Recovery.LexRecovery.abandon FailFast)
        (Lexer.Recovery.LexRecovery.recover FailFast) s.toByteArray.toByteSlice 0
            none)).run t =
        ((r, l'), t') := by
      rw [← hz]
      show _ = (BSmtLib.Lexer.Internal.run l (BSmtLib.Lexer.Internal.lexSliceStep _ _ _)).run t
      unfold BSmtLib.Lexer.Internal.lexSliceStep
      rw [dite_eq_right_of_eq_false (eq_false hs')]
    exact chunks_rel s rest ended 0 none l x t (LooseRel.of h) h.2.2 r l' t' hz'

/-- The library's lexer fed slices by the adapter's steps, and `X1BatchInCore` fed their cut, from
related lexers: the two stand alike, take the same tokens and have related states, and are
related where they do not fail. -/
theorem runInput_cut (ended : Bool) : ∀ (slices : List BSmtLibSpec.Regex.Chars)
    (l : Lexer.lexOps.Lexer consumer) (x : X1BatchInCore.lexOps.Lexer consumer)
    (t : List BSmtLibSpec.Lexer.Handed), LexerRel l x →
    ((Lexer.lexOps.runInput l ended slices).run t).1.1 =
        ((X1BatchInCore.lexOps.runInput x ended (Chunks.cutAll slices)).run t).1.1 ∧
      ((Lexer.lexOps.runInput l ended slices).run t).2 =
        ((X1BatchInCore.lexOps.runInput x ended (Chunks.cutAll slices)).run t).2 ∧
      LooseRel ((Lexer.lexOps.runInput l ended slices).run t).1.2
        ((X1BatchInCore.lexOps.runInput x ended (Chunks.cutAll slices)).run t).1.2 ∧
      (((Lexer.lexOps.runInput l ended slices).run t).1.1.isFailed = false →
        LexerRel ((Lexer.lexOps.runInput l ended slices).run t).1.2
          ((X1BatchInCore.lexOps.runInput x ended (Chunks.cutAll slices)).run t).1.2)
  | [], l, x, t, h => by
    rw [show Chunks.cutAll [] = [] from rfl]
    cases ended with
    | false =>
      have hs : Lexer.lexOps.standing l = X1BatchInCore.lexOps.standing x := by
        unfold LexOps.standing
        rw [show X1BatchInCore.lexOps.held x = Lexer.lexOps.held l from h.2.2]
      exact ⟨hs, rfl, LooseRel.of h, fun _ => h⟩
    | true =>
      rw [runInput_nil_true, runInput_nil_true]
      have hc := run_lexEofStep (m := AnswerM) (R := consumer.Result)
        (E := Option consumer.Error) (Lexer.Recovery.LexRecovery.abandon FailFast)
        (Lexer.Recovery.LexRecovery.recover FailFast) l x h
      obtain ⟨⟨e1, e2⟩, e3⟩ := mcouple_answerM hc t
      change ((Lexer.lexOps.lexEofStep l).run t).1.1 =
        ((X1BatchInCore.lexOps.lexEofStep x).run t).1.1 at e1
      change LexerRel ((Lexer.lexOps.lexEofStep l).run t).1.2
        ((X1BatchInCore.lexOps.lexEofStep x).run t).1.2 at e2
      change ((Lexer.lexOps.lexEofStep l).run t).2 =
        ((X1BatchInCore.lexOps.lexEofStep x).run t).2 at e3
      generalize (Lexer.lexOps.lexEofStep l).run t = A at e1 e2 e3 ⊢
      generalize (X1BatchInCore.lexOps.lexEofStep x).run t = B at e1 e2 e3 ⊢
      obtain ⟨⟨ra, la⟩, ta⟩ := A
      obtain ⟨⟨rb, xb⟩, tb⟩ := B
      simp only at e1 e2 e3
      subst e1 e3
      cases ra with
      | error err => exact ⟨rfl, rfl, LooseRel.of e2, nofun⟩
      | ok flow =>
        dsimp only
        rw [show X1BatchInCore.lexOps.held xb = Lexer.lexOps.held la from e2.2.2]
        have hw : LexerRel (Lexer.lexOps.withHeld la none)
            (X1BatchInCore.lexOps.withHeld xb none) :=
          ⟨e2.1, e2.2.1, rfl⟩
        cases eofResult (Lexer.lexOps.held la) flow with
        | some res => exact ⟨rfl, rfl, LooseRel.of hw, fun _ => hw⟩
        | none => exact ⟨rfl, rfl, LooseRel.of hw, fun _ => hw⟩
  | s :: rest, l, x, t, h => by
    rw [Chunks.cutAll, List.flatMap_cons, ← Chunks.cutAll, runInput_cons]
    have hzh : BSmtLib.Lexer.Internal.held ((Lexer.lexOps.lexSliceStep l
        s.toByteArray.toByteSlice).run t).1.2 =
      BSmtLib.Lexer.Internal.held l := rfl
    generalize hz : (Lexer.lexOps.lexSliceStep l s.toByteArray.toByteSlice).run t = A at hzh
    obtain ⟨⟨r, l'⟩, t'⟩ := A
    obtain ⟨x', hL, hx⟩ := slice_cut s (Chunks.cutAll rest) ended l x t h r l' t' hz
    cases r with
    | error err =>
      rw [hx]
      exact ⟨rfl, rfl, hL, nofun⟩
    | ok d =>
      rw [hx.2]
      exact runInput_cut ended rest _ x' t'
        ⟨hL.1, hL.2, by rw [hx.1]; show _ = d.or (BSmtLib.Lexer.Internal.held l'); rw [hzh]⟩

theorem LooseRel.version {l : Lexer.lexOps.Lexer consumer}
    {x : X1BatchInCore.lexOps.Lexer consumer} (h : LooseRel l x) :
    Lexer.lexOps.version l = X1BatchInCore.lexOps.version x :=
  (congrArg (·.version) h.2).symm

theorem LooseRel.discardedFrom {l : Lexer.lexOps.Lexer consumer}
    {x : X1BatchInCore.lexOps.Lexer consumer} (h : LooseRel l x) :
    Lexer.lexOps.discardedFrom l = X1BatchInCore.lexOps.discardedFrom x :=
  (congrArg (·.discardedFrom) h.2).symm

end

/-- The library's lexer does with every consumer of the spec what `X1BatchInCore` does fed each
input cut: every slice too large for the positions of the library's lexer cut into chunks that
are not. -/
theorem lexing_cut (consumer : BSmtLibSpec.Lexer.Consumer) (version : BSmtLibSpec.Lexicon.Version)
    (earlier : List (List BSmtLibSpec.Regex.Chars)) (slices : List BSmtLibSpec.Regex.Chars)
    (ended : Bool) :
    lexing Lexer.lexOps consumer version earlier slices ended =
      lexing X1BatchInCore.lexOps consumer version (earlier.map Chunks.cutAll)
        (Chunks.cutAll slices) ended := by
  rw [lexing_def, lexing_def]
  have hL := foldl_next_rel Lexer.lexOps X1BatchInCore.lexOps (consumer := consumer) LexerRel
    (toVersion version)
    Chunks.cutAll (lexerRel_new _ _)
    (fun input a b h => ⟨(runInput_cut true input a b [] h).1,
      (runInput_cut true input a b [] h).2.2.2⟩)
    earlier (Lexer.lexOps.new consumer {} (toVersion version))
    (X1BatchInCore.lexOps.new consumer {} (toVersion version)) (lexerRel_new _ _)
  obtain ⟨e1, e2, e3, -⟩ := runInput_cut ended slices _ _ [] hL
  simp only
  rw [e1, e2, e3.version, e3.discardedFrom]

end BSmtLib.Facts.Proofs.Lexer.Consumers.ChainZ
