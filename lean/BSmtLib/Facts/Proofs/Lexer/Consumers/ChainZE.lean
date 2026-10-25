module

public import BSmtLib.Facts.Proofs.Lexer.Consumers.ChainZ
public import BSmtLib.Facts.Proofs.Lexer.Consumers.RunE
import all BSmtLib.Lexer
import all BSmtLib.Lexer.Internal.WRustPort

@[expose] public section

/-!
# The library's lexer and `X1BatchInCore`, keeping the error

`runInput_cutE`: the library's lexer fed slices does what `X1BatchInCore` does fed their cut, as
`ChainZ.runInput_cut` says, with the error itself kept (`RunE.runInputE`): the two give the same
results and the same errors, take the same tokens, and are related where they do not fail.
-/

namespace BSmtLib.Facts.Proofs.Lexer.Consumers.ChainZE

open BSmtLib.Facts.Lexer.Adapters BSmtLib.Facts.Proofs.Lexer.Consumers.Alike
open BSmtLib.Facts.Proofs.Lexer.Consumers.ChainZ BSmtLib.Facts.Proofs.Lexer.Consumers.RunE
open BSmtLib.Facts.Proofs.Lexer.X1BatchInCoreLexer
open BSmtLib.Facts.Proofs.Lexer.X1BatchInCoreLexer.Handed
open BSmtLib.Facts.Proofs.Lexer.X1BatchInCoreLexer.Outer
open BSmtLib.Facts.Proofs.Lexer.X1BatchInCoreLexer.Top

section
variable {consumer : BSmtLibSpec.Lexer.Consumer}

/-- `lexChunks` from `p` on the library's lexer, and the calls of `X1BatchInCore` on the chunks
from `p` on, from lexers with related states, the second holding what the first holds after the
result held from the chunks before: the two give the same result, take the same tokens, and have
related states, the second holding then after the first's held result what the chunks gave. -/
theorem chunks_relE (s : BSmtLibSpec.Regex.Chars) (rest : List BSmtLibSpec.Regex.Chars)
    (ended : Bool)
    (p : Nat) :
    ∀ (acc : Option (Span.Located consumer.Result)) (l : Lexer.lexOps.Lexer consumer)
      (x : X1BatchInCore.lexOps.Lexer consumer) (t : List BSmtLibSpec.Lexer.Handed),
      LooseRel l x → x.held = acc.or (BSmtLib.Lexer.Internal.held l) →
      ∀ r (l' : Lexer.lexOps.Lexer consumer) t',
        (BSmtLib.Lexer.Internal.run l (BSmtLib.Lexer.Internal.lexChunks
            (Lexer.Recovery.LexerRecovery.abandon Lexer.Recovery.FailFast)
          (Lexer.Recovery.LexerRecovery.recover Lexer.Recovery.FailFast) s.toByteArray.toByteSlice p
              acc)).run t =
          ((r, l'), t') →
        ∃ x' : X1BatchInCore.lexOps.Lexer consumer, LooseRel l' x' ∧
          match r with
          | .ok h => x'.held = h.or (BSmtLib.Lexer.Internal.held l) ∧
              (runInputE X1BatchInCore.lexOps x ended (Chunks.chunksFrom s p ++ rest)).run t =
                (runInputE X1BatchInCore.lexOps x' ended rest).run t'
          | .error err =>
              (runInputE X1BatchInCore.lexOps x ended (Chunks.chunksFrom s p ++ rest)).run t =
                ((.error err, x'), t') := by
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
    rw [runInputE_cons]
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

/-- A call of the library's lexer on a slice, and the calls of `X1BatchInCore` on its cut, from
related lexers: the two give the same result, take the same tokens and have related states, the
second holding then what the first holds after the call. -/
theorem slice_cutE (s : BSmtLibSpec.Regex.Chars) (rest : List BSmtLibSpec.Regex.Chars)
    (ended : Bool)
    (l : Lexer.lexOps.Lexer consumer) (x : X1BatchInCore.lexOps.Lexer consumer)
    (t : List BSmtLibSpec.Lexer.Handed) (h : LexerRel l x) :
    ∀ r (l' : Lexer.lexOps.Lexer consumer) t',
      (Lexer.lexOps.lexSliceStep l s.toByteArray.toByteSlice).run t = ((r, l'), t') →
      ∃ x' : X1BatchInCore.lexOps.Lexer consumer, LooseRel l' x' ∧
        match r with
        | .ok h => x'.held = h.or (BSmtLib.Lexer.Internal.held l) ∧
            (runInputE X1BatchInCore.lexOps x ended (Chunks.cut s ++ rest)).run t =
              (runInputE X1BatchInCore.lexOps x' ended rest).run t'
        | .error err =>
            (runInputE X1BatchInCore.lexOps x ended (Chunks.cut s ++ rest)).run t =
              ((.error err, x'), t') := by
  intro r l' t' hz
  unfold Chunks.cut
  by_cases hs : s.length < USize.size
  · rw [ite_eq_left_of_eq_true _ _ (eq_true hs)]
    rw [List.singleton_append, runInputE_cons]
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
        (Lexer.Recovery.LexerRecovery.abandon Lexer.Recovery.FailFast)
        (Lexer.Recovery.LexerRecovery.recover Lexer.Recovery.FailFast) s.toByteArray.toByteSlice 0
            none)).run t =
        ((r, l'), t') := by
      rw [← hz]
      show _ = (BSmtLib.Lexer.Internal.run l (BSmtLib.Lexer.Internal.lexSliceStep _ _ _)).run t
      unfold BSmtLib.Lexer.Internal.lexSliceStep
      rw [dite_eq_right_of_eq_false (eq_false hs')]
    exact chunks_relE s rest ended 0 none l x t (LooseRel.of h) h.2.2 r l' t' hz'

/-- The library's lexer fed slices by the adapter's steps, and `X1BatchInCore` fed their cut, from
related lexers: the two stand alike, take the same tokens and have related states, and are
related where they do not fail. -/
theorem runInput_cutE (ended : Bool) : ∀ (slices : List BSmtLibSpec.Regex.Chars)
    (l : Lexer.lexOps.Lexer consumer) (x : X1BatchInCore.lexOps.Lexer consumer)
    (t : List BSmtLibSpec.Lexer.Handed), LexerRel l x →
    ((runInputE Lexer.lexOps l ended slices).run t).1.1 =
        ((runInputE X1BatchInCore.lexOps x ended (Chunks.cutAll slices)).run t).1.1 ∧
      ((runInputE Lexer.lexOps l ended slices).run t).2 =
        ((runInputE X1BatchInCore.lexOps x ended (Chunks.cutAll slices)).run t).2 ∧
      LooseRel ((runInputE Lexer.lexOps l ended slices).run t).1.2
        ((runInputE X1BatchInCore.lexOps x ended (Chunks.cutAll slices)).run t).1.2 ∧
      (((runInputE Lexer.lexOps l ended slices).run t).1.1.isOk = true →
        LexerRel ((runInputE Lexer.lexOps l ended slices).run t).1.2
          ((runInputE X1BatchInCore.lexOps x ended (Chunks.cutAll slices)).run t).1.2)
  | [], l, x, t, h => by
    rw [show Chunks.cutAll [] = [] from rfl]
    cases ended with
    | false =>
      rw [runInputE_nil_false, runInputE_nil_false,
        show X1BatchInCore.lexOps.held x = Lexer.lexOps.held l from h.2.2]
      exact ⟨rfl, rfl, LooseRel.of h, fun _ => h⟩
    | true =>
      rw [runInputE_nil_true, runInputE_nil_true]
      have hc := run_lexEofStep (m := AnswerM) (R := consumer.Result)
        (E := Option consumer.Error) (Lexer.Recovery.LexerRecovery.abandon Lexer.Recovery.FailFast)
        (Lexer.Recovery.LexerRecovery.recover Lexer.Recovery.FailFast) l x h
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
    rw [Chunks.cutAll, List.flatMap_cons, ← Chunks.cutAll, runInputE_cons]
    have hzh : BSmtLib.Lexer.Internal.held ((Lexer.lexOps.lexSliceStep l
        s.toByteArray.toByteSlice).run t).1.2 =
      BSmtLib.Lexer.Internal.held l := rfl
    generalize hz : (Lexer.lexOps.lexSliceStep l s.toByteArray.toByteSlice).run t = A at hzh
    obtain ⟨⟨r, l'⟩, t'⟩ := A
    obtain ⟨x', hL, hx⟩ := slice_cutE s (Chunks.cutAll rest) ended l x t h r l' t' hz
    cases r with
    | error err =>
      rw [hx]
      exact ⟨rfl, rfl, hL, nofun⟩
    | ok d =>
      rw [hx.2]
      exact runInput_cutE ended rest _ x' t'
        ⟨hL.1, hL.2, by rw [hx.1]; show _ = d.or (BSmtLib.Lexer.Internal.held l'); rw [hzh]⟩

end

end BSmtLib.Facts.Proofs.Lexer.Consumers.ChainZE
