module

public import BSmtLib.Facts.Proofs.Lexer.VNaiveWRustPort.Cursor
import all BSmtLib.Token
import all BSmtLib.Version
import all BSmtLib.Lexer.Cursor

@[expose] public section

/-!
# The adapter's consumer on a cursor over a batch that holds lexemes

One call of the adapter's consumer `Answering C` on a cursor takes the tokens from the next one
on, up to the index `k` of the cursor it gives back, and does with them what `pending` does with
their lexemes, with no result held (`consume_spec`): it goes on (where it ran out of tokens, or
switched to a version with the same lexical rules), waits after a break, or stops, and the
cursor and the answer it gives back say which.
-/

open BSmtLib.Lexer.Cursor (LexerCursor)

namespace BSmtLib.Facts.Proofs.Lexer.VNaiveWRustPort.Consume

open BSmtLib.Facts.Lexer.Adapters BSmtLib.Facts.Proofs.Lexer.Simulation.Batch
open BSmtLib.Lexer.Cursor.LexerCursor.Internal (discardRequested relexRequested)
open BSmtLibSpec.Lexer (Handed)
open BSmtLib.Facts.Proofs.Lexer.VNaive.Run BSmtLib.Facts.Proofs.Lexer.VNaiveWRustPort.Batch
open BSmtLib.Facts.Proofs.Lexer.VNaiveWRustPort.Bytes
open BSmtLib.Facts.Proofs.Lexer.VNaiveWRustPort.Cursor
open BSmtLib.Facts.Proofs.Lexer.VNaiveWRustPort.Model BSmtLib.Lexer.Internal.VNaive

variable {g : Token.BatchTag} (C : BSmtLibSpec.Lexer.Consumer)

/-- What one call of the consumer on the cursor `c` gives, with the lexemes `xs` it took: the
answer, the cursor after it, and the tokens taken, as `pending` says from `p`. -/
def ConsumeSpec (c : LexerCursor g) (p : Prog) (xs : List Lexeme)
    (answer : Except (Option C.Error) (ControlFlow C.Result)) (c' : LexerCursor g)
    (taken : List Handed) : Prop :=
  match pending C false p.ver p.taken xs with
  | .cont p' =>
    answer = .ok .continue ∧ taken = p'.taken ∧ c'.version = p'.ver ∧ cStop c' = cStop c ∧
      (relexRequested c') = relexRequested c ∧ discardRequested c' = discardRequested c
  | .wait r l p' =>
    xs.getLast? = some l ∧
    answer = .ok (.break r) ∧ taken = p'.taken ∧ c'.version = p'.ver ∧ cStop c' = cStop c ∧
      (relexRequested c') = relexRequested c ∧ discardRequested c' = discardRequested c
  | .stop s p' =>
    xs.getLast? = some s.lex ∧ taken = p'.taken ∧ c'.version = p'.ver ∧
      match s with
      | .fail e d _ => answer = .error (some e) ∧ discardRequested c' = (d || (discardRequested c))
      | .layout _ => answer = .error none ∧ discardRequested c' = discardRequested c
      | .brkX r _ =>
        answer = .ok (.break r) ∧ relexRequested c' = true ∧ cStop c' = cNext c' ∧
          (discardRequested c') = discardRequested c
      | .discard r _ =>
        answer = .ok (match r with | some r => .break r | none => .continue) ∧
          (discardRequested c') = true
      | .relex _ =>
        answer = .ok .continue ∧ relexRequested c' = true ∧
          (discardRequested c') = discardRequested c
      | _ => False

theorem requests_eq (taken : List Handed) (c : LexerCursor g) :
    (Answering.requests C taken c).val =
      if C.discards taken then (Answering.switched C taken c).val.discardRest
      else (Answering.switched C taken c).val := by
  unfold Answering.requests
  dsimp only
  split <;> simp_all

theorem runS_bind {σ α β : Type} (x : StateT σ Id α) (f : α → StateT σ Id β) (s : σ) :
    (x >>= f).run s = (f (x.run s).1).run (x.run s).2 := rfl

theorem runS_pure {σ α : Type} (a : α) (s : σ) : (pure a : StateT σ Id α).run s = (a, s) := rfl

theorem id_pure_eq {α : Type} (a : α) : (pure a : Id α) = a := rfl

theorem getLast?_cons_of_ne {α : Type} {a : α} {xs : List α} (h : xs ≠ []) :
    (a :: xs).getLast? = xs.getLast? := by
  cases xs with
  | nil => exact absurd rfl h
  | cons b xs => rfl

theorem take_drop_cons {α : Type} (ls : List α) {i k : Nat} (hi : i < k) (hk : k ≤ ls.length) :
    (ls.take k).drop i = ls[i]'(by omega) :: (ls.take k).drop (i + 1) := by
  have h1 : i < (ls.take k).length := by simp; omega
  rw [List.drop_eq_getElem_cons h1, List.getElem_take]

theorem take_drop_single {α : Type} (ls : List α) {i : Nat} (hi : i < ls.length) :
    (ls.take (i + 1)).drop i = [ls[i]] := by
  rw [take_drop_cons ls (Nat.lt_succ_self i) hi]
  simp

/-- One call of the consumer on a cursor over a batch that holds the lexemes takes at least one
token, and does what `pending` says with the lexemes it took. -/
theorem consume_spec : ∀ (n : Nat) (c : LexerCursor g) (h : c.HasNext) (ls : List Lexeme),
    cStop c - cNext c = n → Holds (BSmtLib.Lexer.Internal.intoBatch c) ls → cStop c ≤ ls.length →
    ∀ (p : Prog), p.ver = c.version →
      cNext c < cNext ((Answering.consume C c h).run p.taken).1.2.val ∧
      cNext ((Answering.consume C c h).run p.taken).1.2.val ≤ cStop c ∧
      ConsumeSpec C c p
        ((ls.take (cNext ((Answering.consume C c h).run p.taken).1.2.val)).drop (cNext c))
        ((Answering.consume C c h).run p.taken).1.1
        ((Answering.consume C c h).run p.taken).1.2.val
        ((Answering.consume C c h).run p.taken).2 := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
  intro c h ls hn hb hs p hv
  have hlt := (Simulation.Batch.hasNext_iff c).mp h
  have hj : cNext c < ls.length := by omega
  have ht := entry_at C c h hb hj
  have hn1 := cNext_next c h
  have hs1 := cStop_next c h
  have hv1 := version_next c h
  have hr1 := relex_next c h
  have hd1 := discard_next c h
  have hb1 : Holds (BSmtLib.Lexer.Internal.intoBatch (c.next h).2.1) ls
      := by rw [intoBatch_next]; exact hb
  rw [Answering.consume]
  generalize hq : c.next h = q at ht hn1 hs1 hv1 hr1 hd1 hb1
  obtain ⟨token, next, consumed⟩ := q
  dsimp only at ht hn1 hs1 hv1 hr1 hd1 hb1 ⊢
  rw [ht]
  have hl1 : (ls.take (cNext c + 1)).drop (cNext c) = [ls[cNext c]] := take_drop_single ls hj
  cases hx : lexemeEntry C.concrete c.version ls[cNext c] with
  | none =>
    have hp1 : hand1 C false (.cont p) ls[cNext c] = .stop (.layout ls[cNext c]) p := by
      simp only [hand1, Bool.false_eq_true, ite_false, hv, hx]
    dsimp only
    have hle := cNext_le_cStop next
    rw [runS_pure]
    dsimp only
    refine ⟨by omega, by omega, ?_⟩
    rw [hn1, hl1]
    unfold ConsumeSpec
    rw [pending, handAll_cons, hp1]
    exact ⟨rfl, rfl, hv1.trans hv.symm, rfl, hd1⟩
  | some x =>
    obtain ⟨taken0, ver0⟩ := p
    simp only at hv
    subst hv
    have hle := cNext_le_cStop next
    have hsw := switched_eq C (taken0 ++ [x]) next
    rw [hv1] at hsw
    simp only [runS_bind, StateT.run_get, StateT.run_set, id_pure_eq]
    cases ha : C.answer (taken0 ++ [x]) with
    | fail e =>
      obtain ⟨w1, w2, w3, w4, w5⟩ := hsw
      dsimp only
      rw [runS_pure]
      dsimp only
      rw [requests_eq]
      have hp1 : hand1 C false (.cont ⟨taken0, c.version⟩) ls[cNext c] =
          .stop (.fail e (C.discards (taken0 ++ [x])) ls[cNext c])
            ⟨taken0 ++ [x], switchedTo c.version (C.switchTo (taken0 ++ [x]))⟩ := by
        simp [hand1, hx, ha]
      cases hdis : C.discards (taken0 ++ [x]) with
      | true =>
        rw [hdis] at hp1
        simp only [ite_true]
        rw [cNext_discardRest, w2]
        refine ⟨by omega, by omega, ?_⟩
        rw [hn1, hl1]
        unfold ConsumeSpec
        rw [pending, handAll_cons, hp1, handAll_nil]
        exact ⟨rfl, rfl, by rw [version_discardRest, w1], rfl,
          by rw [discard_discardRest]; rfl⟩
      | false =>
        rw [hdis] at hp1
        simp only [Bool.false_eq_true, ite_false]
        rw [w2]
        refine ⟨by omega, by omega, ?_⟩
        rw [hn1, hl1]
        unfold ConsumeSpec
        rw [pending, handAll_cons, hp1, handAll_nil]
        exact ⟨rfl, rfl, w1, rfl, by rw [w3, hd1]; rfl⟩
    | «break» r =>
      obtain ⟨w1, w2, w3, w4, w5⟩ := hsw
      dsimp only
      rw [runS_pure]
      dsimp only
      rw [requests_eq]
      cases hdis : C.discards (taken0 ++ [x]) with
      | true =>
        have hp1 : hand1 C false (.cont ⟨taken0, c.version⟩) ls[cNext c] =
            .stop (.discard (some r) ls[cNext c])
              ⟨taken0 ++ [x], switchedTo c.version (C.switchTo (taken0 ++ [x]))⟩ := by
          simp [hand1, hx, ha, hdis]
        simp only [ite_true]
        rw [cNext_discardRest, w2]
        refine ⟨by omega, by omega, ?_⟩
        rw [hn1, hl1]
        unfold ConsumeSpec
        rw [pending, handAll_cons, hp1, handAll_nil]
        exact ⟨rfl, rfl, by rw [version_discardRest, w1], rfl, discard_discardRest _⟩
      | false =>
        simp only [Bool.false_eq_true, ite_false]
        rw [w2]
        refine ⟨by omega, by omega, ?_⟩
        rw [hn1, hl1]
        unfold ConsumeSpec
        rw [pending, handAll_cons, handAll_nil]
        cases hcr : crosses c.version (switchedTo c.version (C.switchTo (taken0 ++ [x]))) with
        | true =>
          have hp1 : hand1 C false (.cont ⟨taken0, c.version⟩) ls[cNext c] =
              .stop (.brkX r ls[cNext c])
                ⟨taken0 ++ [x], switchedTo c.version (C.switchTo (taken0 ++ [x]))⟩ := by
            simp [hand1, hx, ha, hdis, hcr]
          rw [hp1]
          obtain ⟨v1, v2⟩ := w4 hcr
          exact ⟨rfl, rfl, w1, rfl, v1, by rw [v2, w2], w3.trans hd1⟩
        | false =>
          have hp1 : hand1 C false (.cont ⟨taken0, c.version⟩) ls[cNext c] =
              .wait r ls[cNext c]
                ⟨taken0 ++ [x], switchedTo c.version (C.switchTo (taken0 ++ [x]))⟩ := by
            simp [hand1, hx, ha, hdis, hcr]
          rw [hp1]
          obtain ⟨v1, v2⟩ := w5 hcr
          exact ⟨rfl, rfl, rfl, w1, v2.trans hs1, v1.trans hr1, w3.trans hd1⟩
    | «continue» =>
      obtain ⟨w1, w2, w3, w4, w5⟩ := hsw
      dsimp only
      by_cases hdis : C.discards (taken0 ++ [x]) = true
      · have hp1 : hand1 C false (.cont ⟨taken0, c.version⟩) ls[cNext c] =
            .stop (.discard none ls[cNext c])
              ⟨taken0 ++ [x], switchedTo c.version (C.switchTo (taken0 ++ [x]))⟩ := by
          simp [hand1, hx, ha, hdis]
        simp only [hdis, Bool.or_true, ite_true]
        rw [runS_pure]
        dsimp only
        rw [requests_eq]
        simp only [hdis, ite_true]
        rw [cNext_discardRest, w2]
        refine ⟨by omega, by omega, ?_⟩
        rw [hn1, hl1]
        unfold ConsumeSpec
        rw [pending, handAll_cons, hp1, handAll_nil]
        exact ⟨rfl, rfl, by rw [version_discardRest, w1], rfl, discard_discardRest _⟩
      · have hdis' : C.discards (taken0 ++ [x]) = false := by simpa using hdis
        rcases Option.eq_none_or_eq_some (C.switchTo (taken0 ++ [x])) with hsto | ⟨v, hsto⟩
        · have hp1 : hand1 C false (.cont ⟨taken0, c.version⟩) ls[cNext c] =
              .cont ⟨taken0 ++ [x], c.version⟩ := by
            simp [hand1, hx, ha, hdis', hsto, switchedTo, crosses]
          simp only [hsto, hdis', Option.isSome_none, Bool.or_false, Bool.false_eq_true, ite_false]
          split
          · rename_i h'
            have hlt' := (Simulation.Batch.hasNext_iff next).mp h'
            have hrec := ih (cStop next - cNext next) (by omega) next h' ls rfl hb1 (by omega)
              ⟨taken0 ++ [x], c.version⟩ hv1.symm
            rw [runS_bind]
            generalize (Answering.consume C next h').run (taken0 ++ [x]) = R at hrec ⊢
            obtain ⟨⟨answer, last, consumed'⟩, taken'⟩ := R
            rw [runS_pure]
            dsimp only at hrec ⊢
            obtain ⟨k1, k2, k3⟩ := hrec
            refine ⟨by omega, by omega, ?_⟩
            rw [take_drop_cons ls (show cNext c < cNext last by omega) (by omega)]
            unfold ConsumeSpec at k3 ⊢
            rw [pending, handAll_cons, hp1, ← pending, show cNext c + 1 = cNext next by omega]
            rw [hs1, hr1, hd1] at k3
            rw [getLast?_cons_of_ne (by
              apply List.ne_nil_of_length_pos; simp only [List.length_drop,
                  List.length_take]; omega)]
            exact k3
          · rename_i h'
            rw [runS_pure]
            dsimp only
            refine ⟨by omega, by omega, ?_⟩
            rw [hn1, hl1]
            unfold ConsumeSpec
            rw [pending, handAll_cons, hp1, handAll_nil]
            exact ⟨rfl, rfl, hv1, by omega, hr1, hd1⟩
        · simp only [hsto, Option.isSome_some, Bool.true_or, ite_true]
          rw [runS_pure]
          dsimp only
          rw [requests_eq]
          simp only [hdis', Bool.false_eq_true, ite_false]
          rw [w2]
          refine ⟨by omega, by omega, ?_⟩
          rw [hn1, hl1]
          unfold ConsumeSpec
          rw [pending, handAll_cons, handAll_nil]
          rw [hsto] at w1 w4 w5
          cases hcr : crosses c.version (switchedTo c.version (some v)) with
          | true =>
            have hp1 : hand1 C false (.cont ⟨taken0, c.version⟩) ls[cNext c] =
                .stop (.relex ls[cNext c]) ⟨taken0 ++ [x], switchedTo c.version (some v)⟩ := by
              simp [hand1, hx, ha, hdis', hsto, hcr]
            rw [hp1]
            obtain ⟨v1, -⟩ := w4 hcr
            exact ⟨rfl, rfl, w1, rfl, v1, w3.trans hd1⟩
          | false =>
            have hp1 : hand1 C false (.cont ⟨taken0, c.version⟩) ls[cNext c] =
                .cont ⟨taken0 ++ [x], switchedTo c.version (some v)⟩ := by
              simp [hand1, hx, ha, hdis', hsto, hcr]
            rw [hp1]
            obtain ⟨v1, v2⟩ := w5 hcr
            exact ⟨rfl, rfl, w1, v2.trans hs1, v1.trans hr1, w3.trans hd1⟩

end BSmtLib.Facts.Proofs.Lexer.VNaiveWRustPort.Consume
