import BSmtLib.Proofs.WRustPortX1BatchInCore
import BSmtLib.Proofs.Consumers.Alike

/-!
# The Rust port and `X1BatchInCore` with every consumer of the spec

The adapter's consumer for a consumer of the spec (`Adapter.Answering`) reads the cursors only
below the length of their batches (`answering_consumesAlike`), so the simulation of the Rust port
by the lexer with the batch kept in its state holds with it: the steps of the two on a slice and
at the end of the input give the same results and take the same tokens, from lexers that
correspond and with lexers that correspond again, and so the adapter makes the same of the two
(`lexing_wRustPort_x1BatchInCore`).
-/

namespace BSmtLib.Proofs.Simulation

open BSmtLib.Proofs.Adapter BSmtLib.Proofs.WRustPortX1BatchInCore
open BSmtLib.Lexer.Internal (intoBatch)

variable {g g' : BatchTag}

/-- A token below the length of the batches is recorded alike. -/
theorem toHanded_eq {c : BatchCursor g} {d : BatchCursor g'} (h : CursorAgree c d)
    {t : Token g} {t' : Token g'} (et : tokenIndex t = tokenIndex t')
    (ht : tokenIndex t < (intoBatch c).len) : toHanded c t = toHanded d t' := by
  unfold toHanded BatchCursor.syntax SyntaxToken.fromToken SyntaxToken.fromParts
  rw [h.category et ht, h.span et ht, h.content et ht, h.version]

/-- A piece of layout below the length of the batches is recorded alike. -/
theorem toLayout_eq {c : BatchCursor g} {d : BatchCursor g'} (h : CursorAgree c d)
    {t : Token g} {t' : Token g'} (et : tokenIndex t = tokenIndex t')
    (ht : tokenIndex t < (intoBatch c).len) : toLayout c t = toLayout d t' := by
  unfold toLayout
  rw [h.category et ht, h.span et ht, h.content et ht]

/-- An entry below the length of the batches is taken alike. -/
theorem entry_eq (consumer : Spec.Lexer.Consumer) {c : BatchCursor g} {d : BatchCursor g'}
    (h : CursorAgree c d) {t : Token g} {t' : Token g'} (et : tokenIndex t = tokenIndex t')
    (ht : tokenIndex t < (intoBatch c).len) :
    Answering.entry consumer c t = Answering.entry consumer d t' := by
  unfold Answering.entry
  rw [toHanded_eq h et ht, toLayout_eq h et ht]

theorem CursorAgree.discardRest {c : BatchCursor g} {d : BatchCursor g'}
    (h : CursorAgree c d) : CursorAgree c.discardRest d.discardRest := by
  have hle := cNext_le_cStop c
  cases c
  cases d
  obtain ⟨hv, hb, hf, hs, hn, hr, hdc, hbd⟩ := h
  simp only [cFirst, cStop, cNext] at hf hs hn hbd hle
  subst hf hs hn
  exact ⟨hv, hb, rfl, rfl, rfl, hr, rfl, Nat.le_trans hle hbd⟩

theorem CursorAgree.setVersion {c : BatchCursor g} {d : BatchCursor g'}
    (h : CursorAgree c d) (version : Version) {c' : BatchCursor g} {d' : BatchCursor g'}
    (hc : c.setVersion version = .ok c') (hd : d.setVersion version = .ok d') :
    CursorAgree c' d' := by
  have hle := cNext_le_cStop c
  have hv0 := h.version
  cases c
  cases d
  obtain ⟨hv, hb, hf, hs, hn, hr, hdc, hbd⟩ := h
  simp only [cFirst, cStop, cNext] at hf hs hn hbd hle
  subst hf hs hn
  simp only [BatchCursor.setVersion, Except.ok.injEq] at hc hd
  subst hc hd
  simp only at hv0
  rw [hv0]
  split
  · exact ⟨rfl, hb, rfl, rfl, rfl, rfl, hdc, Nat.le_trans hle hbd⟩
  · exact ⟨rfl, hb, rfl, rfl, rfl, hr, hdc, hbd⟩

theorem CursorAgree.switched {c : BatchCursor g} {d : BatchCursor g'} (h : CursorAgree c d)
    (consumer : Spec.Lexer.Consumer) (taken : List Spec.Lexer.Handed) :
    CursorAgree (Answering.switched consumer taken c).val
      (Answering.switched consumer taken d).val := by
  unfold Answering.switched
  split
  · exact h
  · split
    · rename_i nc hc
      split
      · rename_i nd hd
        exact h.setVersion _ hc hd
      · rename_i hd; simp [BatchCursor.setVersion] at hd
    · rename_i hc; simp [BatchCursor.setVersion] at hc

theorem CursorAgree.requests {c : BatchCursor g} {d : BatchCursor g'} (h : CursorAgree c d)
    (consumer : Spec.Lexer.Consumer) (taken : List Spec.Lexer.Handed) :
    CursorAgree (Answering.requests consumer taken c).val
      (Answering.requests consumer taken d).val := by
  unfold Answering.requests
  dsimp only
  split
  · exact (h.switched consumer taken).discardRest
  · exact h.switched consumer taken

end BSmtLib.Proofs.Simulation

namespace BSmtLib.Proofs.WRustPortX1BatchInCore

open BSmtLib.Proofs.Adapter BSmtLib.Proofs.Simulation

variable {g g' : BatchTag}

/-- The adapter's consumer for a consumer of the spec reads the cursors only below the length of
their batches: on cursors that agree it takes the same tokens and gives cursors that agree. -/
theorem answering_consume_agree (consumer : Spec.Lexer.Consumer) : ∀ (n : Nat)
    (c : BatchCursor g) (d : BatchCursor g') (hc : c.HasNext) (hd : d.HasNext),
    c.remaining = n → CursorAgree c d → ∀ taken : List Spec.Lexer.Handed,
    ((Answering.consume consumer c hc).run taken).1.1 =
        ((Answering.consume consumer d hd).run taken).1.1 ∧
      CursorAgree ((Answering.consume consumer c hc).run taken).1.2.val
        ((Answering.consume consumer d hd).run taken).1.2.val ∧
      ((Answering.consume consumer c hc).run taken).2 =
        ((Answering.consume consumer d hd).run taken).2 := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
  intro c d hc hd hn h taken
  obtain ⟨et, hag⟩ := h.takeNext hc hd
  have hlt := tokenIndex_next_lt hc h.bounded
  have hrem : (c.next hc).2.1.remaining < n := hn ▸ (c.next hc).2.2.remaining_lt
  rw [Answering.consume, Answering.consume]
  generalize c.next hc = p at et hag hlt hrem
  generalize d.next hd = q at et hag
  obtain ⟨t, next, consumed⟩ := p
  obtain ⟨t', next', consumed'⟩ := q
  dsimp only at et hag hlt hrem ⊢
  rw [entry_eq consumer h et hlt]
  cases Answering.entry consumer d t' with
  | none => exact ⟨rfl, hag, rfl⟩
  | some handed =>
    simp only [StateT.run_bind, StateT.run_get, StateT.run_set, pure_bind]
    cases consumer.answer (taken ++ [handed]) with
    | fail e => exact ⟨rfl, hag.requests consumer _, rfl⟩
    | «break» r => exact ⟨rfl, hag.requests consumer _, rfl⟩
    | «continue» =>
      dsimp only
      split
      · exact ⟨rfl, hag.requests consumer _, rfl⟩
      · by_cases hn' : next.HasNext
        · have hd' := hag.hasNext_iff.mp hn'
          simp only [hn', hd', dite_true]
          obtain ⟨e1, e2, e3⟩ := ih _ hrem next next' hn' hd' rfl hag (taken ++ [handed])
          simp only [StateT.run_bind] at e1 e2 e3 ⊢
          exact ⟨e1, e2, e3⟩
        · have hd' : ¬ next'.HasNext := mt hag.hasNext_iff.mpr hn'
          simp only [hn', hd', dite_false]
          exact ⟨rfl, hag, rfl⟩

/-- The adapter's consumer for a consumer of the spec reads the cursors only below the length of
their batches. -/
theorem answering_consumesAlike (consumer : Spec.Lexer.Consumer) :
    ConsumesAlike (Answering consumer) AnswerM consumer.Result (Option consumer.Error) := by
  intro _ _ c d hc hd h s
  have hag := fun taken => answering_consume_agree consumer _ c d hc hd rfl h taken
  refine ⟨fun taken =>
    (⟨(((Answering.consume consumer c hc).run taken).1,
      ((Answering.consume consumer d hd).run taken).1, s), (hag taken).1, (hag taken).2.1⟩,
      ((Answering.consume consumer c hc).run taken).2), ?_, ?_⟩
  · funext taken
    rfl
  · funext taken
    show ((((Answering.consume consumer d hd).run taken).1, s),
      ((Answering.consume consumer d hd).run taken).2) = _
    rw [← (hag taken).2.2]
    rfl

theorem slice_alike (consumer : Spec.Lexer.Consumer) (slice : ByteSlice) :
    StepsAlike WRustPort.lexOps X1BatchInCore.lexOps (consumer := consumer) LexRel
      (fun a => WRustPort.lexOps.lexSliceStep a slice)
      (fun b => X1BatchInCore.lexOps.lexSliceStep b slice) := by
  intro a b taken h
  have hc := run_lexSliceStep_sim (H := Answering consumer) (m := AnswerM)
    (R := consumer.Result) (E := Option consumer.Error) (recovery := .failFast)
    (opsSim_rust_x1BatchInCore (answering_consumesAlike consumer))
    (LexRecovery.abandon Recovery.failFast) (LexRecovery.recover Recovery.failFast) slice a b h
  obtain ⟨hr, ht⟩ := mcouple_answerM hc taken
  exact ⟨hr.1, hr.2, ht⟩

theorem eof_alike (consumer : Spec.Lexer.Consumer) :
    StepsAlike WRustPort.lexOps X1BatchInCore.lexOps (consumer := consumer) LexRel
      WRustPort.lexOps.lexEofStep X1BatchInCore.lexOps.lexEofStep := by
  intro a b taken h
  have hc := run_lexEofStep_sim (H := Answering consumer) (m := AnswerM)
    (R := consumer.Result) (E := Option consumer.Error) (recovery := .failFast)
    (opsSim_rust_x1BatchInCore (answering_consumesAlike consumer))
    (LexRecovery.abandon Recovery.failFast) (LexRecovery.recover Recovery.failFast) a b h
  obtain ⟨hr, ht⟩ := mcouple_answerM hc taken
  exact ⟨hr.1, hr.2, ht⟩

/-- The Rust lexer ported to Lean and the lexer with the batch kept in its state do the same with
every consumer of the spec. -/
theorem lexing_wRustPort_x1BatchInCore :
    lexing WRustPort.lexOps = lexing X1BatchInCore.lexOps :=
  lexing_alike _ _ (fun _ => LexRel) (fun _ version => new_rel _ version) slice_alike eof_alike
    (fun _ _ _ h => h.2.2) (fun _ _ _ _ h => ⟨h.1, h.2.1, rfl⟩)
    (fun _ _ _ h => h.2.1.1.version) (fun _ _ _ h => h.2.1.1.discardedFrom)

end BSmtLib.Proofs.WRustPortX1BatchInCore
