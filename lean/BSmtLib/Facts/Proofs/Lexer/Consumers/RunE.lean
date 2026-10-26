module

public import BSmtLib.Facts.Proofs.Lexer.Consumers.AlikeF

@[expose] public section

/-!
# Feeding a lexer slices, keeping its error

`LexOps.runInput` gives where the lexer stands in the form of the specification formalism
(`BSmtLibSpec`), which keeps of an error only its `failureOf`. `runInputE` feeds the lexer the same
way and gives the error itself, or the result the lexer holds at the end: the held one, or after the
end of the input the one it gives there. Two lexers whose steps give results alike as a `g` says
give results alike as `g` says fed the same slices (`runInputE_alikeG`); with steps that give the
same results, the same results (`runInputE_alike`).
-/

namespace BSmtLib.Facts.Proofs.Lexer.Consumers.RunE

open BSmtLibSpec.Lexer (Handed)
open BSmtLib.Facts.Lexer.Adapters BSmtLib.Facts.Proofs.Lexer.Consumers.Alike
open BSmtLib.Facts.Proofs.Lexer.Consumers.AlikeF BSmtLib.Lexer.Error

section
variable {consumer : BSmtLibSpec.Lexer.Consumer}

/-- Feeds the lexer the slices and then, if the input has ended, the end of the input, as
`LexOps.runInput` does, stopping at the first call that fails. Gives the error of that call, or
the result the lexer holds at the end, and the lexer. -/
def runInputE (ops : LexOps) (lexer : ops.Lexer consumer) (ended : Bool) :
    List BSmtLibSpec.Regex.Chars →
      AnswerM (Except (LexerError (Option consumer.Error)) (Option (Span.Located consumer.Result)) ×
        ops.Lexer consumer)
  | [] =>
    if ended then do
      match ← ops.lexEofStep lexer with
      | (.ok flow, lexer) => return (.ok (eofResult (ops.held lexer) flow), ops.withHeld lexer none)
      | (.error error, lexer) => return (.error error, lexer)
    else
      return (.ok (ops.held lexer), lexer)
  | slice :: slices => do
    match ← ops.lexSliceStep lexer slice.toByteArray.toByteSlice with
    | (.ok held, lexer) =>
      runInputE ops (ops.withHeld lexer (held.or (ops.held lexer))) ended slices
    | (.error error, lexer) => return (.error error, lexer)

theorem runInputE_cons (ops : LexOps) (lexer : ops.Lexer consumer) (ended : Bool)
    (slice : BSmtLibSpec.Regex.Chars) (slices : List BSmtLibSpec.Regex.Chars) (t : List Handed) :
    (runInputE ops lexer ended (slice :: slices)).run t =
      match (ops.lexSliceStep lexer slice.toByteArray.toByteSlice).run t with
      | ((.ok held, lexer), t') =>
        (runInputE ops (ops.withHeld lexer (held.or (ops.held lexer))) ended slices).run t'
      | ((.error error, lexer), t') => ((.error error, lexer), t') := by
  simp only [runInputE, StateT.run_bind]
  rcases (ops.lexSliceStep lexer slice.toByteArray.toByteSlice).run t with ⟨⟨_ | _, _⟩, _⟩ <;> rfl

theorem runInputE_nil_true (ops : LexOps) (lexer : ops.Lexer consumer) (t : List Handed) :
    (runInputE ops lexer true []).run t =
      match (ops.lexEofStep lexer).run t with
      | ((.ok flow, lexer), t') =>
        ((.ok (eofResult (ops.held lexer) flow), ops.withHeld lexer none), t')
      | ((.error error, lexer), t') => ((.error error, lexer), t') := by
  simp only [runInputE, ite_true, StateT.run_bind]
  rcases (ops.lexEofStep lexer).run t with ⟨⟨_ | _, _⟩, _⟩ <;> rfl

theorem runInputE_nil_false (ops : LexOps) (lexer : ops.Lexer consumer) (t : List Handed) :
    (runInputE ops lexer false []).run t = ((.ok (ops.held lexer), lexer), t) := rfl

/-- Where the lexer stands in the formalism's form, after the result or the error of `runInputE`. -/
def outcomeOf (ended : Bool) :
    Except (LexerError (Option consumer.Error)) (Option (Span.Located consumer.Result)) →
      BSmtLibSpec.Lexer.Outcome consumer.Result consumer.Error
  | .error error => .failed (failureOf error)
  | .ok (some held) =>
    if ended then .finished held.value (toLocation held.location)
    else .holding held.value (toLocation held.location)
  | .ok none => .running

/-- `LexOps.runInput` is `runInputE` with the result in the formalism's form. -/
theorem runInput_eq (ops : LexOps) (ended : Bool) : ∀ (slices : List BSmtLibSpec.Regex.Chars)
    (lexer : ops.Lexer consumer) (t : List Handed),
    (ops.runInput lexer ended slices).run t =
      ((outcomeOf ended ((runInputE ops lexer ended slices).run t).1.1,
        ((runInputE ops lexer ended slices).run t).1.2),
        ((runInputE ops lexer ended slices).run t).2)
  | [], lexer, t => by
    cases ended with
    | false =>
      rw [runInputE_nil_false]
      simp only [LexOps.runInput, Bool.false_eq_true, ite_false]
      show ((ops.standing lexer, lexer), t) = _
      unfold LexOps.standing
      cases ops.held lexer <;> rfl
    | true =>
      rw [runInputE_nil_true]
      simp only [LexOps.runInput, ite_true, StateT.run_bind]
      rcases (ops.lexEofStep lexer).run t with ⟨⟨_ | flow, l⟩, t'⟩
      · rfl
      · show (match eofResult (ops.held l) flow with
            | some result => (pure (BSmtLibSpec.Lexer.Outcome.finished result.value
                (toLocation result.location), ops.withHeld l none) : AnswerM _)
            | none => pure (.running, ops.withHeld l none)).run t' = _
        dsimp only
        cases eofResult (ops.held l) flow <;> rfl
  | slice :: slices, lexer, t => by
    rw [runInputE_cons]
    simp only [LexOps.runInput, StateT.run_bind]
    rcases (ops.lexSliceStep lexer slice.toByteArray.toByteSlice).run t with ⟨⟨_ | held, l⟩, t'⟩
    · rfl
    · exact runInput_eq ops ended slices _ t'

end

section
variable (ops₁ ops₂ : LexOps) {consumer : BSmtLibSpec.Lexer.Consumer}
  (Rel Weak : ops₁.Lexer consumer → ops₂.Lexer consumer → Prop)

/-- The run from a lexer that has the property `Inv` fails, if it does, with an error that has
`P`. This holds if `Inv` is kept by every call on a slice that does not fail and by keeping a held
result, and every failed call from a lexer that has `Inv` fails with an error that has `P`. -/
theorem runInputE_error_inv (ops : LexOps) {consumer : BSmtLibSpec.Lexer.Consumer}
    (Inv : ops.Lexer consumer → Prop) (P : LexerError (Option consumer.Error) → Prop)
    (hslice : ∀ (slice : BSmtLibSpec.Regex.Chars) a (taken : List Handed), Inv a →
      (∀ held, ((ops.lexSliceStep a slice.toByteArray.toByteSlice).run taken).1.1 = .ok held →
        ∀ held', Inv (ops.withHeld ((ops.lexSliceStep a slice.toByteArray.toByteSlice).run
          taken).1.2 held')) ∧
      ∀ e, ((ops.lexSliceStep a slice.toByteArray.toByteSlice).run taken).1.1 = .error e → P e)
    (heof : ∀ a (taken : List Handed), Inv a →
      ∀ e, ((ops.lexEofStep a).run taken).1.1 = .error e → P e)
    (ended : Bool) : ∀ (slices : List BSmtLibSpec.Regex.Chars) a (taken : List Handed), Inv a →
      ∀ e, ((runInputE ops a ended slices).run taken).1.1 = .error e → P e
  | [], a, taken, h, e, he => by
    cases ended with
    | false => rw [runInputE_nil_false] at he; cases he
    | true =>
      rw [runInputE_nil_true] at he
      have := heof a taken h
      generalize (ops.lexEofStep a).run taken = r at this he
      obtain ⟨⟨r, l⟩, t⟩ := r
      cases r with
      | ok _ => cases he
      | error e' => cases he; exact this e rfl
  | slice :: slices, a, taken, h, e, he => by
    rw [runInputE_cons] at he
    obtain ⟨h1, h2⟩ := hslice slice a taken h
    generalize (ops.lexSliceStep a slice.toByteArray.toByteSlice).run taken = r at h1 h2 he
    obtain ⟨⟨r, l⟩, t⟩ := r
    cases r with
    | ok held =>
      exact runInputE_error_inv ops Inv P hslice heof ended slices _ t
        (h1 held rfl _) e he
    | error e' => cases he; exact h2 e rfl

/-- Two related lexers fed the same slices give results alike as `g` says, take the same tokens,
and are weakly related, and related if they have not failed. This holds if their steps give
results alike as `g` says, as `StepsAlikeG` says, and related lexers hold the same result. -/
theorem runInputE_alikeG {γ : Type} (g : LexerError (Option consumer.Error) → γ)
    (hslice : ∀ slice : BSmtLibSpec.Regex.Chars, StepsAlikeG ops₁ ops₂ Rel Weak g
      (fun a => ops₁.lexSliceStep a slice.toByteArray.toByteSlice)
      (fun b => ops₂.lexSliceStep b slice.toByteArray.toByteSlice))
    (heof : StepsAlikeG ops₁ ops₂ Rel Weak g ops₁.lexEofStep ops₂.lexEofStep)
    (hheld : ∀ a b, Rel a b → ops₁.held a = ops₂.held b)
    (hwith : ∀ a b held, Rel a b → Rel (ops₁.withHeld a held) (ops₂.withHeld b held))
    (hweak : ∀ a b, Rel a b → Weak a b)
    (ended : Bool) (slices : List BSmtLibSpec.Regex.Chars) :
    ∀ a b (taken : List Handed), Rel a b →
      ((runInputE ops₁ a ended slices).run taken).1.1.mapError g =
          ((runInputE ops₂ b ended slices).run taken).1.1.mapError g ∧
        ((runInputE ops₁ a ended slices).run taken).2 =
          ((runInputE ops₂ b ended slices).run taken).2 ∧
        (((runInputE ops₁ a ended slices).run taken).1.1.isOk = true →
          Rel ((runInputE ops₁ a ended slices).run taken).1.2
            ((runInputE ops₂ b ended slices).run taken).1.2) ∧
        Weak ((runInputE ops₁ a ended slices).run taken).1.2
          ((runInputE ops₂ b ended slices).run taken).1.2 := by
  induction slices with
  | nil =>
    intro a b taken h
    cases ended with
    | false =>
      rw [runInputE_nil_false, runInputE_nil_false, hheld a b h]
      exact ⟨rfl, rfl, fun _ => h, hweak a b h⟩
    | true =>
      obtain ⟨e1, e2, e3, e4⟩ := heof a b taken h
      rw [runInputE_nil_true, runInputE_nil_true]
      generalize (ops₁.lexEofStep a).run taken = ra at e1 e2 e3 e4 ⊢
      generalize (ops₂.lexEofStep b).run taken = rb at e1 e2 e3 e4 ⊢
      obtain ⟨⟨r, a'⟩, t⟩ := ra
      obtain ⟨⟨r', b'⟩, t'⟩ := rb
      simp only at e1 e2 e3 e4
      subst e2
      cases r with
      | error e =>
        cases r' with
        | ok _ => cases e1
        | error e' =>
          dsimp only
          refine ⟨?_, rfl, nofun, e4⟩
          simp only [Except.mapError, Except.error.injEq] at e1 ⊢
          exact e1
      | ok flow =>
        have hr := mapError_ok e1 rfl
        subst hr
        have hab := e3 rfl
        dsimp only
        rw [hheld a' b' hab]
        exact ⟨rfl, rfl, fun _ => hwith _ _ _ hab, hweak _ _ (hwith _ _ _ hab)⟩
  | cons slice slices ih =>
    intro a b taken h
    obtain ⟨e1, e2, e3, e4⟩ := hslice slice a b taken h
    rw [runInputE_cons, runInputE_cons]
    generalize (ops₁.lexSliceStep a slice.toByteArray.toByteSlice).run taken = ra
      at e1 e2 e3 e4 ⊢
    generalize (ops₂.lexSliceStep b slice.toByteArray.toByteSlice).run taken = rb
      at e1 e2 e3 e4 ⊢
    obtain ⟨⟨r, a'⟩, t⟩ := ra
    obtain ⟨⟨r', b'⟩, t'⟩ := rb
    simp only at e1 e2 e3 e4
    subst e2
    cases r with
    | error e =>
      cases r' with
      | ok _ => cases e1
      | error e' => dsimp only; exact ⟨e1, rfl, nofun, e4⟩
    | ok held =>
      have hr := mapError_ok e1 rfl
      subst hr
      have hab := e3 rfl
      dsimp only
      rw [hheld a' b' hab]
      exact ih _ _ t (hwith _ _ _ hab)

/-- Steps that give the same results and lexers related again give results alike as the identity
says, with the relation as the weak one. -/
theorem stepsAlike_G {β : Type}
    {step₁ : ops₁.Lexer consumer →
      AnswerM (Except (LexerError (Option consumer.Error)) β × ops₁.Lexer consumer)}
    {step₂ : ops₂.Lexer consumer →
      AnswerM (Except (LexerError (Option consumer.Error)) β × ops₂.Lexer consumer)}
    (h : StepsAlike ops₁ ops₂ Rel step₁ step₂) :
    StepsAlikeG ops₁ ops₂ Rel Rel id step₁ step₂ := by
  intro a b taken hr
  obtain ⟨e1, e2, e3⟩ := h a b taken hr
  exact ⟨by rw [e1], e3, fun _ => e2, e2⟩

/-- Two related lexers fed the same slices give the same results, take the same tokens, and are
related again. This holds if their steps give the same results with lexers related again, and
related lexers hold the same result. -/
theorem runInputE_alike
    (hslice : ∀ slice : BSmtLibSpec.Regex.Chars, StepsAlike ops₁ ops₂ Rel
      (fun a => ops₁.lexSliceStep a slice.toByteArray.toByteSlice)
      (fun b => ops₂.lexSliceStep b slice.toByteArray.toByteSlice))
    (heof : StepsAlike ops₁ ops₂ Rel ops₁.lexEofStep ops₂.lexEofStep)
    (hheld : ∀ a b, Rel a b → ops₁.held a = ops₂.held b)
    (hwith : ∀ a b held, Rel a b → Rel (ops₁.withHeld a held) (ops₂.withHeld b held))
    (ended : Bool) (slices : List BSmtLibSpec.Regex.Chars) :
    ∀ a b (taken : List Handed), Rel a b →
      ((runInputE ops₁ a ended slices).run taken).1.1 =
          ((runInputE ops₂ b ended slices).run taken).1.1 ∧
        ((runInputE ops₁ a ended slices).run taken).2 =
          ((runInputE ops₂ b ended slices).run taken).2 ∧
        Rel ((runInputE ops₁ a ended slices).run taken).1.2
          ((runInputE ops₂ b ended slices).run taken).1.2 := by
  intro a b taken h
  obtain ⟨e1, e2, -, e4⟩ := runInputE_alikeG ops₁ ops₂ Rel Rel id
    (fun slice => stepsAlike_G ops₁ ops₂ Rel (hslice slice)) (stepsAlike_G ops₁ ops₂ Rel heof)
    hheld hwith (fun _ _ h => h) ended slices a b taken h
  refine ⟨?_, e2, e4⟩
  generalize ((runInputE ops₁ a ended slices).run taken).1.1 = x at e1
  generalize ((runInputE ops₂ b ended slices).run taken).1.1 = y at e1
  cases x <;> cases y <;> simp_all [Except.mapError]

end

end BSmtLib.Facts.Proofs.Lexer.Consumers.RunE
