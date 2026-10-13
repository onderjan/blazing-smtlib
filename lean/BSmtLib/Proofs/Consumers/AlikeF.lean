import BSmtLib.Proofs.Consumers.Alike

/-!
# Lexers that do alike with every consumer of the spec, up to how they fail

`lexing_alikeF`: two lexers that are constructed related, and whose steps on a slice and at the
end of the input give results the spec does not tell apart (the same, or errors with the same
`failureOf`) and take the same tokens, with lexers related again when they do not fail and
weakly related always, do the same with every consumer of the spec. The weak relation is what
the adapter reads from a lexer after a failed call: its version and where it discards from.
-/

namespace BSmtLib.Proofs.Adapter

open BSmtLibSpec.Lexer (Handed)

section
variable (ops₁ ops₂ : LexOps) {consumer : BSmtLibSpec.Lexer.Consumer}
  (Rel Weak : ops₁.Lexer consumer → ops₂.Lexer consumer → Prop)

/-- Steps that give results the spec does not tell apart, the same tokens taken, lexers related
again when they do not fail, and weakly related lexers. -/
def StepsAlikeF {β : Type}
    (step₁ : ops₁.Lexer consumer →
      AnswerM (Except (LexError (Option consumer.Error)) β × ops₁.Lexer consumer))
    (step₂ : ops₂.Lexer consumer →
      AnswerM (Except (LexError (Option consumer.Error)) β × ops₂.Lexer consumer)) : Prop :=
  ∀ a b (taken : List Handed), Rel a b →
    ((step₁ a).run taken).1.1.mapError failureOf =
        ((step₂ b).run taken).1.1.mapError failureOf ∧
      ((step₁ a).run taken).2 = ((step₂ b).run taken).2 ∧
      (((step₁ a).run taken).1.1.isOk = true →
        Rel ((step₁ a).run taken).1.2 ((step₂ b).run taken).1.2) ∧
      Weak ((step₁ a).run taken).1.2 ((step₂ b).run taken).1.2

theorem mapError_ok {ε ε' β : Type} {f : ε → ε'} {x y : Except ε β}
    (h : x.mapError f = y.mapError f) {a : β} (hx : x = .ok a) : y = .ok a := by
  subst hx
  cases y with
  | ok b => cases h; rfl
  | error e => cases h

theorem mapError_error {ε ε' β : Type} {f : ε → ε'} {x y : Except ε β}
    (h : x.mapError f = y.mapError f) {e : ε} (hx : x = .error e) :
    ∃ e', y = .error e' ∧ f e = f e' := by
  subst hx
  cases y with
  | ok b => cases h
  | error e' =>
    refine ⟨e', rfl, ?_⟩
    simp only [Except.mapError, Except.error.injEq] at h
    exact h

/-- Two lexers whose steps give results the spec does not tell apart, as `StepsAlikeF` says,
and whose related lexers hold the same result, stand alike after the same input, take the same
tokens, and are weakly related, and related if they have not failed. -/
theorem runInput_alikeF
    (hslice : ∀ slice : BSmtLibSpec.Regex.Chars, StepsAlikeF ops₁ ops₂ Rel Weak
      (fun a => ops₁.lexSliceStep a slice.toByteArray.toByteSlice)
      (fun b => ops₂.lexSliceStep b slice.toByteArray.toByteSlice))
    (heof : StepsAlikeF ops₁ ops₂ Rel Weak ops₁.lexEofStep ops₂.lexEofStep)
    (hheld : ∀ a b, Rel a b → ops₁.held a = ops₂.held b)
    (hwith : ∀ a b held, Rel a b → Rel (ops₁.withHeld a held) (ops₂.withHeld b held))
    (hweak : ∀ a b, Rel a b → Weak a b)
    (ended : Bool) (slices : List BSmtLibSpec.Regex.Chars) :
    ∀ a b (taken : List Handed), Rel a b →
      ((ops₁.runInput a ended slices).run taken).1.1 =
          ((ops₂.runInput b ended slices).run taken).1.1 ∧
        ((ops₁.runInput a ended slices).run taken).2 =
          ((ops₂.runInput b ended slices).run taken).2 ∧
        (((ops₁.runInput a ended slices).run taken).1.1.isFailed = false →
          Rel ((ops₁.runInput a ended slices).run taken).1.2
            ((ops₂.runInput b ended slices).run taken).1.2) ∧
        Weak ((ops₁.runInput a ended slices).run taken).1.2
          ((ops₂.runInput b ended slices).run taken).1.2 := by
  induction slices with
  | nil =>
    intro a b taken h
    cases ended with
    | false =>
      simp only [LexOps.runInput, Bool.false_eq_true, ite_false]
      refine ⟨?_, rfl, fun _ => h, hweak a b h⟩
      show ops₁.standing a = ops₂.standing b
      unfold LexOps.standing
      rw [hheld a b h]
    | true =>
      obtain ⟨e1, e2, e3, e4⟩ := heof a b taken h
      simp only [LexOps.runInput, ite_true, StateT.run_bind]
      generalize (ops₁.lexEofStep a).run taken = ra at e1 e2 e3 e4 ⊢
      generalize (ops₂.lexEofStep b).run taken = rb at e1 e2 e3 e4 ⊢
      obtain ⟨⟨r, a'⟩, t⟩ := ra
      obtain ⟨⟨r', b'⟩, t'⟩ := rb
      simp only at e1 e2 e3 e4
      subst e2
      cases r with
      | error e =>
        obtain ⟨e', rfl, he⟩ := mapError_error e1 rfl
        simp only [idBind]
        exact ⟨by rw [he]; rfl, rfl, nofun, e4⟩
      | ok flow =>
        have hr := mapError_ok e1 rfl
        subst hr
        have hab := e3 rfl
        simp only [idBind]
        rw [hheld a' b' hab]
        cases eofResult (ops₂.held b') flow with
        | none => exact ⟨rfl, rfl, fun _ => hwith _ _ _ hab, hweak _ _ (hwith _ _ _ hab)⟩
        | some res => exact ⟨rfl, rfl, fun _ => hwith _ _ _ hab, hweak _ _ (hwith _ _ _ hab)⟩
  | cons slice slices ih =>
    intro a b taken h
    obtain ⟨e1, e2, e3, e4⟩ := hslice slice a b taken h
    simp only [LexOps.runInput, StateT.run_bind]
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
      obtain ⟨e', rfl, he⟩ := mapError_error e1 rfl
      simp only [idBind]
      exact ⟨by rw [he]; rfl, rfl, nofun, e4⟩
    | ok held =>
      have hr := mapError_ok e1 rfl
      subst hr
      have hab := e3 rfl
      simp only [idBind]
      rw [hheld a' b' hab]
      exact ih _ _ t (hwith _ _ _ hab)

end

/-- Two lexers that are constructed related, and whose steps give results the spec does not tell
apart, as `StepsAlikeF` says, do the same with every consumer of the spec: what the adapter
makes of them is equal. -/
theorem lexing_alikeF (ops₁ ops₂ : LexOps)
    (Rel Weak : ∀ consumer : BSmtLibSpec.Lexer.Consumer,
      ops₁.Lexer consumer → ops₂.Lexer consumer → Prop)
    (hnew : ∀ consumer version,
      Rel consumer (ops₁.new consumer {} version) (ops₂.new consumer {} version))
    (hslice : ∀ consumer (slice : BSmtLibSpec.Regex.Chars), StepsAlikeF ops₁ ops₂ (Rel consumer)
      (Weak consumer) (fun a => ops₁.lexSliceStep a slice.toByteArray.toByteSlice)
      (fun b => ops₂.lexSliceStep b slice.toByteArray.toByteSlice))
    (heof : ∀ consumer,
      StepsAlikeF ops₁ ops₂ (Rel consumer) (Weak consumer) ops₁.lexEofStep ops₂.lexEofStep)
    (hheld : ∀ consumer a b, Rel consumer a b → ops₁.held a = ops₂.held b)
    (hwith : ∀ consumer a b held, Rel consumer a b →
      Rel consumer (ops₁.withHeld a held) (ops₂.withHeld b held))
    (hweak : ∀ consumer a b, Rel consumer a b → Weak consumer a b)
    (hversion : ∀ consumer a b, Weak consumer a b → ops₁.version a = ops₂.version b)
    (hdisc : ∀ consumer a b, Weak consumer a b →
      ops₁.discardedFrom a = ops₂.discardedFrom b) :
    lexing ops₁ = lexing ops₂ := by
  funext consumer version earlier slices ended
  have hrun := runInput_alikeF ops₁ ops₂ (Rel consumer) (Weak consumer) (hslice consumer)
    (heof consumer) (hheld consumer) (hwith consumer) (hweak consumer)
  rw [lexing_def, lexing_def]
  have hL := foldl_next_rel ops₁ ops₂ (Rel consumer) (toVersion version) id
    (hnew consumer (toVersion version))
    (fun input a b h => ⟨(hrun true input a b [] h).1, (hrun true input a b [] h).2.2.1⟩)
    earlier _ _ (hnew consumer (toVersion version))
  rw [List.map_id] at hL
  obtain ⟨e1, e2, -, e4⟩ := hrun ended slices _ _ [] hL
  simp only
  rw [e1, e2, hversion consumer _ _ e4, hdisc consumer _ _ e4]

end BSmtLib.Proofs.Adapter
