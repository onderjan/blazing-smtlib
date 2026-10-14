import BSmtLib.Facts.Proofs.Reader.Param.Steps

/-!
# The loop over a slice on two consumers

The loop over a slice runs in the consumers' monads with the lexer's state passed by hand, and
passes on the results and errors of the consumers in its values, so its lemmas relate those
values: the same answer, with results related by the link's relation of results and errors by
its relation of errors.
-/

namespace BSmtLib.Facts.Proofs.Reader.Param.Slice

open BSmtLib.Lexer BSmtLib.Lexer.Internal
open BSmtLib.Facts.Proofs.Reader.Param.Basic BSmtLib.Facts.Proofs.Reader.Param.HandOver
open BSmtLib.Facts.Proofs.Reader.Param.Steps

section

variable {H₁ H₂ : Type} {m₁ m₂ : Type → Type} [Monad m₁] [Monad m₂] {R₁ R₂ E₁ E₂ : Type}

/-- The same answer of a step, with related results and failures. -/
abbrev FlowLRel (L : Link H₁ m₁ R₁ E₁ H₂ m₂ R₂ E₂) :
    Except (Failure E₁) (ControlFlow R₁) → Except (Failure E₂) (ControlFlow R₂) → Prop :=
  ERel (FailRel L.re) (FlowRel L.rr)

/-- The same exit of the loop over a slice, with related results and failures. -/
def ExitRel (L : Link H₁ m₁ R₁ E₁ H₂ m₂ R₂ E₂) {floor : Option Nat} :
    SliceExit R₁ E₁ floor → SliceExit R₂ E₂ floor → Prop
  | .done r, .done r' => FlowLRel L r r'
  | .stopped s l _, .stopped s' l' _ => StopRel L.rr s s' ∧ l = l'
  | _, _ => False

/-- The same result of lexing a slice, with related held results and failures. -/
abbrev HeldRel (L : Link H₁ m₁ R₁ E₁ H₂ m₂ R₂ E₂) :
    Except (Failure E₁) (Option (Span.Located R₁)) → Except (Failure E₂)
        (Option (Span.Located R₂)) →
      Prop :=
  ERel (FailRel L.re) (ORel (LocRel L.rr))

variable [Token.Consume H₁ R₁ E₁] [Token.Consume H₂ R₂ E₂] [∀ b, Token.ConsumeFrom H₁
    (Token.BatchCursor b) m₁]
  [∀ b, Token.ConsumeFrom H₂ (Token.BatchCursor b) m₂] {L : Link H₁ m₁ R₁ E₁ H₂ m₂ R₂ E₂}

/-- What the loop over a slice descends by: the bytes left, and then whether a failure is still
to be met. -/
def runMeasure {E R : Type} (input : CharClass.Input) (position : USize)
    (fnResult : Except (Failure E) (ControlFlow R)) : Nat :=
  2 * (input.stop.toNat - position.toNat) + match fnResult with | .ok _ => 1 | .error _ => 0

theorem lexSliceRun_sim_lt (hc : Consumers L) {floor : Option Nat} (input : CharClass.Input) :
    ∀ (n : Nat) (position : USize) (fnResult₁ : Except (Failure E₁) (ControlFlow R₁))
      (fnResult₂ : Except (Failure E₂) (ControlFlow R₂)) (_ : FlowLRel L fnResult₁ fnResult₂)
      (core : {c : LexerCore // c.Bound floor 0}), runMeasure input position fnResult₁ < n →
      L.rc.rel (fun a b => ExitRel L a.1 b.1 ∧ a.2 = b.2)
        (lexSliceRun input position fnResult₁ core) (lexSliceRun input position fnResult₂ core)
  | 0, _, _, _, _, _, hn => absurd hn (Nat.not_lt_zero _)
  | n + 1, position, fnResult₁, fnResult₂, hf, core, hn => by
    rw [lexSliceRun.eq_def, lexSliceRun.eq_def]
    rcases fnResult₁ with e₁ | f₁ <;> rcases fnResult₂ with e₂ | f₂ <;> try exact absurd hf id
    all_goals
      dsimp only
      refine Relator.dite_same (fun hflush => ?_) (fun hflush => ?_)
      · refine L.rc.bind (flushBatch_sim hc core) ?_
        rintro ⟨fl₁, c₁⟩ ⟨fl₂, c₂⟩ ⟨hfl, hcore⟩
        cases hcore
        match fl₁, fl₂, hfl with
        | .ok (), .ok (), _ => exact L.rc.pure ⟨hf, rfl⟩
        | .error ⟨r₁, s₁, l₁, a₁⟩, .error ⟨r₂, s₂, l₂, a₂⟩, ⟨hloc, hspan, hres⟩ =>
          cases hloc
          cases hspan
          cases r₁ <;> cases r₂ <;> try exact absurd hres id
          · exact L.rc.pure ⟨⟨hres, rfl, rfl⟩, rfl⟩
          · exact L.rc.pure ⟨⟨hres, rfl⟩, rfl⟩
      · have hlt : position.toNat < input.stop.toNat := by
          simp only [Bool.or_eq_true, decide_eq_true_eq, not_or] at hflush
          have := hflush.1
          simp only [ge_iff_le, USize.le_iff_toNat_le] at this
          omega
        refine L.rc.bind (lexStep_sim hc _ _ _ _ _ _ _ _) ?_
        rintro ⟨st₁, c₁⟩ ⟨st₂, c₂⟩ ⟨hst, hcore⟩
        cases hcore
        match st₁, st₂, hst with
        | .ok ⟨n₁, hn₁⟩, .ok ⟨n₂, hn₂⟩, hnext =>
          cases hnext
          refine lexSliceRun_sim_lt hc input n n₁ _ _ hf _ ?_
          simp only [runMeasure] at hn ⊢
          omega
        | .error ⟨r₁, s₁, l₁, a₁⟩, .error ⟨r₂, s₂, l₂, a₂⟩, ⟨hloc, hspan, hres⟩ =>
          cases hloc
          cases hspan
          cases r₁ <;> cases r₂ <;> try exact absurd hres id
          · refine lexSliceRun_sim_lt hc input n position
              (.error { cause := _, span := s₁, location := l₁ })
              (.error { cause := _, span := s₁, location := l₁ }) ⟨hres, rfl, rfl⟩ _ ?_
            simp only [runMeasure] at hn ⊢
            simp at hflush <;> omega
          · exact L.rc.pure ⟨⟨hres, rfl⟩, rfl⟩

theorem lexSliceRun_sim (hc : Consumers L) {floor : Option Nat} (input : CharClass.Input)
    (position : USize) (fnResult₁ : Except (Failure E₁) (ControlFlow R₁))
    (fnResult₂ : Except (Failure E₂) (ControlFlow R₂)) (hf : FlowLRel L fnResult₁ fnResult₂)
    (core : {c : LexerCore // c.Bound floor 0}) :
    L.rc.rel (fun a b => ExitRel L a.1 b.1 ∧ a.2 = b.2) (lexSliceRun input position fnResult₁ core)
      (lexSliceRun input position fnResult₂ core) :=
  lexSliceRun_sim_lt hc input _ position fnResult₁ fnResult₂ hf core (Nat.lt_succ_self _)
/-- What the loop over the stops in a slice descends by: the bytes after the floor. -/
def fromMeasure (input : CharClass.Input) (initialOffset floor : Nat) : Nat :=
  input.stop.toNat - input.start.toNat + 1 - (floor + 1 - initialOffset)

theorem lexSliceFrom_sim_lt (hc : Consumers L) (input : CharClass.Input) (initialOffset : Nat) :
    ∀ (n floor : Nat) (hfloor : initialOffset ≤ floor + 1) (position : USize)
      (fnResult₁ : Except (Failure E₁) (ControlFlow R₁))
      (fnResult₂ : Except (Failure E₂) (ControlFlow R₂)) (_ : FlowLRel L fnResult₁ fnResult₂)
      (held₁ : Option (Span.Located R₁)) (held₂ : Option (Span.Located R₂))
      (_ : ORel (LocRel L.rr) held₁ held₂)
      (core : {c : LexerCore // c.Bound (some floor) 0}),
      fromMeasure input initialOffset floor < n →
      L.rc.rel (fun a b => HeldRel L a.1 b.1 ∧ a.2 = b.2)
        (lexSliceFrom input initialOffset floor hfloor position fnResult₁ held₁ core)
        (lexSliceFrom input initialOffset floor hfloor position fnResult₂ held₂ core)
  | 0, _, _, _, _, _, _, _, _, _, _, hn => absurd hn (Nat.not_lt_zero _)
  | n + 1, floor, hfloor, position, fnResult₁, fnResult₂, hf, held₁, held₂, hh, core, hn => by
    rw [lexSliceFrom.eq_def, lexSliceFrom.eq_def]
    refine L.rc.bind (lexSliceRun_sim hc input position fnResult₁ fnResult₂ hf core) ?_
    rintro ⟨ex₁, c₁⟩ ⟨ex₂, c₂⟩ ⟨hex, hcore⟩
    cases hcore
    match ex₁, ex₂, hex with
    | .done r₁, .done r₂, hr =>
      refine L.rc.pure ⟨?_, rfl⟩
      match r₁, r₂, hr with
      | .ok _, .ok _, _ => exact hh
      | .error _, .error _, hr => exact hr
    | .stopped s₁ l₁ a₁, .stopped s₂ l₂ a₂, ⟨hs, hl⟩ =>
      cases hl
      have hafter := a₁ floor rfl
      match s₁, s₂, hs with
      | .relex, .relex, _ =>
        refine Relator.dite_same (fun hresumed => ?_) (fun _ => L.rc.pure ⟨hh, rfl⟩)
        refine lexSliceFrom_sim_lt hc input initialOffset n _ _ _ (.ok .continue) (.ok .continue)
          trivial held₁ held₂ hh _ ?_
        simp only [fromMeasure] at hn ⊢
        omega
      | .finished r₁, .finished r₂, hr =>
        refine Relator.dite_same (fun hresumed => ?_) (fun _ => L.rc.pure ⟨⟨hr, rfl⟩, rfl⟩)
        refine lexSliceFrom_sim_lt hc input initialOffset n _ _ _ (.ok .continue) (.ok .continue)
          trivial (some { value := r₁, location := l₁ }) (some { value := r₂, location := l₁ })
          ⟨hr, rfl⟩ _ ?_
        simp only [fromMeasure] at hn ⊢
        omega
      | .discarded o₁, .discarded o₂, ho =>
        match o₁, o₂, ho with
        | some r₁, some r₂, hr => exact L.rc.pure ⟨⟨hr, rfl⟩, rfl⟩
        | none, none, _ => exact L.rc.pure ⟨hh, rfl⟩

theorem lexSliceFrom_sim (hc : Consumers L) (input : CharClass.Input) (initialOffset floor : Nat)
    (hfloor : initialOffset ≤ floor + 1) (position : USize)
    (fnResult₁ : Except (Failure E₁) (ControlFlow R₁))
    (fnResult₂ : Except (Failure E₂) (ControlFlow R₂)) (hf : FlowLRel L fnResult₁ fnResult₂)
    (held₁ : Option (Span.Located R₁)) (held₂ : Option (Span.Located R₂))
    (hh : ORel (LocRel L.rr) held₁ held₂)
    (core : {c : LexerCore // c.Bound (some floor) 0}) :
    L.rc.rel (fun a b => HeldRel L a.1 b.1 ∧ a.2 = b.2)
      (lexSliceFrom input initialOffset floor hfloor position fnResult₁ held₁ core)
      (lexSliceFrom input initialOffset floor hfloor position fnResult₂ held₂ core) :=
  lexSliceFrom_sim_lt hc input initialOffset _ floor hfloor position fnResult₁ fnResult₂ hf held₁
    held₂ hh core (Nat.lt_succ_self _)

theorem lexSliceInner_sim (hc : Consumers L) (input : CharClass.Input) :
    SSim L (HeldRel L) (lexSliceInner (H := H₁) (m := m₁) (R := R₁) (E := E₁) input)
      (lexSliceInner input) := fun _ =>
  lexSliceFrom_sim hc input _ _ _ _ (.ok .continue) (.ok .continue) trivial none none trivial _

end

end BSmtLib.Facts.Proofs.Reader.Param.Slice
