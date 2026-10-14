module

public import BSmtLib.Facts.Proofs.Lexer.Consumers.VSteps
import all BSmtLib.Lexer.Internal.VNaive

@[expose] public section

/-!
# The naive lexer's end of the input with a consumer of the spec

The naive lexer's step at the end of the input with the adapter's consumer `Answering consumer`
(`vEnd`), in each state of the lexer: the end-of-file token is handed over unless a result is
held, after the token in progress that the end of the input ends.
-/

namespace BSmtLib.Facts.Proofs.Lexer.Consumers.VEnd

open BSmtLib.Facts.Lexer.Adapters
open BSmtLibSpec.Lexer (Handed)
open BSmtLib.Facts.Proofs.Lexer.Consumers.VSteps BSmtLib.Facts.Proofs.Lexer.VNaive.Run
open BSmtLib.Lexer.Error BSmtLib.Lexer.Internal.VNaive

section
variable (consumer : BSmtLibSpec.Lexer.Consumer)

/-- The naive lexer's step at the end of the input. -/
def vEnd (core : Core) (taken : List Handed) :
    VRes (Except (LexError (Option consumer.Error)) (ControlFlow (Span.Located consumer.Result))) :=
  vRun consumer (lexEofStep (H := Answering consumer) false (fun _ => pure ()) (fun _ => pure ())
    core) taken

/-- The end-of-file lexeme at the location, as the naive lexer builds it. -/
abbrev eofAt (location : Span.Location) : Lexeme :=
  { category := .endOfFile, content := .empty, start := location, «end» := location }

theorem eofAt_valid (location : Span.Location) : (eofAt location).Valid := .inr ⟨rfl, rfl⟩

/-- The end of the input with nothing in progress, or discarding, and no result held: the
end-of-file token is handed over. -/
theorem vEnd_eof (core : Core) (taken : List Handed)
    (ha : core.activity = .idle ∨ ∃ s, core.activity = .discarding s)
    (hh : core.holding = false) :
    ∀ {r core2 taken2},
      vRun consumer (handOverAt (H := Answering consumer) core (eofAt core.location)
        (eofAt_valid _)) taken = ((r, core2), taken2) →
      vEnd consumer core taken =
        match r with
        | .ok none => ((.ok .continue, core2.reset), taken2)
        | .ok (some located) => ((.ok (.break located), core2.reset), taken2)
        | .error f => ((.error ⟨f.cause, f.span, none⟩, core2), taken2) := by
  intro r core2 taken2 hr
  have hrun := run_of_vRun consumer hr
  rcases ha with ha | ⟨s, ha⟩
  all_goals
    have hw : withEq core.activity = ⟨_, ha⟩ := Subtype.ext ha
    simp only [vEnd, lexEofStep, lexEnd, ha, Bool.false_eq_true, ite_false, pure_bind]
    rw [hw]
    simp only [hh, Bool.false_eq_true, ite_false]
    simp only [vRun, StateT.run_bind]
    rw [hrun]
    cases r with
    | error f => rfl
    | ok held => cases held <;> rfl

/-- The end of the input with nothing in progress, or discarding, and a result held: the held
result is returned, without the end-of-file token handed over. -/
theorem vEnd_held (core : Core) (taken : List Handed)
    (ha : core.activity = .idle ∨ ∃ s, core.activity = .discarding s)
    (hh : core.holding = true) :
    vEnd consumer core taken = ((.ok .continue, core.reset), taken) := by
  rcases ha with ha | ⟨s, ha⟩
  all_goals
    have hw : withEq core.activity = ⟨_, ha⟩ := Subtype.ext ha
    simp only [vEnd, lexEofStep, lexEnd, ha, Bool.false_eq_true, ite_false, pure_bind]
    rw [hw]
    simp only [hh, ite_true]
    rfl


/-- The end of the input in a token that it ends without a lexeme (a comment the consumer does
not take): as with nothing in progress. -/
theorem vEnd_finish_none (core : Core) (taken : List Handed) {p : Pending}
    (ha : core.activity = .token p) (hf : finish consumer.concrete p core.location = .none) :
    (core.holding = true →
      vEnd consumer core taken = ((.ok .continue, (idleAt core).reset), taken)) ∧
    (core.holding = false → ∀ {r core2 taken2},
      vRun consumer (handOverAt (H := Answering consumer) (idleAt core) (eofAt core.location)
        (eofAt_valid _)) taken = ((r, core2), taken2) →
      vEnd consumer core taken =
        match r with
        | .ok none => ((.ok .continue, core2.reset), taken2)
        | .ok (some located) => ((.ok (.break located), core2.reset), taken2)
        | .error f => ((.error ⟨f.cause, f.span, none⟩, core2), taken2)) := by
  have hw : withEq core.activity = ⟨_, ha⟩ := Subtype.ext ha
  have hfs : finishS consumer.concrete p core.location = ⟨.none, trivial⟩ := Subtype.ext hf
  constructor
  · intro hh
    simp only [vEnd, lexEofStep, lexEnd, ha, Bool.false_eq_true, ite_false, pure_bind]
    rw [hw]
    simp only [isConcrete_answering]
    rw [hfs]
    simp only [hh, ite_true]
    rfl
  · intro hh r core2 taken2 hr
    have hrun := run_of_vRun consumer hr
    simp only [idleAt, hh] at hrun
    simp only [vEnd, lexEofStep, lexEnd, ha, Bool.false_eq_true, ite_false, pure_bind]
    rw [hw]
    simp only [isConcrete_answering]
    rw [hfs]
    simp only [hh, Bool.false_eq_true, ite_false]
    simp only [vRun, StateT.run_bind]
    rw [hrun]
    cases r with
    | error f => rfl
    | ok held => cases held <;> rfl

/-- The end of the input in a token that it fails. -/
theorem vEnd_finish_error (core : Core) (taken : List Handed) {p : Pending} {f : LexFailure}
    (ha : core.activity = .token p) (hf : finish consumer.concrete p core.location = .error f) :
    vEnd consumer core taken = ((.error ⟨.lexical f.kind, f.span, none⟩, core), taken) := by
  have hw : withEq core.activity = ⟨_, ha⟩ := Subtype.ext ha
  have hfs : finishS consumer.concrete p core.location = ⟨.error f, trivial⟩ := Subtype.ext hf
  simp only [vEnd, lexEofStep, lexEnd, ha, Bool.false_eq_true, ite_false, pure_bind]
  rw [hw]
  simp only [isConcrete_answering]
  rw [hfs]
  rfl


/-- The end of the input in a token that it ends: the token is handed over; if the consumer
breaks or fails at it, the end of the input stops there. -/
theorem vEnd_finish_token (core : Core) (taken : List Handed) {p : Pending} {l : Lexeme}
    (ha : core.activity = .token p) (hf : finish consumer.concrete p core.location = .token l) :
    ∃ hl, (∀ {f core2 taken2},
      vRun consumer (handOverAt (H := Answering consumer) (idleAt core) l hl) taken =
        ((.error f, core2), taken2) →
      vEnd consumer core taken = ((.error ⟨f.cause, f.span, none⟩, core2), taken2)) ∧
    (∀ {located core2 taken2},
      vRun consumer (handOverAt (H := Answering consumer) (idleAt core) l hl) taken =
        ((.ok (some located), core2), taken2) →
      vEnd consumer core taken = ((.ok (.break located), core2.reset), taken2)) ∧
    (∀ {core2 taken2}, core2.holding = false →
      vRun consumer (handOverAt (H := Answering consumer) (idleAt core) l hl) taken =
        ((.ok none, core2), taken2) →
      ∀ {r core3 taken3},
        vRun consumer (handOverAt (H := Answering consumer) core2 (eofAt core.location)
          (eofAt_valid _)) taken2 = ((r, core3), taken3) →
        vEnd consumer core taken =
          match r with
          | .ok none => ((.ok .continue, core3.reset), taken3)
          | .ok (some located) => ((.ok (.break located), core3.reset), taken3)
          | .error f => ((.error ⟨f.cause, f.span, none⟩, core3), taken3)) := by
  have hw : withEq core.activity = ⟨_, ha⟩ := Subtype.ext ha
  have hft := finish_token hf
  have hl : l.Valid := .inl (by rw [hft.1, hft.2]; exact core.started ha)
  have hfs : finishS consumer.concrete p core.location = ⟨.token l, hft⟩ := Subtype.ext hf
  refine ⟨hl, ?_, ?_, ?_⟩
  · intro f core2 taken2 hr
    have hrun := run_of_vRun consumer hr
    simp only [idleAt] at hrun
    simp only [vEnd, lexEofStep, lexEnd, ha, Bool.false_eq_true, ite_false, pure_bind]
    rw [hw]
    simp only [isConcrete_answering]
    rw [hfs]
    simp only [vRun, StateT.run_bind]
    rw [hrun]
    rfl
  · intro located core2 taken2 hr
    have hrun := run_of_vRun consumer hr
    simp only [idleAt] at hrun
    simp only [vEnd, lexEofStep, lexEnd, ha, Bool.false_eq_true, ite_false, pure_bind]
    rw [hw]
    simp only [isConcrete_answering]
    rw [hfs]
    simp only [vRun, StateT.run_bind]
    rw [hrun]
    rfl
  · intro core2 taken2 hh2 hr r core3 taken3 hr3
    have hrun := run_of_vRun consumer hr
    have hrun3 := run_of_vRun consumer hr3
    simp only [idleAt] at hrun
    simp only [vEnd, lexEofStep, lexEnd, ha, Bool.false_eq_true, ite_false, pure_bind]
    rw [hw]
    simp only [isConcrete_answering]
    rw [hfs]
    simp only [vRun, StateT.run_bind]
    rw [hrun]
    simp only [id_bind, hh2, Bool.false_eq_true, ite_false, StateT.run_bind]
    rw [hrun3]
    cases r with
    | error f => rfl
    | ok held => cases held <;> rfl

end

end BSmtLib.Facts.Proofs.Lexer.Consumers.VEnd
