module

public import BSmtLib.Facts.Lexer.Adapters
import all BSmtLib.Lexer.Internal.WRustPort

@[expose] public section

/-!
# Weakest preconditions in the Rust port's monad, with a consumer of the formalism

The Rust port `WRustPort` runs its steps in `LexM`: interruptions as exceptions, over the bounded
lexer state, over the consumer's state. With the adapter's consumer `Answering C` for a consumer `C`
of the specification formalism (`BSmtLibSpec`), which has no state of its own and whose monad
`AnswerM` keeps the tokens it has taken, running a step from a state and the tokens taken gives one
result. `WP x s coll Q QE` says that the result satisfies `Q` if the step returns, and `QE` if it is
interrupted, with the interruption; the lemmas below take a step apart along the code.
-/

namespace BSmtLib.Facts.Proofs.Lexer.VNaiveWRustPort

/- The Rust port runs its code with the Rust lexer's operations, which every function of
its code takes as an instance. -/
attribute [scoped instance] Lexer.Internal.WRustPort.Rust.ops

end BSmtLib.Facts.Proofs.Lexer.VNaiveWRustPort

namespace BSmtLib.Facts.Proofs.Lexer.VNaiveWRustPort.WP

open BSmtLib.Facts.Lexer.Adapters
open BSmtLibSpec.Lexer (Handed)

/-- The Rust port's lexer state. -/
abbrev WCore := Lexer.Internal.WRustPort.LexerCore

/-- The bounded lexer state of a step. -/
abbrev BS (floor : Option Nat) (low : Nat) := {c : WCore // c.Bound floor low}

/-- The Rust port's monad with the adapter's consumer for `C`. -/
abbrev M (C : BSmtLibSpec.Lexer.Consumer) (floor : Option Nat) (low : Nat) :=
  Lexer.Internal.WRustPort.LexM (Answering C) AnswerM C.Result (Option C.Error) floor low

/-- An interruption of a step. -/
abbrev Intr (C : BSmtLibSpec.Lexer.Consumer) (floor : Option Nat) :=
  BSmtLib.Lexer.Internal.Interrupted C.Result (Option C.Error) floor

section

variable {C : BSmtLibSpec.Lexer.Consumer}

/-- What running the step from the state and the tokens taken gives; the consumer itself has
no state. -/
abbrev runM {floor : Option Nat} {low : Nat} {α : Type} (x : M C floor low α) (s : BS floor low)
    (coll : List Handed) : (Except (Intr C floor) α × BS floor low) × List Handed :=
  ((((x.run.run s).run {}).run coll).1.1, (((x.run.run s).run {}).run coll).2)

/-- The result of the step from the state and the tokens taken satisfies `Q` if it returns, and
`QE` if it is interrupted. -/
def _root_.BSmtLib.Facts.Proofs.Lexer.VNaiveWRustPort.WP {floor : Option Nat} {low : Nat}
    {α : Type} (x : WP.M C floor low α) (s : WP.BS floor low)
    (coll : List Handed) (Q : α → WP.BS floor low → List Handed → Prop)
    (QE : WP.Intr C floor → WP.BS floor low → List Handed → Prop) : Prop :=
  match WP.runM x s coll with
  | ((.ok a, s'), coll') => Q a s' coll'
  | ((.error e, s'), coll') => QE e s' coll'

variable {floor : Option Nat} {low : Nat} {α β : Type} {s : BS floor low} {coll : List Handed}
  {Q : β → BS floor low → List Handed → Prop}
  {QE : Intr C floor → BS floor low → List Handed → Prop}

theorem wp_pure (a : β) (h : Q a s coll) : WP (pure a : M C floor low β) s coll Q QE := h

theorem wp_bind {x : M C floor low α} {f : α → M C floor low β}
    (h : WP x s coll (fun a s' coll' => WP (f a) s' coll' Q QE) QE) :
    WP (x >>= f) s coll Q QE := by
  unfold WP at h ⊢
  simp only [runM, ExceptT.run_bind, StateT.run_bind] at h ⊢
  generalize (((x.run.run s).run {}).run coll) = r at h ⊢
  obtain ⟨⟨⟨r, s'⟩, h'⟩, coll'⟩ := r
  cases r with
  | ok a => exact h
  | error e => exact h

theorem wp_throw (e : Intr C floor) (h : QE e s coll) :
    WP (throw e : M C floor low β) s coll Q QE := h

theorem wp_mono {x : M C floor low β} {Q' : β → BS floor low → List Handed → Prop}
    {QE' : Intr C floor → BS floor low → List Handed → Prop} (h : WP x s coll Q QE)
    (hq : ∀ a s' coll', Q a s' coll' → Q' a s' coll')
    (hqe : ∀ e s' coll', QE e s' coll' → QE' e s' coll') : WP x s coll Q' QE' := by
  unfold WP at h ⊢
  generalize runM x s coll = r at h ⊢
  obtain ⟨⟨r, s'⟩, coll'⟩ := r
  cases r with
  | ok a => exact hq _ _ _ h
  | error e => exact hqe _ _ _ h

theorem wp_ite {c : Prop} [Decidable c] {x y : M C floor low β}
    (hx : c → WP x s coll Q QE) (hy : ¬ c → WP y s coll Q QE) :
    WP (if c then x else y) s coll Q QE := by
  by_cases hc : c
  · rw [ite_eq_left_of_eq_true _ _ (eq_true hc)]; exact hx hc
  · rw [ite_eq_right_of_eq_false _ _ (eq_false hc)]; exact hy hc

theorem wp_dite {c : Prop} [Decidable c] {x : c → M C floor low β} {y : ¬ c → M C floor low β}
    (hx : ∀ h, WP (x h) s coll Q QE) (hy : ∀ h, WP (y h) s coll Q QE) :
    WP (dite c x y) s coll Q QE := by
  by_cases hc : c
  · rw [dite_eq_left_of_eq_true (eq_true hc)]; exact hx _
  · rw [dite_eq_right_of_eq_false (eq_false hc)]; exact hy _

/-- Reading the lexer state. -/
theorem wp_getCore {Q : WCore → BS floor low → List Handed → Prop} (h : Q s.val s coll) :
    WP (Lexer.Internal.WRustPort.getCore (H := Answering C) (m := AnswerM) (R := C.Result)
      (E := Option C.Error)) s coll Q QE := h

/-- Changing the lexer state. -/
theorem wp_modifyCore {Q : Unit → BS floor low → List Handed → Prop} {f : WCore → WCore}
    {hf : ∀ c, c.Bound floor low → (f c).Bound floor low}
    (h : Q () ⟨f s.val, hf s.val s.property⟩ coll) :
    WP (Lexer.Internal.WRustPort.modifyCore (H := Answering C) (m := AnswerM) (R := C.Result)
      (E := Option C.Error) f hf) s coll Q QE := h

/-- Changing the lexer state with its bounds. -/
theorem wp_modifyBound {Q : Unit → BS floor low → List Handed → Prop}
    {f : (c : WCore) → c.Bound floor low → BS floor low}
    (h : Q () (f s.val s.property) coll) :
    WP (Lexer.Internal.WRustPort.modifyBound (H := Answering C) (m := AnswerM) (R := C.Result)
      (E := Option C.Error) f) s coll Q QE := h

/-- Changing the lexer state and reading a value from it. -/
theorem wp_modifyGetThe {Q : β → BS floor low → List Handed → Prop}
    {f : BS floor low → β × BS floor low} (h : Q (f s).1 (f s).2 coll) :
    WP (modifyGetThe (BS floor low) f : M C floor low β) s coll Q QE := h

/-- Reading the lexer state. -/
theorem wp_getThe {Q : BS floor low → BS floor low → List Handed → Prop} (h : Q s s coll) :
    WP (getThe (BS floor low) : M C floor low (BS floor low)) s coll Q QE := h

/-- A step of the consumer's monad. -/
theorem wp_liftConsumer {Q : β → BS floor low → List Handed → Prop}
    {x : StateT (Answering C) AnswerM β}
    (h : Q ((x.run {}).run coll).1.1 s ((x.run {}).run coll).2) :
    WP (liftM x : M C floor low β) s coll Q QE := h

end

/-! ## The Rust lexer's operations

The code of the Rust port calls the operations of its instance; with the Rust lexer's, each is
the function of the Rust port of the same name.
-/

section

variable {C : BSmtLibSpec.Lexer.Consumer} {floor : Option Nat} {low : Nat}

open BSmtLib.Lexer.Internal.WRustPort (Ops FastState)

theorem rust_loadLocals :
    Ops.loadLocals (H := Answering C) (m := AnswerM) (R := C.Result) (E := Option C.Error)
      (floor := floor) (low := low) =
      FastState.load := rfl

theorem rust_storeLocals :
    Ops.storeLocals (H := Answering C) (m := AnswerM) (R := C.Result) (E := Option C.Error)
      (floor := floor) (low := low) = FastState.store := rfl

theorem rust_eofBatch (c : Lexer.Internal.WRustPort.LexerCore) :
    Ops.eofBatch (H := Answering C) (m := AnswerM) (R := C.Result) (E := Option C.Error) c =
      ⟨(Token.Internal.TokenBatch.empty BSmtLib.Lexer.Internal.BATCH_CAPACITY).clear c.offset,
        Nat.le_of_eq (Token.Internal.TokenBatch.lastEnd_clear _ _)⟩ := rfl

end

end BSmtLib.Facts.Proofs.Lexer.VNaiveWRustPort.WP
