import BSmtLib.Proofs.Lexer.WRustPort
import BSmtLib.Proofs.Adapter

/-!
# Weakest preconditions in the Rust port's monad

The Rust port `WRustPort` runs its steps in `LexM`: interruptions as exceptions, over the
bounded lexer state, over the consumer's state. With the adapter's consumer `Collector`, whose
monad is `Id`, running a step from a state and a consumer gives one result. `WP x s coll Q QE`
says that the result satisfies `Q` if the step returns, and if it is interrupted, that the
interruption is an error, not a stop of the consumer (`IsErr`), and satisfies `QE`; the lemmas
below take a step apart along the code. Every interruption that the code raises with this
consumer is an error, as the consumer never asks to relex and has no result to finish with.


The code of the Rust port is written over a structure of operations; the Rust port runs it with
the Rust lexer's (`Rust.ops`), which is an instance in this namespace, and whose operations
unfold to the Rust port's functions (`rust_loadLocals`, `rust_storeLocals`, `rust_eofBatch`).
-/

namespace BSmtLib.Proofs.Lexer.VNaiveWRustPort

open BSmtLib.Proofs.Adapter

/- The Rust port runs its code with the Rust lexer's operations, which every function of
its code takes as an instance. -/
attribute [scoped instance] Lexer.WRustPort.Rust.ops

/-- The Rust port's lexer state. -/
abbrev WCore := Lexer.WRustPort.LexerCore

/-- The bounded lexer state of a step. -/
abbrev BS (floor : Option Nat) (low : Nat) := {c : WCore // c.Bound floor low}

/-- The Rust port's monad with the adapter's consumer. -/
abbrev M (floor : Option Nat) (low : Nat) :=
  Lexer.WRustPort.LexM Collector Id Empty Unit floor low

/-- An interruption of a step. -/
abbrev Intr (floor : Option Nat) := BSmtLib.Lexer.Interrupted Empty Unit floor

/-- What running the step from the state and the consumer gives. -/
abbrev runM {floor : Option Nat} {low : Nat} {α : Type} (x : M floor low α) (s : BS floor low)
    (coll : Collector) : (Except (Intr floor) α × BS floor low) × Collector :=
  (x.run.run s).run coll

/-- The interruption is an error, not a stop of the consumer: the adapter's consumer never
asks to relex, and has no result to finish with. -/
def IsErr {floor : Option Nat} (e : Intr floor) : Prop :=
  ∃ cause, e.result = .error cause

/-- The result of the step from the state and the consumer satisfies `Q` if it returns, and is
an error that satisfies `QE` if it is interrupted. -/
def WP {floor : Option Nat} {low : Nat} {α : Type} (x : M floor low α) (s : BS floor low)
    (coll : Collector) (Q : α → BS floor low → Collector → Prop)
    (QE : Intr floor → BS floor low → Collector → Prop) : Prop :=
  match runM x s coll with
  | ((.ok a, s'), coll') => Q a s' coll'
  | ((.error e, s'), coll') => IsErr e ∧ QE e s' coll'

section

variable {floor : Option Nat} {low : Nat} {α β : Type} {s : BS floor low} {coll : Collector}
  {Q : β → BS floor low → Collector → Prop} {QE : Intr floor → BS floor low → Collector → Prop}

theorem wp_pure (a : β) (h : Q a s coll) : WP (pure a : M floor low β) s coll Q QE := h

theorem wp_bind {x : M floor low α} {f : α → M floor low β}
    (h : WP x s coll (fun a s' coll' => WP (f a) s' coll' Q QE) QE) :
    WP (x >>= f) s coll Q QE := by
  unfold WP at h ⊢
  simp only [runM, ExceptT.run_bind, StateT.run_bind] at h ⊢
  generalize ((x.run.run s).run coll) = r at h ⊢
  obtain ⟨⟨r, s'⟩, coll'⟩ := r
  cases r with
  | ok a => exact h
  | error e => exact h

theorem wp_throw (e : Intr floor) (he : IsErr e) (h : QE e s coll) :
    WP (throw e : M floor low β) s coll Q QE := ⟨he, h⟩

theorem wp_mono {x : M floor low β} {Q' : β → BS floor low → Collector → Prop}
    {QE' : Intr floor → BS floor low → Collector → Prop} (h : WP x s coll Q QE)
    (hq : ∀ a s' coll', Q a s' coll' → Q' a s' coll')
    (hqe : ∀ e s' coll', QE e s' coll' → QE' e s' coll') : WP x s coll Q' QE' := by
  unfold WP at h ⊢
  generalize runM x s coll = r at h ⊢
  obtain ⟨⟨r, s'⟩, coll'⟩ := r
  cases r with
  | ok a => exact hq _ _ _ h
  | error e => exact ⟨h.1, hqe _ _ _ h.2⟩

theorem wp_ite {c : Prop} [Decidable c] {x y : M floor low β}
    (hx : c → WP x s coll Q QE) (hy : ¬ c → WP y s coll Q QE) :
    WP (if c then x else y) s coll Q QE := by
  by_cases hc : c
  · rw [ite_eq_left_of_eq_true _ _ (eq_true hc)]; exact hx hc
  · rw [ite_eq_right_of_eq_false _ _ (eq_false hc)]; exact hy hc

theorem wp_dite {c : Prop} [Decidable c] {x : c → M floor low β} {y : ¬ c → M floor low β}
    (hx : ∀ h, WP (x h) s coll Q QE) (hy : ∀ h, WP (y h) s coll Q QE) :
    WP (dite c x y) s coll Q QE := by
  by_cases hc : c
  · rw [dite_eq_left_of_eq_true (eq_true hc)]; exact hx _
  · rw [dite_eq_right_of_eq_false (eq_false hc)]; exact hy _

end

section

variable {floor : Option Nat} {low : Nat} {β : Type} {s : BS floor low} {coll : Collector}
  {QE : Intr floor → BS floor low → Collector → Prop}

/-- Reading the lexer state. -/
theorem wp_getCore {Q : WCore → BS floor low → Collector → Prop} (h : Q s.val s coll) :
    WP (Lexer.WRustPort.getCore (H := Collector) (m := Id) (R := Empty) (E := Unit)) s coll
      Q QE := h

/-- Changing the lexer state. -/
theorem wp_modifyCore {Q : Unit → BS floor low → Collector → Prop} {f : WCore → WCore}
    {hf : ∀ c, c.Bound floor low → (f c).Bound floor low}
    (h : Q () ⟨f s.val, hf s.val s.property⟩ coll) :
    WP (Lexer.WRustPort.modifyCore (H := Collector) (m := Id) (R := Empty) (E := Unit) f hf) s
      coll Q QE := h

/-- Changing the lexer state with its bounds. -/
theorem wp_modifyBound {Q : Unit → BS floor low → Collector → Prop}
    {f : (c : WCore) → c.Bound floor low → BS floor low}
    (h : Q () (f s.val s.property) coll) :
    WP (Lexer.WRustPort.modifyBound (H := Collector) (m := Id) (R := Empty) (E := Unit) f) s coll
      Q QE := h

/-- Changing the lexer state and reading a value from it. -/
theorem wp_modifyGetThe {Q : β → BS floor low → Collector → Prop}
    {f : BS floor low → β × BS floor low} (h : Q (f s).1 (f s).2 coll) :
    WP (modifyGetThe (BS floor low) f : M floor low β) s coll Q QE := h

/-- Reading the lexer state. -/
theorem wp_getThe {Q : BS floor low → BS floor low → Collector → Prop} (h : Q s s coll) :
    WP (getThe (BS floor low) : M floor low (BS floor low)) s coll Q QE := h

/-- A step of the consumer's monad. -/
theorem wp_liftConsumer {Q : β → BS floor low → Collector → Prop} {x : StateT Collector Id β}
    (h : Q (x.run coll).1 s (x.run coll).2) :
    WP (liftM x : M floor low β) s coll Q QE := h

end

/-! ## The Rust lexer's operations

The code of the Rust port calls the operations of its instance; with the Rust lexer's, each is
the function of the Rust port of the same name.
-/

section

variable {floor : Option Nat} {low : Nat}

open Lexer.WRustPort (Ops FastState)

theorem rust_loadLocals :
    Ops.loadLocals (H := Collector) (m := Id) (R := Empty) (E := Unit) (floor := floor)
      (low := low) =
      FastState.load := rfl

theorem rust_storeLocals :
    Ops.storeLocals (H := Collector) (m := Id) (R := Empty) (E := Unit) (floor := floor)
      (low := low) = FastState.store := rfl

theorem rust_eofBatch (c : Lexer.WRustPort.LexerCore) :
    Ops.eofBatch (H := Collector) (m := Id) (R := Empty) (E := Unit) c =
      ⟨(TokenBatch.empty BSmtLib.Lexer.BATCH_CAPACITY).clear c.offset,
        Nat.le_of_eq (TokenBatch.lastEnd_clear _ _)⟩ := rfl

end

end BSmtLib.Proofs.Lexer.VNaiveWRustPort
