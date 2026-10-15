module

public import BSmtLib.Facts.Proofs.Lexer.Consumers.VFlatten
public import BSmtLib.Facts.Proofs.Lexer.Consumers.RunE
import all BSmtLib.Lexer.Internal.VNaive

@[expose] public section

/-!
# The naive lexer does not tell how its input is cut into slices, keeping the error

`runInputE_flatten`: feeding the naive lexer the slices is feeding it their bytes as one slice,
as `VFlatten.runInput_flatten` says, with the error itself kept (`RunE.runInputE`).
-/

namespace BSmtLib.Facts.Proofs.Lexer.Consumers.VFlattenE

open BSmtLibSpec.Lexer (Handed)
open BSmtLib.Facts.Lexer.Adapters BSmtLib.Facts.Proofs.Lexer.Consumers.Alike
open BSmtLib.Facts.Proofs.Lexer.Consumers.RunE BSmtLib.Facts.Proofs.Lexer.Consumers.VFlatten
open BSmtLib.Facts.Proofs.Lexer.Consumers.VReset BSmtLib.Facts.Proofs.Lexer.Consumers.VSession
open BSmtLib.Facts.Proofs.Lexer.Consumers.VSession.Core BSmtLib.Facts.Proofs.Lexer.Consumers.VSteps
open BSmtLib.Lexer.Internal.VNaive

section
variable (consumer : BSmtLibSpec.Lexer.Consumer)

/-- Two feedings of the naive lexer that give the same result or error, take the same tokens and
leave the same lexer state, and the same lexer if they have not failed. -/
def WeakEqE (r₁ r₂ : (Except (Lexer.Error.LexError (Option consumer.Error))
    (Option (Span.Located consumer.Result)) × VNaive.lexOps.Lexer consumer) × List Handed) :
    Prop :=
  r₁.1.1 = r₂.1.1 ∧ r₁.2 = r₂.2 ∧ r₁.1.2.core = r₂.1.2.core ∧
    (r₁.1.1.isOk = true → r₁.1.2 = r₂.1.2)

theorem WeakEqE.trans {r₁ r₂ r₃ : (Except (Lexer.Error.LexError (Option consumer.Error))
    (Option (Span.Located consumer.Result)) × VNaive.lexOps.Lexer consumer) × List Handed}
    (h₁ : WeakEqE consumer r₁ r₂) (h₂ : WeakEqE consumer r₂ r₃) : WeakEqE consumer r₁ r₃ :=
  ⟨h₁.1.trans h₂.1, h₁.2.1.trans h₂.2.1, h₁.2.2.1.trans h₂.2.2.1,
    fun hf => (h₁.2.2.2 hf).trans (h₂.2.2.2 (h₁.1 ▸ hf))⟩

/-- Feeding the naive lexer the slices is feeding it their bytes as one slice. -/
theorem runInputE_flatten (ended : Bool) (slices : List BSmtLibSpec.Regex.Chars) :
    ∀ (core : Core) (held : Option (Span.Located consumer.Result)) (taken : List Handed),
        (Plain core) →
      WeakEqE consumer
        ((runInputE VNaive.lexOps (consumer := consumer) ⟨{}, core, held⟩ ended slices).run taken)
        ((runInputE VNaive.lexOps (consumer := consumer) ⟨{}, core, held⟩ ended
          [slices.flatten]).run taken) := by
  induction slices with
  | nil =>
    intro core held taken hp
    have e : (runInputE VNaive.lexOps (consumer := consumer) ⟨{}, core, held⟩ ended
        [[].flatten]).run taken =
        (runInputE VNaive.lexOps (consumer := consumer) ⟨{}, core, held⟩ ended []).run taken := by
      simp only [List.flatten_nil, runInputE, StateT.run_bind]
      rw [lexSliceStep_ops consumer core hp held [] taken]
      simp only [vBytes]
      rfl
    rw [e]
    exact ⟨rfl, rfl, rfl, fun _ => rfl⟩
  | cons slice slices ih =>
    intro core held taken hp
    simp only [List.flatten_cons, runInputE, StateT.run_bind]
    rw [lexSliceStep_ops consumer core hp held slice taken,
      lexSliceStep_ops consumer core hp held (slice ++ slices.flatten) taken,
      vBytes_append]
    have hpl := vBytes_plain consumer slice core none taken hp
    generalize vBytes consumer core none slice taken = r at hpl
    obtain ⟨⟨res, core'⟩, taken'⟩ := r
    cases res with
    | error f => exact ⟨rfl, rfl, rfl, fun _ => rfl⟩
    | ok h' =>
      simp only [idBind, withHeld_v, held_v]
      refine (ih core' (h'.or held) taken' hpl).trans consumer ?_
      simp only [runInputE, StateT.run_bind]
      rw [lexSliceStep_ops consumer core' hpl (h'.or held) slices.flatten taken',
        vBytes_held consumer core' h' slices.flatten taken']
      generalize vBytes consumer core' none slices.flatten taken' = r
      obtain ⟨⟨res, core''⟩, taken''⟩ := r
      cases res with
      | error f => exact ⟨rfl, rfl, rfl, nofun⟩
      | ok h'' =>
        simp only [idBind, withHeld_v, held_v, Option.or_assoc]
        exact ⟨rfl, rfl, rfl, fun _ => rfl⟩

end

end BSmtLib.Facts.Proofs.Lexer.Consumers.VFlattenE
