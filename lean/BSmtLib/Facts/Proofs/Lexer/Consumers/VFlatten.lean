module

public import BSmtLib.Facts.Proofs.Lexer.Consumers.VReset
public import BSmtLib.Facts.Proofs.Lexer.Consumers.Alike
import all BSmtLib.Lexer.Internal.VNaive
import all BSmtLib.Span
import all BSmtLib.Lexer.Error

@[expose] public section

/-!
# The naive lexer does not tell how its input is cut into slices

`lexing_flatten`: what the adapter makes of the naive lexer depends only on the bytes of each
input, not on how they are cut into slices (`runInput_flatten`): a call on a slice is the loop
over its bytes, and the loop over two pieces is the loop over the first and then the second
(`vBytes_append`, `vBytes_held`).
-/

namespace BSmtLib.Facts.Proofs.Lexer.Consumers.VFlatten

open BSmtLibSpec.Lexer (Handed)
open BSmtLib.Facts.Lexer.Adapters BSmtLib.Facts.Proofs.Lexer.Consumers.Alike
open BSmtLib.Facts.Proofs.Lexer.Consumers.VReset BSmtLib.Facts.Proofs.Lexer.Consumers.VSession
open BSmtLib.Facts.Proofs.Lexer.Consumers.VSession.Core BSmtLib.Facts.Proofs.Lexer.Consumers.VSteps
open BSmtLib.Lexer.Internal.VNaive

section
variable (consumer : BSmtLibSpec.Lexer.Consumer)

/-- A call on a slice, as the loop over its bytes, from a lexer that lexes or discards. -/
theorem lexSliceStep_ops (core : Core) (hp : (Plain core))
    (held : Option (Span.Located consumer.Result))
    (bytes : List UInt8) (taken : List Handed) :
    (VNaive.lexOps.lexSliceStep (consumer := consumer) ⟨{}, core, held⟩
      bytes.toByteArray.toByteSlice).run taken =
      match vBytes consumer core none bytes taken with
      | ((.ok h, core'), taken') => ((.ok h, ⟨{}, core', held⟩), taken')
      | ((.error f, core'), taken') =>
        ((.error (Lexer.Error.LexerError.Internal.new f.kind f.span none), ⟨{}, core', held⟩),
          taken') := by
  rw [lexOps_lexSliceStep, lexSliceStep_vBytes consumer core hp bytes taken]
  generalize vBytes consumer core none bytes taken = r
  obtain ⟨⟨res, core'⟩, taken'⟩ := r
  cases res <;> rfl

theorem withHeld_v (core : Core) (held held' : Option (Span.Located consumer.Result)) :
    VNaive.lexOps.withHeld (consumer := consumer) ⟨{}, core, held⟩ held' = ⟨{}, core, held'⟩ :=
  rfl

theorem held_v (core : Core) (held : Option (Span.Located consumer.Result)) :
    VNaive.lexOps.held (consumer := consumer) ⟨{}, core, held⟩ = held :=
  rfl

/-- Two feedings of the naive lexer that stand alike, take the same tokens and leave the same
lexer state, and the same lexer if they have not failed. -/
def WeakEq (r₁ r₂ : (BSmtLibSpec.Lexer.Outcome consumer.Result consumer.Error ×
    VNaive.lexOps.Lexer consumer) × List Handed) : Prop :=
  r₁.1.1 = r₂.1.1 ∧ r₁.2 = r₂.2 ∧ r₁.1.2.core = r₂.1.2.core ∧
    (r₁.1.1.isFailed = false → r₁.1.2 = r₂.1.2)

theorem WeakEq.trans {r₁ r₂ r₃ : (BSmtLibSpec.Lexer.Outcome consumer.Result consumer.Error ×
    VNaive.lexOps.Lexer consumer) × List Handed} (h₁ : WeakEq consumer r₁ r₂)
    (h₂ : WeakEq consumer r₂ r₃) : WeakEq consumer r₁ r₃ :=
  ⟨h₁.1.trans h₂.1, h₁.2.1.trans h₂.2.1, h₁.2.2.1.trans h₂.2.2.1,
    fun hf => (h₁.2.2.2 hf).trans (h₂.2.2.2 (h₁.1 ▸ hf))⟩

/-- Feeding the naive lexer the slices is feeding it their bytes as one slice. -/
theorem runInput_flatten (ended : Bool) (slices : List BSmtLibSpec.Regex.Chars) :
    ∀ (core : Core) (held : Option (Span.Located consumer.Result)) (taken : List Handed),
        (Plain core) →
      WeakEq consumer
        ((VNaive.lexOps.runInput (consumer := consumer) ⟨{}, core, held⟩ ended slices).run taken)
        ((VNaive.lexOps.runInput (consumer := consumer) ⟨{}, core, held⟩ ended
          [slices.flatten]).run taken) := by
  induction slices with
  | nil =>
    intro core held taken hp
    have e : (VNaive.lexOps.runInput (consumer := consumer) ⟨{}, core, held⟩ ended
        [[].flatten]).run taken =
        (VNaive.lexOps.runInput (consumer := consumer) ⟨{}, core, held⟩ ended []).run taken := by
      simp only [List.flatten_nil, LexOps.runInput, StateT.run_bind]
      rw [lexSliceStep_ops consumer core hp held [] taken]
      simp only [vBytes]
      rfl
    rw [e]
    exact ⟨rfl, rfl, rfl, fun _ => rfl⟩
  | cons slice slices ih =>
    intro core held taken hp
    simp only [List.flatten_cons, LexOps.runInput, StateT.run_bind]
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
      simp only [LexOps.runInput, StateT.run_bind]
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

/-- The lexer the naive lexer gives the next input, after an input cut into slices, is the one
after the input as one slice. -/
theorem next_flatten {consumer : BSmtLibSpec.Lexer.Consumer} (version : Version)
    (L : VNaive.lexOps.Lexer consumer) (hp : (Plain L.core))
    (input : List BSmtLibSpec.Regex.Chars) :
    VNaive.lexOps.next consumer version L input =
      VNaive.lexOps.next consumer version L [input.flatten] := by
  unfold LexOps.next
  rw [vLexer_eta L]
  obtain ⟨e1, -, -, e4⟩ := runInput_flatten consumer true input L.core L.held [] hp
  generalize ((VNaive.lexOps.runInput ⟨{}, L.core, L.held⟩ true input).run []) = r₁ at e1 e4
  generalize ((VNaive.lexOps.runInput ⟨{}, L.core, L.held⟩ true [input.flatten]).run []) = r₂
    at e1 e4
  obtain ⟨⟨o₁, L₁⟩, t₁⟩ := r₁
  obtain ⟨⟨o₂, L₂⟩, t₂⟩ := r₂
  simp only at e1 e4
  subst e1
  cases o₁ with
  | failed f => rfl
  | _ => simp only [e4 rfl]

/-- What the adapter makes of the naive lexer depends only on the bytes of each input. -/
theorem lexing_flatten (consumer : BSmtLibSpec.Lexer.Consumer)
    (version : BSmtLibSpec.Lexicon.Version)
    (earlier : List (List BSmtLibSpec.Regex.Chars)) (slices : List BSmtLibSpec.Regex.Chars)
    (ended : Bool) :
    lexing VNaive.lexOps consumer version earlier slices ended =
      lexing VNaive.lexOps consumer version (earlier.map fun input => [input.flatten])
        [slices.flatten] ended := by
  have hfold : ∀ (inputs : List (List BSmtLibSpec.Regex.Chars)) (L : VNaive.lexOps.Lexer consumer),
      (Plain L.core) → L.core.initialVersion = toVersion version →
      inputs.foldl (VNaive.lexOps.next consumer (toVersion version)) L =
        (inputs.map fun input => [input.flatten]).foldl
          (VNaive.lexOps.next consumer (toVersion version)) L := by
    intro inputs
    induction inputs with
    | nil => intro L _ _; rfl
    | cons input inputs ih =>
      intro L hp hv
      simp only [List.foldl_cons, List.map_cons]
      rw [← next_flatten (toVersion version) L hp input]
      obtain ⟨hp', hv'⟩ := foldl_inputs_inv (consumer := consumer) (toVersion version) [input] L
        hp hv
      exact ih _ hp' hv'
  rw [lexing_def, lexing_def,
    ← hfold earlier (VNaive.lexOps.new consumer {} (toVersion version)) trivial rfl]
  obtain ⟨hp, -⟩ := foldl_inputs_inv (consumer := consumer) (toVersion version) earlier
    (VNaive.lexOps.new consumer {} (toVersion version)) trivial rfl
  generalize earlier.foldl (VNaive.lexOps.next consumer (toVersion version))
    (VNaive.lexOps.new consumer {} (toVersion version)) = L at hp ⊢
  rw [vLexer_eta L]
  obtain ⟨e1, e2, e3, -⟩ := runInput_flatten consumer ended slices L.core L.held [] hp
  simp only
  generalize ((VNaive.lexOps.runInput ⟨{}, L.core, L.held⟩ ended slices).run []) = r₁ at e1 e2 e3
  generalize ((VNaive.lexOps.runInput ⟨{}, L.core, L.held⟩ ended [slices.flatten]).run []) = r₂
    at e1 e2 e3
  obtain ⟨⟨o₁, L₁⟩, t₁⟩ := r₁
  obtain ⟨⟨o₂, L₂⟩, t₂⟩ := r₂
  simp only at e1 e2 e3 ⊢
  subst e1 e2
  have hv : VNaive.lexOps.version L₁ = VNaive.lexOps.version L₂ := by
    show L₁.core.version = L₂.core.version
    rw [e3]
  have hd : VNaive.lexOps.discardedFrom L₁ = VNaive.lexOps.discardedFrom L₂ := by
    show Lexer.Internal.VNaive.Lexer.discardedFrom L₁ = Lexer.Internal.VNaive.Lexer.discardedFrom L₂
    unfold Lexer.Internal.VNaive.Lexer.discardedFrom
    rw [e3]
  rw [hv, hd]

end BSmtLib.Facts.Proofs.Lexer.Consumers.VFlatten
