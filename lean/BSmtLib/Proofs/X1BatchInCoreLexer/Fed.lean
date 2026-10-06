import BSmtLib.Proofs.X1BatchInCoreLexer.Handed

/-!
# What the adapter's `fed` records

The adapter's `fed` feeds the slices by the calls of a lexer (`feedSlices`), which are those of
`runSlices` (`feedSlices_eq_runSlices`); fed the slices, the library's lexer has recorded what
the lexer with the batch kept in its state has recorded fed their cut, and has failed exactly
when it has (`fed_eq_cutAll`).
-/

namespace BSmtLib.Proofs.X1BatchInCoreLexer

open BSmtLib.Proofs.Adapter (Collector feedSlices fed)

/-- Whether a call failed. -/
def Called.failed {L : Type} (called : Called L) : Bool :=
  match called.1 with
  | .error _ => true
  | .ok _ => false

/-- The adapter feeds the slices before the end of the input by the calls of `runSlices`, when
its step is the lexer's call. -/
theorem feedSlices_eq_runSlices (ops : Adapter.Ops)
    (step : ops.Lexer → ByteSlice → Called ops.Lexer)
    (hstep : ∀ l slice, ops.lexSliceStep l slice = step l slice) :
    ∀ (slices : List Spec.Lexicon.Chars) (l : ops.Lexer),
      feedSlices ops l slices =
        (ops.handler (runSlices step l slices).2, (runSlices step l slices).failed)
  | [], l => rfl
  | s :: rest, l => by
    simp only [feedSlices, runSlices, hstep]
    rcases step l s.toByteArray.toByteSlice with ⟨e | flow, l'⟩
    · rfl
    · cases flow with
      | «continue» => exact feedSlices_eq_runSlices ops step hstep rest l'
      | «break» finished => exact finished.value.elim

/-- The library's lexer, fed the slices by the adapter before the end of the input, has done what
the lexer with the batch kept in its state has done fed their cut. -/
theorem fed_eq_cutAll (version : Spec.Lexicon.Version) (slices : List Spec.Lexicon.Chars) :
    fed Adapter.Lexer.ops version slices =
      fed Adapter.X1BatchInCore.ops version (Chunks.cutAll slices) := by
  simp only [fed]
  rw [feedSlices_eq_runSlices Adapter.Lexer.ops lexerStep (fun _ _ => rfl),
    feedSlices_eq_runSlices Adapter.X1BatchInCore.ops x1Step (fun _ _ => rfl)]
  obtain ⟨e, hr⟩ := runSlices_cutAll slices _ _ (lexerRel_new _ _) ⟨rfl, rfl⟩
  have key : (Adapter.Lexer.ops.handler (runSlices lexerStep
        (Adapter.Lexer.ops.new { handed := [] } (Adapter.toVersion version)) slices).2,
      (runSlices lexerStep
        (Adapter.Lexer.ops.new { handed := [] } (Adapter.toVersion version)) slices).failed) =
      (Adapter.X1BatchInCore.ops.handler (runSlices x1Step
        (Adapter.X1BatchInCore.ops.new { handed := [] } (Adapter.toVersion version))
        (Chunks.cutAll slices)).2,
      (runSlices x1Step
        (Adapter.X1BatchInCore.ops.new { handed := [] } (Adapter.toVersion version))
        (Chunks.cutAll slices)).failed) :=
    Prod.ext hr.1.symm (by
      unfold Called.failed
      exact congrArg (fun r : Except (LexError Unit) (ControlFlow (Located Empty)) =>
        match r with
        | .error _ => true
        | .ok _ => false) e)
  exact congrArg (fun p : Collector × Bool => ({ handed := p.1.handed, failed := p.2 } :
    Spec.Lexer.Fed)) key

end BSmtLib.Proofs.X1BatchInCoreLexer
