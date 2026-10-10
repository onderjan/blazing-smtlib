import BSmtLib.Proofs.X1BatchInCoreLexer.Handed

/-!
# What the adapter's `fedInput` records

Fed the slices and then, if the input has ended, the end of the input, the library's lexer has
recorded what the lexer with the batch kept in its state has recorded fed their cut, and has
failed exactly when it has (`fedInput_eq_cutAll`).
-/

namespace BSmtLib.Proofs.X1BatchInCoreLexer

open BSmtLib.Proofs.Adapter (Collector fedInput)

/-- The library's lexer, fed by the adapter the slices and then, if the input has ended, the end
of the input, has done what the lexer with the batch kept in its state has done fed their
cut. -/
theorem fedInput_eq_cutAll (version : Spec.Lexicon.Version) (slices : List Spec.Lexicon.Chars)
    (ended : Bool) :
    fedInput Adapter.Lexer.ops version slices ended =
      fedInput Adapter.X1BatchInCore.ops version (Chunks.cutAll slices) ended := by
  simp only [fedInput]
  rw [feedInput_eq_cutAll version ended slices]

end BSmtLib.Proofs.X1BatchInCoreLexer
