namespace BSmtLib

/-- Whether an operation should go on or stop early with a value. -/
/- LEAN: Rust's `std::ops::ControlFlow<B>`, which Lean's standard library lacks. `continue`
and `break` are keywords, so the constructor names are quoted where they are declared;
they are used as `.continue` and `.break value`. -/
inductive ControlFlow (β : Type) where
  /-- Go on as normal. -/
  | «continue»
  /-- Stop with the value. -/
  | «break» (value : β)
  deriving BEq, Repr, Inhabited

end BSmtLib
