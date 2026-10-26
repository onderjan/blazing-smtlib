module

public import BSmtLib.Facts.Parser.Adapters

@[expose] public section

/-!
# Every handler of the formalism is a handler of the library

`Bridged h₀ nonstandard` (an adapter, in `Adapters.Handler`) is a library handler with no state of
its own: each of its calls turns the parser's values into those of the specification formalism
(`BSmtLibSpec`), through the bridge, and asks the formalism's handler `h₀`, in the monad `h₀` runs
in, lifted into the parser's `StateT`. A non-standard command fails with `nonstandard`. `liftHandler
h₀` is `h₀` lifted into the same monad, and the two agree (`agrees_liftHandler`), so every theorem
stated for an agreeing pair holds for every handler of the formalism.
-/

namespace BSmtLib.Facts.Proofs.Parser.Link

open BSmtLibSpec.Parser
open BSmtLibSpec.Parser.Traversal
open BSmtLib.Facts.Parser.Adapters.Bridge BSmtLib.Facts.Parser.Adapters.Handler

section

variable {m : Type → Type} [Monad m] {ε : Type} {values : Values}
variable {h₀ : Traversal.Handler m ε values} {nonstandard : ε}

/-- The bridged handler agrees with the lifted formalism handler. -/
theorem agrees_liftHandler :
    Agrees (H := Bridged h₀ nonstandard) (m := m) (liftHandler h₀ nonstandard) where
  handleSort _ _ := rfl
  handleTerm node := by cases node <;> rfl
  handleSExpr node := by cases node <;> rfl
  handleAttribute _ v := by rcases v with _ | v <;> (try cases v) <;> rfl
  annotateTerm _ _ := rfl
  startLet _ := rfl
  endLet _ _ := rfl
  startQuantifier _ _ := rfl
  endQuantifier _ _ _ := rfl
  startLambda _ := rfl
  endLambda _ _ := rfl
  startMatch _ := rfl
  startMatchCase _ _ := rfl
  endMatchCase _ _ _ := rfl
  endMatch _ _ := rfl
  setVersion _ := rfl
  commandAssert _ := rfl
  commandCheckSat := rfl
  commandCheckSatAssuming _ := rfl
  commandDeclareConst _ _ := rfl
  startDeclareDatatype _ _ := rfl
  endDeclareDatatype _ := rfl
  startDeclareDatatypes _ := rfl
  startDatatypeDeclaration _ := rfl
  endDatatypeDeclaration _ := rfl
  endDeclareDatatypes := rfl
  commandDeclareFun _ _ _ := rfl
  commandDeclareSort _ _ := rfl
  commandDeclareSortParameter _ := rfl
  commandDefineConst _ _ _ := rfl
  startDefineFun _ := rfl
  endDefineFun _ := rfl
  startDefineFunRec _ := rfl
  endDefineFunRec _ := rfl
  startDefineFunsRec _ := rfl
  startRecursiveBody _ := rfl
  endRecursiveBody _ := rfl
  endDefineFunsRec := rfl
  startDefineSort _ _ := rfl
  endDefineSort _ := rfl
  commandEcho _ := rfl
  commandExit := rfl
  commandGetAssertions := rfl
  commandGetAssignment := rfl
  commandGetInfo _ := rfl
  commandGetModel := rfl
  commandGetOption _ := rfl
  commandGetProof := rfl
  commandGetUnsatAssumptions := rfl
  commandGetUnsatCore := rfl
  commandGetValue _ := rfl
  commandPop _ := rfl
  commandPush _ := rfl
  commandReset := rfl
  commandResetAssertions := rfl
  commandSetInfo _ := rfl
  commandSetLogic _ := rfl
  commandSetOption _ := rfl

end

end BSmtLib.Facts.Proofs.Parser.Link
