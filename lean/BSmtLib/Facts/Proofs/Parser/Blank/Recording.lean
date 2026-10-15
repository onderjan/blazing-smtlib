module

public import BSmtLib.Facts.Proofs.Parser.Blank.Basic
public import BSmtLib.Facts.Parser.Adapters.Handler
import all BSmtLib.Facts.Parser.Adapters.Handler

@[expose] public section

/-!
# The recording handler never fails

Every call of the recording handler (`recordingLibrary`) writes down what it is told and gives
the number of the calls before it; none fails.
-/

namespace BSmtLib.Facts.Proofs.Parser.Blank.Recording

open Basic
open BSmtLibSpec.Parser.Properties (Event)
open BSmtLib.Facts.Parser.Adapters.Handler

instance : NoFails (List Event) where
  noNonstandard parser := Empty.elim parser
  handleSort := by intros; exact ⟨fun _ => ⟨_, _, rfl⟩⟩
  handleTerm := by intros; exact ⟨fun _ => ⟨_, _, rfl⟩⟩
  handleSExpr := by intros; exact ⟨fun _ => ⟨_, _, rfl⟩⟩
  handleAttribute := by intros; exact ⟨fun _ => ⟨_, _, rfl⟩⟩
  annotateTerm := by intros; exact ⟨fun _ => ⟨_, _, rfl⟩⟩
  startLet := by intros; exact ⟨fun _ => ⟨_, _, rfl⟩⟩
  endLet := by intros; exact ⟨fun _ => ⟨_, _, rfl⟩⟩
  startQuantifier := by intros; exact ⟨fun _ => ⟨_, _, rfl⟩⟩
  endQuantifier := by intros; exact ⟨fun _ => ⟨_, _, rfl⟩⟩
  startLambda := by intros; exact ⟨fun _ => ⟨_, _, rfl⟩⟩
  endLambda := by intros; exact ⟨fun _ => ⟨_, _, rfl⟩⟩
  startMatch := by intros; exact ⟨fun _ => ⟨_, _, rfl⟩⟩
  startMatchCase := by intros; exact ⟨fun _ => ⟨_, _, rfl⟩⟩
  endMatchCase := by intros; exact ⟨fun _ => ⟨_, _, rfl⟩⟩
  endMatch := by intros; exact ⟨fun _ => ⟨_, _, rfl⟩⟩
  commandAssert := by intros; exact ⟨fun _ => ⟨_, _, rfl⟩⟩
  commandCheckSat := by intros; exact ⟨fun _ => ⟨_, _, rfl⟩⟩
  commandCheckSatAssuming := by intros; exact ⟨fun _ => ⟨_, _, rfl⟩⟩
  commandDeclareConst := by intros; exact ⟨fun _ => ⟨_, _, rfl⟩⟩
  startDeclareDatatype := by intros; exact ⟨fun _ => ⟨_, _, rfl⟩⟩
  endDeclareDatatype := by intros; exact ⟨fun _ => ⟨_, _, rfl⟩⟩
  startDeclareDatatypes := by intros; exact ⟨fun _ => ⟨_, _, rfl⟩⟩
  startDatatypeDeclaration := by intros; exact ⟨fun _ => ⟨_, _, rfl⟩⟩
  endDatatypeDeclaration := by intros; exact ⟨fun _ => ⟨_, _, rfl⟩⟩
  endDeclareDatatypes := by intros; exact ⟨fun _ => ⟨_, _, rfl⟩⟩
  commandDeclareFun := by intros; exact ⟨fun _ => ⟨_, _, rfl⟩⟩
  commandDeclareSort := by intros; exact ⟨fun _ => ⟨_, _, rfl⟩⟩
  commandDeclareSortParameter := by intros; exact ⟨fun _ => ⟨_, _, rfl⟩⟩
  commandDefineConst := by intros; exact ⟨fun _ => ⟨_, _, rfl⟩⟩
  startDefineFun := by intros; exact ⟨fun _ => ⟨_, _, rfl⟩⟩
  endDefineFun := by intros; exact ⟨fun _ => ⟨_, _, rfl⟩⟩
  startDefineFunRec := by intros; exact ⟨fun _ => ⟨_, _, rfl⟩⟩
  endDefineFunRec := by intros; exact ⟨fun _ => ⟨_, _, rfl⟩⟩
  startDefineFunsRec := by intros; exact ⟨fun _ => ⟨_, _, rfl⟩⟩
  startRecursiveBody := by intros; exact ⟨fun _ => ⟨_, _, rfl⟩⟩
  endRecursiveBody := by intros; exact ⟨fun _ => ⟨_, _, rfl⟩⟩
  endDefineFunsRec := by intros; exact ⟨fun _ => ⟨_, _, rfl⟩⟩
  startDefineSort := by intros; exact ⟨fun _ => ⟨_, _, rfl⟩⟩
  endDefineSort := by intros; exact ⟨fun _ => ⟨_, _, rfl⟩⟩
  commandEcho := by intros; exact ⟨fun _ => ⟨_, _, rfl⟩⟩
  commandExit := by intros; exact ⟨fun _ => ⟨_, _, rfl⟩⟩
  commandGetAssertions := by intros; exact ⟨fun _ => ⟨_, _, rfl⟩⟩
  commandGetAssignment := by intros; exact ⟨fun _ => ⟨_, _, rfl⟩⟩
  commandGetInfo := by intros; exact ⟨fun _ => ⟨_, _, rfl⟩⟩
  commandGetModel := by intros; exact ⟨fun _ => ⟨_, _, rfl⟩⟩
  commandGetOption := by intros; exact ⟨fun _ => ⟨_, _, rfl⟩⟩
  commandGetProof := by intros; exact ⟨fun _ => ⟨_, _, rfl⟩⟩
  commandGetUnsatAssumptions := by intros; exact ⟨fun _ => ⟨_, _, rfl⟩⟩
  commandGetUnsatCore := by intros; exact ⟨fun _ => ⟨_, _, rfl⟩⟩
  commandGetValue := by intros; exact ⟨fun _ => ⟨_, _, rfl⟩⟩
  commandPop := by intros; exact ⟨fun _ => ⟨_, _, rfl⟩⟩
  commandPush := by intros; exact ⟨fun _ => ⟨_, _, rfl⟩⟩
  commandReset := by intros; exact ⟨fun _ => ⟨_, _, rfl⟩⟩
  commandResetAssertions := by intros; exact ⟨fun _ => ⟨_, _, rfl⟩⟩
  commandSetInfo := by intros; exact ⟨fun _ => ⟨_, _, rfl⟩⟩
  commandSetLogic := by intros; exact ⟨fun _ => ⟨_, _, rfl⟩⟩
  commandSetOption := by intros; exact ⟨fun _ => ⟨_, _, rfl⟩⟩

end BSmtLib.Facts.Proofs.Parser.Blank.Recording
