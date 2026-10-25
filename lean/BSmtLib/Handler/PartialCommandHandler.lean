module

public import BSmtLib.Handler.CommandHandler

public section

/- LEAN: in Rust, `SmtPartialCommandHandler` is in `traits.rs` with `SmtCommandHandler`. It
names the non-standard parser's bound `SmtParse` as `SmtCommandHandler` does, so it has a
module of its own here, next to that class's; the root module `BSmtLib` imports it. -/

namespace BSmtLib.Handler

open BSmtLib.Grammar.Nodes BSmtLib.Lexicon.Value BSmtLib.Grammar.Multiple

/--
A command handler that implements only the commands it supports.

Every command it does not implement fails with `PartialCommandError.unsupported` naming the
command, or with `PartialCommandError.unsupportedNonstandard` for a nonstandard command.
Each implementor is a `CommandHandler`.
-/
/- LEAN: Rust's trait `SmtPartialCommandHandler: SmtHandler<Error =
SmtPartialCommandError<Self::HandlerError>>`. The bound on the parent's `Error` is the field
`error_eq`, which `rfl` proves when the instance sets `Error` to
`PartialCommandError HandlerError`; the defaults fail through it. A default fails in the monad
`m`, so the class asks for `Monad m`, which Rust has no counterpart of. The methods that are
not given keep the defaults, as Rust's do. -/
class PartialCommandHandler (H : Type) (m : outParam (Type → Type)) [Monad m]
    extends Handler H m where
  /-- The error of the handler itself. -/
  HandlerError : Type
  /-- The handler's errors are the partial handler's errors over its own. -/
  error_eq : Error = PartialCommandError HandlerError := by rfl
  /- LEAN: Rust's associated type `NonstandardParser: SmtParse<Self, Result = ()>`, as in
  `CommandHandler`. -/
  NonstandardParser : Type
  [parseNonstandard : Parser.Parse NonstandardParser H m Error Unit]
  /-- Returns a parser that parses a non-standard command with the given name. -/
  nonstandardCommand : Symbol → ExceptT Error (StateT H m) NonstandardParser := fun name =>
    error_eq ▸ throw (PartialCommandError.unsupportedNonstandard name.intoOwned)
  commandAssert : Term → ExceptT Error (StateT H m) Unit := fun _ =>
    error_eq ▸ throw (PartialCommandError.unsupported .assert)
  commandCheckSat : ExceptT Error (StateT H m) Unit :=
    error_eq ▸ throw (PartialCommandError.unsupported .checkSat)
  commandCheckSatAssuming : Grammar.Multiple Term → ExceptT Error (StateT H m) Unit := fun _ =>
    error_eq ▸ throw (PartialCommandError.unsupported .checkSatAssuming)
  commandDeclareConst : Symbol → «Sort» → ExceptT Error (StateT H m) Unit := fun _ _ =>
    error_eq ▸ throw (PartialCommandError.unsupported .declareConst)
  startDeclareDatatype : Symbol → Symbols → ExceptT Error (StateT H m) Unit := fun _ _ =>
    error_eq ▸ throw (PartialCommandError.unsupported .declareDatatype)
  endDeclareDatatype : Constructors «Sort» → ExceptT Error (StateT H m) Unit := fun _ =>
    error_eq ▸ throw (PartialCommandError.unsupported .declareDatatype)
  startDeclareDatatypes : SortArities → ExceptT Error (StateT H m) Unit := fun _ =>
    error_eq ▸ throw (PartialCommandError.unsupported .declareDatatypes)
  startDatatypeDeclaration : Symbols → ExceptT Error (StateT H m) Unit := fun _ =>
    error_eq ▸ throw (PartialCommandError.unsupported .declareDatatypes)
  endDatatypeDeclaration : Constructors «Sort» → ExceptT Error (StateT H m) Unit := fun _ =>
    error_eq ▸ throw (PartialCommandError.unsupported .declareDatatypes)
  endDeclareDatatypes : ExceptT Error (StateT H m) Unit :=
    error_eq ▸ throw (PartialCommandError.unsupported .declareDatatypes)
  commandDeclareFun : Symbol → Grammar.Multiple «Sort» → «Sort» → ExceptT Error (StateT H m) Unit :=
    fun _ _ _ => error_eq ▸ throw (PartialCommandError.unsupported .declareFun)
  commandDeclareSort : Symbol → Numeral → ExceptT Error (StateT H m) Unit := fun _ _ =>
    error_eq ▸ throw (PartialCommandError.unsupported .declareSort)
  commandDeclareSortParameter : Symbol → ExceptT Error (StateT H m) Unit := fun _ =>
    error_eq ▸ throw (PartialCommandError.unsupported .declareSortParameter)
  commandDefineConst : Symbol → «Sort» → Term → ExceptT Error (StateT H m) Unit := fun _ _ _ =>
    error_eq ▸ throw (PartialCommandError.unsupported .defineConst)
  startDefineFun :
    Grammar.Multiple.FunctionSignature «Sort» → ExceptT Error (StateT H m) Unit := fun _ =>
    error_eq ▸ throw (PartialCommandError.unsupported .defineFun)
  endDefineFun : Term → ExceptT Error (StateT H m) Unit := fun _ =>
    error_eq ▸ throw (PartialCommandError.unsupported .defineFun)
  startDefineFunRec : Grammar.Multiple.FunctionSignature «Sort» → ExceptT Error (StateT H m) Unit :=
    fun _ => error_eq ▸ throw (PartialCommandError.unsupported .defineFunRec)
  endDefineFunRec : Term → ExceptT Error (StateT H m) Unit := fun _ =>
    error_eq ▸ throw (PartialCommandError.unsupported .defineFunRec)
  startDefineFunsRec : FunctionSignatures «Sort» → ExceptT Error (StateT H m) Unit := fun _ =>
    error_eq ▸ throw (PartialCommandError.unsupported .defineFunsRec)
  startRecursiveBody :
    Grammar.Multiple.FunctionSignature «Sort» → ExceptT Error (StateT H m) Unit :=
    fun _ => error_eq ▸ throw (PartialCommandError.unsupported .defineFunsRec)
  endRecursiveBody : Term → ExceptT Error (StateT H m) Unit := fun _ =>
    error_eq ▸ throw (PartialCommandError.unsupported .defineFunsRec)
  endDefineFunsRec : ExceptT Error (StateT H m) Unit :=
    error_eq ▸ throw (PartialCommandError.unsupported .defineFunsRec)
  startDefineSort : Symbol → Symbols → ExceptT Error (StateT H m) Unit := fun _ _ =>
    error_eq ▸ throw (PartialCommandError.unsupported .defineSort)
  endDefineSort : «Sort» → ExceptT Error (StateT H m) Unit := fun _ =>
    error_eq ▸ throw (PartialCommandError.unsupported .defineSort)
  commandEcho : StringContent → ExceptT Error (StateT H m) Unit := fun _ =>
    error_eq ▸ throw (PartialCommandError.unsupported .echo)
  commandExit : ExceptT Error (StateT H m) Unit :=
    error_eq ▸ throw (PartialCommandError.unsupported .exit)
  commandGetAssertions : ExceptT Error (StateT H m) Unit :=
    error_eq ▸ throw (PartialCommandError.unsupported .getAssertions)
  commandGetAssignment : ExceptT Error (StateT H m) Unit :=
    error_eq ▸ throw (PartialCommandError.unsupported .getAssignment)
  commandGetInfo : Keyword → ExceptT Error (StateT H m) Unit := fun _ =>
    error_eq ▸ throw (PartialCommandError.unsupported .getInfo)
  commandGetModel : ExceptT Error (StateT H m) Unit :=
    error_eq ▸ throw (PartialCommandError.unsupported .getModel)
  commandGetOption : Keyword → ExceptT Error (StateT H m) Unit := fun _ =>
    error_eq ▸ throw (PartialCommandError.unsupported .getOption)
  commandGetProof : ExceptT Error (StateT H m) Unit :=
    error_eq ▸ throw (PartialCommandError.unsupported .getProof)
  commandGetUnsatAssumptions : ExceptT Error (StateT H m) Unit :=
    error_eq ▸ throw (PartialCommandError.unsupported .getUnsatAssumptions)
  commandGetUnsatCore : ExceptT Error (StateT H m) Unit :=
    error_eq ▸ throw (PartialCommandError.unsupported .getUnsatCore)
  commandGetValue : Grammar.Multiple Term → ExceptT Error (StateT H m) Unit := fun _ =>
    error_eq ▸ throw (PartialCommandError.unsupported .getValue)
  commandPop : Numeral → ExceptT Error (StateT H m) Unit := fun _ =>
    error_eq ▸ throw (PartialCommandError.unsupported .pop)
  commandPush : Numeral → ExceptT Error (StateT H m) Unit := fun _ =>
    error_eq ▸ throw (PartialCommandError.unsupported .push)
  commandReset : ExceptT Error (StateT H m) Unit :=
    error_eq ▸ throw (PartialCommandError.unsupported .reset)
  commandResetAssertions : ExceptT Error (StateT H m) Unit :=
    error_eq ▸ throw (PartialCommandError.unsupported .resetAssertions)
  commandSetInfo : Attribute → ExceptT Error (StateT H m) Unit := fun _ =>
    error_eq ▸ throw (PartialCommandError.unsupported .setInfo)
  commandSetLogic : Symbol → ExceptT Error (StateT H m) Unit := fun _ =>
    error_eq ▸ throw (PartialCommandError.unsupported .setLogic)
  commandSetOption : Attribute → ExceptT Error (StateT H m) Unit := fun _ =>
    error_eq ▸ throw (PartialCommandError.unsupported .setOption)

/- The non-standard parser's `Parse` instance, found from the handler's. -/
attribute [instance_reducible, instance] PartialCommandHandler.parseNonstandard

/- LEAN: Rust's blanket `impl<T: SmtPartialCommandHandler> SmtCommandHandler for T`. The class
`PartialCommandHandler` is not found from `CommandHandler`, so the search cannot loop. -/
instance {H : Type} {m : Type → Type} [Monad m] [PartialCommandHandler H m] :
    CommandHandler H m where
  NonstandardParser := PartialCommandHandler.NonstandardParser H
  nonstandardCommand := PartialCommandHandler.nonstandardCommand
  commandAssert := PartialCommandHandler.commandAssert
  commandCheckSat := PartialCommandHandler.commandCheckSat
  commandCheckSatAssuming := PartialCommandHandler.commandCheckSatAssuming
  commandDeclareConst := PartialCommandHandler.commandDeclareConst
  startDeclareDatatype := PartialCommandHandler.startDeclareDatatype
  endDeclareDatatype := PartialCommandHandler.endDeclareDatatype
  startDeclareDatatypes := PartialCommandHandler.startDeclareDatatypes
  startDatatypeDeclaration := PartialCommandHandler.startDatatypeDeclaration
  endDatatypeDeclaration := PartialCommandHandler.endDatatypeDeclaration
  endDeclareDatatypes := PartialCommandHandler.endDeclareDatatypes
  commandDeclareFun := PartialCommandHandler.commandDeclareFun
  commandDeclareSort := PartialCommandHandler.commandDeclareSort
  commandDeclareSortParameter := PartialCommandHandler.commandDeclareSortParameter
  commandDefineConst := PartialCommandHandler.commandDefineConst
  startDefineFun := PartialCommandHandler.startDefineFun
  endDefineFun := PartialCommandHandler.endDefineFun
  startDefineFunRec := PartialCommandHandler.startDefineFunRec
  endDefineFunRec := PartialCommandHandler.endDefineFunRec
  startDefineFunsRec := PartialCommandHandler.startDefineFunsRec
  startRecursiveBody := PartialCommandHandler.startRecursiveBody
  endRecursiveBody := PartialCommandHandler.endRecursiveBody
  endDefineFunsRec := PartialCommandHandler.endDefineFunsRec
  startDefineSort := PartialCommandHandler.startDefineSort
  endDefineSort := PartialCommandHandler.endDefineSort
  commandEcho := PartialCommandHandler.commandEcho
  commandExit := PartialCommandHandler.commandExit
  commandGetAssertions := PartialCommandHandler.commandGetAssertions
  commandGetAssignment := PartialCommandHandler.commandGetAssignment
  commandGetInfo := PartialCommandHandler.commandGetInfo
  commandGetModel := PartialCommandHandler.commandGetModel
  commandGetOption := PartialCommandHandler.commandGetOption
  commandGetProof := PartialCommandHandler.commandGetProof
  commandGetUnsatAssumptions := PartialCommandHandler.commandGetUnsatAssumptions
  commandGetUnsatCore := PartialCommandHandler.commandGetUnsatCore
  commandGetValue := PartialCommandHandler.commandGetValue
  commandPop := PartialCommandHandler.commandPop
  commandPush := PartialCommandHandler.commandPush
  commandReset := PartialCommandHandler.commandReset
  commandResetAssertions := PartialCommandHandler.commandResetAssertions
  commandSetInfo := PartialCommandHandler.commandSetInfo
  commandSetLogic := PartialCommandHandler.commandSetLogic
  commandSetOption := PartialCommandHandler.commandSetOption

end BSmtLib.Handler
