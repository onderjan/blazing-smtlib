module

public import BSmtLib.Handler.CommandHandler

public section

/- LEAN: in Rust, `SmtPartialCommandHandler` is in `handler.rs` with `SmtCommandHandler`. It
names the nonstandard parser's bound `SmtParse` as `SmtCommandHandler` does, so it has a
module of its own here, next to that class's; the root module `BSmtLib` imports it. -/

namespace BSmtLib.Handler

open BSmtLib.Grammar.Nodes BSmtLib.Lexicon.Value BSmtLib.Grammar.Multiple

/- LEAN: Rust's trait `SmtPartialCommandHandler: SmtHandler<Error =
SmtPartialCommandError<Self::HandlerError>>`. The bound on the parent's `Error` is the field
`error_eq`, which `rfl` proves when the instance sets `Error` to
`PartialCommandError HandlerError`; the defaults fail through it. A default fails in the monad
`m`, so the class asks for `Monad m`, which Rust has no counterpart of. The methods that are
not given keep the defaults, as Rust's do. -/
/--
Handles a subset of SMT-LIB commands.

This class can be used to implement only a subset of SMT-LIB commands without having to
implement the handler methods for the other commands. Every instance of this class is also a
`CommandHandler`, and every command that it does not implement fails with
`PartialCommandError.unsupported` for a standard command or with
`PartialCommandError.unsupportedNonstandard` for a nonstandard command.
-/
class PartialCommandHandler (H : Type) (m : outParam (Type → Type)) [Monad m]
    extends Handler H m where
  /-- Error of the handler itself. -/
  HandlerError : Type
  /-- Proof that `Error` is `PartialCommandError HandlerError`. -/
  error_eq : Error = PartialCommandError HandlerError := by rfl
  /- LEAN: Rust's associated type `NonstandardParser: SmtParse<Self, Result = ()>`, as in
  `CommandHandler`. -/
  /--
  Parses the tokens after the name of a nonstandard command, up to and including its closing
  parenthesis.

  See `CommandHandler.NonstandardParser`.
  -/
  NonstandardParser : Type
  /-- Instance of `Parser.Parse` of `NonstandardParser`, filled in by instance search. -/
  [parseNonstandard : Parser.Parse NonstandardParser H m Error Unit]
  /--
  Returns a parser that parses a nonstandard command with the given name.

  See `CommandHandler.nonstandardCommand`.
  -/
  nonstandardCommand : Symbol → ExceptT Error (StateT H m) NonstandardParser := fun name =>
    error_eq ▸ throw (PartialCommandError.unsupportedNonstandard name.intoOwned)
  /--
  Asserts a term (`assert`).

  See `CommandHandler.commandAssert`.
  -/
  commandAssert : Term → ExceptT Error (StateT H m) Unit := fun _ =>
    error_eq ▸ throw (PartialCommandError.unsupported .assert)
  /--
  Checks satisfiability (`check-sat`).

  See `CommandHandler.commandCheckSat`.
  -/
  commandCheckSat : ExceptT Error (StateT H m) Unit :=
    error_eq ▸ throw (PartialCommandError.unsupported .checkSat)
  /--
  Checks satisfiability with additional assumptions (`check-sat-assuming`).

  See `CommandHandler.commandCheckSatAssuming`.
  -/
  commandCheckSatAssuming : Grammar.Multiple Term → ExceptT Error (StateT H m) Unit := fun _ =>
    error_eq ▸ throw (PartialCommandError.unsupported .checkSatAssuming)
  /--
  Declares a constant (`declare-const`).

  See `CommandHandler.commandDeclareConst`.
  -/
  commandDeclareConst : Symbol → «Sort» → ExceptT Error (StateT H m) Unit := fun _ _ =>
    error_eq ▸ throw (PartialCommandError.unsupported .declareConst)
  /--
  Starts a datatype declaration (`declare-datatype`).

  See `CommandHandler.startDeclareDatatype`.
  -/
  startDeclareDatatype : Symbol → Symbols → ExceptT Error (StateT H m) Unit := fun _ _ =>
    error_eq ▸ throw (PartialCommandError.unsupported .declareDatatype)
  /--
  Ends a datatype declaration (`declare-datatype`).

  See `CommandHandler.endDeclareDatatype`.
  -/
  endDeclareDatatype : Constructors «Sort» → ExceptT Error (StateT H m) Unit := fun _ =>
    error_eq ▸ throw (PartialCommandError.unsupported .declareDatatype)
  /--
  Starts datatype declarations (`declare-datatypes`).

  See `CommandHandler.startDeclareDatatypes`.
  -/
  startDeclareDatatypes : SortArities → ExceptT Error (StateT H m) Unit := fun _ =>
    error_eq ▸ throw (PartialCommandError.unsupported .declareDatatypes)
  /--
  Starts a datatype declaration (in `declare-datatypes`).

  See `CommandHandler.startDatatypeDeclaration`.
  -/
  startDatatypeDeclaration : Symbols → ExceptT Error (StateT H m) Unit := fun _ =>
    error_eq ▸ throw (PartialCommandError.unsupported .declareDatatypes)
  /--
  Ends a datatype declaration (in `declare-datatypes`).

  See `CommandHandler.endDatatypeDeclaration`.
  -/
  endDatatypeDeclaration : Constructors «Sort» → ExceptT Error (StateT H m) Unit := fun _ =>
    error_eq ▸ throw (PartialCommandError.unsupported .declareDatatypes)
  /--
  Ends datatype declarations (`declare-datatypes`).

  See `CommandHandler.endDeclareDatatypes`.
  -/
  endDeclareDatatypes : ExceptT Error (StateT H m) Unit :=
    error_eq ▸ throw (PartialCommandError.unsupported .declareDatatypes)
  /--
  Declares a function (`declare-fun`).

  See `CommandHandler.commandDeclareFun`.
  -/
  commandDeclareFun : Symbol → Grammar.Multiple «Sort» → «Sort» → ExceptT Error (StateT H m) Unit :=
    fun _ _ _ => error_eq ▸ throw (PartialCommandError.unsupported .declareFun)
  /--
  Declares a sort with an arity (`declare-sort`).

  See `CommandHandler.commandDeclareSort`.
  -/
  commandDeclareSort : Symbol → Numeral → ExceptT Error (StateT H m) Unit := fun _ _ =>
    error_eq ▸ throw (PartialCommandError.unsupported .declareSort)
  /--
  Declares a global sort parameter (`declare-sort-parameter`).

  See `CommandHandler.commandDeclareSortParameter`.
  -/
  commandDeclareSortParameter : Symbol → ExceptT Error (StateT H m) Unit := fun _ =>
    error_eq ▸ throw (PartialCommandError.unsupported .declareSortParameter)
  /--
  Defines a constant (`define-const`).

  See `CommandHandler.commandDefineConst`.
  -/
  commandDefineConst : Symbol → «Sort» → Term → ExceptT Error (StateT H m) Unit := fun _ _ _ =>
    error_eq ▸ throw (PartialCommandError.unsupported .defineConst)
  /--
  Starts a function definition (`define-fun`).

  See `CommandHandler.startDefineFun`.
  -/
  startDefineFun :
    Grammar.Multiple.FunctionSignature «Sort» → ExceptT Error (StateT H m) Unit := fun _ =>
    error_eq ▸ throw (PartialCommandError.unsupported .defineFun)
  /--
  Ends a function definition (`define-fun`).

  See `CommandHandler.endDefineFun`.
  -/
  endDefineFun : Term → ExceptT Error (StateT H m) Unit := fun _ =>
    error_eq ▸ throw (PartialCommandError.unsupported .defineFun)
  /--
  Starts a recursive function definition (`define-fun-rec`).

  See `CommandHandler.startDefineFunRec`.
  -/
  startDefineFunRec : Grammar.Multiple.FunctionSignature «Sort» → ExceptT Error (StateT H m) Unit :=
    fun _ => error_eq ▸ throw (PartialCommandError.unsupported .defineFunRec)
  /--
  Ends a recursive function definition (`define-fun-rec`).

  See `CommandHandler.endDefineFunRec`.
  -/
  endDefineFunRec : Term → ExceptT Error (StateT H m) Unit := fun _ =>
    error_eq ▸ throw (PartialCommandError.unsupported .defineFunRec)
  /--
  Starts recursive function definitions (`define-funs-rec`).

  See `CommandHandler.startDefineFunsRec`.
  -/
  startDefineFunsRec : FunctionSignatures «Sort» → ExceptT Error (StateT H m) Unit := fun _ =>
    error_eq ▸ throw (PartialCommandError.unsupported .defineFunsRec)
  /--
  Starts the body of a recursive function (in `define-funs-rec`).

  See `CommandHandler.startRecursiveBody`.
  -/
  startRecursiveBody :
    Grammar.Multiple.FunctionSignature «Sort» → ExceptT Error (StateT H m) Unit :=
    fun _ => error_eq ▸ throw (PartialCommandError.unsupported .defineFunsRec)
  /--
  Ends the body of a recursive function (in `define-funs-rec`).

  See `CommandHandler.endRecursiveBody`.
  -/
  endRecursiveBody : Term → ExceptT Error (StateT H m) Unit := fun _ =>
    error_eq ▸ throw (PartialCommandError.unsupported .defineFunsRec)
  /--
  Ends recursive function definitions (`define-funs-rec`).

  See `CommandHandler.endDefineFunsRec`.
  -/
  endDefineFunsRec : ExceptT Error (StateT H m) Unit :=
    error_eq ▸ throw (PartialCommandError.unsupported .defineFunsRec)
  /--
  Starts a sort definition (`define-sort`).

  See `CommandHandler.startDefineSort`.
  -/
  startDefineSort : Symbol → Symbols → ExceptT Error (StateT H m) Unit := fun _ _ =>
    error_eq ▸ throw (PartialCommandError.unsupported .defineSort)
  /--
  Ends a sort definition (`define-sort`).

  See `CommandHandler.endDefineSort`.
  -/
  endDefineSort : «Sort» → ExceptT Error (StateT H m) Unit := fun _ =>
    error_eq ▸ throw (PartialCommandError.unsupported .defineSort)
  /--
  Echoes a string (`echo`).

  See `CommandHandler.commandEcho`.
  -/
  commandEcho : StringContent → ExceptT Error (StateT H m) Unit := fun _ =>
    error_eq ▸ throw (PartialCommandError.unsupported .echo)
  /--
  Exits the solver (`exit`).

  See `CommandHandler.commandExit`.
  -/
  commandExit : ExceptT Error (StateT H m) Unit :=
    error_eq ▸ throw (PartialCommandError.unsupported .exit)
  /--
  Gets the assertions (`get-assertions`).

  See `CommandHandler.commandGetAssertions`.
  -/
  commandGetAssertions : ExceptT Error (StateT H m) Unit :=
    error_eq ▸ throw (PartialCommandError.unsupported .getAssertions)
  /--
  Gets the values of the named Boolean terms (`get-assignment`).

  See `CommandHandler.commandGetAssignment`.
  -/
  commandGetAssignment : ExceptT Error (StateT H m) Unit :=
    error_eq ▸ throw (PartialCommandError.unsupported .getAssignment)
  /--
  Gets information (`get-info`).

  See `CommandHandler.commandGetInfo`.
  -/
  commandGetInfo : Keyword → ExceptT Error (StateT H m) Unit := fun _ =>
    error_eq ▸ throw (PartialCommandError.unsupported .getInfo)
  /--
  Gets the model (`get-model`).

  See `CommandHandler.commandGetModel`.
  -/
  commandGetModel : ExceptT Error (StateT H m) Unit :=
    error_eq ▸ throw (PartialCommandError.unsupported .getModel)
  /--
  Gets the value of an option (`get-option`).

  See `CommandHandler.commandGetOption`.
  -/
  commandGetOption : Keyword → ExceptT Error (StateT H m) Unit := fun _ =>
    error_eq ▸ throw (PartialCommandError.unsupported .getOption)
  /--
  Gets a proof (`get-proof`).

  See `CommandHandler.commandGetProof`.
  -/
  commandGetProof : ExceptT Error (StateT H m) Unit :=
    error_eq ▸ throw (PartialCommandError.unsupported .getProof)
  /--
  Gets an unsatisfiable subset of the assumptions (`get-unsat-assumptions`).

  See `CommandHandler.commandGetUnsatAssumptions`.
  -/
  commandGetUnsatAssumptions : ExceptT Error (StateT H m) Unit :=
    error_eq ▸ throw (PartialCommandError.unsupported .getUnsatAssumptions)
  /--
  Gets an unsatisfiable core (`get-unsat-core`).

  See `CommandHandler.commandGetUnsatCore`.
  -/
  commandGetUnsatCore : ExceptT Error (StateT H m) Unit :=
    error_eq ▸ throw (PartialCommandError.unsupported .getUnsatCore)
  /--
  Gets the values of terms (`get-value`).

  See `CommandHandler.commandGetValue`.
  -/
  commandGetValue : Grammar.Multiple Term → ExceptT Error (StateT H m) Unit := fun _ =>
    error_eq ▸ throw (PartialCommandError.unsupported .getValue)
  /--
  Pops `amount` assertion levels from the assertion stack (`pop`).

  See `CommandHandler.commandPop`.
  -/
  commandPop : Numeral → ExceptT Error (StateT H m) Unit := fun _ =>
    error_eq ▸ throw (PartialCommandError.unsupported .pop)
  /--
  Pushes `amount` empty assertion levels onto the assertion stack (`push`).

  See `CommandHandler.commandPush`.
  -/
  commandPush : Numeral → ExceptT Error (StateT H m) Unit := fun _ =>
    error_eq ▸ throw (PartialCommandError.unsupported .push)
  /--
  Resets the solver to its initial state (`reset`).

  See `CommandHandler.commandReset`.
  -/
  commandReset : ExceptT Error (StateT H m) Unit :=
    error_eq ▸ throw (PartialCommandError.unsupported .reset)
  /--
  Empties the assertion stack (`reset-assertions`).

  See `CommandHandler.commandResetAssertions`.
  -/
  commandResetAssertions : ExceptT Error (StateT H m) Unit :=
    error_eq ▸ throw (PartialCommandError.unsupported .resetAssertions)
  /--
  Sets information (`set-info`).

  See `CommandHandler.commandSetInfo`.
  -/
  commandSetInfo : Attribute → ExceptT Error (StateT H m) Unit := fun _ =>
    error_eq ▸ throw (PartialCommandError.unsupported .setInfo)
  /--
  Sets the logic (`set-logic`).

  See `CommandHandler.commandSetLogic`.
  -/
  commandSetLogic : Symbol → ExceptT Error (StateT H m) Unit := fun _ =>
    error_eq ▸ throw (PartialCommandError.unsupported .setLogic)
  /--
  Sets an option (`set-option`).

  See `CommandHandler.commandSetOption`.
  -/
  commandSetOption : Attribute → ExceptT Error (StateT H m) Unit := fun _ =>
    error_eq ▸ throw (PartialCommandError.unsupported .setOption)

/- The nonstandard parser's `Parse` instance, found from the handler's. -/
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
