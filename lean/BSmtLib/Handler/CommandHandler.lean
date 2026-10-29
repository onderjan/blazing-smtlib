module

public import BSmtLib.Parser

public section

/- LEAN: in Rust, `SmtCommandHandler` is in `handler.rs` with `SmtHandler`. Its associated type
`NonstandardParser` is bounded by `SmtParse`, whose module imports `BSmtLib.Handler` for the
handler, so the class has a module of its own here; the root module `BSmtLib` imports it. -/

namespace BSmtLib.Handler

open BSmtLib.Grammar.Nodes BSmtLib.Lexicon.Value BSmtLib.Grammar.Multiple

/--
Handles SMT-LIB commands.

A command handler is a `Handler` that also handles the commands of a script, e.g.
`commandAssert` gets the term that the command asserts. Such a method is called once the command
has been read to its closing parenthesis.

A definition or a datatype declaration is handled by a pair of methods instead, e.g.
`startDefineFun` and `endDefineFun`: the start method is called before the body is handled, so
that the handler can bring the parameters into scope, and the end method, like the other
methods, once the command has been read to its closing parenthesis. If reading fails within a
command, the methods that would follow are not called.

A command introduced in a later version than the one in force is not standard: its name is a
symbol, so it is handled by `nonstandardCommand`.

For only implementing a partial list of SMT-LIB commands, `PartialCommandHandler` can be used:
it is a command handler that fails on unimplemented commands with
`PartialCommandError.unsupported`.
-/
class CommandHandler (H : Type) (m : outParam (Type → Type)) extends Handler H m where
  /- LEAN: Rust's associated type `NonstandardParser: SmtParse<Self, Result = ()>`: the type is
  a field, and its bound an instance field, filled in by instance search. -/
  /--
  Parses the tokens after the name of a nonstandard command, up to and including its closing
  parenthesis.

  An example is a `Parser.Command.CommandPayloadParser` with a rule whose parser is a
  `Parser.Category.Combinator.ClosedParser`. A handler that refuses every nonstandard command can
  use `Empty`.
  -/
  NonstandardParser : Type
  /-- Instance of `Parser.Parse` of `NonstandardParser`, filled in by instance search. -/
  [parseNonstandard : Parser.Parse NonstandardParser H m Error Unit]
  /--
  Returns a parser that parses a nonstandard command with the given name.

  A command is nonstandard if its name is a symbol rather than the reserved word of a standard
  command. This includes a quoted symbol spelled like one, e.g. `|assert|`, and the name of a
  command introduced in a later version than the one in force, e.g. `define-const` before
  SMT-LIB 2.7.
  -/
  nonstandardCommand : Symbol → ExceptT Error (StateT H m) NonstandardParser
  /-- Asserts a term (`assert`). -/
  commandAssert : Term → ExceptT Error (StateT H m) Unit
  /--
  Checks satisfiability (`check-sat`).

  The command has the same semantic effect as `check-sat-assuming` without assumptions.
  -/
  commandCheckSat : ExceptT Error (StateT H m) Unit
  /--
  Checks satisfiability with additional assumptions (`check-sat-assuming`).

  The assumptions hold for this check only, together with the assertions. There may be none.

  The command was introduced in SMT-LIB 2.5. Before SMT-LIB 2.7, an assumption must be a symbol
  or its negation, e.g. `p` or `(not p)`: library parsers accept no other term there, and hand
  over each assumption as a term.
  -/
  commandCheckSatAssuming : Grammar.Multiple Term → ExceptT Error (StateT H m) Unit
  /--
  Declares a constant (`declare-const`).

  The command has the same semantic effect as `declare-fun` without parameters, e.g.
  `(declare-const c Int)` as `(declare-fun c () Int)`.

  The command was introduced in SMT-LIB 2.5.
  -/
  commandDeclareConst : Symbol → «Sort» → ExceptT Error (StateT H m) Unit
  /--
  Starts a datatype declaration (`declare-datatype`).

  The parameters are those after `par`, and there are none for a declaration without `par`. The
  datatype and its parameters are in scope in the selector sorts, which are handled between this
  method and `endDeclareDatatype`.

  SMT-LIB prohibits the name from being a sort symbol that is already in the current signature.
  Library parsers do not check this.

  The command has the same semantic effect as `declare-datatypes` with one datatype whose arity
  is the number of parameters.

  Datatypes were introduced in SMT-LIB 2.6.
  -/
  startDeclareDatatype : Symbol → Symbols → ExceptT Error (StateT H m) Unit
  /--
  Ends a datatype declaration (`declare-datatype`).

  The constructors are in the order of the input, each with its selectors. The caller guarantees
  that there is at least one constructor. For each constructor `c`, SMT-LIB also declares the
  tester `(_ is c)`.

  SMT-LIB prohibits the constructors and selectors from being function symbols that are already
  in the current signature, which also prohibits repeating one. Library parsers do not check
  this.

  Datatypes were introduced in SMT-LIB 2.6.
  -/
  endDeclareDatatype : Constructors «Sort» → ExceptT Error (StateT H m) Unit
  /--
  Starts datatype declarations (`declare-datatypes`).

  Receives the name and arity of each datatype, so that every datatype is in scope in every
  declaration. The declarations follow in the same order, each started by
  `startDatatypeDeclaration` and ended by `endDatatypeDeclaration`, after which
  `endDeclareDatatypes` ends the command. The caller guarantees that there is at least one
  datatype, starts no more declarations than there are datatypes, and ends the command only
  after one declaration per datatype.

  SMT-LIB prohibits the names of the datatypes from being sort symbols that are already in the
  current signature. Library parsers do not check this.

  Datatypes were introduced in SMT-LIB 2.6.
  -/
  startDeclareDatatypes : SortArities → ExceptT Error (StateT H m) Unit
  /--
  Starts a datatype declaration (in `declare-datatypes`).

  The declaration is of the datatype at the same index in `startDeclareDatatypes`. The
  parameters are those after `par`, and there are none for a declaration without `par`. They are
  in scope in the selector sorts, which are handled between this method and
  `endDatatypeDeclaration`.

  SMT-LIB requires a declaration to have `par` with as many parameters as the arity of its
  datatype if the arity is positive, and no `par` otherwise. Library parsers do not check this.
  -/
  startDatatypeDeclaration : Symbols → ExceptT Error (StateT H m) Unit
  /--
  Ends a datatype declaration (in `declare-datatypes`).

  The constructors are in the order of the input, each with its selectors. The caller guarantees
  that there is at least one constructor. For each constructor `c`, SMT-LIB also declares the
  tester `(_ is c)`.

  SMT-LIB prohibits the constructors and selectors from being function symbols that are already
  in the current signature, which also prohibits repeating one. Library parsers do not check
  this.
  -/
  endDatatypeDeclaration : Constructors «Sort» → ExceptT Error (StateT H m) Unit
  /--
  Ends datatype declarations (`declare-datatypes`).

  Datatypes were introduced in SMT-LIB 2.6.
  -/
  endDeclareDatatypes : ExceptT Error (StateT H m) Unit
  /--
  Declares a function (`declare-fun`).

  SMT-LIB prohibits the name from being a function symbol that is already in the current
  signature. Library parsers do not check this.
  -/
  commandDeclareFun : Symbol → Grammar.Multiple «Sort» → «Sort» → ExceptT Error (StateT H m) Unit
  /--
  Declares a sort with an arity (`declare-sort`).

  SMT-LIB prohibits the name from being a sort symbol or sort parameter that is already in the
  current signature. Library parsers do not check this.
  -/
  commandDeclareSort : Symbol → Numeral → ExceptT Error (StateT H m) Unit
  /--
  Declares a global sort parameter (`declare-sort-parameter`).

  SMT-LIB prohibits the name from being a sort symbol, sort parameter or theory symbol that is
  already in the current signature. Library parsers do not check this.

  The command was introduced in SMT-LIB 2.7.
  -/
  commandDeclareSortParameter : Symbol → ExceptT Error (StateT H m) Unit
  /--
  Defines a constant (`define-const`).

  The command has the same semantic effect as `define-fun` without parameters, e.g.
  `(define-const c Int 1)` as `(define-fun c () Int 1)`.

  The command was introduced in SMT-LIB 2.7.
  -/
  commandDefineConst : Symbol → «Sort» → Term → ExceptT Error (StateT H m) Unit
  /--
  Starts a function definition (`define-fun`).

  The parameters are in scope in the body, which is handled between this method and
  `endDefineFun`. The function itself is not: SMT-LIB prohibits the body from containing it, and
  the name from being a function symbol that is already in the current signature. Library
  parsers do not check this.
  -/
  startDefineFun : Grammar.Multiple.FunctionSignature «Sort» → ExceptT Error (StateT H m) Unit
  /-- Ends a function definition (`define-fun`). -/
  endDefineFun : Term → ExceptT Error (StateT H m) Unit
  /--
  Starts a recursive function definition (`define-fun-rec`).

  The function and its parameters are in scope in the body, which is handled between this method
  and `endDefineFunRec`.

  SMT-LIB prohibits the name from being a function symbol that is already in the current
  signature. Library parsers do not check this.

  The command has the same semantic effect as `define-funs-rec` with one function.

  Recursive function definitions were introduced in SMT-LIB 2.5.
  -/
  startDefineFunRec : Grammar.Multiple.FunctionSignature «Sort» → ExceptT Error (StateT H m) Unit
  /--
  Ends a recursive function definition (`define-fun-rec`).

  Recursive function definitions were introduced in SMT-LIB 2.5.
  -/
  endDefineFunRec : Term → ExceptT Error (StateT H m) Unit
  /--
  Starts recursive function definitions (`define-funs-rec`).

  The bodies follow in the order of the signatures, each started by `startRecursiveBody` and
  ended by `endRecursiveBody`, after which `endDefineFunsRec` ends the command. The caller
  guarantees that there is at least one signature, starts no more bodies than there are
  signatures, and ends the command only after one body per signature.

  The functions are in scope in every body, and the parameters of a function in its body.

  SMT-LIB requires the names of the functions to be distinct and prohibits them from being
  function symbols that are already in the current signature. Library parsers do not check this.

  Recursive function definitions were introduced in SMT-LIB 2.5.
  -/
  startDefineFunsRec : FunctionSignatures «Sort» → ExceptT Error (StateT H m) Unit
  /--
  Starts the body of a recursive function (in `define-funs-rec`).

  Receives the signature of the function whose body follows, the one at the same index in
  `startDefineFunsRec`, so that the handler can bring its parameters into scope.
  -/
  startRecursiveBody : Grammar.Multiple.FunctionSignature «Sort» → ExceptT Error (StateT H m) Unit
  /--
  Ends the body of a recursive function (in `define-funs-rec`).

  Receives the body of the function whose signature `startRecursiveBody` received.
  -/
  endRecursiveBody : Term → ExceptT Error (StateT H m) Unit
  /--
  Ends recursive function definitions (`define-funs-rec`).

  Recursive function definitions were introduced in SMT-LIB 2.5.
  -/
  endDefineFunsRec : ExceptT Error (StateT H m) Unit
  /--
  Starts a sort definition (`define-sort`).

  The parameters are in scope in the sort that follows, where they shadow the user-declared sort
  symbols and sort parameters of the same names, but not the theory sort symbols.

  SMT-LIB prohibits a parameter from being a theory sort symbol, and the name from being a sort
  symbol or sort parameter that is already in the current signature. Library parsers do not check
  this.
  -/
  startDefineSort : Symbol → Symbols → ExceptT Error (StateT H m) Unit
  /--
  Ends a sort definition (`define-sort`).

  SMT-LIB treats a later sort `(s t1 … tn)` of the defined sort symbol `s` as an abbreviation of
  this sort, with `t1`, …, `tn` substituted for the parameters.
  -/
  endDefineSort : «Sort» → ExceptT Error (StateT H m) Unit
  /--
  Echoes a string (`echo`).

  The string is given with its escapes resolved. SMT-LIB requires the string literal to be
  printed back as-is (with its quotation marks and properly escaped), so a handler that prints it
  must escape it again.

  The command was introduced in SMT-LIB 2.5.
  -/
  commandEcho : StringContent → ExceptT Error (StateT H m) Unit
  /--
  Exits the solver (`exit`).

  After calling this method, `Parser.Script.ScriptParser` discards the rest of the input, so no
  handler method is called for it.
  -/
  commandExit : ExceptT Error (StateT H m) Unit
  /-- Gets the assertions (`get-assertions`). -/
  commandGetAssertions : ExceptT Error (StateT H m) Unit
  /-- Gets the values of the named Boolean terms (`get-assignment`). -/
  commandGetAssignment : ExceptT Error (StateT H m) Unit
  /-- Gets information (`get-info`). -/
  commandGetInfo : Keyword → ExceptT Error (StateT H m) Unit
  /--
  Gets the model (`get-model`).

  The command was introduced in SMT-LIB 2.5.
  -/
  commandGetModel : ExceptT Error (StateT H m) Unit
  /-- Gets the value of an option (`get-option`). -/
  commandGetOption : Keyword → ExceptT Error (StateT H m) Unit
  /-- Gets a proof (`get-proof`). -/
  commandGetProof : ExceptT Error (StateT H m) Unit
  /--
  Gets an unsatisfiable subset of the assumptions (`get-unsat-assumptions`).

  The command was introduced in SMT-LIB 2.5.
  -/
  commandGetUnsatAssumptions : ExceptT Error (StateT H m) Unit
  /-- Gets an unsatisfiable core (`get-unsat-core`). -/
  commandGetUnsatCore : ExceptT Error (StateT H m) Unit
  /--
  Gets the values of terms (`get-value`).

  The caller guarantees that there is at least one term.

  SMT-LIB requires the terms to contain no free variables and no quantifiers. Library parsers do
  not check this.
  -/
  commandGetValue : Grammar.Multiple Term → ExceptT Error (StateT H m) Unit
  /--
  Pops `amount` assertion levels from the assertion stack (`pop`).

  If `amount` is `0`, no levels are popped.

  SMT-LIB requires `amount` to be smaller than the number of assertion levels, as the first level
  cannot be popped. Library parsers do not check this.
  -/
  commandPop : Numeral → ExceptT Error (StateT H m) Unit
  /--
  Pushes `amount` empty assertion levels onto the assertion stack (`push`).

  If `amount` is `0`, no levels are pushed.
  -/
  commandPush : Numeral → ExceptT Error (StateT H m) Unit
  /--
  Resets the solver to its initial state (`reset`).

  The command was introduced in SMT-LIB 2.5.
  -/
  commandReset : ExceptT Error (StateT H m) Unit
  /--
  Empties the assertion stack (`reset-assertions`).

  The command was introduced in SMT-LIB 2.5.
  -/
  commandResetAssertions : ExceptT Error (StateT H m) Unit
  /--
  Sets information (`set-info`).

  When a script is read, a version declaration `(set-info :smt-lib-version …)` is handled by this
  method before the version is switched: `Handler.setVersion` follows if the version is accepted,
  and reading fails otherwise.
  -/
  commandSetInfo : Attribute → ExceptT Error (StateT H m) Unit
  /-- Sets the logic (`set-logic`). -/
  commandSetLogic : Symbol → ExceptT Error (StateT H m) Unit
  /-- Sets an option (`set-option`). -/
  commandSetOption : Attribute → ExceptT Error (StateT H m) Unit

/- The nonstandard parser's `Parse` instance, found from the handler's. -/
attribute [instance_reducible, instance] CommandHandler.parseNonstandard

end BSmtLib.Handler
