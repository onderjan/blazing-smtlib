module

public import BSmtLib.Handler.CommandHandler

public section

/- LEAN: in Rust, `SmtSyntaxChecker` is in `handler.rs` with the handler classes. Its instance of
`CommandHandler` names the parser of no values (`Empty`) as its nonstandard parser, whose
`Parse` instance is in `BSmtLib.Parser`, so it has a module of its own here, after
`Handler.CommandHandler`; the root module `BSmtLib` imports it. -/

namespace BSmtLib.Handler

/- LEAN: Rust's unit struct; its calls run in `Id`. -/
/--
Handler that checks compliance with SMT-LIB syntax.

The checker accepts every node and every standard command, and refuses every nonstandard command
with `NonstandardCommandError`.
-/
structure SyntaxChecker where
  deriving Repr, Inhabited

instance : Handler SyntaxChecker Id where
  Error := NonstandardCommandError
  SExpr := Unit
  Attribute := Unit
  «Sort» := Unit
  Term := Unit
  Scope := Unit
  setVersion _ := pure ()
  handleSort _ _ := pure ()
  handleTerm _ := pure ()
  handleSExpr _ := pure ()
  handleAttribute _ _ := pure ()
  annotateTerm _ _ := pure ()
  startLet _ := pure ()
  endLet _ _ := pure ()
  startQuantifier _ _ := pure ()
  endQuantifier _ _ _ := pure ()
  startLambda _ := pure ()
  endLambda _ _ := pure ()
  startMatch _ := pure ()
  startMatchCase _ _ := pure ()
  endMatchCase _ _ _ := pure ()
  endMatch _ _ := pure ()

instance : CommandHandler SyntaxChecker Id where
  NonstandardParser := Empty
  -- reject nonstandard command
  nonstandardCommand name := throw (NonstandardCommandError.new name.intoOwned)
  commandAssert _ := pure ()
  commandCheckSat := pure ()
  commandCheckSatAssuming _ := pure ()
  commandDeclareConst _ _ := pure ()
  startDeclareDatatype _ _ := pure ()
  endDeclareDatatype _ := pure ()
  startDeclareDatatypes _ := pure ()
  startDatatypeDeclaration _ := pure ()
  endDatatypeDeclaration _ := pure ()
  endDeclareDatatypes := pure ()
  commandDeclareFun _ _ _ := pure ()
  commandDeclareSort _ _ := pure ()
  commandDeclareSortParameter _ := pure ()
  commandDefineConst _ _ _ := pure ()
  startDefineFun _ := pure ()
  endDefineFun _ := pure ()
  startDefineFunRec _ := pure ()
  endDefineFunRec _ := pure ()
  startDefineFunsRec _ := pure ()
  startRecursiveBody _ := pure ()
  endRecursiveBody _ := pure ()
  endDefineFunsRec := pure ()
  startDefineSort _ _ := pure ()
  endDefineSort _ := pure ()
  commandEcho _ := pure ()
  commandExit := pure ()
  commandGetAssertions := pure ()
  commandGetAssignment := pure ()
  commandGetInfo _ := pure ()
  commandGetModel := pure ()
  commandGetOption _ := pure ()
  commandGetProof := pure ()
  commandGetUnsatAssumptions := pure ()
  commandGetUnsatCore := pure ()
  commandGetValue _ := pure ()
  commandPop _ := pure ()
  commandPush _ := pure ()
  commandReset := pure ()
  commandResetAssertions := pure ()
  commandSetInfo _ := pure ()
  commandSetLogic _ := pure ()
  commandSetOption _ := pure ()

end BSmtLib.Handler
