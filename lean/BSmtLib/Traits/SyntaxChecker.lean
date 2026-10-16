module

public import BSmtLib.Traits.CommandHandler

public section

/- LEAN: in Rust, `SmtSyntaxChecker` is in `traits.rs` with the handler classes. Its instance of
`CommandHandler` names the parser of no values (`Empty`) as its non-standard parser, whose
`Parse` instance is in `BSmtLib.Parser`, so it has a module of its own here, after
`Traits.CommandHandler`; the root module `BSmtLib` imports it. -/

namespace BSmtLib.Traits

/- LEAN: Rust's unit struct; its calls run in `Id`. -/
/-- A handler that checks the syntax only: every value it makes is `Unit`, every call succeeds,
and it rejects every non-standard command with its name. -/
structure SyntaxChecker where
  deriving Repr

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

end BSmtLib.Traits
