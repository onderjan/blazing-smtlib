module

public import BSmtLib.Parser

public section

/- LEAN: in Rust, `SmtCommandHandler` is in `traits.rs` with `SmtHandler`. Its associated type
`NonstandardParser` is bounded by `SmtParse`, whose module imports `BSmtLib.Traits` for the
handler, so the class has a module of its own here; the root module `BSmtLib` imports it. -/

namespace BSmtLib.Traits

open BSmtLib.Nodes BSmtLib.Plain BSmtLib.Multiple

/--
The handler of commands and scripts (`SmtCommandHandler`). Commands bring no scope values.

Every command has calls of its own, `declare-const`, `define-const`, `check-sat`,
`define-fun-rec` and `declare-datatype` among them, although they mean what other commands
mean: the parser never makes the calls of one command for another. Every command's last call
comes at its `)`.

`startRecursiveBody` comes when the first token of a body of `define-funs-rec` arrives, before
the parser looks at it, and is the only call made at a token's arrival; a `)` gets no such call.
-/
class CommandHandler (H : Type) (m : outParam (Type → Type)) extends Handler H m where
  /- LEAN: Rust's associated type `NonstandardParser: SmtParse<Self, Result = ()>`: the type is
  a field, and its bound an instance field, filled in by instance search. -/
  NonstandardParser : Type
  [parseNonstandard : Parser.Parse NonstandardParser H m Error Unit]
  /-- Returns a parser that parses a non-standard command with the given name. -/
  nonstandardCommand : SymbolView → ExceptT Error (StateT H m) NonstandardParser
  commandAssert : Term → ExceptT Error (StateT H m) Unit
  commandCheckSat : ExceptT Error (StateT H m) Unit
  commandCheckSatAssuming : Multiple Term → ExceptT Error (StateT H m) Unit
  commandDeclareConst : SymbolView → «Sort» → ExceptT Error (StateT H m) Unit
  /-- The start of `declare-datatype`, when its sort parameters are known. -/
  startDeclareDatatype : SymbolView → SymbolsView → ExceptT Error (StateT H m) Unit
  endDeclareDatatype : ConstructorsView «Sort» → ExceptT Error (StateT H m) Unit
  /-- The sorts that `declare-datatypes` declares, with their arities, at the `)` after them. -/
  startDeclareDatatypes : SortAritiesView → ExceptT Error (StateT H m) Unit
  /-- The start of a datatype declaration of `declare-datatypes`, when its sort parameters
  are known. -/
  startDatatypeDeclaration : SymbolsView → ExceptT Error (StateT H m) Unit
  endDatatypeDeclaration : ConstructorsView «Sort» → ExceptT Error (StateT H m) Unit
  endDeclareDatatypes : ExceptT Error (StateT H m) Unit
  commandDeclareFun : SymbolView → Multiple «Sort» → «Sort» → ExceptT Error (StateT H m) Unit
  commandDeclareSort : SymbolView → NumeralView → ExceptT Error (StateT H m) Unit
  commandDeclareSortParameter : SymbolView → ExceptT Error (StateT H m) Unit
  commandDefineConst : SymbolView → «Sort» → Term → ExceptT Error (StateT H m) Unit
  /-- The signature of `define-fun`, after its result sort, before the body. -/
  startDefineFun : Signature «Sort» → ExceptT Error (StateT H m) Unit
  endDefineFun : Term → ExceptT Error (StateT H m) Unit
  /-- The signature of `define-fun-rec`, after its result sort, before the body. -/
  startDefineFunRec : Signature «Sort» → ExceptT Error (StateT H m) Unit
  endDefineFunRec : Term → ExceptT Error (StateT H m) Unit
  /-- The signatures of `define-funs-rec`, at the `)` after them. -/
  startDefineFunsRec : FunctionSignaturesView «Sort» → ExceptT Error (StateT H m) Unit
  /-- The start of a body of `define-funs-rec`, with the signature of its function: when the
  body's first token arrives. -/
  startRecursiveBody : Signature «Sort» → ExceptT Error (StateT H m) Unit
  /-- The end of a body of `define-funs-rec`, at the body's last token. -/
  endRecursiveBody : Term → ExceptT Error (StateT H m) Unit
  endDefineFunsRec : ExceptT Error (StateT H m) Unit
  /-- The name and parameters of `define-sort`, at the `)` after the parameters. -/
  startDefineSort : SymbolView → SymbolsView → ExceptT Error (StateT H m) Unit
  endDefineSort : «Sort» → ExceptT Error (StateT H m) Unit
  commandEcho : StringContentView → ExceptT Error (StateT H m) Unit
  commandExit : ExceptT Error (StateT H m) Unit
  commandGetAssertions : ExceptT Error (StateT H m) Unit
  commandGetAssignment : ExceptT Error (StateT H m) Unit
  commandGetInfo : KeywordView → ExceptT Error (StateT H m) Unit
  commandGetModel : ExceptT Error (StateT H m) Unit
  commandGetOption : KeywordView → ExceptT Error (StateT H m) Unit
  commandGetProof : ExceptT Error (StateT H m) Unit
  commandGetUnsatAssumptions : ExceptT Error (StateT H m) Unit
  commandGetUnsatCore : ExceptT Error (StateT H m) Unit
  commandGetValue : Multiple Term → ExceptT Error (StateT H m) Unit
  commandPop : NumeralView → ExceptT Error (StateT H m) Unit
  commandPush : NumeralView → ExceptT Error (StateT H m) Unit
  commandReset : ExceptT Error (StateT H m) Unit
  commandResetAssertions : ExceptT Error (StateT H m) Unit
  commandSetInfo : Attribute → ExceptT Error (StateT H m) Unit
  commandSetLogic : SymbolView → ExceptT Error (StateT H m) Unit
  commandSetOption : Attribute → ExceptT Error (StateT H m) Unit

/- The non-standard parser's `Parse` instance, found from the handler's. -/
attribute [instance_reducible, instance] CommandHandler.parseNonstandard

end BSmtLib.Traits
