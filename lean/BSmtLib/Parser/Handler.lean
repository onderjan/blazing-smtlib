import BSmtLib.Parser.Syntax

/-!
# The handler

What the parser calls, in the order the handler contract states, with the parts of each
construct already handled.

A handler is a type `H` with an instance of `Handler` (and of `CommandHandler` to be handed
commands). Its calls run in `StateT H m`, so a call reads and changes the handler, and can fail
with an error of the handler's type `Error`. The values it returns for what it is told about
are of its types `SExpr`, `Attribute`, `Sort` and `Term`; a call that brings names into scope
returns a value of its type `Scope`, which the call that ends the scope receives back.

Names and constants are handed over as views of the bytes they were written with. A view keeps
the storage it points into alive for as long as it lives, which may be the storage of a whole
batch of tokens; a handler that keeps a name for long should keep a copy of it
(`SymbolView.intoOwned` and the like).
-/

/- LEAN: Rust's traits `SmtHandler` and `SmtCommandHandler`. The associated types are fields
of the class, and `&mut self` is the state of the monad `StateT H m` that every call runs in;
the monad `m` is an `outParam`, determined by the handler's type, as the monad of `Consume` is.
`Sort` is a keyword of Lean, hence the quotes on the field `«Sort»`. -/

namespace BSmtLib.Parser

/--
The handler of the categories that terms are built from (`SmtHandler`).

A call that brings names into scope in a term (`startLet`, `startQuantifier`, `startLambda`,
`startMatchCase`) returns a scope value, which the matching end call receives back. All bindings
of a `let` and all sorted variables of a binder come in one start, in order. `startMatch` is an
early check of the scrutinee; each case start and end receives the scrutinee again, and
`endMatch` receives it with the cases, each a pattern and its handled body, at the match's `)`.

`setVersion` tells the handler the version in force, and cannot fail: the parse adapter calls it
at the start of every input, before any other call, and the script parser after each version
declaration, once the producer has switched.
-/
class Handler (H : Type) (m : outParam (Type → Type)) where
  /-- The handler's errors. -/
  Error : Type
  /-- What the handler makes of an s-expression. -/
  SExpr : Type
  /-- What the handler makes of an attribute. -/
  Attribute : Type
  /-- What the handler makes of a sort. -/
  «Sort» : Type
  /-- What the handler makes of a term. -/
  Term : Type
  /-- What the handler returns for a scope, and receives back at its end. -/
  Scope : Type
  /-- The version in force, at the start of every input and after a version declaration. -/
  setVersion : Version → StateT H m Unit
  /-- A sort: its identifier and its argument sorts, none if it is not applied. -/
  handleSort : Identifier → Array «Sort» → ExceptT Error (StateT H m) «Sort»
  /-- A term that binds nothing: a constant, a qualified identifier or an application. -/
  handleTerm : TermNode «Sort» Term → ExceptT Error (StateT H m) Term
  /-- An s-expression. -/
  handleSExpr : SExprNode SExpr → ExceptT Error (StateT H m) SExpr
  /-- An attribute: its keyword and its value, if it has one. -/
  handleAttribute : KeywordView → Option (AttributeValueNode SExpr) →
    ExceptT Error (StateT H m) Attribute
  /-- An annotated term, `(` `!` term attribute+ `)`, at its `)`. -/
  annotateTerm : Term → Array Attribute → ExceptT Error (StateT H m) Term
  /-- The bindings of a `let`, at the `)` after them, before its body. -/
  startLet : Array (Symbol × Term) → ExceptT Error (StateT H m) Scope
  /-- The end of a `let`, with its body, at its `)`. -/
  endLet : Scope → Term → ExceptT Error (StateT H m) Term
  /-- The variables of a quantifier, at the `)` after them, before its body. -/
  startQuantifier : Quantifier → Array (Symbol × «Sort») → ExceptT Error (StateT H m) Scope
  /-- The end of a quantifier, with its body, at its `)`. -/
  endQuantifier : Quantifier → Scope → Term → ExceptT Error (StateT H m) Term
  /-- The variables of a `lambda`, at the `)` after them, before its body. -/
  startLambda : Array (Symbol × «Sort») → ExceptT Error (StateT H m) Scope
  /-- The end of a `lambda`, with its body, at its `)`. -/
  endLambda : Scope → Term → ExceptT Error (StateT H m) Term
  /-- The scrutinee of a `match`, at its last token, before the first case. -/
  startMatch : Term → ExceptT Error (StateT H m) Unit
  /-- A case of a `match`: the scrutinee and the case's pattern, at the pattern's last token. -/
  startMatchCase : Term → Pattern → ExceptT Error (StateT H m) Scope
  /-- The end of a case of a `match`, with the scrutinee and its body, at the case's `)`. -/
  endMatchCase : Scope → Term → Term → ExceptT Error (StateT H m) Term
  /-- The end of a `match`: its scrutinee and its cases, at its `)`. -/
  endMatch : Term → Array (Pattern × Term) → ExceptT Error (StateT H m) Term

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
  /- LEAN: provisional. Rust hands a non-standard command to a parser that the handler
  supplies; here the handler only names the error, and the parse fails at the command's
  name. -/
  /-- The error of a command named by a symbol, which no standard command is. -/
  nonstandardCommand : Symbol → Error
  commandAssert : Term → ExceptT Error (StateT H m) Unit
  commandCheckSat : ExceptT Error (StateT H m) Unit
  commandCheckSatAssuming : Array Term → ExceptT Error (StateT H m) Unit
  commandDeclareConst : Symbol → «Sort» → ExceptT Error (StateT H m) Unit
  /-- The start of `declare-datatype`, when its sort parameters are known. -/
  startDeclareDatatype : Symbol → Array Symbol → ExceptT Error (StateT H m) Unit
  endDeclareDatatype : Array (Constructor «Sort») → ExceptT Error (StateT H m) Unit
  /-- The sorts that `declare-datatypes` declares, with their arities, at the `)` after them. -/
  startDeclareDatatypes : Array (Symbol × NumeralView) → ExceptT Error (StateT H m) Unit
  /-- The start of a datatype declaration of `declare-datatypes`, when its sort parameters
  are known. -/
  startDatatypeDeclaration : Array Symbol → ExceptT Error (StateT H m) Unit
  endDatatypeDeclaration : Array (Constructor «Sort») → ExceptT Error (StateT H m) Unit
  endDeclareDatatypes : ExceptT Error (StateT H m) Unit
  commandDeclareFun : Symbol → Array «Sort» → «Sort» → ExceptT Error (StateT H m) Unit
  commandDeclareSort : Symbol → NumeralView → ExceptT Error (StateT H m) Unit
  commandDeclareSortParameter : Symbol → ExceptT Error (StateT H m) Unit
  commandDefineConst : Symbol → «Sort» → Term → ExceptT Error (StateT H m) Unit
  /-- The signature of `define-fun`, after its result sort, before the body. -/
  startDefineFun : Signature «Sort» → ExceptT Error (StateT H m) Unit
  endDefineFun : Term → ExceptT Error (StateT H m) Unit
  /-- The signature of `define-fun-rec`, after its result sort, before the body. -/
  startDefineFunRec : Signature «Sort» → ExceptT Error (StateT H m) Unit
  endDefineFunRec : Term → ExceptT Error (StateT H m) Unit
  /-- The signatures of `define-funs-rec`, at the `)` after them. -/
  startDefineFunsRec : Array (Signature «Sort») → ExceptT Error (StateT H m) Unit
  /-- The start of a body of `define-funs-rec`, with the signature of its function: when the
  body's first token arrives. -/
  startRecursiveBody : Signature «Sort» → ExceptT Error (StateT H m) Unit
  /-- The end of a body of `define-funs-rec`, at the body's last token. -/
  endRecursiveBody : Term → ExceptT Error (StateT H m) Unit
  endDefineFunsRec : ExceptT Error (StateT H m) Unit
  /-- The name and parameters of `define-sort`, at the `)` after the parameters. -/
  startDefineSort : Symbol → Array Symbol → ExceptT Error (StateT H m) Unit
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
  commandGetValue : Array Term → ExceptT Error (StateT H m) Unit
  commandPop : NumeralView → ExceptT Error (StateT H m) Unit
  commandPush : NumeralView → ExceptT Error (StateT H m) Unit
  commandReset : ExceptT Error (StateT H m) Unit
  commandResetAssertions : ExceptT Error (StateT H m) Unit
  commandSetInfo : Attribute → ExceptT Error (StateT H m) Unit
  commandSetLogic : Symbol → ExceptT Error (StateT H m) Unit
  commandSetOption : Attribute → ExceptT Error (StateT H m) Unit

end BSmtLib.Parser
