module

public import BSmtLib.Nodes
public import BSmtLib.Multiple.MatchCases
public import BSmtLib.Multiple.FunctionSignatures

public section

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

namespace BSmtLib.Traits

open BSmtLib.Nodes BSmtLib.Plain BSmtLib.Multiple

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
  setVersion : Token.Version → StateT H m Unit
  /-- A sort: its identifier and its argument sorts, none if it is not applied. -/
  /- LEAN: Rust's `handle_sort(SmtSort { ident, applied })`; the fields of `SmtSort` are the
  arguments, as Lean does not unbox a structure of several fields, so a nested structure would
  be allocated for every sort handed over. -/
  handleSort : Identifier → Sorts «Sort» → ExceptT Error (StateT H m) «Sort»
  /-- A term that binds nothing: a constant, a qualified identifier or an application. -/
  handleTerm : TermNode «Sort» Term → ExceptT Error (StateT H m) Term
  /-- An s-expression. -/
  handleSExpr : SExprNode SExpr → ExceptT Error (StateT H m) SExpr
  /-- An attribute: its keyword and its value, if it has one. -/
  handleAttribute : KeywordView → Option (AttributeValueNode SExpr) →
    ExceptT Error (StateT H m) Attribute
  /-- An annotated term, `(` `!` term attribute+ `)`, at its `)`. -/
  annotateTerm : Term → Attributes Attribute → ExceptT Error (StateT H m) Term
  /-- The bindings of a `let`, at the `)` after them, before its body. -/
  startLet : BindingsView Term → ExceptT Error (StateT H m) Scope
  /-- The end of a `let`, with its body, at its `)`. -/
  endLet : Scope → Term → ExceptT Error (StateT H m) Term
  /-- The variables of a quantifier, at the `)` after them, before its body. -/
  startQuantifier : Quantifier → SortedVarsView «Sort» → ExceptT Error (StateT H m) Scope
  /-- The end of a quantifier, with its body, at its `)`. -/
  endQuantifier : Quantifier → Scope → Term → ExceptT Error (StateT H m) Term
  /-- The variables of a `lambda`, at the `)` after them, before its body. -/
  startLambda : SortedVarsView «Sort» → ExceptT Error (StateT H m) Scope
  /-- The end of a `lambda`, with its body, at its `)`. -/
  endLambda : Scope → Term → ExceptT Error (StateT H m) Term
  /-- The scrutinee of a `match`, at its last token, before the first case. -/
  startMatch : Term → ExceptT Error (StateT H m) Unit
  /-- A case of a `match`: the scrutinee and the case's pattern, at the pattern's last token. -/
  startMatchCase : Term → Pattern → ExceptT Error (StateT H m) Scope
  /-- The end of a case of a `match`, with the scrutinee and its body, at the case's `)`. -/
  endMatchCase : Scope → Term → Term → ExceptT Error (StateT H m) Term
  /-- The end of a `match`: its scrutinee and its cases, at its `)`. -/
  endMatch : Term → MatchCases Term → ExceptT Error (StateT H m) Term

/- LEAN: Rust's `NonstandardCommandError(pub SmtSymbolBuf)`, a tuple struct, whose one field is
named here. Rust derives `Debug` and `Clone`; a Lean value is copied freely. -/
/-- The error of `SyntaxChecker`: the name of the non-standard command it rejected. -/
structure NonstandardCommandError where
  /-- The command's name. -/
  name : Symbol
  deriving Repr

end BSmtLib.Traits
