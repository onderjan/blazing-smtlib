module

public import BSmtLib.Grammar.Nodes
public import BSmtLib.Grammar.Multiple.MatchCases
public import BSmtLib.Grammar.Multiple

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
(`Symbol.intoOwned` and the like).
-/

/- LEAN: Rust's traits `SmtHandler` and `SmtCommandHandler`. The associated types are fields
of the class, and `&mut self` is the state of the monad `StateT H m` that every call runs in;
the monad `m` is an `outParam`, determined by the handler's type, as the monad of `ConsumeFrom` is.
`Sort` is a keyword of Lean, hence the quotes on the field `«Sort»`. -/

namespace BSmtLib.Handler

open BSmtLib.Grammar.Nodes BSmtLib.Lexicon.Value BSmtLib.Grammar.Multiple

/--
Handles grammar nodes (sorts, terms, etc.).

A handler is called in a post-order traversal over the SMT-LIB abstract syntax tree: it handles
the inner items (terms, sorts, etc.) first, then the outer items that only see the returned
values. It can construct the abstract syntax tree or perform any other processing, e.g.
immediately evaluating constant expressions.

Commands are handled by `Handler.CommandHandler`, which extends this class.
-/
class _root_.BSmtLib.Handler (H : Type) (m : outParam (Type → Type)) where
  /-- Error returned by the handler on failure. -/
  Error : Type
  /--
  S-expression that has been handled.

  Returned by `handleSExpr`.
  -/
  SExpr : Type
  /--
  Attribute that has been handled.

  Returned by `handleAttribute`.
  -/
  Attribute : Type
  /--
  Sort that has been handled.

  Returned by `handleSort`.
  -/
  «Sort» : Type
  /--
  Term that has been handled.

  Returned by `handleTerm`, `annotateTerm`, and the methods that end binders and `match`, such
  as `endLet`.
  -/
  Term : Type
  /--
  Scope of a binder, returned at its start and given back at its end.

  The binders are `let`, the quantifiers, `lambda`, and the cases of `match`. The body of a binder
  is handled between its start and its end, so the handler can bring the bound variables into
  scope at the start and keep in the scope what it needs to restore at the end, e.g. the
  bindings that the bound variables shadow. If reading fails within a binder, its end method is
  not called.

  A bound variable shadows the variables and user-defined function symbols of the same name in
  the enclosing scopes, but SMT-LIB prohibits it from having the name of a theory function symbol
  of the current logic. Library parsers do not check this.
  -/
  Scope : Type
  /--
  Informs the handler of the version in force.

  A caller must set the version before it calls the other methods, so that the handler can
  process the nodes by the semantics of the version. A handler starts with the default `Version`
  in force.

  `Parser.Adapter.ParseAdapter` calls this method before any other, and
  `Parser.Script.ScriptParser` calls it again when a script declares its version
  (`set-info :smt-lib-version`).
  -/
  setVersion : Version → StateT H m Unit
  /- LEAN: Rust's `handle_sort(SmtSort { ident, args })`; the fields of `SmtSort` are the
  arguments, as Lean does not unbox a structure of several fields, so a nested structure would
  be allocated for every sort handed over. -/
  /--
  Handles a sort.

  The sort is given by its identifier and its argument sorts, which are none if the sort is not
  applied.
  -/
  handleSort : Ident → Grammar.Multiple «Sort» → ExceptT Error (StateT H m) «Sort»
  /--
  Handles a term (special constant, qualified identifier, or application).

  Annotations, binders and `match` terms are terms too, but are handled by methods of their own
  because of their structure: annotations by `annotateTerm`, binders by pairs of methods that
  start and end their body, such as `startLet` and `endLet`, and `match` terms by `startMatch`
  and the methods that follow it.
  -/
  handleTerm : Grammar.Nodes.Term «Sort» Term → ExceptT Error (StateT H m) Term
  /--
  Handles an S-expression.

  S-expressions mainly occur in attribute values, e.g. `a` and `(f x)` in
  `:my-attribute (a (f x))`.
  -/
  handleSExpr : Grammar.Nodes.SExpr SExpr → ExceptT Error (StateT H m) SExpr
  /--
  Handles an attribute.

  The value is `none` for an attribute without a value, e.g. `:left-assoc`. Library parsers do
  not check well-formedness of the attribute content, e.g. that `:named` has a symbol value.
  -/
  handleAttribute : Keyword → Option (AttributeValue SExpr) →
    ExceptT Error (StateT H m) Attribute
  /--
  Annotates a term with attributes, e.g. `(! (> x 0) :named p)`.

  The caller guarantees that there is at least one attribute.

  SMT-LIB defines the name of a `:named` attribute at the annotation: the name can be used in
  what is handled after this method, in the rest of the command and after it. SMT-LIB requires
  the named term to contain no free variables and the name to be fresh, and allows `:pattern`
  only on the body of a quantified term. Library parsers do not check this.
  -/
  annotateTerm : Term → Grammar.Multiple Attribute → ExceptT Error (StateT H m) Term
  /--
  Starts a `let` term.

  The bound terms are handled outside the scope of the `let`, before this method is called: in
  `(let ((x 1) (y x)) (+ x y))`, the `x` bound to `y` is not the `x` that this `let` binds.

  SMT-LIB requires the binding names to be distinct. Library parsers do not check this.
  -/
  startLet : Bindings Term → ExceptT Error (StateT H m) Scope
  /--
  Ends a `let` term.

  Receives the scope returned by the corresponding `startLet`.
  -/
  endLet : Scope → Term → ExceptT Error (StateT H m) Term
  /--
  Starts a quantified term (`forall` or `exists`).

  The variable names need not be distinct: the binder stands for nested binders of one variable
  each, so a later variable shadows an earlier one of the same name.
  -/
  startQuantifier : QuantifierKind → SortedVars «Sort» → ExceptT Error (StateT H m) Scope
  /--
  Ends a quantified term (`forall` or `exists`).

  Receives the scope returned by the corresponding `startQuantifier`.
  -/
  endQuantifier : QuantifierKind → Scope → Term → ExceptT Error (StateT H m) Term
  /--
  Starts a `lambda` term.

  The variable names need not be distinct: the binder stands for nested binders of one variable
  each, so a later variable shadows an earlier one of the same name.

  Lambda terms were introduced in SMT-LIB 2.7.
  -/
  startLambda : SortedVars «Sort» → ExceptT Error (StateT H m) Scope
  /--
  Ends a `lambda` term.

  Receives the scope returned by the corresponding `startLambda`.

  Lambda terms were introduced in SMT-LIB 2.7.
  -/
  endLambda : Scope → Term → ExceptT Error (StateT H m) Term
  /--
  Starts a `match` term.

  The scrutinee is the term that is matched, e.g. `l` in `(match l ((nil 0) ((cons h t) h)))`. At
  least one case follows, each case started by `startMatchCase` and ended by `endMatchCase`,
  after which `endMatch` ends the `match` term. A `match` in the body of a match case is nested
  properly: it ends before the match case does.

  Match terms were introduced in SMT-LIB 2.6.
  -/
  startMatch : Term → ExceptT Error (StateT H m) Unit
  /--
  Starts a case of a `match` term.

  Returns the scope in which the body of the case is handled, e.g. with `h` and `t` bound for the
  pattern `(cons h t)`. The case belongs to the innermost `match` that has been started and not
  ended. A case ends before the next case of its `match` starts.

  A constructor pattern has at least one argument, and its arguments are variables or the
  wildcard `_`, even if a symbol has the name of a constructor, e.g. `nil` in `(cons h nil)`. A
  simple pattern, e.g. `nil` or `x`, can be a constructor or a variable: library parsers do not
  tell them apart. They do not check the names of constructors or their arities.

  SMT-LIB requires the variables of a constructor pattern to be distinct, e.g. it prohibits
  `(pair x x)`, while the wildcard can repeat, as in `(pair _ _)`. Library parsers do not check
  this.

  Match terms were introduced in SMT-LIB 2.6.
  -/
  startMatchCase : Term → Pattern → ExceptT Error (StateT H m) Scope
  /--
  Ends a case of a `match` term.

  Receives the scope returned by the corresponding `startMatchCase`. The result of this method
  is given to `endMatch` as the case, next to its pattern.

  Match terms were introduced in SMT-LIB 2.6.
  -/
  endMatchCase : Scope → Term → Term → ExceptT Error (StateT H m) Term
  /--
  Ends a `match` term.

  The cases are in the order of the input, each with its pattern and the result of
  `endMatchCase` for it. The caller guarantees that there is at least one case.

  SMT-LIB requires a variable pattern among the cases unless every constructor of the sort of the
  scrutinee has a case. Library parsers do not check this.

  Match terms were introduced in SMT-LIB 2.6.
  -/
  endMatch : Term → MatchCases Term → ExceptT Error (StateT H m) Term

/- LEAN: Rust's `SmtNonstandardCommandError`, a tuple struct with a private field, which is named
here. The constructor is private, as Rust's field is; the name is readable as `error.name`,
replacing the getters `name` and `into_name`. Rust derives `Debug` and `Clone`; a Lean value is
copied freely. -/
/--
Error due to a nonstandard command.

`SyntaxChecker` returns it for every nonstandard command.
-/
structure NonstandardCommandError where
  private mk ::
  /-- Returns the name of the nonstandard command. -/
  name : SymbolBuf
  deriving Repr

/-- Creates the error for the nonstandard command named `name`. -/
def NonstandardCommandError.new (name : SymbolBuf) : NonstandardCommandError :=
  { name }

/-- Error of a partial command handler (unsupported command or handler error). -/
inductive PartialCommandError (E : Type) where
  /-- The handler does not implement the standard command. -/
  | unsupported (command : Lexicon.Reserved.CommandNameReserved)
  /-- The handler does not implement the nonstandard command with the given name. -/
  | unsupportedNonstandard (name : SymbolBuf)
  /-- The handler failed. -/
  | handler (error : E)
  deriving Repr

/- LEAN: Rust's `From<E>`, which makes the handler's error the error `handler` where the
error of a partial command handler is expected. -/
@[no_expose] instance {E : Type} : Coe E (PartialCommandError E) := ⟨.handler⟩

/--
The length of the bytes from `i` on that are replaced by one replacement character when they are
no character: the longest start of a character's encoding there, or one byte.
-/
private def invalidLength (bytes : ByteArray) (i : Nat) : Nat :=
  -- a missing byte reads as zero, which continues no encoding
  let byte (k : Nat) : UInt8 := bytes[i + k]?.getD 0
  let first := byte 0
  if first < 0xC2 || first > 0xF4 then 1 else
  -- the range of the second byte excludes overlong encodings, surrogates and values beyond
  -- U+10FFFF
  let (low, high) : UInt8 × UInt8 :=
    if first == 0xE0 then (0xA0, 0xBF)
    else if first == 0xED then (0x80, 0x9F)
    else if first == 0xF0 then (0x90, 0xBF)
    else if first == 0xF4 then (0x80, 0x8F)
    else (0x80, 0xBF)
  if byte 1 < low || byte 1 > high then 1
  else if first < 0xE0 || byte 2 < 0x80 || byte 2 > 0xBF then 2
  else 3

/--
The bytes as UTF-8, each longest invalid sequence replaced by the replacement character U+FFFD,
as Rust's `String::from_utf8_lossy` does.
-/
private def utf8Lossy (bytes : ByteArray) : String :=
  -- each step reads at least one byte, so the bytes' size bounds the steps
  go bytes.size 0 ""
where
  go : Nat → Nat → String → String
    | 0, _, text => text
    | fuel + 1, i, text =>
      if i < bytes.size then
        match bytes.utf8DecodeChar? i with
        | some c => go fuel (i + c.utf8Size) (text.push c)
        | none => go fuel (i + invalidLength bytes i) (text.push '�')
      else text

/--
The symbol for an error message: its bytes as UTF-8, invalid sequences replaced, enclosed in
backticks, with the pipes of a quoted symbol.
-/
private def symbolText (symbol : SymbolBuf) : String :=
  let name := utf8Lossy symbol.asSlice.toByteArray
  if symbol.isQuoted then s!"`|{name}|`" else s!"`{name}`"

/- LEAN: Rust's `Display` implementations are `ToString` instances, with the same text. -/
@[no_expose] instance : ToString NonstandardCommandError :=
  ⟨fun self => s!"unsupported nonstandard command {symbolText self.name}"⟩

@[no_expose] instance {E : Type} [ToString E] : ToString (PartialCommandError E) where
  toString
    | .unsupported command => s!"unsupported command `{command.asStr}`"
    | .unsupportedNonstandard name => s!"unsupported nonstandard command {symbolText name}"
    | .handler error => toString error

end BSmtLib.Handler
