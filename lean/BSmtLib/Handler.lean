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
the monad `m` is an `outParam`, determined by the handler's type, as the monad of `Consume` is.
`Sort` is a keyword of Lean, hence the quotes on the field `«Sort»`. -/

namespace BSmtLib.Handler

open BSmtLib.Grammar.Nodes BSmtLib.Lexicon.Value BSmtLib.Grammar.Multiple

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
class _root_.BSmtLib.Handler (H : Type) (m : outParam (Type → Type)) where
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
  /- LEAN: Rust's `handle_sort(SmtSort { ident, args })`; the fields of `SmtSort` are the
  arguments, as Lean does not unbox a structure of several fields, so a nested structure would
  be allocated for every sort handed over. -/
  handleSort : Ident → Grammar.Multiple «Sort» → ExceptT Error (StateT H m) «Sort»
  /-- A term that binds nothing: a constant, a qualified identifier or an application. -/
  handleTerm : Grammar.Nodes.Term «Sort» Term → ExceptT Error (StateT H m) Term
  /-- An s-expression. -/
  handleSExpr : Grammar.Nodes.SExpr SExpr → ExceptT Error (StateT H m) SExpr
  /-- An attribute: its keyword and its value, if it has one. -/
  handleAttribute : Keyword → Option (AttributeValue SExpr) →
    ExceptT Error (StateT H m) Attribute
  /-- An annotated term, `(` `!` term attribute+ `)`, at its `)`. -/
  annotateTerm : Term → Grammar.Multiple Attribute → ExceptT Error (StateT H m) Term
  /-- The bindings of a `let`, at the `)` after them, before its body. -/
  startLet : Bindings Term → ExceptT Error (StateT H m) Scope
  /-- The end of a `let`, with its body, at its `)`. -/
  endLet : Scope → Term → ExceptT Error (StateT H m) Term
  /-- The variables of a quantifier, at the `)` after them, before its body. -/
  startQuantifier : QuantifierKind → SortedVars «Sort» → ExceptT Error (StateT H m) Scope
  /-- The end of a quantifier, with its body, at its `)`. -/
  endQuantifier : QuantifierKind → Scope → Term → ExceptT Error (StateT H m) Term
  /-- The variables of a `lambda`, at the `)` after them, before its body. -/
  startLambda : SortedVars «Sort» → ExceptT Error (StateT H m) Scope
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

/- LEAN: Rust's `SmtNonstandardCommandError`, a tuple struct with a private field, which is named
here. The constructor is private, as Rust's field is; the name is readable as `error.name`,
replacing the getters `name` and `into_name`. Rust derives `Debug` and `Clone`; a Lean value is
copied freely. -/
/-- The error of `SyntaxChecker`: the name of the non-standard command it rejected. -/
structure NonstandardCommandError where
  private mk ::
  /-- The command's name. -/
  name : SymbolBuf
  deriving Repr

/-- The error of the non-standard command of the name. -/
def NonstandardCommandError.new (name : SymbolBuf) : NonstandardCommandError :=
  { name }

/-- Error of a `PartialCommandHandler`. -/
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
