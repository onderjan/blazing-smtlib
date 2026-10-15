module

public import BSmtLib.Plain
public import BSmtLib.Token.Reserved

public section

/-!
# What the parser hands over

The data that the parser hands to its handler: names and constants as views of the bytes they
were written with, the nodes of terms, s-expressions and attribute values with their parts
already handled, and the parts of commands.
-/

/- LEAN: Rust hands borrowed views (`SmtSymbol<'a>`) over and keeps owned twins
(`SmtSymbolBuf`). Lean has no borrows: a view is a byte slice, which keeps the storage it
points into alive for as long as the view lives. -/

namespace BSmtLib.Nodes

open BSmtLib.Plain (SymbolView NumeralView DecimalView HexDigitsView BinDigitsView
  StringContentView KeywordView)

/--
A symbol: a view of its content, without the bars of a quoted symbol, and whether it was
quoted. `|abc|` and `abc` are the same symbol; the flag only records how it was written.
-/
/- LEAN: Rust's `SmtSymbol` view with `is_quoted()`. The library's `SymbolView` does not carry
the flag yet, so the parser pairs it with the flag. -/
structure Symbol where
  content : SymbolView
  quoted : Bool

/- LEAN: Rust's `Debug` of `SmtSymbol`, which writes a quoted symbol in bars around the view's
`Debug`. -/
@[no_expose] instance : Repr Symbol where
  reprPrec symbol prec :=
    if symbol.quoted then .text "|" ++ reprPrec symbol.content prec ++ .text "|"
    else reprPrec symbol.content prec

/-- An index of an indexed identifier. -/
inductive Index where
  | numeral (digits : NumeralView)
  | symbol (symbol : Symbol)
  deriving Repr

/-- An identifier: a symbol, with its indices if it is indexed. -/
/- LEAN: Rust's owned `SmtIdentBuf`; the port's name for it is not aligned with Rust's yet. -/
structure Identifier where
  symbol : Symbol
  indices : Array Index
  deriving Repr

/-- A qualified identifier: an identifier, with the sort it is qualified with by `as`, if it is
qualified. -/
structure QualifiedIdent (HandledSort : Type) where
  identifier : Identifier
  sort : Option HandledSort

/-- An identifier that is a symbol alone, not indexed. -/
/- LEAN: Rust's `SmtIdentBuf::new_simple`. -/
def Identifier.newSimple (symbol : Symbol) : Identifier :=
  { symbol, indices := #[] }

namespace QualifiedIdent

variable {HandledSort : Type}

/-- A qualified identifier that is a symbol alone, neither indexed nor qualified. -/
def newSimple (symbol : Symbol) : QualifiedIdent HandledSort :=
  { identifier := .newSimple symbol, sort := none }

/-- An identifier, not qualified. -/
def newUnqualified (identifier : Identifier) : QualifiedIdent HandledSort :=
  { identifier, sort := none }

/-- An identifier qualified with the sort. -/
def newQualified (identifier : Identifier) (sort : HandledSort) : QualifiedIdent HandledSort :=
  { identifier, sort := some sort }

end QualifiedIdent

/-- A constant, as a view of its token's content. -/
/- LEAN: Rust's `SmtSpecialConstant` and its owned `SmtSpecialConstantBuf` in one type; the
port's name for it is not aligned with Rust's yet. -/
inductive SpecConstant where
  | numeral (digits : NumeralView)
  | decimal (text : DecimalView)
  | hexadecimal (digits : HexDigitsView)
  | binary (digits : BinDigitsView)
  | string (content : StringContentView)
  deriving Repr

/-- A symbol, or the wildcard `_`, in a pattern. -/
/- LEAN: Rust's `SmtSimplePattern` and its owned `SmtSimplePatternBuf`, in one type; the port's
name for it is not aligned with Rust's yet. -/
inductive SymbolOrWildcard where
  | symbol (symbol : Symbol)
  | wildcard
  deriving Repr

/-- The pattern of a case of `match`. -/
inductive Pattern where
  | single (symbol : SymbolOrWildcard)
  | constructor (constructor : Symbol) (arguments : Array SymbolOrWildcard)
  deriving Repr

/-- The two quantifiers. -/
/- LEAN: Rust's `SmtQuantifierKind`; the port's name for it is not aligned with Rust's yet. -/
inductive Quantifier where
  | «forall»
  | «exists»
  deriving BEq, Repr

/-- A term as the handler receives it, its parts already handled. -/
/- LEAN: Rust's `SmtTerm`; the port's name for it is not aligned with Rust's yet. -/
inductive TermNode (HandledSort HandledTerm : Type) where
  | constant (constant : SpecConstant)
  /-- A qualified identifier, with its sort if it is qualified by `as`. -/
  | identifier (identifier : Identifier) (sort : Option HandledSort)
  /-- An application of a qualified identifier to at least one argument. -/
  | application (function : Identifier) (sort : Option HandledSort)
      (arguments : Array HandledTerm)
  deriving Repr

/-- An s-expression as the handler receives it, its items already handled. -/
/- LEAN: Rust's `SmtSExpr`; the port's name for it is not aligned with Rust's yet. -/
inductive SExprNode (HandledSExpr : Type) where
  | constant (constant : SpecConstant)
  | symbol (symbol : Symbol)
  | reserved (word : Token.Reserved)
  | keyword (name : KeywordView)
  | list (items : Array HandledSExpr)
  deriving Repr

/--
The value of an attribute as the handler receives it, the s-expressions of a list value already
handled. A list value is handed over as its items.
-/
/- LEAN: Rust's `SmtAttributeValue`; the port's name for it is not aligned with Rust's yet. -/
inductive AttributeValueNode (HandledSExpr : Type) where
  | constant (constant : SpecConstant)
  | symbol (symbol : Symbol)
  | list (items : Array HandledSExpr)
  deriving Repr

/-- The signature of a defined function, its sorts already handled. -/
/- LEAN: Rust's `SmtFunctionSignature` (`multiple.rs`), which has no counterpart module here. -/
structure Signature (HandledSort : Type) where
  symbol : Symbol
  parameters : Array (Symbol × HandledSort)
  result : HandledSort
  deriving Repr

/-- A datatype constructor, the sorts of its selectors already handled. -/
/- LEAN: an entry of Rust's `SmtConstructors` (`multiple.rs`), which has no counterpart module
here. -/
structure Constructor (HandledSort : Type) where
  symbol : Symbol
  selectors : Array (Symbol × HandledSort)
  deriving Repr

end BSmtLib.Nodes
