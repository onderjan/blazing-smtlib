module

public import BSmtLib.Plain
public import BSmtLib.Token.Reserved
public import BSmtLib.Multiple

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

open BSmtLib.Plain (Symbol SymbolView Numeral NumeralView Decimal DecimalView HexDigits
  HexDigitsView BinDigits BinDigitsView StringContent StringContentView KeywordView)

/- LEAN: Rust's `SmtIndexBuf`, named with Rust's suffix `Buf` because its view holds the name
`Index`. -/
inductive IndexBuf where
  | numeral (digits : Numeral)
  | symbol (symbol : Symbol)
  deriving Repr

/- LEAN: Rust's `SmtIdentBuf`, named after its view, `Identifier`, with Rust's suffix `Buf`; its
fields are named as its view's. -/
structure IdentifierBuf where
  symbol : Symbol
  indices : Array IndexBuf
  deriving Repr

/-- An identifier that is a symbol alone, not indexed. -/
/- LEAN: Rust's `SmtIdentBuf::new_simple`. -/
def IdentifierBuf.newSimple (symbol : Symbol) : IdentifierBuf :=
  { symbol, indices := #[] }

/- LEAN: Rust's `SmtQualifiedIdentBuf`, named with Rust's suffix `Buf` because its view holds the
name `QualifiedIdent`; its fields are named as its view's. -/
structure QualifiedIdentBuf (HandledSort : Type) where
  identifier : IdentifierBuf
  sort : Option HandledSort
  deriving Repr

namespace QualifiedIdentBuf

variable {HandledSort : Type}

/-- A qualified identifier that is a symbol alone, neither indexed nor qualified. -/
/- LEAN: Rust's `SmtQualifiedIdentBuf::new_simple`. -/
def newSimple (symbol : Symbol) : QualifiedIdentBuf HandledSort :=
  { identifier := .newSimple symbol, sort := none }

/-- An identifier, not qualified. -/
/- LEAN: Rust's `SmtQualifiedIdentBuf::new_unqualified`. -/
def newUnqualified (identifier : IdentifierBuf) : QualifiedIdentBuf HandledSort :=
  { identifier, sort := none }

/-- An identifier qualified with the sort. -/
/- LEAN: Rust's `SmtQualifiedIdentBuf::new_qualified`. -/
def newQualified (identifier : IdentifierBuf) (sort : HandledSort) :
    QualifiedIdentBuf HandledSort :=
  { identifier, sort := some sort }

end QualifiedIdentBuf

/-- An index of an indexed identifier. -/
inductive Index where
  | numeral (digits : NumeralView)
  | symbol (symbol : SymbolView)
  deriving Repr

/- LEAN: Rust's `SmtIndex::into_owned`, on the view that the port names `Index` rather than
`IndexView`. -/
def Index.intoOwned : Index → IndexBuf
  | .numeral digits => .numeral digits.intoOwned
  | .symbol name => .symbol name.intoOwned

/-- An identifier: a symbol, with its indices if it is indexed. -/
/- LEAN: Rust's `SmtIdent`; the port's name for it is not aligned with Rust's yet. -/
structure Identifier where
  symbol : SymbolView
  indices : Array Index
  deriving Repr

/- LEAN: Rust's `SmtIdent::into_owned`; the port's name of the view is not aligned with Rust's
yet. -/
def Identifier.intoOwned (self : Identifier) : IdentifierBuf :=
  { symbol := self.symbol.intoOwned, indices := self.indices.map Index.intoOwned }

/-- A qualified identifier: an identifier, with the sort it is qualified with by `as`, if it is
qualified. -/
structure QualifiedIdent (HandledSort : Type) where
  identifier : Identifier
  sort : Option HandledSort
  deriving Repr

/- LEAN: Rust's `SmtQualifiedIdent::into_owned`, on the view that the port names
`QualifiedIdent` rather than `QualifiedIdentView`. -/
def QualifiedIdent.intoOwned {HandledSort : Type} (self : QualifiedIdent HandledSort) :
    QualifiedIdentBuf HandledSort :=
  { identifier := self.identifier.intoOwned, sort := self.sort }

/- LEAN: Rust's `SmtSpecialConstantBuf`, named after its view, `SpecConstant`, with Rust's suffix
`Buf`; its constructors are named as its view's. -/
inductive SpecConstantBuf where
  | numeral (digits : Numeral)
  | decimal (text : Decimal)
  | hexadecimal (digits : HexDigits)
  | binary (digits : BinDigits)
  | string (content : StringContent)
  deriving Repr

/-- A constant, as a view of its token's content. -/
/- LEAN: Rust's `SmtSpecialConstant`; the port's name for it is not aligned with Rust's yet. -/
inductive SpecConstant where
  | numeral (digits : NumeralView)
  | decimal (text : DecimalView)
  | hexadecimal (digits : HexDigitsView)
  | binary (digits : BinDigitsView)
  | string (content : StringContentView)
  deriving Repr

/- LEAN: Rust's `SmtSpecialConstant::into_owned`; the port's name of the view is not aligned
with Rust's yet. -/
def SpecConstant.intoOwned : SpecConstant → SpecConstantBuf
  | .numeral digits => .numeral digits.intoOwned
  | .decimal text => .decimal text.intoOwned
  | .hexadecimal digits => .hexadecimal digits.intoOwned
  | .binary digits => .binary digits.intoOwned
  | .string content => .string content.intoOwned

/-- Simple match pattern: a symbol or a wildcard. -/
/- LEAN: Rust's `SmtSimplePatternBuf`, named after its view, `SymbolOrWildcard`, with Rust's
suffix `Buf`; its constructors are named as its view's. -/
inductive SymbolOrWildcardBuf where
  /--
  A symbol as a pattern.

  In the match pattern position, the symbol should be
  either a variable or a nullary constructor, and
  it is not possible to determine syntactically which one it is.
  In the constructor application argument position,
  it should be a variable.
  -/
  | symbol (symbol : Symbol)
  /-- A wildcard (reserved word underscore `_`) as a pattern. -/
  | wildcard
  deriving Repr

/-- Match pattern: a symbol, a wildcard, or a constructor application. -/
/- LEAN: Rust's `SmtPatternBuf`, named with Rust's suffix `Buf` because its view holds the name
`Pattern`; its constructors and fields are named as its view's. -/
inductive PatternBuf where
  /-- A simple match pattern, either a symbol or a wildcard. -/
  | single (symbol : SymbolOrWildcardBuf)
  /-- A constructor applied to at least one variable or wildcard. -/
  | constructor (constructor : Symbol) (arguments : Array SymbolOrWildcardBuf)
  deriving Repr

/-- A symbol, or the wildcard `_`, in a pattern. -/
/- LEAN: Rust's `SmtSimplePattern`; the port's name for it is not aligned with Rust's yet. -/
inductive SymbolOrWildcard where
  | symbol (symbol : SymbolView)
  | wildcard
  deriving Repr

/- LEAN: Rust's `SmtSimplePattern::into_owned`; the port's name of the view is not aligned with
Rust's yet. -/
def SymbolOrWildcard.intoOwned : SymbolOrWildcard → SymbolOrWildcardBuf
  | .symbol name => .symbol name.intoOwned
  | .wildcard => .wildcard

/-- The pattern of a case of `match`. -/
inductive Pattern where
  | single (symbol : SymbolOrWildcard)
  | constructor (constructor : SymbolView) (arguments : Array SymbolOrWildcard)
  deriving Repr

/- LEAN: Rust's `SmtPattern::into_owned`, on the view that the port names `Pattern` rather than
`PatternView`. -/
def Pattern.intoOwned : Pattern → PatternBuf
  | .single symbol => .single symbol.intoOwned
  | .constructor name arguments =>
    .constructor name.intoOwned (arguments.map SymbolOrWildcard.intoOwned)

/-- The two quantifiers. -/
/- LEAN: Rust's `SmtQuantifierKind`; the port's name for it is not aligned with Rust's yet. -/
inductive Quantifier where
  | «forall»
  | «exists»
  deriving BEq, Repr

/-- Sorts to be handled. -/
/- LEAN: parameterised by the handled sorts, where Rust's is by the handler. -/
abbrev Sorts (HandledSort : Type) := Multiple HandledSort

/-- Terms to be handled. -/
/- LEAN: parameterised by the handled terms, where Rust's is by the handler. -/
abbrev Terms (HandledTerm : Type) := Multiple HandledTerm

/-- A term to be handled. -/
/- LEAN: Rust's `SmtTerm`; the port's names for it and its constructors are not aligned with
Rust's yet. Rust's variants hold the structures `SmtQualifiedIdent { ident, sort }` and
`SmtApplication { function, args }`; here their fields are the constructors' own, as Lean does
not unbox a structure of several fields, so a nested structure would be allocated for every
term handed over. -/
inductive TermNode (HandledSort HandledTerm : Type) where
  | constant (constant : SpecConstant)
  /-- A qualified identifier: Rust's `SmtQualifiedIdent { ident, sort }`, its fields flat. -/
  | identifier (ident : Identifier) (sort : Option HandledSort)
  /--
  A term that is an application: Rust's `SmtApplication { function, args }`, its fields flat,
  the qualified identifier `function` as `function` and `sort`.

  It is guaranteed that `args` are nonempty.
  -/
  | application (function : Identifier) (sort : Option HandledSort) (args : Terms HandledTerm)
  deriving Repr

/-- S-expressions to be handled. -/
/- LEAN: parameterised by the handled s-expressions, where Rust's is by the handler. -/
abbrev SExprs (HandledSExpr : Type) := Multiple HandledSExpr

/-- Attributes to be handled. -/
/- LEAN: parameterised by the handled attributes, where Rust's is by the handler. -/
abbrev Attributes (HandledAttribute : Type) := Multiple HandledAttribute

/-- An s-expression as the handler receives it, its items already handled. -/
/- LEAN: Rust's `SmtSExpr`; the port's name for it is not aligned with Rust's yet. -/
inductive SExprNode (HandledSExpr : Type) where
  | constant (constant : SpecConstant)
  | symbol (symbol : SymbolView)
  | reserved (word : Token.Reserved)
  | keyword (name : KeywordView)
  | list (items : SExprs HandledSExpr)
  deriving Repr

/--
The value of an attribute as the handler receives it, the s-expressions of a list value already
handled. A list value is handed over as its items.
-/
/- LEAN: Rust's `SmtAttributeValue`; the port's name for it is not aligned with Rust's yet. -/
inductive AttributeValueNode (HandledSExpr : Type) where
  | constant (constant : SpecConstant)
  | symbol (symbol : SymbolView)
  | list (items : SExprs HandledSExpr)
  deriving Repr

/--
A function signature to be handled: the name, the parameters
with their sorts, and the result sort.
-/
/- LEAN: Rust's `SmtFunctionSignature` (`multiple.rs`), named `Signature` until the port's names
are aligned with Rust's. Rust's accessors are the fields; the parameters are an array, where Rust's
`params` is an iterator. -/
structure Signature (HandledSort : Type) where
  name : SymbolView
  /-- The parameters with their sorts, in order. -/
  params : Array (SymbolView × HandledSort)
  resultSort : HandledSort
  deriving Repr

end BSmtLib.Nodes
