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

/-- An index of an indexed identifier. -/
inductive Index where
  | numeral (digits : NumeralView)
  | symbol (symbol : Symbol)

/-- An identifier: a symbol, with its indices if it is indexed. -/
structure Identifier where
  symbol : Symbol
  indices : Array Index

/-- A constant, as a view of its token's content. -/
inductive SpecConstant where
  | numeral (digits : NumeralView)
  | decimal (text : DecimalView)
  | hexadecimal (digits : HexDigitsView)
  | binary (digits : BinDigitsView)
  | string (content : StringContentView)

/-- A symbol, or the wildcard `_`, in a pattern. -/
inductive SymbolOrWildcard where
  | symbol (symbol : Symbol)
  | wildcard

/-- The pattern of a case of `match`. -/
inductive Pattern where
  | single (symbol : SymbolOrWildcard)
  | constructor (constructor : Symbol) (arguments : Array SymbolOrWildcard)

/-- The two quantifiers. -/
inductive Quantifier where
  | «forall»
  | «exists»
  deriving BEq

/-- A term as the handler receives it, its parts already handled. -/
inductive TermNode (HandledSort HandledTerm : Type) where
  | constant (constant : SpecConstant)
  /-- A qualified identifier, with its sort if it is qualified by `as`. -/
  | identifier (identifier : Identifier) (sort : Option HandledSort)
  /-- An application of a qualified identifier to at least one argument. -/
  | application (function : Identifier) (sort : Option HandledSort)
      (arguments : Array HandledTerm)

/-- An s-expression as the handler receives it, its items already handled. -/
inductive SExprNode (HandledSExpr : Type) where
  | constant (constant : SpecConstant)
  | symbol (symbol : Symbol)
  | reserved (word : Token.Reserved)
  | keyword (name : KeywordView)
  | list (items : Array HandledSExpr)

/--
The value of an attribute as the handler receives it, the s-expressions of a list value already
handled. A list value is handed over as its items.
-/
inductive AttributeValueNode (HandledSExpr : Type) where
  | constant (constant : SpecConstant)
  | symbol (symbol : Symbol)
  | list (items : Array HandledSExpr)

/-- The signature of a defined function, its sorts already handled. -/
structure Signature (HandledSort : Type) where
  symbol : Symbol
  parameters : Array (Symbol × HandledSort)
  result : HandledSort

/-- A datatype constructor, the sorts of its selectors already handled. -/
structure Constructor (HandledSort : Type) where
  symbol : Symbol
  selectors : Array (Symbol × HandledSort)

end BSmtLib.Nodes
