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

open BSmtLib.Plain (SymbolBuf Symbol NumeralBuf Numeral DecimalBuf Decimal HexDigitsBuf
  HexDigits BinDigitsBuf BinDigits StringContentBuf StringContent Keyword)

inductive IndexBuf where
  | numeral (digits : NumeralBuf)
  | symbol (symbol : SymbolBuf)
  deriving Repr

structure IdentBuf where
  name : SymbolBuf
  indices : Array IndexBuf
  deriving Repr

/-- An identifier that is a symbol alone, not indexed. -/
def IdentBuf.newSimple (name : SymbolBuf) : IdentBuf :=
  { name, indices := #[] }

structure QualifiedIdentBuf (HandledSort : Type) where
  ident : IdentBuf
  sort : Option HandledSort
  deriving Repr

namespace QualifiedIdentBuf

variable {HandledSort : Type}

/-- A qualified identifier that is a symbol alone, neither indexed nor qualified. -/
def newSimple (name : SymbolBuf) : QualifiedIdentBuf HandledSort :=
  { ident := .newSimple name, sort := none }

/-- An identifier, not qualified. -/
def newUnqualified (ident : IdentBuf) : QualifiedIdentBuf HandledSort :=
  { ident, sort := none }

/-- An identifier qualified with the sort. -/
def newQualified (ident : IdentBuf) (sort : HandledSort) : QualifiedIdentBuf HandledSort :=
  { ident, sort := some sort }

end QualifiedIdentBuf

/-- An index of an indexed identifier. -/
inductive Index where
  | numeral (digits : Numeral)
  | symbol (symbol : Symbol)
  deriving Repr

def Index.intoOwned : Index → IndexBuf
  | .numeral digits => .numeral digits.intoOwned
  | .symbol name => .symbol name.intoOwned

/-- An identifier: a symbol, with its indices if it is indexed. -/
/- LEAN: Rust's `indices` are `SmtIndices`, a container of the views; here an array. -/
structure Ident where
  name : Symbol
  indices : Array Index
  deriving Repr

def Ident.intoOwned (self : Ident) : IdentBuf :=
  { name := self.name.intoOwned, indices := self.indices.map Index.intoOwned }

/- LEAN: the index with its bytes copied, so that it holds no storage of the input; how the owned
buffers keep what they are given. -/
@[inline]
def Index.Internal.copy : Index → Index
  | .numeral digits => .numeral digits.intoOwned.asView
  | .symbol name => .symbol name.intoOwned.asView

/-- Owned indices of an identifier, from which `Ident.indices` is viewed. -/
/- LEAN: Rust's `SmtIndicesBuf`, from which `SmtIndices` is viewed; Lean's indices are an
`Array` of the views (see `Ident`), which `view` gives. Each index is a view of a copy of its
bytes that the buffer made, so the view needs no copy. -/
structure IndicesBuf where
  private ofArray ::
  private entries : Array Index

namespace IndicesBuf

def new : IndicesBuf := ⟨#[]⟩

def push (self : IndicesBuf) (index : Index) : IndicesBuf :=
  ⟨self.entries.push (Index.Internal.copy index)⟩

def clear (_ : IndicesBuf) : IndicesBuf := new

def view (self : IndicesBuf) : Array Index := self.entries

def len (self : IndicesBuf) : Nat := self.entries.size

def isEmpty (self : IndicesBuf) : Bool := self.entries.isEmpty

@[no_expose] instance : Inhabited IndicesBuf := ⟨new⟩

end IndicesBuf

/-- A qualified identifier: an identifier, with the sort it is qualified with by `as`, if it is
qualified. -/
structure QualifiedIdent (HandledSort : Type) where
  ident : Ident
  sort : Option HandledSort
  deriving Repr

def QualifiedIdent.intoOwned {HandledSort : Type} (self : QualifiedIdent HandledSort) :
    QualifiedIdentBuf HandledSort :=
  { ident := self.ident.intoOwned, sort := self.sort }

inductive SpecialConstantBuf where
  | numeral (digits : NumeralBuf)
  | decimal (text : DecimalBuf)
  | hexadecimal (digits : HexDigitsBuf)
  | binary (digits : BinDigitsBuf)
  | string (content : StringContentBuf)
  deriving BEq, Hashable, Repr

/-- A constant, as a view of its token's content. -/
inductive SpecialConstant where
  | numeral (digits : Numeral)
  | decimal (text : Decimal)
  | hexadecimal (digits : HexDigits)
  | binary (digits : BinDigits)
  | string (content : StringContent)
  deriving BEq, Hashable, Repr

def SpecialConstant.intoOwned : SpecialConstant → SpecialConstantBuf
  | .numeral digits => .numeral digits.intoOwned
  | .decimal text => .decimal text.intoOwned
  | .hexadecimal digits => .hexadecimal digits.intoOwned
  | .binary digits => .binary digits.intoOwned
  | .string content => .string content.intoOwned

/-- Simple match pattern: a symbol or a wildcard. -/
inductive SimplePatternBuf where
  /--
  A symbol as a pattern.

  In the match pattern position, the symbol should be
  either a variable or a nullary constructor, and
  it is not possible to determine syntactically which one it is.
  In the constructor application argument position,
  it should be a variable.
  -/
  | symbol (symbol : SymbolBuf)
  /-- A wildcard (reserved word underscore `_`) as a pattern. -/
  | wildcard
  deriving Repr

/-- Match pattern: a symbol, a wildcard, or a constructor application. -/
inductive PatternBuf where
  /-- A simple match pattern, either a symbol or a wildcard. -/
  | simple (pattern : SimplePatternBuf)
  /-- A constructor applied to at least one variable or wildcard. -/
  | application (constructor : SymbolBuf) (args : Array SimplePatternBuf)
  deriving Repr

/-- A symbol, or the wildcard `_`, in a pattern. -/
inductive SimplePattern where
  | symbol (symbol : Symbol)
  | wildcard
  deriving Repr

def SimplePattern.intoOwned : SimplePattern → SimplePatternBuf
  | .symbol name => .symbol name.intoOwned
  | .wildcard => .wildcard

/-- The pattern of a case of `match`. -/
/- LEAN: Rust's `args` of an application are `SmtSimplePatterns`, a container of the views; here
an array. -/
inductive Pattern where
  /-- A simple match pattern, either a symbol or a wildcard. -/
  | simple (pattern : SimplePattern)
  /-- A constructor applied to at least one variable or wildcard. -/
  | application (constructor : Symbol) (args : Array SimplePattern)
  deriving Repr

def Pattern.intoOwned : Pattern → PatternBuf
  | .simple pattern => .simple pattern.intoOwned
  | .application constructor args =>
    .application constructor.intoOwned (args.map SimplePattern.intoOwned)

/- LEAN: the simple pattern with its bytes copied, so that it holds no storage of the input; how
the owned buffers keep what they are given. -/
@[inline]
def SimplePattern.Internal.copy : SimplePattern → SimplePattern
  | .symbol name => .symbol name.intoOwned.asView
  | .wildcard => .wildcard

/- LEAN: the pattern with its bytes copied, as `SimplePattern.Internal.copy`. -/
@[inline]
def Pattern.Internal.copy : Pattern → Pattern
  | .simple pattern => .simple (SimplePattern.Internal.copy pattern)
  | .application constructor args =>
    .application constructor.intoOwned.asView (args.map SimplePattern.Internal.copy)

/-- Owned arguments of a constructor pattern, from which the `args` of `Pattern.application` are
viewed. -/
/- LEAN: Rust's `SmtSimplePatternsBuf`, from which `SmtSimplePatterns` is viewed; Lean's
arguments are an `Array` of the views (see `Pattern`), which `view` gives. Each pattern is a view
of a copy of its bytes that the buffer made, so the view needs no copy. -/
structure SimplePatternsBuf where
  private ofArray ::
  private entries : Array SimplePattern

namespace SimplePatternsBuf

def new : SimplePatternsBuf := ⟨#[]⟩

def push (self : SimplePatternsBuf) (pattern : SimplePattern) : SimplePatternsBuf :=
  ⟨self.entries.push (SimplePattern.Internal.copy pattern)⟩

def clear (_ : SimplePatternsBuf) : SimplePatternsBuf := new

def view (self : SimplePatternsBuf) : Array SimplePattern := self.entries

def len (self : SimplePatternsBuf) : Nat := self.entries.size

def isEmpty (self : SimplePatternsBuf) : Bool := self.entries.isEmpty

@[no_expose] instance : Inhabited SimplePatternsBuf := ⟨new⟩

end SimplePatternsBuf

/-- The two quantifiers. -/
inductive QuantifierKind where
  | «exists»
  | «forall»
  deriving BEq, Hashable, Repr

/-- Sorts to be handled. -/
/- LEAN: parameterised by the handled sorts, where Rust's is by the handler. -/
abbrev Sorts (HandledSort : Type) := Multiple HandledSort

/-- Terms to be handled. -/
/- LEAN: parameterised by the handled terms, where Rust's is by the handler. -/
abbrev Terms (HandledTerm : Type) := Multiple HandledTerm

/-- A term to be handled. -/
/- LEAN: Rust's variants hold the structures `SmtQualifiedIdent { ident, sort }` and
`SmtApplication { function, args }`; here their fields are the constructors' own, as Lean does
not unbox a structure of several fields, so a nested structure would be allocated for every
term handed over. -/
inductive Term (HandledSort HandledTerm : Type) where
  | specialConstant (constant : SpecialConstant)
  /-- A qualified identifier: Rust's `SmtQualifiedIdent { ident, sort }`, its fields flat. -/
  | qualifiedIdent (ident : Ident) (sort : Option HandledSort)
  /--
  A term that is an application: Rust's `SmtApplication { function, args }`, its fields flat,
  the qualified identifier `function` as `function` and `sort`.

  It is guaranteed that `args` are nonempty.
  -/
  | application (function : Ident) (sort : Option HandledSort) (args : Terms HandledTerm)
  deriving Repr

/-- S-expressions to be handled. -/
/- LEAN: parameterised by the handled s-expressions, where Rust's is by the handler. -/
abbrev SExprs (HandledSExpr : Type) := Multiple HandledSExpr

/-- Attributes to be handled. -/
/- LEAN: parameterised by the handled attributes, where Rust's is by the handler. -/
abbrev Attributes (HandledAttribute : Type) := Multiple HandledAttribute

/-- An s-expression as the handler receives it, its items already handled. -/
inductive SExpr (HandledSExpr : Type) where
  | specialConstant (constant : SpecialConstant)
  | symbol (symbol : Symbol)
  | reserved (word : Token.Reserved)
  | keyword (name : Keyword)
  | sExprs (items : SExprs HandledSExpr)
  deriving Repr

/--
The value of an attribute as the handler receives it, the s-expressions of a list value already
handled. A list value is handed over as its items.
-/
inductive AttributeValue (HandledSExpr : Type) where
  | specialConstant (constant : SpecialConstant)
  | symbol (symbol : Symbol)
  | sExprs (items : SExprs HandledSExpr)
  deriving Repr

end BSmtLib.Nodes
