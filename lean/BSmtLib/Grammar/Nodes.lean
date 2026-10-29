module

public import BSmtLib.Lexicon.Value
public import BSmtLib.Lexicon.Reserved
public import BSmtLib.Grammar.Multiple
public import BSmtLib.Token.AppendTokens

public section

/-!
SMT-LIB grammar: identifiers, sorts, terms, attributes etc.

SMT-LIB grammar encodes an abstract syntax tree. For example, the input `(- (+ a b) c)` read as a
term has the meaning of a rooted tree of subterms.

```text
a   b   c
 \ /   /
  +   /
   \ /
    -
```

As **BSmtLib** is a streaming library, it never constructs the tree. Instead, parsers call
handlers that implement `Handler` in post-order traversal through the tree. For the given example,
`TermParser` calls `Handler.handleTerm` multiple times with the following arguments:
1. `Term.qualifiedIdent` for `a`.
2. `Term.qualifiedIdent` for `b`.
3. `Term.application` with the function `+` and the 2 `Handler.Term` results returned for `a`
   and `b`.
4. `Term.qualifiedIdent` for `c`.
5. `Term.application` with the function `-` and the 2 `Handler.Term` results returned for
   `(+ a b)` and `c`.

Other grammar nodes such as `let` and quantifier binders are handled through `Handler` methods of
their own.

The handler could construct the abstract syntax tree from the traversal, but does not have to: it
can act on the terms as they come, improving speed and lowering memory consumption.

The types in this module and in `Grammar.Multiple` are views into the grammar nodes seen by the
handler (the node has information only about itself and the result values for its already
handled children) and their owned versions. They take the types of the handled children (sorts,
terms, and S-expressions) as parameters, which a handler instantiates with its own `Sort`, `Term`
and `SExpr`.
-/

/- LEAN: Rust hands borrowed views (`SmtSymbol<'a>`) over and keeps owned twins
(`SmtSymbolBuf`). Lean has no borrows: a view is a byte slice, which keeps the storage it
points into alive for as long as the view lives. -/

namespace BSmtLib.Grammar.Nodes

open BSmtLib.Lexicon.Value (SymbolBuf Symbol NumeralBuf Numeral DecimalBuf Decimal HexDigitsBuf
  HexDigits BinDigitsBuf BinDigits StringContentBuf StringContent KeywordBuf Keyword)

/-- Owned index of an identifier (numeral or symbol). -/
inductive IndexBuf where
  /-- Numeral, e.g. `32` in `(_ BitVec 32)`. -/
  | numeral (digits : NumeralBuf)
  /-- Symbol, e.g. `up` in `(_ move up)`. -/
  | symbol (symbol : SymbolBuf)
  deriving Repr

/-- View of an index of an identifier (numeral or symbol). -/
inductive Index where
  /-- Numeral, e.g. `32` in `(_ BitVec 32)`. -/
  | numeral (digits : Numeral)
  /-- Symbol, e.g. `up` in `(_ move up)`. -/
  | symbol (symbol : Symbol)
  deriving Repr

/-- Converts into `IndexBuf`. -/
def Index.intoOwned : Index → IndexBuf
  | .numeral digits => .numeral digits.intoOwned
  | .symbol name => .symbol name.intoOwned

/-- Views as `Index`. -/
def IndexBuf.view : IndexBuf → Index
  | .numeral digits => .numeral digits.view
  | .symbol name => .symbol name.view

/- LEAN: the index with its bytes copied, so that it holds no storage of the input; how the owned
buffers keep what they are given. -/
@[inline]
def Index.Internal.copy : Index → Index
  | .numeral digits => .numeral digits.intoOwned.view
  | .symbol name => .symbol name.intoOwned.view

/- LEAN: Rust's `SmtIndicesBuf`, from which `SmtIndices` is viewed; Lean's indices are an
`Array` of the views (see `Ident`), which `view` gives. Each index is a view of a copy of its
bytes that the buffer made, so the view needs no copy. -/
/-- Owned indices of an identifier. -/
structure IndicesBuf where
  private ofArray ::
  private entries : Array Index

namespace IndicesBuf

/-- Creates empty indices. -/
def new : IndicesBuf := ⟨#[]⟩

/-- Copies the index after the others. -/
def push (self : IndicesBuf) (index : Index) : IndicesBuf :=
  ⟨self.entries.push (Index.Internal.copy index)⟩

/-- Removes all indices. -/
def clear (_ : IndicesBuf) : IndicesBuf := new

/-- Views as an array of `Index`, the indices of an `Ident`. -/
def view (self : IndicesBuf) : Array Index := self.entries

/-- Returns the number of indices. -/
def len (self : IndicesBuf) : Nat := self.entries.size

/-- Returns `true` if there are no indices. -/
def isEmpty (self : IndicesBuf) : Bool := self.entries.isEmpty

/-- Returns the index at the position, or `none` if it is out of bounds. -/
def get? (self : IndicesBuf) (index : Nat) : Option Index := self.entries[index]?

@[no_expose] instance : Inhabited IndicesBuf := ⟨new⟩

/- LEAN: Rust's `iter`, as for the containers of `BSmtLib.Grammar.Multiple`. -/
@[no_expose] instance {m : Type → Type} [Monad m] : ForIn m IndicesBuf Index where
  forIn self init f := ForIn.forIn self.entries init f

/- LEAN: Rust's `Debug`, which lists the indices. -/
@[no_expose] instance : Repr IndicesBuf := ⟨fun s p => reprPrec s.entries p⟩

end IndicesBuf

/-- Owned identifier. -/
structure IdentBuf where
  /-- Name of the identifier. -/
  name : SymbolBuf
  /-- Indices of the identifier. -/
  indices : IndicesBuf
  deriving Repr

/- LEAN: Rust's `indices` are `SmtIndices`, a container of the views; here an array. -/
/-- View of an identifier. -/
structure Ident where
  /-- Name of the identifier. -/
  name : Symbol
  /-- Indices of the identifier. -/
  indices : Array Index
  deriving Repr

namespace IdentBuf

/-- Creates a simple identifier: a name with no indices. -/
def newSimple (name : SymbolBuf) : IdentBuf :=
  { name, indices := .new }

/-- Views as `Ident`. -/
def view (self : IdentBuf) : Ident :=
  { name := self.name.view, indices := self.indices.view }

end IdentBuf

/-- Converts into `IdentBuf`. -/
def Ident.intoOwned (self : Ident) : IdentBuf :=
  { name := self.name.intoOwned, indices := self.indices.foldl IndicesBuf.push .new }

/-- Owned qualified identifier. -/
structure QualifiedIdentBuf (HandledSort : Type) where
  /-- Identifier. -/
  ident : IdentBuf
  /-- Sort that qualifies the identifier, if any. -/
  sort : Option HandledSort
  deriving Repr

namespace QualifiedIdentBuf

variable {HandledSort : Type}

/-- Creates a qualified identifier from a simple identifier, without a sort. -/
def newSimple (name : SymbolBuf) : QualifiedIdentBuf HandledSort :=
  { ident := .newSimple name, sort := none }

/-- Creates a qualified identifier without a sort. -/
def newUnqualified (ident : IdentBuf) : QualifiedIdentBuf HandledSort :=
  { ident, sort := none }

/-- Creates an identifier qualified by the sort. -/
def newQualified (ident : IdentBuf) (sort : HandledSort) : QualifiedIdentBuf HandledSort :=
  { ident, sort := some sort }

end QualifiedIdentBuf

/-- View of a qualified identifier. -/
structure QualifiedIdent (HandledSort : Type) where
  /-- Identifier. -/
  ident : Ident
  /-- Sort that qualifies the identifier, if any. -/
  sort : Option HandledSort
  deriving Repr

/-- Converts into `QualifiedIdentBuf`. -/
def QualifiedIdent.intoOwned {HandledSort : Type} (self : QualifiedIdent HandledSort) :
    QualifiedIdentBuf HandledSort :=
  { ident := self.ident.intoOwned, sort := self.sort }

/- LEAN: parameterised by the handled sorts, as `QualifiedIdentBuf` is. A sort is handed over
flat, as its identifier and its argument sorts, so there is no view of a sort to convert from or
to (Rust's `SmtSort::into_owned` and `SmtSortBuf::view_mut`); the fields are built from the
parts handed over. -/
/-- Owned sort. -/
structure SortBuf (HandledSort : Type) where
  /-- Identifier of the sort. -/
  ident : IdentBuf
  /-- Arguments of the sort. -/
  args : Array HandledSort
  deriving Repr

/-- Owned special constant (numeral, decimal, hexadecimal, binary, or string). -/
inductive SpecialConstantBuf where
  /-- Numeral, e.g. `0` or `42`. -/
  | numeral (digits : NumeralBuf)
  /-- Decimal, e.g. `0.5` or `3.14`. -/
  | decimal (text : DecimalBuf)
  /-- Hexadecimal, e.g. `#xA04`. -/
  | hexadecimal (digits : HexDigitsBuf)
  /-- Binary, e.g. `#b0101`. -/
  | binary (digits : BinDigitsBuf)
  /-- String literal, e.g. `"hello"` or `""`. -/
  | string (content : StringContentBuf)
  deriving BEq, Hashable, Repr

/-- View of a special constant (numeral, decimal, hexadecimal, binary, or string). -/
inductive SpecialConstant where
  /-- Numeral, e.g. `0` or `42`. -/
  | numeral (digits : Numeral)
  /-- Decimal, e.g. `0.5` or `3.14`. -/
  | decimal (text : Decimal)
  /-- Hexadecimal, e.g. `#xA04`. -/
  | hexadecimal (digits : HexDigits)
  /-- Binary, e.g. `#b0101`. -/
  | binary (digits : BinDigits)
  /-- String literal, e.g. `"hello"` or `""`. -/
  | string (content : StringContent)
  deriving BEq, Hashable, Repr

/-- Converts into `SpecialConstantBuf`. -/
def SpecialConstant.intoOwned : SpecialConstant → SpecialConstantBuf
  | .numeral digits => .numeral digits.intoOwned
  | .decimal text => .decimal text.intoOwned
  | .hexadecimal digits => .hexadecimal digits.intoOwned
  | .binary digits => .binary digits.intoOwned
  | .string content => .string content.intoOwned

/-- Views as `SpecialConstant`. -/
def SpecialConstantBuf.view : SpecialConstantBuf → SpecialConstant
  | .numeral digits => .numeral digits.view
  | .decimal text => .decimal text.view
  | .hexadecimal digits => .hexadecimal digits.view
  | .binary digits => .binary digits.view
  | .string content => .string content.view

/-- Owned simple match pattern (symbol or wildcard). -/
inductive SimplePatternBuf where
  /--
  Symbol as a pattern, e.g. `x` or `nil`.

  In the match pattern position, the symbol should be
  either a variable or a nullary constructor, and
  it is not possible to determine syntactically which one it is.
  In the constructor application argument position,
  it should be a variable.
  -/
  | symbol (symbol : SymbolBuf)
  /--
  Wildcard as a pattern.

  The wildcard is the reserved word `_`.

  The wildcard was introduced in SMT-LIB 2.7.
  -/
  | wildcard
  deriving Repr

/-- View of a simple match pattern (symbol or wildcard). -/
inductive SimplePattern where
  /--
  Symbol as a pattern, e.g. `x` or `nil`.

  In the match pattern position, the symbol should be
  either a variable or a nullary constructor, and
  it is not possible to determine syntactically which one it is.
  In the constructor application argument position,
  it should be a variable.
  -/
  | symbol (symbol : Symbol)
  /--
  Wildcard as a pattern.

  The wildcard is the reserved word `_`.

  The wildcard was introduced in SMT-LIB 2.7.
  -/
  | wildcard
  deriving Repr

/-- Converts into `SimplePatternBuf`. -/
def SimplePattern.intoOwned : SimplePattern → SimplePatternBuf
  | .symbol name => .symbol name.intoOwned
  | .wildcard => .wildcard

/-- Views as `SimplePattern`. -/
def SimplePatternBuf.view : SimplePatternBuf → SimplePattern
  | .symbol name => .symbol name.view
  | .wildcard => .wildcard

/- LEAN: the simple pattern with its bytes copied, so that it holds no storage of the input; how
the owned buffers keep what they are given. -/
@[inline]
def SimplePattern.Internal.copy : SimplePattern → SimplePattern
  | .symbol name => .symbol name.intoOwned.view
  | .wildcard => .wildcard

/- LEAN: Rust's `SmtSimplePatternsBuf`, from which `SmtSimplePatterns` is viewed; Lean's
arguments are an `Array` of the views (see `PatternApplication`), which `view` gives. Each
pattern is a view of a copy of its bytes that the buffer made, so the view needs no copy. -/
/-- Owned arguments of a constructor pattern. -/
structure SimplePatternsBuf where
  private ofArray ::
  private entries : Array SimplePattern

namespace SimplePatternsBuf

/-- Creates empty arguments. -/
def new : SimplePatternsBuf := ⟨#[]⟩

/-- Copies the argument after the others. -/
def push (self : SimplePatternsBuf) (pattern : SimplePattern) : SimplePatternsBuf :=
  ⟨self.entries.push (SimplePattern.Internal.copy pattern)⟩

/-- Removes all arguments. -/
def clear (_ : SimplePatternsBuf) : SimplePatternsBuf := new

/-- Views as an array of `SimplePattern`, the arguments of a `PatternApplication`. -/
def view (self : SimplePatternsBuf) : Array SimplePattern := self.entries

/-- Returns the number of arguments. -/
def len (self : SimplePatternsBuf) : Nat := self.entries.size

/-- Returns `true` if there are no arguments. -/
def isEmpty (self : SimplePatternsBuf) : Bool := self.entries.isEmpty

/-- Returns the argument at the position, or `none` if it is out of bounds. -/
def get? (self : SimplePatternsBuf) (index : Nat) : Option SimplePattern := self.entries[index]?

/-- The arguments viewed are as many as the buffer holds. -/
theorem size_view (self : SimplePatternsBuf) : self.view.size = self.len :=
  (rfl)

/- LEAN: a buffer of the views, copied: how `PatternApplication.intoOwned` makes its
arguments. -/
/-- The buffer of the patterns, each copied. -/
def Internal.ofViews (patterns : Array SimplePattern) : SimplePatternsBuf :=
  ⟨patterns.map SimplePattern.Internal.copy⟩

theorem Internal.len_ofViews (patterns : Array SimplePattern) :
    (Internal.ofViews patterns).len = patterns.size := by
  simp [Internal.ofViews, len]

@[no_expose] instance : Inhabited SimplePatternsBuf := ⟨new⟩

/- LEAN: Rust's `iter`, as for the containers of `BSmtLib.Grammar.Multiple`. -/
@[no_expose] instance {m : Type → Type} [Monad m] : ForIn m SimplePatternsBuf SimplePattern where
  forIn self init f := ForIn.forIn self.entries init f

/- LEAN: Rust's `Debug`, which lists the patterns. -/
@[no_expose] instance : Repr SimplePatternsBuf := ⟨fun s p => reprPrec s.entries p⟩

end SimplePatternsBuf

/-- Error constructing an application or a constructor pattern without arguments. -/
structure EmptyArgumentsError where
  deriving BEq, Hashable, Repr

@[no_expose] instance : ToString EmptyArgumentsError :=
  ⟨fun _ => "no arguments provided where at least one is required"⟩

/- LEAN: Rust's fields are private, so that the arguments cannot be empty, and read through the
getters `constructor` and `args`; here the fields are public and the proof `nonempty` guards
the arguments. Rust's `args` are `SmtSimplePatterns`, a container of the views; here an
array. -/
/--
View of a constructor pattern.

It is a constructor applied to at least one variable or wildcard.
-/
structure PatternApplication where
  /-- Applied constructor. -/
  constructor : Symbol
  /-- Arguments of the pattern. -/
  args : Array SimplePattern
  /-- There is at least one argument. -/
  nonempty : 0 < args.size
  deriving Repr

/- LEAN: the fields are public, as `PatternApplication`'s are, with the proof `nonempty`. -/
/--
Owned constructor pattern.

It is a constructor applied to at least one variable or wildcard.
-/
structure PatternApplicationBuf where
  /-- Applied constructor. -/
  constructor : SymbolBuf
  /-- Arguments of the pattern. -/
  args : SimplePatternsBuf
  /-- There is at least one argument. -/
  nonempty : 0 < args.len
  deriving Repr

namespace PatternApplication

/-- The arguments of an array that is not empty are at least one. -/
theorem Internal.size_pos {args : Array SimplePattern} (h : ¬args.isEmpty) : 0 < args.size :=
  Nat.pos_of_ne_zero fun hz => h (Array.isEmpty_iff_size_eq_zero.mpr hz)

/-- Creates a pattern that applies `constructor` to `args` if `args` is nonempty. -/
def new (constructor : Symbol) (args : Array SimplePattern) :
    Except EmptyArgumentsError PatternApplication :=
  if h : 0 < args.size then .ok ⟨constructor, args, h⟩ else .error {}

/-- Converts into `PatternApplicationBuf`. -/
def intoOwned (self : PatternApplication) : PatternApplicationBuf :=
  { constructor := self.constructor.intoOwned
    args := SimplePatternsBuf.Internal.ofViews self.args
    nonempty := by rw [SimplePatternsBuf.Internal.len_ofViews]; exact self.nonempty }

end PatternApplication

namespace PatternApplicationBuf

/-- Creates a pattern that applies `constructor` to `args` if `args` is nonempty. -/
def new (constructor : SymbolBuf) (args : SimplePatternsBuf) :
    Except EmptyArgumentsError PatternApplicationBuf :=
  if h : 0 < args.len then .ok ⟨constructor, args, h⟩ else .error {}

/-- Destructures into the constructor and the arguments. -/
def intoParts (self : PatternApplicationBuf) : SymbolBuf × SimplePatternsBuf :=
  (self.constructor, self.args)

/-- Views as `PatternApplication`. -/
def view (self : PatternApplicationBuf) : PatternApplication :=
  { constructor := self.constructor.view, args := self.args.view,
    nonempty := by rw [SimplePatternsBuf.size_view]; exact self.nonempty }

end PatternApplicationBuf

/-- Owned match pattern (simple or constructor pattern). -/
inductive PatternBuf where
  /-- Simple match pattern, e.g. `x`, `nil` or `_`. -/
  | simple (pattern : SimplePatternBuf)
  /-- Constructor pattern, e.g. `(cons h t)`. -/
  | application (application : PatternApplicationBuf)
  deriving Repr

/-- View of a match pattern (simple or constructor pattern). -/
inductive Pattern where
  /-- Simple match pattern, e.g. `x`, `nil` or `_`. -/
  | simple (pattern : SimplePattern)
  /-- Constructor pattern, e.g. `(cons h t)`. -/
  | application (application : PatternApplication)
  deriving Repr

/-- Converts into `PatternBuf`. -/
def Pattern.intoOwned : Pattern → PatternBuf
  | .simple pattern => .simple pattern.intoOwned
  | .application app => .application app.intoOwned

/-- Views as `Pattern`. -/
def PatternBuf.view : PatternBuf → Pattern
  | .simple pattern => .simple pattern.view
  | .application app => .application app.view

/- LEAN: the pattern with its bytes copied, as `SimplePattern.Internal.copy`. -/
@[inline]
def Pattern.Internal.copy : Pattern → Pattern
  | .simple pattern => .simple (SimplePattern.Internal.copy pattern)
  | .application app =>
    .application
      { constructor := app.constructor.intoOwned.view
        args := app.args.map SimplePattern.Internal.copy
        nonempty := by rw [Array.size_map]; exact app.nonempty }

/-- Kind of a quantifier (existential or universal). -/
inductive QuantifierKind where
  /-- Existential quantifier (`exists`). -/
  | «exists»
  /-- Universal quantifier (`forall`). -/
  | «forall»
  deriving BEq, Hashable, Repr

/- LEAN: Rust's variants hold the structures `SmtQualifiedIdent { ident, sort }` and
`SmtApplication { function, args }`; here their fields are the constructors' own, as Lean does
not unbox a structure of several fields, so a nested structure would be allocated for every
term handed over. -/
/-- View of a term (special constant, qualified identifier, or application). -/
inductive Term (HandledSort HandledTerm : Type) where
  /-- Special constant, e.g. `42` or `"hello"`. -/
  | specialConstant (constant : SpecialConstant)
  /--
  Qualified identifier, e.g. `x`, `(_ bv0 32)` or `(as nil (List Int))`.

  The identifier and the sort that qualifies it, if any, are the fields of the variant.
  -/
  | qualifiedIdent (ident : Ident) (sort : Option HandledSort)
  /--
  Application, e.g. `(+ x 1)`.

  The applied function is the qualified identifier given by `function` and `sort`.
  The arguments are never empty.
  -/
  | application (function : Ident) (sort : Option HandledSort) (args : Multiple HandledTerm)
      (nonempty : 0 < args.len)
  deriving Repr

/- LEAN: Rust's `SmtApplication::new`, which builds the application that `SmtTerm::Application`
holds; here the term, as the application is handed over flat. -/
/-- Creates an application of `function` to `args` if `args` is nonempty. -/
def Term.newApplication {HandledSort HandledTerm : Type} (function : Ident)
    (sort : Option HandledSort) (args : Multiple HandledTerm) :
    Except EmptyArgumentsError (Term HandledSort HandledTerm) :=
  if h : 0 < args.len then .ok (.application function sort args h) else .error {}

/- LEAN: Rust's variants hold `SmtQualifiedIdentBuf` and `SmtApplicationBuf`; here their fields
are the constructors' own, as those of `Term` are. -/
/-- Owned term (special constant, qualified identifier, or application). -/
inductive TermBuf (HandledSort HandledTerm : Type) where
  /-- Special constant, e.g. `42` or `"hello"`. -/
  | specialConstant (constant : SpecialConstantBuf)
  /--
  Qualified identifier, e.g. `x`, `(_ bv0 32)` or `(as nil (List Int))`.

  The identifier and the sort that qualifies it, if any, are the fields of the variant.
  -/
  | qualifiedIdent (ident : IdentBuf) (sort : Option HandledSort)
  /--
  Application, e.g. `(+ x 1)`.

  The applied function is the qualified identifier given by `function` and `sort`.
  The arguments are never empty.
  -/
  | application (function : IdentBuf) (sort : Option HandledSort) (args : Array HandledTerm)
      (nonempty : 0 < args.size)
  deriving Repr

/-- Converts into `TermBuf`. -/
def Term.intoOwned {HandledSort HandledTerm : Type} :
    Term HandledSort HandledTerm → TermBuf HandledSort HandledTerm
  | .specialConstant constant => .specialConstant constant.intoOwned
  | .qualifiedIdent ident sort => .qualifiedIdent ident.intoOwned sort
  | .application function sort args nonempty =>
    .application function.intoOwned sort args.asSlice
      (by rw [Grammar.Multiple.size_asSlice]; exact nonempty)

/- LEAN: Rust's `SmtApplicationBuf::new`, which builds the application that
`SmtTermBuf::Application` holds; here the term, as the application is held flat. -/
/-- Creates an application of `function` to `args` if `args` is nonempty. -/
def TermBuf.newApplication {HandledSort HandledTerm : Type} (function : IdentBuf)
    (sort : Option HandledSort) (args : Array HandledTerm) :
    Except EmptyArgumentsError (TermBuf HandledSort HandledTerm) :=
  if h : 0 < args.size then .ok (.application function sort args h) else .error {}

/--
View of an S-expression (special constant, symbol, reserved word, keyword, or a list of
S-expressions).
-/
inductive SExpr (HandledSExpr : Type) where
  /-- Special constant, e.g. `42` or `"hello"`. -/
  | specialConstant (constant : SpecialConstant)
  /-- Symbol, e.g. `x` or `|a b|`. -/
  | symbol (symbol : Symbol)
  /-- Reserved word, e.g. `let` or `_`. -/
  | reserved (word : Lexicon.Reserved)
  /-- Keyword, e.g. `:named`. -/
  | keyword (name : Keyword)
  /-- List of S-expressions, e.g. `(a (b 1))`. -/
  | sExprs (items : Multiple HandledSExpr)
  deriving Repr

/-- View of an attribute value (special constant, symbol, or a list of S-expressions). -/
inductive AttributeValue (HandledSExpr : Type) where
  /-- Special constant, e.g. `2.6` in `:smt-lib-version 2.6`. -/
  | specialConstant (constant : SpecialConstant)
  /-- Symbol, e.g. `sat` in `:status sat`. -/
  | symbol (symbol : Symbol)
  /-- List of S-expressions, e.g. `(a 1)` in `:my-attribute (a 1)`. -/
  | sExprs (items : Multiple HandledSExpr)
  deriving Repr

/--
Owned S-expression (special constant, symbol, reserved word, keyword, or a list of
S-expressions).
-/
inductive SExprBuf (HandledSExpr : Type) where
  /-- Special constant, e.g. `42` or `"hello"`. -/
  | specialConstant (constant : SpecialConstantBuf)
  /-- Symbol, e.g. `x` or `|a b|`. -/
  | symbol (symbol : SymbolBuf)
  /-- Reserved word, e.g. `let` or `_`. -/
  | reserved (word : Lexicon.Reserved)
  /-- Keyword, e.g. `:named`. -/
  | keyword (name : KeywordBuf)
  /-- List of S-expressions, e.g. `(a (b 1))`. -/
  | sExprs (items : Array HandledSExpr)
  deriving Repr

/-- Converts into `SExprBuf`. -/
def SExpr.intoOwned {HandledSExpr : Type} : SExpr HandledSExpr → SExprBuf HandledSExpr
  | .specialConstant constant => .specialConstant constant.intoOwned
  | .symbol name => .symbol name.intoOwned
  | .reserved word => .reserved word
  | .keyword name => .keyword name.intoOwned
  | .sExprs items => .sExprs items.asSlice

/-- Views as `SExpr`. -/
def SExprBuf.viewMut {HandledSExpr : Type} : SExprBuf HandledSExpr → SExpr HandledSExpr
  | .specialConstant constant => .specialConstant constant.view
  | .symbol name => .symbol name.view
  | .reserved word => .reserved word
  | .keyword name => .keyword name.view
  | .sExprs items => .sExprs (Multiple.new items)

/-- Owned attribute value (special constant, symbol, or a list of S-expressions). -/
inductive AttributeValueBuf (HandledSExpr : Type) where
  /-- Special constant, e.g. `2.6` in `:smt-lib-version 2.6`. -/
  | specialConstant (constant : SpecialConstantBuf)
  /-- Symbol, e.g. `sat` in `:status sat`. -/
  | symbol (symbol : SymbolBuf)
  /-- List of S-expressions, e.g. `(a 1)` in `:my-attribute (a 1)`. -/
  | sExprs (items : Array HandledSExpr)
  deriving Repr

/-- Converts into `AttributeValueBuf`. -/
def AttributeValue.intoOwned {HandledSExpr : Type} :
    AttributeValue HandledSExpr → AttributeValueBuf HandledSExpr
  | .specialConstant constant => .specialConstant constant.intoOwned
  | .symbol name => .symbol name.intoOwned
  | .sExprs items => .sExprs items.asSlice

/-- Views as `AttributeValue`. -/
def AttributeValueBuf.viewMut {HandledSExpr : Type} :
    AttributeValueBuf HandledSExpr → AttributeValue HandledSExpr
  | .specialConstant constant => .specialConstant constant.view
  | .symbol name => .symbol name.view
  | .sExprs items => .sExprs (Multiple.new items)

/-! ## Tokens of the nodes -/

section AppendTokens

open BSmtLib.Token (AppendTokens TokensCursor)
open BSmtLib (Token)

private def appendIndex (index : Index) (tokens : TokensCursor) : TokensCursor :=
  tokens.push (match index with
    | .numeral numeral => .numeral numeral
    | .symbol symbol => .symbol symbol)

private def appendIndices (indices : Array Index) (tokens : TokensCursor) : TokensCursor :=
  indices.foldl (fun tokens index => appendIndex index tokens) tokens

/-- Appends an identifier. -/
private def appendIdent (ident : Ident) (tokens : TokensCursor) : TokensCursor :=
  if ident.indices.isEmpty then
    -- just the symbol
    tokens.push (.symbol ident.name)
  else
    -- indexed identifier: ( _ symbol index+ ).
    let tokens := tokens.push .parenOpen
    let tokens := tokens.push (.reserved (.general .underscore))
    let tokens := tokens.push (.symbol ident.name)
    let tokens := appendIndices ident.indices tokens
    tokens.push .parenClose

/-- Appends a potentially qualified identifier. -/
private def appendQualifiedIdent {HandledSort : Type} [AppendTokens HandledSort] (ident : Ident)
    (sort : Option HandledSort) (tokens : TokensCursor) : TokensCursor :=
  match sort with
  | none => appendIdent ident tokens
  | some sort =>
    -- use the qualification syntax: ( as identifier sort )
    let tokens := tokens.push .parenOpen
    let tokens := tokens.push (.reserved (.general .as))
    let tokens := appendIdent ident tokens
    let tokens := AppendTokens.appendTokens sort tokens
    tokens.push .parenClose

private def appendSpecialConstant (constant : SpecialConstant) (tokens : TokensCursor) :
    TokensCursor :=
  tokens.push (match constant with
    | .numeral value => .numeral value
    | .decimal value => .decimal value
    | .hexadecimal value => .hexadecimal value
    | .binary value => .binary value
    | .string value => .string value)

private def appendSimplePattern (pattern : SimplePattern) (tokens : TokensCursor) :
    TokensCursor :=
  tokens.push (match pattern with
    | .symbol symbol => .symbol symbol
    | .wildcard => .reserved (.general .underscore))

private def appendSimplePatterns (patterns : Array SimplePattern) (tokens : TokensCursor) :
    TokensCursor :=
  patterns.foldl (fun tokens pattern => appendSimplePattern pattern tokens) tokens

/-- Appends a pattern application. -/
private def appendPatternApplication (application : PatternApplication)
    (tokens : TokensCursor) : TokensCursor :=
  -- use the pattern application syntax: ( constructor pattern+ )
  let tokens := tokens.push .parenOpen
  let tokens := tokens.push (.symbol application.constructor)
  let tokens := appendSimplePatterns application.args tokens
  tokens.push .parenClose

private def appendPattern (pattern : Pattern) (tokens : TokensCursor) : TokensCursor :=
  match pattern with
  | .simple simple => appendSimplePattern simple tokens
  | .application application => appendPatternApplication application tokens

/- LEAN: the counterpart of the Rust macro `append_tokens_by_view!`: the appending of a node,
viewed or owned, by the function that appends its view. The views of Rust's `SmtIndices` and
`SmtSimplePatterns` are arrays here, which the instance for arrays appends. -/
set_option hygiene false in
local macro "append_tokens_by_view " view:ident buf:ident append:ident : command =>
  `(@[no_expose] instance : AppendTokens $view := ⟨$append⟩

    @[no_expose] instance : AppendTokens $buf := ⟨fun self tokens => $append self.view tokens⟩)

append_tokens_by_view Index IndexBuf appendIndex
append_tokens_by_view Ident IdentBuf appendIdent
append_tokens_by_view SpecialConstant SpecialConstantBuf appendSpecialConstant
append_tokens_by_view SimplePattern SimplePatternBuf appendSimplePattern
append_tokens_by_view PatternApplication PatternApplicationBuf appendPatternApplication
append_tokens_by_view Pattern PatternBuf appendPattern

@[no_expose] instance : AppendTokens IndicesBuf :=
  ⟨fun self tokens => appendIndices self.view tokens⟩

@[no_expose] instance : AppendTokens SimplePatternsBuf :=
  ⟨fun self tokens => appendSimplePatterns self.view tokens⟩

@[no_expose] instance {HandledSort : Type} [AppendTokens HandledSort] :
    AppendTokens (QualifiedIdent HandledSort) :=
  ⟨fun self tokens => appendQualifiedIdent self.ident self.sort tokens⟩

@[no_expose] instance {HandledSort : Type} [AppendTokens HandledSort] :
    AppendTokens (QualifiedIdentBuf HandledSort) :=
  ⟨fun self tokens => appendQualifiedIdent self.ident.view self.sort tokens⟩

/-- Appends a sort of the identifier with the arguments. -/
private def appendSort {HandledSort : Type} [AppendTokens HandledSort] (ident : Ident)
    (args : Array HandledSort) (tokens : TokensCursor) : TokensCursor :=
  if args.isEmpty then
    -- a sort without arguments is represented by its identifier
    appendIdent ident tokens
  else
    -- use the syntax for a sort with arguments: ( identifier sort+ )
    let tokens := tokens.push .parenOpen
    let tokens := appendIdent ident tokens
    let tokens := AppendTokens.appendTokens args tokens
    tokens.push .parenClose

/-- Appends an application of the potentially qualified identifier to the arguments. -/
private def appendApplication {HandledSort HandledTerm : Type} [AppendTokens HandledSort]
    [AppendTokens HandledTerm] (function : Ident) (sort : Option HandledSort)
    (args : Array HandledTerm) (tokens : TokensCursor) : TokensCursor :=
  -- use the application syntax: ( function term+ )
  let tokens := tokens.push .parenOpen
  let tokens := appendQualifiedIdent function sort tokens
  let tokens := AppendTokens.appendTokens args tokens
  tokens.push .parenClose

/-- Appends a list of S-expressions, enclosed in parentheses: ( s_expr* ). -/
private def appendSExprs {HandledSExpr : Type} [AppendTokens HandledSExpr]
    (items : Array HandledSExpr) (tokens : TokensCursor) : TokensCursor :=
  let tokens := tokens.push .parenOpen
  let tokens := AppendTokens.appendTokens items tokens
  tokens.push .parenClose

@[no_expose] instance {HandledSort : Type} [AppendTokens HandledSort] :
    AppendTokens (SortBuf HandledSort) :=
  ⟨fun self tokens => appendSort self.ident.view self.args tokens⟩

@[no_expose] instance {HandledSort HandledTerm : Type} [AppendTokens HandledSort]
    [AppendTokens HandledTerm] : AppendTokens (Term HandledSort HandledTerm) where
  appendTokens self tokens :=
    match self with
    | .specialConstant constant => appendSpecialConstant constant tokens
    | .qualifiedIdent ident sort => appendQualifiedIdent ident sort tokens
    | .application function sort args _ => appendApplication function sort args.asSlice tokens

@[no_expose] instance {HandledSort HandledTerm : Type} [AppendTokens HandledSort]
    [AppendTokens HandledTerm] : AppendTokens (TermBuf HandledSort HandledTerm) where
  appendTokens self tokens :=
    match self with
    | .specialConstant constant => appendSpecialConstant constant.view tokens
    | .qualifiedIdent ident sort => appendQualifiedIdent ident.view sort tokens
    | .application function sort args _ => appendApplication function.view sort args tokens

@[no_expose] instance {HandledSExpr : Type} [AppendTokens HandledSExpr] :
    AppendTokens (AttributeValue HandledSExpr) where
  appendTokens self tokens :=
    match self with
    | .specialConstant constant => appendSpecialConstant constant tokens
    | .symbol symbol => tokens.push (.symbol symbol)
    | .sExprs items => appendSExprs items.asSlice tokens

@[no_expose] instance {HandledSExpr : Type} [AppendTokens HandledSExpr] :
    AppendTokens (AttributeValueBuf HandledSExpr) where
  appendTokens self tokens :=
    match self with
    | .specialConstant constant => appendSpecialConstant constant.view tokens
    | .symbol symbol => tokens.push (.symbol symbol.view)
    | .sExprs items => appendSExprs items tokens

@[no_expose] instance {HandledSExpr : Type} [AppendTokens HandledSExpr] :
    AppendTokens (SExpr HandledSExpr) where
  appendTokens self tokens :=
    match self with
    | .specialConstant constant => appendSpecialConstant constant tokens
    | .symbol symbol => tokens.push (.symbol symbol)
    | .reserved word => tokens.push (.reserved word)
    | .keyword name => tokens.push (.keyword name)
    | .sExprs items => appendSExprs items.asSlice tokens

@[no_expose] instance {HandledSExpr : Type} [AppendTokens HandledSExpr] :
    AppendTokens (SExprBuf HandledSExpr) where
  appendTokens self tokens :=
    match self with
    | .specialConstant constant => appendSpecialConstant constant.view tokens
    | .symbol symbol => tokens.push (.symbol symbol.view)
    | .reserved word => tokens.push (.reserved word)
    | .keyword name => tokens.push (.keyword name.view)
    | .sExprs items => appendSExprs items tokens

end AppendTokens

end BSmtLib.Grammar.Nodes
