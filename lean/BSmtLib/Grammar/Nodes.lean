module

public import BSmtLib.Lexicon.Value
public import BSmtLib.Lexicon.Reserved
public import BSmtLib.Grammar.Multiple
public import BSmtLib.Token.AppendTokens

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

namespace BSmtLib.Grammar.Nodes

open BSmtLib.Lexicon.Value (SymbolBuf Symbol NumeralBuf Numeral DecimalBuf Decimal HexDigitsBuf
  HexDigits BinDigitsBuf BinDigits StringContentBuf StringContent KeywordBuf Keyword)

inductive IndexBuf where
  | numeral (digits : NumeralBuf)
  | symbol (symbol : SymbolBuf)
  deriving Repr

/-- An index of an indexed identifier. -/
inductive Index where
  | numeral (digits : Numeral)
  | symbol (symbol : Symbol)
  deriving Repr

def Index.intoOwned : Index → IndexBuf
  | .numeral digits => .numeral digits.intoOwned
  | .symbol name => .symbol name.intoOwned

def IndexBuf.view : IndexBuf → Index
  | .numeral digits => .numeral digits.view
  | .symbol name => .symbol name.view

/- LEAN: the index with its bytes copied, so that it holds no storage of the input; how the owned
buffers keep what they are given. -/
@[inline]
def Index.Internal.copy : Index → Index
  | .numeral digits => .numeral digits.intoOwned.view
  | .symbol name => .symbol name.intoOwned.view

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

def get? (self : IndicesBuf) (index : Nat) : Option Index := self.entries[index]?

@[no_expose] instance : Inhabited IndicesBuf := ⟨new⟩

/- LEAN: Rust's `iter`, as for the containers of `BSmtLib.Grammar.Multiple`. -/
@[no_expose] instance {m : Type → Type} [Monad m] : ForIn m IndicesBuf Index where
  forIn self init f := ForIn.forIn self.entries init f

/- LEAN: Rust's `Debug`, which lists the indices. -/
@[no_expose] instance : Repr IndicesBuf := ⟨fun s p => reprPrec s.entries p⟩

end IndicesBuf

structure IdentBuf where
  name : SymbolBuf
  indices : IndicesBuf
  deriving Repr

/-- An identifier: a symbol, with its indices if it is indexed. -/
/- LEAN: Rust's `indices` are `SmtIndices`, a container of the views; here an array. -/
structure Ident where
  name : Symbol
  indices : Array Index
  deriving Repr

namespace IdentBuf

/-- An identifier that is a symbol alone, not indexed. -/
def newSimple (name : SymbolBuf) : IdentBuf :=
  { name, indices := .new }

def view (self : IdentBuf) : Ident :=
  { name := self.name.view, indices := self.indices.view }

end IdentBuf

def Ident.intoOwned (self : Ident) : IdentBuf :=
  { name := self.name.intoOwned, indices := self.indices.foldl IndicesBuf.push .new }

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

/-- A qualified identifier: an identifier, with the sort it is qualified with by `as`, if it is
qualified. -/
structure QualifiedIdent (HandledSort : Type) where
  ident : Ident
  sort : Option HandledSort
  deriving Repr

def QualifiedIdent.intoOwned {HandledSort : Type} (self : QualifiedIdent HandledSort) :
    QualifiedIdentBuf HandledSort :=
  { ident := self.ident.intoOwned, sort := self.sort }

/-- Owned sort. -/
/- LEAN: parameterised by the handled sorts, as `QualifiedIdentBuf` is. A sort is handed over
flat, as its identifier and its argument sorts, so there is no view of a sort to convert from or
to (Rust's `SmtSort::into_owned` and `SmtSortBuf::view_mut`); the fields are built from the
parts handed over. -/
structure SortBuf (HandledSort : Type) where
  ident : IdentBuf
  args : Array HandledSort
  deriving Repr

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

def SpecialConstantBuf.view : SpecialConstantBuf → SpecialConstant
  | .numeral digits => .numeral digits.view
  | .decimal text => .decimal text.view
  | .hexadecimal digits => .hexadecimal digits.view
  | .binary digits => .binary digits.view
  | .string content => .string content.view

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

/-- A symbol, or the wildcard `_`, in a pattern. -/
inductive SimplePattern where
  | symbol (symbol : Symbol)
  | wildcard
  deriving Repr

def SimplePattern.intoOwned : SimplePattern → SimplePatternBuf
  | .symbol name => .symbol name.intoOwned
  | .wildcard => .wildcard

def SimplePatternBuf.view : SimplePatternBuf → SimplePattern
  | .symbol name => .symbol name.view
  | .wildcard => .wildcard

/- LEAN: the simple pattern with its bytes copied, so that it holds no storage of the input; how
the owned buffers keep what they are given. -/
@[inline]
def SimplePattern.Internal.copy : SimplePattern → SimplePattern
  | .symbol name => .symbol name.intoOwned.view
  | .wildcard => .wildcard

/-- Owned arguments of a constructor pattern, from which the `args` of `PatternApplication` are
viewed. -/
/- LEAN: Rust's `SmtSimplePatternsBuf`, from which `SmtSimplePatterns` is viewed; Lean's
arguments are an `Array` of the views (see `PatternApplication`), which `view` gives. Each
pattern is a view of a copy of its bytes that the buffer made, so the view needs no copy. -/
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

/-- An application or a constructor pattern was to be built without arguments. -/
structure EmptyArgumentsError where
  deriving BEq, Hashable, Repr

@[no_expose] instance : ToString EmptyArgumentsError :=
  ⟨fun _ => "no arguments provided where at least one is required"⟩

/--
A constructor applied to at least one variable or wildcard, as a match pattern to be handled.
-/
/- LEAN: Rust's fields are private, so that the arguments cannot be empty, and read through the
getters `constructor` and `args`; here the fields are public and the proof `nonempty` guards
the arguments. Rust's `args` are `SmtSimplePatterns`, a container of the views; here an
array. -/
structure PatternApplication where
  constructor : Symbol
  args : Array SimplePattern
  /-- There is at least one argument. -/
  nonempty : 0 < args.size
  deriving Repr

/--
A constructor applied to at least one variable or wildcard, from which `PatternApplication` is
viewed.
-/
/- LEAN: the fields are public, as `PatternApplication`'s are, with the proof `nonempty`. -/
structure PatternApplicationBuf where
  constructor : SymbolBuf
  args : SimplePatternsBuf
  /-- There is at least one argument. -/
  nonempty : 0 < args.len
  deriving Repr

namespace PatternApplication

/-- The arguments of an array that is not empty are at least one. -/
theorem Internal.size_pos {args : Array SimplePattern} (h : ¬args.isEmpty) : 0 < args.size :=
  Nat.pos_of_ne_zero fun hz => h (Array.isEmpty_iff_size_eq_zero.mpr hz)

/-- The constructor applied to the arguments; an error if there are none. -/
def new (constructor : Symbol) (args : Array SimplePattern) :
    Except EmptyArgumentsError PatternApplication :=
  if h : 0 < args.size then .ok ⟨constructor, args, h⟩ else .error {}

def intoOwned (self : PatternApplication) : PatternApplicationBuf :=
  { constructor := self.constructor.intoOwned
    args := SimplePatternsBuf.Internal.ofViews self.args
    nonempty := by rw [SimplePatternsBuf.Internal.len_ofViews]; exact self.nonempty }

end PatternApplication

namespace PatternApplicationBuf

/-- The constructor applied to the arguments; an error if there are none. -/
def new (constructor : SymbolBuf) (args : SimplePatternsBuf) :
    Except EmptyArgumentsError PatternApplicationBuf :=
  if h : 0 < args.len then .ok ⟨constructor, args, h⟩ else .error {}

def intoParts (self : PatternApplicationBuf) : SymbolBuf × SimplePatternsBuf :=
  (self.constructor, self.args)

def view (self : PatternApplicationBuf) : PatternApplication :=
  { constructor := self.constructor.view, args := self.args.view,
    nonempty := by rw [SimplePatternsBuf.size_view]; exact self.nonempty }

end PatternApplicationBuf

/-- Match pattern: a symbol, a wildcard, or a constructor application. -/
inductive PatternBuf where
  /-- A simple match pattern, either a symbol or a wildcard. -/
  | simple (pattern : SimplePatternBuf)
  /-- A constructor applied to at least one variable or wildcard. -/
  | application (application : PatternApplicationBuf)
  deriving Repr

/-- The pattern of a case of `match`. -/
inductive Pattern where
  /-- A simple match pattern, either a symbol or a wildcard. -/
  | simple (pattern : SimplePattern)
  /-- A constructor applied to at least one variable or wildcard. -/
  | application (application : PatternApplication)
  deriving Repr

def Pattern.intoOwned : Pattern → PatternBuf
  | .simple pattern => .simple pattern.intoOwned
  | .application app => .application app.intoOwned

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

/-- The two quantifiers. -/
inductive QuantifierKind where
  | «exists»
  | «forall»
  deriving BEq, Hashable, Repr

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
  | application (function : Ident) (sort : Option HandledSort) (args : Multiple HandledTerm)
      (nonempty : 0 < args.len)
  deriving Repr

/- LEAN: Rust's `SmtApplication::new`, which builds the application that `SmtTerm::Application`
holds; here the term, as the application is handed over flat. -/
/-- The term that applies the function to the arguments; an error if there are none. -/
def Term.newApplication {HandledSort HandledTerm : Type} (function : Ident)
    (sort : Option HandledSort) (args : Multiple HandledTerm) :
    Except EmptyArgumentsError (Term HandledSort HandledTerm) :=
  if h : 0 < args.len then .ok (.application function sort args h) else .error {}

/-- Owned term (special constant, qualified identifier, or application). -/
/- LEAN: Rust's variants hold `SmtQualifiedIdentBuf` and `SmtApplicationBuf`; here their fields
are the constructors' own, as those of `Term` are. -/
inductive TermBuf (HandledSort HandledTerm : Type) where
  | specialConstant (constant : SpecialConstantBuf)
  /-- A qualified identifier: Rust's `SmtQualifiedIdentBuf { ident, sort }`, its fields flat. -/
  | qualifiedIdent (ident : IdentBuf) (sort : Option HandledSort)
  /--
  A term that is an application: Rust's `SmtApplicationBuf { function, args }`, its fields flat,
  the qualified identifier `function` as `function` and `sort`.

  It is guaranteed that `args` are nonempty.
  -/
  | application (function : IdentBuf) (sort : Option HandledSort) (args : Array HandledTerm)
      (nonempty : 0 < args.size)
  deriving Repr

def Term.intoOwned {HandledSort HandledTerm : Type} :
    Term HandledSort HandledTerm → TermBuf HandledSort HandledTerm
  | .specialConstant constant => .specialConstant constant.intoOwned
  | .qualifiedIdent ident sort => .qualifiedIdent ident.intoOwned sort
  | .application function sort args nonempty =>
    .application function.intoOwned sort args.asSlice
      (by rw [Grammar.Multiple.size_asSlice]; exact nonempty)

/- LEAN: Rust's `SmtApplicationBuf::new`, which builds the application that
`SmtTermBuf::Application` holds; here the term, as the application is held flat. -/
/-- The term that applies the function to the arguments; an error if there are none. -/
def TermBuf.newApplication {HandledSort HandledTerm : Type} (function : IdentBuf)
    (sort : Option HandledSort) (args : Array HandledTerm) :
    Except EmptyArgumentsError (TermBuf HandledSort HandledTerm) :=
  if h : 0 < args.size then .ok (.application function sort args h) else .error {}

/-- An s-expression as the handler receives it, its items already handled. -/
inductive SExpr (HandledSExpr : Type) where
  | specialConstant (constant : SpecialConstant)
  | symbol (symbol : Symbol)
  | reserved (word : Lexicon.Reserved)
  | keyword (name : Keyword)
  | sExprs (items : Multiple HandledSExpr)
  deriving Repr

/--
The value of an attribute as the handler receives it, the s-expressions of a list value already
handled. A list value is handed over as its items.
-/
inductive AttributeValue (HandledSExpr : Type) where
  | specialConstant (constant : SpecialConstant)
  | symbol (symbol : Symbol)
  | sExprs (items : Multiple HandledSExpr)
  deriving Repr

/--
Owned S-expression (special constant, symbol, reserved word, keyword, or a list of
S-expressions).
-/
inductive SExprBuf (HandledSExpr : Type) where
  | specialConstant (constant : SpecialConstantBuf)
  | symbol (symbol : SymbolBuf)
  | reserved (word : Lexicon.Reserved)
  | keyword (name : KeywordBuf)
  | sExprs (items : Array HandledSExpr)
  deriving Repr

def SExpr.intoOwned {HandledSExpr : Type} : SExpr HandledSExpr → SExprBuf HandledSExpr
  | .specialConstant constant => .specialConstant constant.intoOwned
  | .symbol name => .symbol name.intoOwned
  | .reserved word => .reserved word
  | .keyword name => .keyword name.intoOwned
  | .sExprs items => .sExprs items.asSlice

def SExprBuf.viewMut {HandledSExpr : Type} : SExprBuf HandledSExpr → SExpr HandledSExpr
  | .specialConstant constant => .specialConstant constant.view
  | .symbol name => .symbol name.view
  | .reserved word => .reserved word
  | .keyword name => .keyword name.view
  | .sExprs items => .sExprs (Multiple.new items)

/-- Owned attribute value (special constant, symbol, or a list of S-expressions). -/
inductive AttributeValueBuf (HandledSExpr : Type) where
  | specialConstant (constant : SpecialConstantBuf)
  | symbol (symbol : SymbolBuf)
  | sExprs (items : Array HandledSExpr)
  deriving Repr

def AttributeValue.intoOwned {HandledSExpr : Type} :
    AttributeValue HandledSExpr → AttributeValueBuf HandledSExpr
  | .specialConstant constant => .specialConstant constant.intoOwned
  | .symbol name => .symbol name.intoOwned
  | .sExprs items => .sExprs items.asSlice

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
