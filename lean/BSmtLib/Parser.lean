module

public import BSmtLib.Handler
public import BSmtLib.Token
public import BSmtLib.Token.Cursor

public section

/-!
# Parsers of syntactic categories, commands, and scripts, and parser combinators

A parser implements `Parse` and parses tokens, calling a handler that implements `Handler` to
handle grammar constructs. The parser can be connected to a token producer through
`ParseAdapter` that implements `Token.Consume` and `Token.ConsumeFrom` for all token cursors,
and passes the handler and the parse state (`ParseState`) to the parser.

Parsers for all SMT-LIB grammar nodes are provided. As it is unknown if an attribute is a
name-only attribute (`:name`) or a name-value attribute (`:key value`) before the next parsed
token, only parsers for attribute and multiple-attribute occurrences followed by a closing
parenthesis are provided through `ClosedAttributeParser` and `ClosedMultipleAttributeParser`.
This is enough to parse all attribute occurrences in standard SMT-LIB.

A single SMT-LIB command can be parsed using `CommandParser`, which requires the handler to also
implement `CommandHandler`.

A whole SMT-LIB script can be parsed using `ScriptParser`. It automatically discards after
`(exit)` by calling `Token.Cursor.discardRest` and switches SMT-LIB versions after the SMT-LIB
command `(set-info :smt-lib-version <version>)` by requesting the cursor to switch through
`Token.Cursor.setVersion` and informing the handler of the new version in force through
`Handler.setVersion` if successful.

A custom parser can be crafted using combinators:
- sequential combinators `PairParser`, `Tuple3Parser` etc.,
- parenthesis enclosers `OpenedParser`, `ClosedParser`, `ParenParser`,
- multiple-item parsers `ClosedMultipleParser`, `ParenMultipleParser`, `ClosedMaximumParser`
  and `ParenMaximumParser`.

Additionally, `CommandPayloadParser` is provided to simplify implementing parsing of
nonstandard commands for handlers that support them.

If needed, a parser can also be implemented manually.
-/

namespace BSmtLib.Parser

open BSmtLib.Grammar.Nodes BSmtLib.Handler
open BSmtLib.Lexicon.Value (Keyword Symbol)
open BSmtLib.Token (TokenCategory)
open BSmtLib (Version Token)
open BSmtLib.Lexicon.Reserved (GeneralReserved)


/--
Syntax item expected by a parser.

Used in `SyntaxErrorKind.expected`.
-/
inductive SyntaxExpected where
  /-- Token of the given category. -/
  | token (category : TokenCategory)
  /-- Reserved word, e.g. `_` or `as`. -/
  | reserved (word : Lexicon.Reserved)
  /-- Symbol (quoted or unquoted), e.g. `x` or `|a b|`. -/
  | symbol
  /-- Index of an identifier (a numeral or a symbol), e.g. `32` in `(_ BitVec 32)`. -/
  | index
  /-- Identifier, e.g. `x` or `(_ bv0 32)`. -/
  | ident
  /-- Sort, e.g. `Int` or `(Array Int Bool)`. -/
  | sort
  /-- Term, e.g. `x` or `(+ x 1)`. -/
  | term
  /-- S-expression, e.g. `a` or `(a (b 1))`. -/
  | sExpr
  /-- Attribute, e.g. `:status sat` or `:named p`. -/
  | attribute
  /--
  What follows the opening parenthesis of a compound term, e.g. `f` in `(f x)` or `let` in
  `(let ((x 1)) x)`.
  -/
  | operator
  /-- Name of a command, e.g. `assert` or `check-sat`. -/
  | commandName
  /-- Propositional literal (a symbol or its negation), e.g. `p` or `(not p)`. -/
  | propositionalLiteral
  deriving BEq, Hashable, Repr

/--
List that was expected to be non-empty.

Used in `SyntaxErrorKind.empty`.
-/
inductive NonEmptyList where
  /-- Indices of an identifier, e.g. `32` in `(_ BitVec 32)`. -/
  | identIndices
  /-- Arguments of a sort, e.g. `Int Bool` in `(Array Int Bool)`. -/
  | sortApplication
  /-- Arguments of an application, e.g. `x 1` in `(+ x 1)`. -/
  | termApplication
  /-- Bindings of `let`, e.g. `((x 1))` in `(let ((x 1)) x)`. -/
  | letBindings
  /-- Attributes of an annotation, e.g. `:named p` in `(! x :named p)`. -/
  | annotation
  /-- Variables of a quantifier, e.g. `((x Int))` in `(forall ((x Int)) p)`. -/
  | quantifierVars
  /-- Variables of `lambda`, e.g. `((x Int))` in `(lambda ((x Int)) x)`. -/
  | lambdaVars
  /-- Functions of `define-funs-rec`, e.g. `((f () Int) (g () Int))`. -/
  | functionSignatures
  /-- Sorts of `declare-datatypes`, e.g. `((A 0) (B 0))`. -/
  | datatypeIntroductions
  /-- Parameters of a datatype, e.g. `(T)` in `(par (T) ((c (f T))))`. -/
  | datatypeParameters
  /--
  Constructors of a datatype, e.g. `((c (f T)))` in `(par (T) ((c (f T))))`.

  This arises only in the `par` form: without it, the first `(` opens a constructor.
  -/
  | datatypeConstructors
  /-- Arguments of a constructor pattern, e.g. `h t` in `(cons h t)`. -/
  | patternArguments
  /-- Cases of `match`, e.g. `((nil 0) ((cons h t) h))`. -/
  | matchCases
  /-- Terms of `get-value`, e.g. `(x y)` in `(get-value (x y))`. -/
  | getValueTerms
  deriving BEq, Hashable, Repr

/--
Announced item that did not arrive (function body or datatype).

Used in `SyntaxErrorKind.missing`.
-/
inductive MissingItem where
  /--
  Body of a function of `define-funs-rec`.

  For example, `(define-funs-rec ((f () Int) (g () Int)) (1))` lacks the body of `g`.
  -/
  | functionBody
  /--
  Datatype of `declare-datatypes`.

  For example, `(declare-datatypes ((A 0) (B 0)) (((a))))` lacks the datatype `B`.
  -/
  | datatype
  deriving BEq, Hashable, Repr

/- LEAN: Rust's `SmtSyntaxErrorKind`. Rust's `Expected` holds a static slice; here it is an
array, which the library builds from literals. -/
/-- Why the syntax was rejected (expected item, empty list, or missing item). -/
inductive SyntaxErrorKind where
  /-- One of the items was expected here, e.g. a term in `(assert)`. -/
  | expected (items : Array SyntaxExpected)
  /-- A list that must not be empty is empty, e.g. the indices in `(_ BitVec)`. -/
  | empty (list : NonEmptyList)
  /--
  Fewer items arrived than were announced, e.g. fewer bodies than functions in
  `define-funs-rec`.
  -/
  | missing (item : MissingItem)
  deriving BEq, Hashable, Repr

/-- Why switching the version failed (unsupported version or too many declarations). -/
inductive VersionErrorKind where
  /--
  The requested version was rejected as not supported, e.g. `3.0`.

  The declared version is unknown (e.g. `3.0` or `foo`), not allowed by the posture, or
  refused by the cursor.
  -/
  | unsupported
  /--
  The script declared its version more times than allowed.

  The number is the maximum that the posture allows.
  -/
  | tooManyDeclarations (limit : Nat)
  deriving BEq, Hashable, Repr

/-- Why parsing failed (syntax, version, or handler error). -/
inductive ParseErrorKind (ε : Type) where
  /-- The tokens do not form the syntax the parser accepts. -/
  | syntax (kind : SyntaxErrorKind)
  /-- The script declares a version that cannot be used. -/
  | version (kind : VersionErrorKind)
  /-- The handler failed. -/
  | handler (error : ε)
  deriving BEq, Repr

/- LEAN: Rust's `SmtParseError`, which boxes its kind so that parser results stay small. A
structure of one field is represented by the field, so no box is needed. The constructor is
private, as Rust's field is, and the library builds an error with `ParseError.Internal.new`. The
kind is readable as `error.kind`, replacing the getters `kind` and `into_kind`. -/
/-- Error that forced parsing to stop. -/
structure ParseError (E : Type) where
  private mk ::
  /-- Returns the kind of the error. -/
  kind : ParseErrorKind E
  deriving BEq, Repr

/-- The error with the given cause. -/
@[inline]
def ParseError.Internal.new {E : Type} (kind : ParseErrorKind E) : ParseError E :=
  { kind }

@[simp]
theorem ParseError.Internal.kind_new {E : Type} (kind : ParseErrorKind E) :
    (ParseError.Internal.new kind).kind = kind :=
  (rfl)

/-- An error is the one built from its cause. -/
@[simp]
theorem ParseError.Internal.new_eta {E : Type} (error : ParseError E) :
    ParseError.Internal.new error.kind = error :=
  (rfl)

/-- Two errors built from the same cause are equal. -/
theorem ParseError.Internal.new_inj {E : Type} {kind kind' : ParseErrorKind E} :
    ParseError.Internal.new kind = ParseError.Internal.new kind' ↔ kind = kind' := by
  constructor
  · intro h
    exact congrArg ParseError.kind h
  · rintro rfl
    rfl

/- LEAN: Rust's `Display` implementations are `ToString` instances, with the same text. -/
/-- The name of the item in a message. -/
private def SyntaxExpected.name : SyntaxExpected → String
  | .token category =>
    match category with
    | .parenOpen => "`(`"
    | .parenClose => "`)`"
    | .numeral => "numeral"
    | .decimal => "decimal"
    | .hexadecimal => "hexadecimal"
    | .binary => "binary"
    | .string => "string literal"
    | .keyword => "keyword"
    | .unquotedSymbol => "simple symbol"
    | .quotedSymbol => "quoted symbol"
    | .whitespace => "whitespace"
    | .comment => "comment"
    | .endOfFile => "end of input"
  | .reserved word => s!"`{word.asStr}`"
  | .symbol => "symbol"
  | .index => "index"
  | .ident => "identifier"
  | .sort => "sort"
  | .term => "term"
  | .sExpr => "s-expression"
  | .attribute => "attribute"
  | .operator => "operator"
  | .commandName => "command name"
  | .propositionalLiteral => "propositional literal"

@[no_expose] instance : ToString SyntaxExpected := ⟨fun self => s!"expected {self.name}"⟩

@[no_expose] instance : ToString NonEmptyList where
  toString self :=
    let list := match self with
      | .identIndices => "indices of identifier"
      | .sortApplication => "arguments of sort"
      | .termApplication => "arguments of application"
      | .letBindings => "bindings of `let`"
      | .annotation => "attributes of annotation"
      | .quantifierVars => "variables of quantifier"
      | .lambdaVars => "variables of `lambda`"
      | .functionSignatures => "functions of `define-funs-rec`"
      | .datatypeIntroductions => "sorts of `declare-datatypes`"
      | .datatypeParameters => "parameters of datatype"
      | .datatypeConstructors => "constructors of datatype"
      | .patternArguments => "arguments of constructor pattern"
      | .matchCases => "cases of `match`"
      | .getValueTerms => "terms of `get-value`"
    s!"{list} must not be empty"

@[no_expose] instance : ToString MissingItem where
  toString
    | .functionBody => "too few function bodies for `define-funs-rec`"
    | .datatype => "too few datatypes for `declare-datatypes`"

@[no_expose] instance : ToString SyntaxErrorKind where
  toString
    | .expected expected =>
      match expected.back? with
      | none => "unexpected token"
      | some last =>
        let rest := expected.pop
        let names := rest.toList.map SyntaxExpected.name
        let joined := match names with
          | [] => ""
          | [first] => s!"{first} or "
          | _ => String.intercalate ", " names ++ ", or "
        s!"expected {joined}{last.name}"
    | .empty list => toString list
    | .missing item => toString item

@[no_expose] instance : ToString VersionErrorKind where
  toString
    | .unsupported => "unsupported version"
    | .tooManyDeclarations max => s!"too many version declarations (at most {max})"

@[no_expose] instance {E : Type} [ToString E] : ToString (ParseErrorKind E) where
  toString
    | .syntax kind => toString kind
    | .version kind => toString kind
    | .handler error => toString error

@[no_expose] instance {E : Type} [ToString E] : ToString (ParseError E) :=
  ⟨fun self => toString self.kind⟩

/-- Creates a handler error. -/
@[inline]
def ParseError.handler {E : Type} (error : E) : ParseError E :=
  ParseError.Internal.new (.handler error)

/-- Creates a syntax error. -/
@[inline]
def ParseError.syntax {E : Type} (kind : SyntaxErrorKind) : ParseError E :=
  ParseError.Internal.new (.syntax kind)

/-- Creates a version error. -/
@[inline]
def ParseError.version {E : Type} (kind : VersionErrorKind) : ParseError E :=
  ParseError.Internal.new (.version kind)

/- LEAN: Rust's `SmtParseState` holds the arena and the slots that the standard parsers share,
all crate-private. The parsers of the port keep their state in themselves, so this one holds
nothing; it is handed to every parser and given back unchanged. The command parser creates a
fresh one for the parser of a nonstandard payload, where Rust passes its own on; as it holds
nothing, the difference cannot be observed. -/
/--
Current state of library parsers.

The state is handed to every parser and given back unchanged.
-/
structure ParseState (H : Type) where
  private mk ::

/- LEAN: Rust's `SmtParseState::new`. -/
/-- Creates the parse state with fresh resources. -/
def ParseState.new {H : Type} : ParseState H := ⟨⟩

instance {H : Type} : Inhabited (ParseState H) := ⟨.new⟩

/- LEAN: Rust's trait `SmtParse<H>`, with the handler as a parameter of the class, so that a
parser type serves every handler. Rust's `parse` takes `&mut self`, the handler, the parse state
and the cursor; here the handler is the state of the monad, and the parser, the parse state and
the cursor are given back. The cursor is given back with the proof that the parser took a
token of it if it had one: the rule that Rust states in words for `SmtConsumeFrom::consume`. -/
/--
Parses a grammar item.

A parser is handed tokens through a cursor until it breaks with its result, e.g. by a
`ParseAdapter` or by a parser that contains it. A library parser that has broken with its
result can parse the next item.

The parser is of the type `P`, with the handler of the type `H` in the monad `m`, whose errors
are of the type `E`, finishing with results of the type `R`.
-/
class Parse (P : Type) (H : Type) (m : outParam (Type → Type)) (E R : outParam Type) where
  /--
  Parses tokens from the cursor, progressing the parser.

  If the cursor has a token, the parser takes at least one, whatever it returns, an error
  included.

  If the parser returns `ControlFlow.continue`, it means all tokens were handled and more are
  wanted: the cursor given back must be empty.

  If the parser returns `ControlFlow.break`, it means it finished the input it accepts (consuming
  exactly its tokens), is returning a result and waiting for processing of the next value.

  Returning an error means that the tokens do not form what the parser accepts, that a version
  switch failed, or that the handler failed. The state of the parser, cursor, and parse state
  given back is then unspecified.

  All library parsers that have an instance of `Parse` are fully self-resetting: after returning
  `ControlFlow.break`, they are back in their initial state.

  The parse state is given back with the parser.
  -/
  parse {Z : Type} [Token.Cursor Z] : P → ParseState H → (cursor : Z) →
    StateT H m (Except (ParseError E) (ControlFlow R) × P × ParseState H ×
      { next : Z // Token.Cursor.HasNext cursor → Token.Cursor.Consumed next cursor })

/- LEAN: Rust's `impl<H: SmtCommandHandler> SmtParse<H> for Infallible`: `Empty` is Lean's type
without values. It asks only for a `Handler`, so that a `CommandHandler` instance can name it as
its non-standard parser while it is being declared. -/
instance {H : Type} {m : Type → Type} [Handler H m] : Parse Empty H m (Handler.Error H) Unit where
  parse parser := nomatch parser

namespace Internal

/-- The monad of the parsers: the handler's, failing with a parse error. -/
abbrev PM (H : Type) {m : Type → Type} [Handler H m] :=
  ExceptT (ParseErrorKind (Handler.Error H)) (StateT H m)

section

variable {H : Type} {m : Type → Type} [Monad m] [Handler H m]

/-- A handler call in a parse: its failure is the handler's. -/
@[inline]
def call {α : Type} (action : ExceptT (Handler.Error H) (StateT H m) α) : PM H α :=
  ExceptT.adapt ParseErrorKind.handler action

/-- A syntax error. -/
@[inline]
def syntaxError {α : Type} (kind : SyntaxErrorKind) : PM H α :=
  throw (.syntax kind)

/-- A version error. -/
@[inline]
def versionError {α : Type} (kind : VersionErrorKind) : PM H α :=
  throw (.version kind)

end

/-! ## The parsers that step by single tokens

The parsers of the port step by single tokens: each is a state machine whose step takes the
version, its state and one token, makes the handler calls the token completes, and either goes
on with a new state or finishes with a result. Before it takes a token it is told that the token
has arrived, so that it can make the calls due at a token's arrival. A step may ask to act on the
cursor: to switch the version, or to discard the rest of the input; the parser goes on once the
cursor has done so. In a state in which a parser holds a parser of its own that takes a cursor
(the command parser in a nonstandard command), it hands the cursor to that parser instead of
taking a token, and goes on as that parser's answer says. `Internal.parseByToken` takes the
tokens of a cursor one by one with such a parser, handing the cursor over where it asks: it is
the `parse` of each of them.
-/


/- LEAN: Rust's parsers match on `SmtToken`. The parser has a type of its own for it,
with the constants as one constructor and whitespace and comments as one, which the loop makes
from the syntax token (`Input.ofSyntax`). -/
/--
A token as the parsers take it: what it stands for in the version it was cut in, or the end of
the input. Words reserved in the version are reserved words; every other simple or quoted
symbol is a symbol.
-/
inductive Input where
  | parenOpen
  | parenClose
  | constant (constant : SpecialConstant)
  | symbol (symbol : Symbol)
  | keyword (name : Keyword)
  | reserved (word : Lexicon.Reserved)
  /-- The end of the input. -/
  | endOfInput
  /-- Whitespace or a comment, which no parser takes. -/
  | layout

namespace Input

/-- Whether the token is the general reserved word. -/
@[inline]
def isWord (token : Input) (word : GeneralReserved) : Bool :=
  match token with
  | .reserved (.general w) => w == word
  | _ => false

end Input

/-- What the token, viewed under its producer's version, stands for. -/
@[inline]
def Input.ofSyntax : Token → Input
  | .parenOpen => .parenOpen
  | .parenClose => .parenClose
  | .numeral value => .constant (.numeral value)
  | .decimal value => .constant (.decimal value)
  | .hexadecimal value => .constant (.hexadecimal value)
  | .binary value => .constant (.binary value)
  | .string value => .constant (.string value)
  | .keyword value => .keyword value
  | .symbol value => .symbol value
  | .reserved word => .reserved word
  | .whitespace _ | .comment _ => .layout
  | .endOfFile => .endOfInput

/-- The syntax token the token was made from (`Input.ofSyntax`), with whitespace and comments as
empty whitespace. -/
def Input.toSyntax : Input → Token
  | .parenOpen => .parenOpen
  | .parenClose => .parenClose
  | .constant (.numeral value) => .numeral value
  | .constant (.decimal value) => .decimal value
  | .constant (.hexadecimal value) => .hexadecimal value
  | .constant (.binary value) => .binary value
  | .constant (.string value) => .string value
  | .keyword value => .keyword value
  | .symbol value => .symbol value
  | .reserved word => .reserved word
  | .layout =>
    .whitespace (Lexicon.Value.Whitespace.Internal.newUnchecked ByteArray.empty.toByteSlice)
  | .endOfInput => .endOfFile

/-- A token made into a syntax token and back is the token. -/
theorem Input.ofSyntax_toSyntax (token : Input) : Input.ofSyntax token.toSyntax = token := by
  rcases token with _ | _ | (_ | _ | _ | _ | _) | _ | _ | _ | _ | _ <;> rfl

/- LEAN: Rust's `SingleTokenCursor`, with which a parser hands a token it took on to a parser
it holds. A parser stepped by single tokens has the token as an `Input`, so this producer gives
one; as Rust's, it refuses every version switch, and its consumer does not call
`discardRest` on it (Rust's panics), which here drops the token. -/
/-- A producer of one token, in a version. -/
structure InputCursor where
  /-- The version in force. -/
  version : Version
  /-- The token, if it was not consumed yet. -/
  token : Option Input

instance : Token.Cursor InputCursor where
  Token := Input
  «syntax» _ token := token.toSyntax
  HasNext cursor := cursor.token.isSome
  decideHasNext _ := inferInstance
  Consumed next cursor := cursor.token.isSome ∧ next.token = none
  peek? cursor := cursor.token
  next?
    | ⟨version, some token⟩ => some (token, ⟨⟨version, none⟩, ⟨rfl, rfl⟩⟩)
    | ⟨_, none⟩ => none
  version cursor := cursor.version
  setVersion _ _ := .error ⟨⟩
  discardRest cursor := { cursor with token := none }
  next?_isSome {cursor} h := by
    rcases cursor with ⟨_, _ | _⟩
    · exact absurd h (by simp)
    · rfl
  consumed_trans hab hbc := ⟨hbc.1, hab.2⟩
  consumed_wf :=
    ⟨fun b => .intro b fun a hab => .intro a fun _ hca => absurd hca.1 (by simp [hab.2])⟩
  setVersion_consumed _ h := nomatch h
  discardRest_consumed h := ⟨h.1, rfl⟩

/-- What a step of a parser gives: a new state to go on from, or its result. -/
inductive Step (σ ρ : Type) where
  | more (state : σ)
  | done (result : ρ)

/-- What a step of a parser asks of its loop, with `μ` the parser's monad. -/
inductive Flow (μ : Type → Type) (σ ρ : Type) where
  /-- Go on with the next token. -/
  | more (state : σ)
  /-- The parser finished, with its result. -/
  | done (result : ρ)
  /-- Switch the cursor to the version, then go on as `resume` says. The cursor may refuse,
  which fails the parse with `VersionErrorKind.unsupported`. -/
  | switchVersion (version : Version) (resume : μ (Step σ ρ))
  /-- Make the cursor discard the rest of its input, up to the end of the input, then go on as
  `resume` says. -/
  | discardRest (resume : μ (Step σ ρ))

/-- What the parser did with a token, or with a cursor it handed over. -/
inductive After (P R E : Type) where
  /-- It goes on: take the next token. -/
  | goOn (parser : P)
  /-- It stops with the answer, and the parser to go on from after. -/
  | stop (answer : Except (ParseError E) (ControlFlow R)) (parser : P)

/- LEAN: Rust's parsers that step by single tokens call `parse_by_token` with their step; here
the step is a class, so that the proofs about the parsers can speak of the step of every one.
Rust's command parser, in a non-standard command, hands its cursor to the handler's parser
instead of taking a token itself; `handOver?` is that request. -/
/--
A parser that steps by single tokens: the parser of the type `P`, with the handler of the type
`H` in the monad `m`, whose errors are of the type `E`, finishing with results of the type `R`.
-/
class ParseByToken (P : Type) (H : outParam Type) (m : outParam (Type → Type))
    (E R : outParam Type) where
  /-- The calls due when the token arrives, before the parser takes it. -/
  arrive : P → Input → ExceptT (ParseErrorKind E) (StateT H m) Unit
  /-- The parser takes the token, cut in the version. -/
  step : Version → P → Input →
    ExceptT (ParseErrorKind E) (StateT H m) (Flow (ExceptT (ParseErrorKind E) (StateT H m)) P R)
  /-- The parser from which the next value starts, after it finished. -/
  reset : P → P
  /--
  If the parser, in its state, hands its cursor to a parser it holds instead of taking a token:
  what it does with a cursor, which the loop runs, if the cursor has a token, in place of taking
  one. It gives back what the parser does after, and the cursor the held parser gave back, which
  took a token if the cursor had one.
  -/
  handOver? {Z : Type} [Token.Cursor Z] : P → (cursor : Z) →
    Option (StateT H m (After P R E ×
      { next : Z // Token.Cursor.HasNext cursor → Token.Cursor.Consumed next cursor })) :=
    fun _ _ => none

/-- What the parser's step asks after the cursor did what the step asked. A parser that
finished goes on from `fresh`, its reset. -/
def resumed {P R E : Type} (fresh : P) : Step P R → After P R E
  | .more parser => .goOn parser
  | .done result => .stop (.ok (.break result)) fresh

section

variable {H P R E : Type} {m : Type → Type} [Monad m] [ParseByToken P H m E R]
variable {Z : Type} [Token.Cursor Z]

/- LEAN: as Rust's script parser, the step acts on the cursor and the parser goes on with it. An
action stands when the step fails after it, as in Rust, where the cursor is changed in place.

The reset parser is made before the step, and the parser is not used after it: the step then
holds the only reference to the parser's state, so that the state is updated in place and not
copied at every token. A failed parser goes on from its reset too, as a parser that failed is
in no state it promises. -/
/--
Has the parser take the token, taken from `cursor` and leaving `next`: its arrival, its step, and
what the step asks of the cursor. A refused version switch fails with
`VersionErrorKind.unsupported`.
-/
@[inline]
def takeOne (parser : P) (cursor : Z) (token : Token.Cursor.Token Z) (next : Z)
    (consumed : Token.Cursor.Consumed next cursor) :
    StateT H m (After P R E × { z : Z // Token.Cursor.Consumed z cursor }) := do
  let fresh := ParseByToken.reset parser
  let input := Input.ofSyntax (Token.Cursor.«syntax» next token)
  match ← (do
      ParseByToken.arrive parser input
      ParseByToken.step (Token.Cursor.version next) parser input).run with
  | .error error =>
    return (.stop (.error (ParseError.Internal.new error)) fresh, ⟨next, consumed⟩)
  | .ok (.more parser) => return (.goOn parser, ⟨next, consumed⟩)
  | .ok (.done result) =>
    return (.stop (.ok (.break result)) fresh, ⟨next, consumed⟩)
  | .ok (.switchVersion declared resume) =>
    match switch : Token.Cursor.setVersion next declared with
    | .error _ =>
      return (.stop (.error (ParseError.Internal.new (.version .unsupported))) fresh,
        ⟨next, consumed⟩)
    | .ok switched =>
      let after := Token.Cursor.setVersion_consumed consumed switch
      match ← resume.run with
      | .error error =>
        return (.stop (.error (ParseError.Internal.new error)) fresh, ⟨switched, after⟩)
      | .ok step => return (resumed fresh step, ⟨switched, after⟩)
  | .ok (.discardRest resume) =>
    let after := Token.Cursor.discardRest_consumed consumed
    match ← resume.run with
    | .error error =>
      return (.stop (.error (ParseError.Internal.new error)) fresh,
        ⟨Token.Cursor.discardRest next, after⟩)
    | .ok step => return (resumed fresh step, ⟨Token.Cursor.discardRest next, after⟩)

/- LEAN: the loop is the recursion, which ends as every token taken is consumed, by the
producer's well-founded consumption. -/
/-- A producer, ordered by its consumption: the loop over its tokens descends by it. -/
structure Consuming (Z : Type) where
  cursor : Z

instance : WellFoundedRelation (Consuming Z) :=
  invImage Consuming.cursor ⟨Token.Cursor.Consumed, Token.Cursor.consumed_wf⟩

/--
Has the parser take the tokens of `cursor`, which comes from `origin` with tokens consumed, one
by one, or hand the cursor over where it asks to, until there are none or the parser stops.
-/
def rest (origin : Z) (parser : P) (cursor : Z) (consumed : Token.Cursor.Consumed cursor origin) :
    StateT H m (Except (ParseError E) (ControlFlow R) × P ×
      { z : Z // Token.Cursor.Consumed z origin }) :=
  match ParseByToken.handOver? parser cursor with
  | some handOver =>
    match Token.Cursor.decideHasNext cursor with
    | isTrue has => do
      match ← handOver with
      | (.goOn parser, ⟨later, taken⟩) =>
        rest origin parser later (Token.Cursor.consumed_trans (taken has) consumed)
      | (.stop answer parser, ⟨later, taken⟩) =>
        return (answer, parser, ⟨later, Token.Cursor.consumed_trans (taken has) consumed⟩)
    | isFalse _ => return (.ok .continue, parser, ⟨cursor, consumed⟩)
  | none =>
    match Token.Cursor.next? cursor with
    | none => return (.ok .continue, parser, ⟨cursor, consumed⟩)
    | some (token, ⟨next, step⟩) => do
      match ← takeOne parser cursor token next step with
      | (.goOn parser, ⟨later, taken⟩) =>
        rest origin parser later (Token.Cursor.consumed_trans taken consumed)
      | (.stop answer parser, ⟨later, taken⟩) =>
        return (answer, parser, ⟨later, Token.Cursor.consumed_trans taken consumed⟩)
termination_by (⟨cursor⟩ : Consuming Z)
decreasing_by
  · exact taken has
  · exact taken

/-- A producer that gives no token has none. -/
theorem not_hasNext {cursor : Z} (h : Token.Cursor.next? cursor = none) :
    ¬ Token.Cursor.HasNext cursor := fun hn =>
  absurd (Token.Cursor.next?_isSome hn) (by rw [h]; exact Bool.false_ne_true)

/- LEAN: Rust's `parse_by_token`, which takes the step as a closure. -/
/--
Parses the cursor one token at a time with the parser's steps, handing the cursor over where the
parser asks to, until the cursor is empty or the parser stops: the `parse` of a parser that steps
by single tokens.
-/
def parseByToken (parser : P) (state : ParseState H) (cursor : Z) :
    StateT H m (Except (ParseError E) (ControlFlow R) × P × ParseState H ×
      { next : Z // Token.Cursor.HasNext cursor → Token.Cursor.Consumed next cursor }) :=
  match ParseByToken.handOver? parser cursor with
  | some handOver =>
    match Token.Cursor.decideHasNext cursor with
    | isTrue has => do
      match ← handOver with
      | (.goOn parser, ⟨later, taken⟩) =>
        let (answer, parser, ⟨done, hd⟩) ← rest cursor parser later (taken has)
        return (answer, parser, state, ⟨done, fun _ => hd⟩)
      | (.stop answer parser, ⟨later, taken⟩) => return (answer, parser, state, ⟨later, taken⟩)
    | isFalse empty =>
      return (.ok .continue, parser, state, ⟨cursor, fun hn => absurd hn empty⟩)
  | none =>
    match h : Token.Cursor.next? cursor with
    | none => return (.ok .continue, parser, state, ⟨cursor, fun hn => absurd hn (not_hasNext h)⟩)
    | some (token, ⟨next, consumed⟩) => do
      match ← takeOne parser cursor token next consumed with
      | (.goOn parser, ⟨later, taken⟩) =>
        let (answer, parser, ⟨done, hd⟩) ← rest cursor parser later taken
        return (answer, parser, state, ⟨done, fun _ => hd⟩)
      | (.stop answer parser, ⟨later, taken⟩) => return (answer, parser, state, ⟨later,
          fun _ => taken⟩)

end

end Internal

end BSmtLib.Parser
