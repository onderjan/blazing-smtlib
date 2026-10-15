module

public import BSmtLib.Facts.Trusted
public import BSmtLib.Facts.Proofs.Parser.Term
public import BSmtLib.Facts.Proofs.Parser.Command
public import BSmtLib.Facts.Proofs.Parser.Script
public import BSmtLib.Facts.Proofs.Parser.Link
public import BSmtLib.Facts.Proofs.Parser.Cut
public import BSmtLib.Facts.Proofs.Parser.Rejection.Discard
public import BSmtLib.Facts.Proofs.Parser.Fused.Step
public import BSmtLib.Facts.Proofs.Parser.Category.Maximum
public import BSmtLib.Facts.Proofs.Parser.Category.SortedVars
public import BSmtLib.Facts.Proofs.Parser.Category.Pattern
public import BSmtLib.Facts.Proofs.Parser.Category.Attribute

@[expose] public section

/-!
# The parser against the specification's traversal

Proofs that the library's parser (`BSmtLib.Parser`) makes the calls of the specification's
traversal (`BSmtLibSpec.Parser.Traversal`), at the places among the tokens that the traversal
states.

- The handler: a library handler is a class instance, the spec's handler a structure. `Agrees h`
  says that the instance answers every call as the spec's handler `h` answers it, the views and
  arrays handed over turned into the spec's characters and lists. Every spec handler, in any
  monad, has a library handler that agrees with it (`every_handler_linked`), so the theorems
  below hold for every spec handler.
- The tokens: a list of the parser's tokens stands for the spec's tokens when each turns into
  the spec's (`Stands`, `Bridge.received`). The parser is run as its adapter runs it over a
  producer (`driveInput`, which first tells the handler the version, then `driveParse`): each
  token arrives, the calls due at its arrival are made, it is processed and the parser takes it;
  what the parser asks of the producer, the spec's producer does. The spec's token points mark each
  arrival and processing.
- Valid input: on the tokens of a valid term, of a valid command, and of a valid script, the
  parser does exactly what the traversal does, in every monad, with every handler, token points,
  producer and posture (`term_follows_traversal`, `command_follows_traversal`,
  `script_follows_traversal`). Failures are the traversal's failures, as the parser's causes.
- Placement: in a recording run, the parser's events on any input that agrees with what a parser
  receives for a valid script up to an item are the traversal's before that item arrives, and
  before it is processed, its arrival left out (`placement_before_arrival`,
  `placement_before_processing`); where the input stops, they are the traversal's before the
  next item arrives (`placement_where_input_stops`). The last of these is what the parser has
  done when its producer has no further token; the second, what it has done when it rejects the
  item.
- Rejection: the parser as a recording parser of the spec (`Rejection.libraryParser`) takes what
  a parser takes for a script, or for commands that a declaration of a version that is not
  supported ends, as the traversal does (`follows_the_traversal`), and rejects the first item
  that no script continues with, where its producer hands over nothing but the end of the input
  after `exit` (`rejects_first_unviable`). The second rests on the parser's every step keeping
  what it has taken viable, the first on that and on the valid input above. After `exit`, the
  parser goes back to reading commands; only the end of the input keeps what it has taken
  viable there, and the traversal asks for the discarding exactly there.
- The fused reader: the script parser's `parse` on a batch cursor is the fused script reader
  (`Parser.Internal.Fused`), which runs the script parser in one loop over the cursor and falls
  back to the parser's own steps for rare constructs; it parses the cursor as the parser's loop
  over single tokens does, in every lawful monad and with every handler
  (`fused_parses_as_port`). So what holds of that loop holds of the script parser's `parse`.
- The category parsers and the combinators: each parses a cursor of any producer. On a cursor
  that gives the tokens of a valid identifier, qualified identifier, sorted variable, sorted
  variables in parentheses, pattern or attribute, followed by anything, the parser finishes
  right after them with the spec's tree through the bridge, making the traversal's calls; the
  parsers of single tokens finish at a token of their kind with its content; the combinators do
  what their inner parsers do, composed, at the same places. On the tokens of a prefix that
  nothing of the category continues with, a parser fails with the Rust parser's error kind right
  after the token that nothing continues with, having made the calls for what it took before it;
  on the tokens of a part of a value, it wants more, as a parser that finishes on the rest.
-/

/-!
## What holds

Each theorem below is proved in the modules imported above. Each is followed by the axioms its
proof uses: only those of Lean's standard library, no `sorry` and no axiom of its own. The build
fails if that changes.
-/

namespace BSmtLib.Facts.Parser

open BSmtLibSpec.Grammar
open BSmtLibSpec.Parser
open BSmtLibSpec.Parser.Properties
open BSmtLibSpec.Parser.Traversal
open BSmtLib.Facts.Proofs.Parser.Command BSmtLib.Facts.Proofs.Parser.Cut
open BSmtLib.Facts.Proofs.Parser.Link BSmtLib.Facts.Proofs.Parser.Script
open BSmtLib.Facts.Proofs.Parser.Term

/-- Every spec handler, in any monad, is answered alike by a library handler. -/
theorem every_handler_linked {m : Type → Type} [Monad m] {ε : Type} {values : Values}
    (h₀ : Traversal.Handler m ε values) (nonstandard : ε) :
    Adapters.Bridge.Agrees (H := Adapters.Handler.Bridged h₀ nonstandard) (m := m)
        (Adapters.Handler.liftHandler h₀ nonstandard) :=
  agrees_liftHandler

/--
info: 'BSmtLib.Facts.Parser.every_handler_linked' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms every_handler_linked

/--
On the tokens of a valid term, the term parser from its start makes the traversal's calls among
the traversal's token points, and ends with the handled term.
-/
theorem term_follows_traversal {H : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    [Traits.Handler H m] {points : Points (StateT H m)} {version : Token.Version}
    {h : Traversal.Handler (StateT H m) (Traits.Handler.Error H) (Adapters.Bridge.valuesOf H)}
    (hA : Adapters.Bridge.TermAgrees h) (term : Tree.Term)
    (hvalid : term.Valid (Adapters.Bridge.Bridge.version version))
    {tokens : List Parser.Internal.Input} (hs : Adapters.Bridge.Stands tokens term.tokens)
    (rest : List Parser.Internal.Input) :
    Adapters.Run.drive points (Parser.Category.Term.Internal.termStep version)
        Parser.Category.Term.Internal.TermState.init (tokens ++ rest) =
      (do
        let handled ← Adapters.Run.adaptRun (Traversal.term points h term)
        pure (some (handled, rest))) := by
  rw [term_runs_init (points := points) hA term hvalid hs rest]
  simp

/--
info: 'BSmtLib.Facts.Parser.term_follows_traversal' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms term_follows_traversal

/--
On the tokens of a valid command, the command parser makes the traversal's calls among the
traversal's token points, the calls due at a token's arrival made at that arrival, and ends
with the command's outcome.
-/
theorem command_follows_traversal {H : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    [Traits.CommandHandler H m] {points : Points (StateT H m)} {version : Token.Version}
    {h : Traversal.Handler (StateT H m) (Traits.Handler.Error H) (Adapters.Bridge.valuesOf H)}
    (hA : Adapters.Bridge.Agrees h) (command : Tree.Command)
    (hvalid : command.Valid (Adapters.Bridge.Bridge.version version))
    (hmode : command.modeAfter (Adapters.Bridge.Bridge.version version) ≠ none)
    {tokens : List Parser.Internal.Input}
    (hs : Adapters.Bridge.Stands tokens command.tokens) (rest : List Parser.Internal.Input) :
    Adapters.Run.drive points (Parser.Command.Internal.commandStep version) .awaiting
        (tokens ++ rest) Parser.Command.Internal.commandArrive =
      (do
        Adapters.Run.adaptRun (Traversal.command points h command)
        pure (some (Adapters.Bridge.outcomeOf command, rest))) :=
  command_runs hA command hvalid hmode hs rest

/--
info: 'BSmtLib.Facts.Parser.command_follows_traversal' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms command_follows_traversal

/--
On the tokens a parser receives for a valid script read from the version, followed by anything,
the script parser run as the parse adapter runs it, the handler told the version first, makes the
traversal's calls among the traversal's token points, under the policy of its posture, with the
same producer, and finishes at the end of the input, before the rest.
-/
theorem script_follows_traversal {H : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    [Traits.CommandHandler H m] {points : Points (StateT H m)}
    {h : Traversal.Handler (StateT H m) (Traits.Handler.Error H) (Adapters.Bridge.valuesOf H)}
    (hA : Adapters.Bridge.Agrees h)
    (producer : Producer (StateT H m)) (posture : Token.VersionPosture)
    {version : Token.Version} {commands : List Tree.Command}
    (hscript : Script (Adapters.Bridge.Bridge.version version) commands)
    {inputs : List Parser.Internal.Input}
    (hs : inputs.map Adapters.Bridge.Bridge.received =
    (BSmtLibSpec.Parser.Properties.received commands).map some)
    (rest : List Parser.Internal.Input) :
    Adapters.Run.driveInput points producer version
        (Parser.Script.ScriptParser.new (H := H) posture)
        (inputs ++ rest) =
      (do
        Adapters.Run.adaptRun (Traversal.script points h producer
            (Adapters.Bridge.policyOf posture) (Adapters.Bridge.Bridge.version version)
          commands)
        pure (some ((), rest))) :=
  script_correct hA producer posture hscript hs rest

/--
info: 'BSmtLib.Facts.Parser.script_follows_traversal' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms script_follows_traversal

/-- The parser's recording run on what a parser receives for a valid script is `record`. -/
theorem recording_is_record {version : Token.Version} {commands : List Tree.Command}
    (hscript : Script (Adapters.Bridge.Bridge.version version) commands)
    {inputs : List Parser.Internal.Input}
    (hs : inputs.map Adapters.Bridge.Bridge.received =
    (BSmtLibSpec.Parser.Properties.received commands).map some) :
    Adapters.Run.parserRecord version inputs = record
        (Adapters.Bridge.Bridge.version version) commands :=
  parserRecord_script hscript hs

/--
info: 'BSmtLib.Facts.Parser.recording_is_record' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms recording_is_record

/--
On any input that agrees with what a parser receives for a valid script before the item at
position `k`, the parser's recording run has written, before that item arrives, what the
traversal of the script has.
-/
theorem placement_before_arrival {version : Token.Version} {commands : List Tree.Command}
    (hscript : Script (Adapters.Bridge.Bridge.version version) commands)
    {inputs : List Parser.Internal.Input}
    (hs : inputs.map Adapters.Bridge.Bridge.received =
    (BSmtLibSpec.Parser.Properties.received commands).map some)
    {items : List Parser.Internal.Input} (hlayout : Adapters.Bridge.NoLayout items) (k : Nat)
    (htake : items.take k = inputs.take k) :
    eventsBefore k (Adapters.Run.parserRecord version items) =
      eventsBefore k (record (Adapters.Bridge.Bridge.version version) commands) :=
  placement_arrival hscript hs hlayout k htake

/--
info: 'BSmtLib.Facts.Parser.placement_before_arrival' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms placement_before_arrival

/--
On any input that agrees with what a parser receives for a valid script before the item at
position `k` and has an item there, the parser's recording run has written, before that item is
processed and its arrival left out, what the traversal of the script has, where a `)` gets none
of the calls due at its arrival.
-/
theorem placement_before_processing {version : Token.Version} {commands : List Tree.Command}
    (hscript : Script (Adapters.Bridge.Bridge.version version) commands)
    {inputs : List Parser.Internal.Input}
    (hs : inputs.map Adapters.Bridge.Bridge.received =
    (BSmtLibSpec.Parser.Properties.received commands).map some)
    {items : List Parser.Internal.Input} (hlayout : Adapters.Bridge.NoLayout items) (k : Nat)
    {item : Parser.Internal.Input}
    (hitem : items[k]? = some item) {stands : Received}
    (hstands : Adapters.Bridge.Bridge.received item = some stands) (hk : k < inputs.length)
    (htake : items.take k = inputs.take k) :
    eventsBeforeProcessing k (Adapters.Run.parserRecord version items) =
      eventsBeforeProcessingOf stands k (record (Adapters.Bridge.Bridge.version version) commands)
          :=
  Proofs.Parser.Rejection.Library.placement_processingOf hscript hs hlayout k hitem hstands hk htake

/--
info: 'BSmtLib.Facts.Parser.placement_before_processing' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms placement_before_processing

/--
Where its input stops before the item at position `k` of what a parser receives for a valid
script, the parser's recording run has written what the traversal of the script has before that
item arrives.
-/
theorem placement_where_input_stops {version : Token.Version} {commands : List Tree.Command}
    (hscript : Script (Adapters.Bridge.Bridge.version version) commands)
    {inputs : List Parser.Internal.Input}
    (hs : inputs.map Adapters.Bridge.Bridge.received =
    (BSmtLibSpec.Parser.Properties.received commands).map some) (k : Nat) :
    Adapters.Run.parserRecord version (inputs.take k) =
      eventsBefore k (record (Adapters.Bridge.Bridge.version version) commands) :=
  placement_prefix hscript hs k

/--
info: 'BSmtLib.Facts.Parser.placement_where_input_stops' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms placement_where_input_stops

/--
The parser takes what a parser takes for a script, or for commands that a declaration of a
version that is not supported ends, as the traversal does: on any start of it, its recording run
has the traversal's events before the next item, and ends as `Takes` says.
-/
theorem follows_the_traversal : FollowsTheTraversal Adapters.Run.Rejection.libraryParser :=
  Proofs.Parser.Rejection.Library.library_follows

/--
info: 'BSmtLib.Facts.Parser.follows_the_traversal' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms follows_the_traversal

/--
The parser rejects the first item that no script continues with: it takes the items before it,
rejects it with a cause that is no version's, has made the traversal's events before the item's
processing, and makes no call at the item: its processing is the last event of the run. After
`exit`, it relies on its producer to hand over nothing but the end of the input.
-/
theorem rejects_first_unviable : RejectsFirstUnviable Adapters.Run.Rejection.libraryParser :=
  Proofs.Parser.Rejection.Discard.library_rejects

/--
info: 'BSmtLib.Facts.Parser.rejects_first_unviable' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms rejects_first_unviable

/--
The script parser parses a batch cursor of the library's lexer, by the fused script reader
(`Parser.Internal.Fused`), as its loop over single tokens does (`Parser.Internal.parseByToken`):
from every parser and handler, it gives the same answer, parser, parse state and cursor, and leaves
the same handler, in every lawful monad and with every handler. So every theorem about that loop
holds of the script parser's `parse` on the lexer's cursors.
-/
theorem fused_parses_as_port {H : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    [Traits.CommandHandler H m] {batch : Token.BatchTag}
    (parser : BSmtLib.Parser.Script.ScriptParser H) (state : BSmtLib.Parser.ParseState H)
    (cursor : Token.BatchCursor batch) :
    BSmtLib.Parser.Parse.parse (m := m) parser state cursor =
      BSmtLib.Parser.Internal.parseByToken parser state cursor :=
  Proofs.Parser.Fused.Step.parse_eq parser state cursor

/--
info: 'BSmtLib.Facts.Parser.fused_parses_as_port' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms fused_parses_as_port

/-!
## The category parsers and the combinators on a cursor

The parsers of the categories and the combinators parse a cursor of any producer
(`Token.Produce`). What they do is stated against the tokens the cursor gives, as the parsers
take them, all in one version, read as `Adapters.Outcome.outcome` reads a parse: on a cursor that
has given tokens first, followed by anything, a parser makes the effects of a handler-only
program and finishes with its result right after the tokens, as a parser it gives back
(`Adapters.Outcome.Finishes`), or fails with a syntax error of a kind right after the tokens,
having taken exactly them (`Adapters.Outcome.Rejects`); on a cursor that has exactly the tokens,
it makes the effects of the program and wants more, as a parser that the program's result gives
(`Adapters.Outcome.Waits`). Where the program fails with the handler's error, so does the parser.
The programs are the spec's traversal with the token points that mark nothing
(`Adapters.Cursor.noPoints`), as a parse of a cursor marks no point; a parser that makes no call
has a pure program.

- The parsers of single tokens finish at a token of their kind with its content, reject any
  other token, and want more on no token, making no call.
- The combinators are stated for any inner parsers: given what the inner parsers do, the pair,
  the closed, opened and parenthesised parsers and the list parsers do the composite, at the
  same places. A value split over two cursors is stated at one split point at a time: the
  parser wants more after the first part, as a parser that does on the rest what the whole
  value asks.
- The list parsers with a maximum take at most the maximum of values; setting the maximum before
  the first value is the parser with the new maximum, and setting it while the parser waits
  between values applies to the values after them.
- The category parsers finish on the tokens of a valid value with it, through the bridge, and
  reject the first token that no value continues with, also after the calls for an inner sort or
  attribute value.
-/

section

open BSmtLib.Parser.Category.Token
open BSmtLib.Parser (SyntaxErrorKind)
open BSmtLib.Parser.Internal (PM)
open BSmtLib.Plain (Numeral Keyword StringContent)
open Adapters.Outcome (Finishes Waits Rejects)

variable {H : Type} {m : Type → Type} [Monad m] [LawfulMonad m] [Traits.Handler H m]
variable (version : Token.Version)

/-- The symbol parser finishes at a symbol with its owned value, making no call. -/
theorem symbol_parser_parses (symbol : Plain.Symbol) :
    Finishes version SymbolParser.new [.symbol symbol]
      (pure symbol.intoOwned : PM H Plain.SymbolBuf) SymbolParser.new := by
  apply Proofs.Parser.Category.Token.symbol_parses <;> assumption

/--
info: 'BSmtLib.Facts.Parser.symbol_parser_parses' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms symbol_parser_parses

/-- The symbol parser rejects any other token with `expectedSymbol`, making no call. -/
theorem symbol_parser_rejects {token : Parser.Internal.Input}
    (h : ∀ symbol, token ≠ .symbol symbol) :
    Rejects version SymbolParser.new [token] (pure () : PM H Unit) .expectedSymbol := by
  apply Proofs.Parser.Category.Token.symbol_rejects <;> assumption

/--
info: 'BSmtLib.Facts.Parser.symbol_parser_rejects' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms symbol_parser_rejects

/-- The `(` parser finishes at a `(`, making no call. -/
theorem openParen_parser_parses :
    Finishes version OpenParenParser.new [.parenOpen] (pure () : PM H Unit)
      OpenParenParser.new := by
  apply Proofs.Parser.Category.Token.openParen_parses <;> assumption

/--
info: 'BSmtLib.Facts.Parser.openParen_parser_parses' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms openParen_parser_parses

/-- The `(` parser rejects any other token with `expectedToken [(]`, making no call. -/
theorem openParen_parser_rejects {token : Parser.Internal.Input} (h : token ≠ .parenOpen) :
    Rejects version OpenParenParser.new [token] (pure () : PM H Unit)
      (.expectedToken #[.parenOpen]) := by
  apply Proofs.Parser.Category.Token.openParen_rejects <;> assumption

/--
info: 'BSmtLib.Facts.Parser.openParen_parser_rejects' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms openParen_parser_rejects

/-- The `)` parser finishes at a `)`, making no call. -/
theorem closeParen_parser_parses :
    Finishes version CloseParenParser.new [.parenClose] (pure () : PM H Unit)
      CloseParenParser.new := by
  apply Proofs.Parser.Category.Token.closeParen_parses <;> assumption

/--
info: 'BSmtLib.Facts.Parser.closeParen_parser_parses' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms closeParen_parser_parses

/-- The `)` parser rejects any other token with `expectedToken [)]`, making no call. -/
theorem closeParen_parser_rejects {token : Parser.Internal.Input} (h : token ≠ .parenClose) :
    Rejects version CloseParenParser.new [token] (pure () : PM H Unit)
      (.expectedToken #[.parenClose]) := by
  apply Proofs.Parser.Category.Token.closeParen_rejects <;> assumption

/--
info: 'BSmtLib.Facts.Parser.closeParen_parser_rejects' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms closeParen_parser_rejects

/-- The numeral parser finishes at a numeral with its digits, owned, making no call. -/
theorem numeral_parser_parses (digits : Numeral) :
    Finishes version NumeralParser.new [.constant (.numeral digits)]
      (pure digits.intoOwned : PM H Plain.NumeralBuf) NumeralParser.new := by
  apply Proofs.Parser.Category.Token.numeral_parses <;> assumption

/--
info: 'BSmtLib.Facts.Parser.numeral_parser_parses' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms numeral_parser_parses

/-- The numeral parser rejects any other token with `expectedToken [numeral]`, making no
call. -/
theorem numeral_parser_rejects {token : Parser.Internal.Input}
    (h : ∀ digits, token ≠ .constant (.numeral digits)) :
    Rejects version NumeralParser.new [token] (pure () : PM H Unit)
      (.expectedToken #[.numeral]) := by
  apply Proofs.Parser.Category.Token.numeral_rejects <;> assumption

/--
info: 'BSmtLib.Facts.Parser.numeral_parser_rejects' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms numeral_parser_rejects

/-- The keyword parser finishes at a keyword with its name, owned, making no call. -/
theorem keyword_parser_parses (name : Keyword) :
    Finishes version KeywordParser.new [.keyword name]
      (pure name.intoOwned : PM H Plain.KeywordBuf) KeywordParser.new := by
  apply Proofs.Parser.Category.Token.keyword_parses <;> assumption

/--
info: 'BSmtLib.Facts.Parser.keyword_parser_parses' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms keyword_parser_parses

/-- The keyword parser rejects any other token with `expectedToken [keyword]`, making no
call. -/
theorem keyword_parser_rejects {token : Parser.Internal.Input} (h : ∀ name, token ≠ .keyword name) :
    Rejects version KeywordParser.new [token] (pure () : PM H Unit)
      (.expectedToken #[.keyword]) := by
  apply Proofs.Parser.Category.Token.keyword_rejects <;> assumption

/--
info: 'BSmtLib.Facts.Parser.keyword_parser_rejects' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms keyword_parser_rejects

/-- The string literal parser finishes at a string literal with its content, owned, making no
call. -/
theorem string_parser_parses (content : StringContent) :
    Finishes version StringParser.new [.constant (.string content)]
      (pure content.intoOwned : PM H Plain.StringContentBuf) StringParser.new := by
  apply Proofs.Parser.Category.Token.string_parses <;> assumption

/--
info: 'BSmtLib.Facts.Parser.string_parser_parses' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms string_parser_parses

/-- The string literal parser rejects any other token with `expectedToken [string]`, making no
call. -/
theorem string_parser_rejects {token : Parser.Internal.Input}
    (h : ∀ content, token ≠ .constant (.string content)) :
    Rejects version StringParser.new [token] (pure () : PM H Unit)
      (.expectedToken #[.string]) := by
  apply Proofs.Parser.Category.Token.string_rejects <;> assumption

/--
info: 'BSmtLib.Facts.Parser.string_parser_rejects' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms string_parser_rejects

/-- The symbol parser on no token wants more, as it is, making no call. -/
theorem symbol_parser_waits :
    Waits version SymbolParser.new [] (pure () : PM H Unit) fun _ => SymbolParser.new := by
  apply Proofs.Parser.Category.Token.symbol_waits <;> assumption

/--
info: 'BSmtLib.Facts.Parser.symbol_parser_waits' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms symbol_parser_waits

/-- The `(` parser on no token wants more, as it is, making no call. -/
theorem openParen_parser_waits :
    Waits version OpenParenParser.new [] (pure () : PM H Unit)
      fun _ => OpenParenParser.new := by
  apply Proofs.Parser.Category.Token.openParen_waits <;> assumption

/--
info: 'BSmtLib.Facts.Parser.openParen_parser_waits' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms openParen_parser_waits

/-- The `)` parser on no token wants more, as it is, making no call. -/
theorem closeParen_parser_waits :
    Waits version CloseParenParser.new [] (pure () : PM H Unit)
      fun _ => CloseParenParser.new := by
  apply Proofs.Parser.Category.Token.closeParen_waits <;> assumption

/--
info: 'BSmtLib.Facts.Parser.closeParen_parser_waits' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms closeParen_parser_waits

/-- The numeral parser on no token wants more, as it is, making no call. -/
theorem numeral_parser_waits :
    Waits version NumeralParser.new [] (pure () : PM H Unit) fun _ => NumeralParser.new := by
  apply Proofs.Parser.Category.Token.numeral_waits <;> assumption

/--
info: 'BSmtLib.Facts.Parser.numeral_parser_waits' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms numeral_parser_waits

/-- The keyword parser on no token wants more, as it is, making no call. -/
theorem keyword_parser_waits :
    Waits version KeywordParser.new [] (pure () : PM H Unit) fun _ => KeywordParser.new := by
  apply Proofs.Parser.Category.Token.keyword_waits <;> assumption

/--
info: 'BSmtLib.Facts.Parser.keyword_parser_waits' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms keyword_parser_waits

/-- The string literal parser on no token wants more, as it is, making no call. -/
theorem string_parser_waits :
    Waits version StringParser.new [] (pure () : PM H Unit) fun _ => StringParser.new := by
  apply Proofs.Parser.Category.Token.string_waits <;> assumption

/--
info: 'BSmtLib.Facts.Parser.string_parser_waits' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms string_parser_waits

end

section

open BSmtLib.Parser.Category.Combinator
open BSmtLib.Parser (SyntaxErrorKind)
open BSmtLib.Parser.Internal (PM)
open Adapters.Outcome (Finishes Waits Rejects)

variable {H P P₁ P₂ R R₁ R₂ : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
  [Traits.Handler H m] [BSmtLib.Parser.Parse P H m (Traits.Handler.Error H) R]
  [BSmtLib.Parser.Parse P₁ H m (Traits.Handler.Error H) R₁]
  [BSmtLib.Parser.Parse P₂ H m (Traits.Handler.Error H) R₂]

/-- The pair on the values of its two parsers, one after the other. -/
theorem pair_parser_parses {version : Token.Version} {p₁ b₁ : P₁} {p₂ b₂ : P₂}
    {tokens₁ tokens₂ : List Parser.Internal.Input} {program₁ : PM H R₁} {program₂ : PM H R₂}
    (h₁ : Finishes version p₁ tokens₁ program₁ b₁)
    (h₂ : Finishes version p₂ tokens₂ program₂ b₂) (hne₁ : tokens₁ ≠ [])
    (hne₂ : tokens₂ ≠ []) :
    Finishes version (PairParser.new (H := H) p₁ p₂) (tokens₁ ++ tokens₂)
      (do let first ← program₁; let second ← program₂; pure (first, second))
      (PairParser.new b₁ b₂) := by
  apply Proofs.Parser.Category.Combinator.pair_parses <;> assumption

/--
info: 'BSmtLib.Facts.Parser.pair_parser_parses' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms pair_parser_parses

/-- The pair rejects where its first parser rejects. -/
theorem pair_parser_rejects_first {version : Token.Version} {p₁ : P₁} {p₂ : P₂}
    {tokens : List Parser.Internal.Input} {program : PM H Unit} {kind : SyntaxErrorKind}
    (h : Rejects version p₁ tokens program kind) (hne : tokens ≠ []) :
    Rejects version (PairParser.new (H := H) p₁ p₂) tokens program kind := by
  apply Proofs.Parser.Category.Combinator.pair_rejects_first <;> assumption

/--
info: 'BSmtLib.Facts.Parser.pair_parser_rejects_first' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms pair_parser_rejects_first

/-- The pair rejects where its second parser rejects, after the first finished. -/
theorem pair_parser_rejects_second {version : Token.Version} {p₁ b₁ : P₁} {p₂ : P₂}
    {tokens₁ tokens₂ : List Parser.Internal.Input} {program₁ : PM H R₁} {program₂ : PM H Unit}
    {kind : SyntaxErrorKind}
    (h₁ : Finishes version p₁ tokens₁ program₁ b₁)
    (h₂ : Rejects version p₂ tokens₂ program₂ kind) (hne₁ : tokens₁ ≠ [])
    (hne₂ : tokens₂ ≠ []) :
    Rejects version (PairParser.new (H := H) p₁ p₂) (tokens₁ ++ tokens₂)
      (do let _ ← program₁; program₂) kind := by
  apply Proofs.Parser.Category.Combinator.pair_rejects_second <;> assumption

/--
info: 'BSmtLib.Facts.Parser.pair_parser_rejects_second' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms pair_parser_rejects_second

/-- The pair on tokens on which its first parser wants more: it wants more, its first parser as
the first's. -/
theorem pair_parser_waits_first {version : Token.Version} {p₁ : P₁} {p₂ : P₂}
    {tokens : List Parser.Internal.Input} {α : Type} {program : PM H α} {after : α → P₁}
    (h : Waits version p₁ tokens program after) :
    Waits version (PairParser.new (H := H) p₁ p₂) tokens program
      fun a => PairParser.new (after a) p₂ := by
  apply Proofs.Parser.Category.Combinator.pair_waits_first <;> assumption

/--
info: 'BSmtLib.Facts.Parser.pair_parser_waits_first' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms pair_parser_waits_first

/--
The pair on tokens on which its first parser finishes, and no more: it wants more, as a pair
that, on the tokens after, finishes and rejects as its second parser does.
-/
theorem pair_parser_waits_between {version : Token.Version} {p₁ b₁ : P₁} {p₂ : P₂}
    {tokens : List Parser.Internal.Input} {program : PM H R₁}
    (h : Finishes version p₁ tokens program b₁) (hne : tokens ≠ []) :
    ∃ after : R₁ → PairParser H P₁ P₂,
      Waits version (PairParser.new (H := H) p₁ p₂) tokens program after ∧
      (∀ first {tokens₂ : List Parser.Internal.Input} {program₂ : PM H R₂} {b₂ : P₂},
        Finishes version p₂ tokens₂ program₂ b₂ →
        Finishes version (after first) tokens₂ ((fun second => (first, second)) <$>
          program₂) (PairParser.new b₁ b₂)) ∧
      (∀ first {tokens₂ : List Parser.Internal.Input} {program₂ : PM H Unit}
        {kind : SyntaxErrorKind}, Rejects version p₂ tokens₂ program₂ kind →
        Rejects version (after first) tokens₂ program₂ kind) := by
  apply Proofs.Parser.Category.Combinator.pair_waits_between <;> assumption

/--
info: 'BSmtLib.Facts.Parser.pair_parser_waits_between' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms pair_parser_waits_between

/--
The pair on tokens on which its first parser finishes and then its second wants more: it wants
more, as a pair that, on the tokens after, finishes and rejects as the second parser does then.
-/
theorem pair_parser_waits_second {version : Token.Version} {p₁ b₁ : P₁} {p₂ : P₂}
    {tokens₁ tokens₂ : List Parser.Internal.Input} {program₁ : PM H R₁} {α : Type}
    {program₂ : PM H α} {after₂ : α → P₂}
    (h₁ : Finishes version p₁ tokens₁ program₁ b₁)
    (h₂ : Waits version p₂ tokens₂ program₂ after₂) (hne₁ : tokens₁ ≠ [])
    (hne₂ : tokens₂ ≠ []) :
    ∃ after : R₁ × α → PairParser H P₁ P₂,
      Waits version (PairParser.new (H := H) p₁ p₂) (tokens₁ ++ tokens₂)
        (do let first ← program₁; let a ← program₂; pure (first, a)) after ∧
      (∀ first a {tokens₃ : List Parser.Internal.Input} {program₃ : PM H R₂} {b₂ : P₂},
        Finishes version (after₂ a) tokens₃ program₃ b₂ →
        Finishes version (after (first, a)) tokens₃ ((fun second => (first, second)) <$>
          program₃) (PairParser.new b₁ b₂)) ∧
      (∀ first a {tokens₃ : List Parser.Internal.Input} {program₃ : PM H Unit}
        {kind : SyntaxErrorKind}, Rejects version (after₂ a) tokens₃ program₃ kind →
        Rejects version (after (first, a)) tokens₃ program₃ kind) := by
  apply Proofs.Parser.Category.Combinator.pair_waits_second <;> assumption

/--
info: 'BSmtLib.Facts.Parser.pair_parser_waits_second' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms pair_parser_waits_second

/-- The closed parser on the inner value and the `)` after it. -/
theorem closed_parser_parses {version : Token.Version} {p b : P}
    {tokens : List Parser.Internal.Input}
    {program : PM H R} (h : Finishes version p tokens program b) (hne : tokens ≠ []) :
    Finishes version (ClosedParser.new (H := H) p) (tokens ++ [.parenClose]) program
      (ClosedParser.new b) := by
  apply Proofs.Parser.Category.Combinator.closed_parses <;> assumption

/--
info: 'BSmtLib.Facts.Parser.closed_parser_parses' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms closed_parser_parses

/-- The closed parser rejects where its inner parser rejects. -/
theorem closed_parser_rejects_inner {version : Token.Version} {p : P}
    {tokens : List Parser.Internal.Input}
    {program : PM H Unit} {kind : SyntaxErrorKind}
    (h : Rejects version p tokens program kind) (hne : tokens ≠ []) :
    Rejects version (ClosedParser.new (H := H) p) tokens program kind := by
  apply Proofs.Parser.Category.Combinator.closed_rejects_inner <;> assumption

/--
info: 'BSmtLib.Facts.Parser.closed_parser_rejects_inner' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms closed_parser_rejects_inner

/-- The closed parser on the inner value and a token after it that is not `)`. -/
theorem closed_parser_rejects_close {version : Token.Version} {p b : P}
    {tokens : List Parser.Internal.Input} {program : PM H R} {token : Parser.Internal.Input}
    (h : Finishes version p tokens program b) (hne : tokens ≠ [])
    (htoken : token ≠ .parenClose) :
    Rejects version (ClosedParser.new (H := H) p) (tokens ++ [token])
      (do let _ ← program; pure ()) (.expectedToken #[.parenClose]) := by
  apply Proofs.Parser.Category.Combinator.closed_rejects_close <;> assumption

/--
info: 'BSmtLib.Facts.Parser.closed_parser_rejects_close' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms closed_parser_rejects_close

/-- The closed parser on tokens on which its inner parser wants more. -/
theorem closed_parser_waits_inner {version : Token.Version} {p : P}
    {tokens : List Parser.Internal.Input}
    {α : Type} {program : PM H α} {after : α → P}
    (h : Waits version p tokens program after) :
    Waits version (ClosedParser.new (H := H) p) tokens program
      fun a => ClosedParser.new (after a) := by
  apply Proofs.Parser.Category.Combinator.closed_waits_inner <;> assumption

/--
info: 'BSmtLib.Facts.Parser.closed_parser_waits_inner' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms closed_parser_waits_inner

/-- The closed parser on its inner value and no more: it wants more, as a parser that finishes
at a `)` and rejects any other token. -/
theorem closed_parser_waits_close {version : Token.Version} {p b : P}
    {tokens : List Parser.Internal.Input} {program : PM H R}
    (h : Finishes version p tokens program b) (hne : tokens ≠ []) :
    ∃ after : R → ClosedParser H P,
      Waits version (ClosedParser.new (H := H) p) tokens program after ∧
      (∀ result, Finishes version (after result) [.parenClose]
        (pure result : PM H R) (ClosedParser.new b)) ∧
      (∀ result {token : Parser.Internal.Input}, token ≠ .parenClose →
        Rejects version (after result) [token] (pure () : PM H Unit)
          (.expectedToken #[.parenClose])) := by
  apply Proofs.Parser.Category.Combinator.closed_waits_close <;> assumption

/--
info: 'BSmtLib.Facts.Parser.closed_parser_waits_close' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms closed_parser_waits_close

/-- The opened parser on a `(` and the inner value. -/
theorem opened_parser_parses {version : Token.Version} {p b : P}
    {tokens : List Parser.Internal.Input}
    {program : PM H R} (h : Finishes version p tokens program b) (hne : tokens ≠ []) :
    Finishes version (OpenedParser.new (H := H) p) (.parenOpen :: tokens) program
      (OpenedParser.new b) := by
  apply Proofs.Parser.Category.Combinator.opened_parses <;> assumption

/--
info: 'BSmtLib.Facts.Parser.opened_parser_parses' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms opened_parser_parses

/-- The opened parser on a first token that is not `(`. -/
theorem opened_parser_rejects_open {version : Token.Version} {p : P} {token : Parser.Internal.Input}
    (htoken : token ≠ .parenOpen) :
    Rejects version (OpenedParser.new (H := H) p) [token] (pure () : PM H Unit)
      (.expectedToken #[.parenOpen]) := by
  apply Proofs.Parser.Category.Combinator.opened_rejects_open <;> assumption

/--
info: 'BSmtLib.Facts.Parser.opened_parser_rejects_open' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms opened_parser_rejects_open

/-- The opened parser rejects where its inner parser rejects after the `(`. -/
theorem opened_parser_rejects_inner {version : Token.Version} {p : P}
    {tokens : List Parser.Internal.Input} {program : PM H Unit} {kind : SyntaxErrorKind}
    (h : Rejects version p tokens program kind) (hne : tokens ≠ []) :
    Rejects version (OpenedParser.new (H := H) p) (.parenOpen :: tokens) program kind := by
  apply Proofs.Parser.Category.Combinator.opened_rejects_inner <;> assumption

/--
info: 'BSmtLib.Facts.Parser.opened_parser_rejects_inner' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms opened_parser_rejects_inner

/-- The opened parser on a cursor with no token: it wants more, as it was. -/
theorem opened_parser_waits_open {version : Token.Version} {p : P} :
    Waits version (OpenedParser.new (H := H) p) [] (pure () : PM H Unit)
      fun _ => OpenedParser.new p := by
  apply Proofs.Parser.Category.Combinator.opened_waits_open <;> assumption

/--
info: 'BSmtLib.Facts.Parser.opened_parser_waits_open' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms opened_parser_waits_open

/-- The opened parser on its `(` and no more: it wants more, as a parser that finishes and
rejects on the inner tokens as the inner parser. -/
theorem opened_parser_waits_after_open {version : Token.Version} {p : P} :
    ∃ after : Unit → OpenedParser H P,
      Waits version (OpenedParser.new (H := H) p) [.parenOpen] (pure () : PM H Unit)
        after ∧
      (∀ {tokens : List Parser.Internal.Input} {program : PM H R} {b : P},
        Finishes version p tokens program b →
        Finishes version (after ()) tokens program (OpenedParser.new b)) ∧
      (∀ {tokens : List Parser.Internal.Input} {program : PM H Unit} {kind : SyntaxErrorKind},
        Rejects version p tokens program kind →
        Rejects version (after ()) tokens program kind) := by
  apply Proofs.Parser.Category.Combinator.opened_waits_after_open <;> assumption

/--
info: 'BSmtLib.Facts.Parser.opened_parser_waits_after_open' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms opened_parser_waits_after_open

/-- The opened parser on a `(` and tokens on which its inner parser wants more. -/
theorem opened_parser_waits_inner {version : Token.Version} {p : P}
    {tokens : List Parser.Internal.Input}
    {α : Type} {program : PM H α} {after : α → P}
    (h : Waits version p tokens program after) (hne : tokens ≠ []) :
    ∃ after' : α → OpenedParser H P,
      Waits version (OpenedParser.new (H := H) p) (.parenOpen :: tokens) program after' ∧
      (∀ a {tokens' : List Parser.Internal.Input} {program' : PM H R} {b : P},
        Finishes version (after a) tokens' program' b →
        Finishes version (after' a) tokens' program' (OpenedParser.new b)) ∧
      (∀ a {tokens' : List Parser.Internal.Input} {program' : PM H Unit}
        {kind : SyntaxErrorKind}, Rejects version (after a) tokens' program' kind →
        Rejects version (after' a) tokens' program' kind) := by
  apply Proofs.Parser.Category.Combinator.opened_waits_inner <;> assumption

/--
info: 'BSmtLib.Facts.Parser.opened_parser_waits_inner' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms opened_parser_waits_inner

/-- The parenthesised parser on a `(`, the inner value and a `)`. -/
theorem paren_parser_parses {version : Token.Version} {p b : P}
    {tokens : List Parser.Internal.Input}
    {program : PM H R} (h : Finishes version p tokens program b) (hne : tokens ≠ []) :
    Finishes version (ParenParser.new (ClosedParser.new (H := H) p))
      (.parenOpen :: (tokens ++ [.parenClose]))
      program (ParenParser.new (ClosedParser.new b)) := by
  apply Proofs.Parser.Category.Combinator.paren_parses <;> assumption

/--
info: 'BSmtLib.Facts.Parser.paren_parser_parses' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms paren_parser_parses

/-- The parenthesised parser on a first token that is not `(`. -/
theorem paren_parser_rejects_open {version : Token.Version} {p : P} {token : Parser.Internal.Input}
    (htoken : token ≠ .parenOpen) :
    Rejects version (ParenParser.new (ClosedParser.new (H := H) p)) [token] (pure () : PM H Unit)
      (.expectedToken #[.parenOpen]) := by
  apply Proofs.Parser.Category.Combinator.paren_rejects_open <;> assumption

/--
info: 'BSmtLib.Facts.Parser.paren_parser_rejects_open' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms paren_parser_rejects_open

/-- The parenthesised parser rejects where its inner parser rejects after the `(`. -/
theorem paren_parser_rejects_inner {version : Token.Version} {p : P}
    {tokens : List Parser.Internal.Input} {program : PM H Unit} {kind : SyntaxErrorKind}
    (h : Rejects version p tokens program kind) (hne : tokens ≠ []) :
    Rejects version (ParenParser.new (ClosedParser.new (H := H) p))
      (.parenOpen :: tokens) program kind := by
  apply Proofs.Parser.Category.Combinator.paren_rejects_inner <;> assumption

/--
info: 'BSmtLib.Facts.Parser.paren_parser_rejects_inner' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms paren_parser_rejects_inner

/-- The parenthesised parser on a `(`, the inner value and a token that is not `)`. -/
theorem paren_parser_rejects_close {version : Token.Version} {p b : P}
    {tokens : List Parser.Internal.Input} {program : PM H R} {token : Parser.Internal.Input}
    (h : Finishes version p tokens program b) (hne : tokens ≠ [])
    (htoken : token ≠ .parenClose) :
    Rejects version (ParenParser.new (ClosedParser.new (H := H) p))
      (.parenOpen :: (tokens ++ [token]))
      (do let _ ← program; pure ()) (.expectedToken #[.parenClose]) := by
  apply Proofs.Parser.Category.Combinator.paren_rejects_close <;> assumption

/--
info: 'BSmtLib.Facts.Parser.paren_parser_rejects_close' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms paren_parser_rejects_close

/-- The closed list parser on its values and the `)` after them. -/
theorem closedMultiple_parser_parses {version : Token.Version} {p : P}
    {values : List (List Parser.Internal.Input × PM H R)}
    (hvalues : ∀ value ∈ values, Finishes version p value.1 value.2 p ∧
      ∃ token tokens, value.1 = token :: tokens ∧ token ≠ .parenClose) :
    Finishes version (ClosedMultipleParser.new (H := H) p)
      (values.flatMap (·.1) ++ [.parenClose])
      ((fun results => results.toArray) <$> values.mapM fun value => value.2)
      (ClosedMultipleParser.new p) := by
  apply Proofs.Parser.Category.Multiple.closedMultiple_parses <;> assumption

/--
info: 'BSmtLib.Facts.Parser.closedMultiple_parser_parses' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms closedMultiple_parser_parses

/-- The closed list parser on its values and then tokens that its inner parser rejects, not
starting with `)`. -/
theorem closedMultiple_parser_rejects_inner {version : Token.Version} {p : P}
    {values : List (List Parser.Internal.Input × PM H R)}
    (hvalues : ∀ value ∈ values, Finishes version p value.1 value.2 p ∧
      ∃ token tokens, value.1 = token :: tokens ∧ token ≠ .parenClose)
    {tokens : List Parser.Internal.Input} {program : PM H Unit} {kind : SyntaxErrorKind}
    (h : Rejects version p tokens program kind)
    (hfirst : ∃ token tokens', tokens = token :: tokens' ∧ token ≠ .parenClose) :
    Rejects version (ClosedMultipleParser.new (H := H) p) (values.flatMap (·.1) ++ tokens)
      (do let _ ← values.mapM fun value => value.2; program) kind := by
  apply Proofs.Parser.Category.Multiple.closedMultiple_rejects_inner <;> assumption

/--
info: 'BSmtLib.Facts.Parser.closedMultiple_parser_rejects_inner' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms closedMultiple_parser_rejects_inner

/--
The closed list parser on its values and no more: it wants more, as a parser that finishes on
further values and the `)`, and rejects further values and tokens that its inner parser rejects.
-/
theorem closedMultiple_parser_waits_between {version : Token.Version} {p : P}
    {values : List (List Parser.Internal.Input × PM H R)}
    (hvalues : ∀ value ∈ values, Finishes version p value.1 value.2 p ∧
      ∃ token tokens, value.1 = token :: tokens ∧ token ≠ .parenClose) :
    ∃ after : List R → ClosedMultipleParser H P,
      Waits version (ClosedMultipleParser.new (H := H) p) (values.flatMap (·.1))
        (values.mapM fun value => value.2) after ∧
      (∀ found {values' : List (List Parser.Internal.Input × PM H R)},
        (∀ value ∈ values', Finishes version p value.1 value.2 p ∧
          ∃ token tokens, value.1 = token :: tokens ∧ token ≠ .parenClose) →
        Finishes version (after found) (values'.flatMap (·.1) ++ [.parenClose])
          ((fun results => (found ++ results).toArray) <$> values'.mapM fun value => value.2)
          (ClosedMultipleParser.new p)) ∧
      (∀ found {values' : List (List Parser.Internal.Input × PM H R)}
        {tokens : List Parser.Internal.Input} {program : PM H Unit} {kind : SyntaxErrorKind},
        (∀ value ∈ values', Finishes version p value.1 value.2 p ∧
          ∃ token tokens, value.1 = token :: tokens ∧ token ≠ .parenClose) →
        Rejects version p tokens program kind →
        (∃ token tokens', tokens = token :: tokens' ∧ token ≠ .parenClose) →
        Rejects version (after found) (values'.flatMap (·.1) ++ tokens)
          (do let _ ← values'.mapM fun value => value.2; program) kind) := by
  apply Proofs.Parser.Category.Multiple.closedMultiple_waits_between <;> assumption

/--
info: 'BSmtLib.Facts.Parser.closedMultiple_parser_waits_between' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms closedMultiple_parser_waits_between

/--
The closed list parser on its values and then tokens on which its inner parser wants more, not
starting with `)`: it wants more, as a parser that finishes once the inner parser finishes its
value and further values and the `)` follow.
-/
theorem closedMultiple_parser_waits_inner {version : Token.Version} {p : P}
    {values : List (List Parser.Internal.Input × PM H R)}
    (hvalues : ∀ value ∈ values, Finishes version p value.1 value.2 p ∧
      ∃ token tokens, value.1 = token :: tokens ∧ token ≠ .parenClose)
    {tokens : List Parser.Internal.Input} {α : Type} {program : PM H α} {after : α → P}
    (h : Waits version p tokens program after)
    (hfirst : ∃ token tokens', tokens = token :: tokens' ∧ token ≠ .parenClose) :
    ∃ after' : List R × α → ClosedMultipleParser H P,
      Waits version (ClosedMultipleParser.new (H := H) p) (values.flatMap (·.1) ++ tokens)
        (do let found ← values.mapM fun value => value.2; let a ← program; pure (found, a))
        after' ∧
      ∀ found a {tokens' : List Parser.Internal.Input} {program' : PM H R}
        {values' : List (List Parser.Internal.Input × PM H R)},
        Finishes version (after a) tokens' program' p → tokens' ≠ [] →
        (∀ value ∈ values', Finishes version p value.1 value.2 p ∧
          ∃ token tokens, value.1 = token :: tokens ∧ token ≠ .parenClose) →
        Finishes version (after' (found, a)) (tokens' ++ values'.flatMap (·.1) ++
          [.parenClose])
          ((fun results => (found ++ results).toArray) <$> (program' >>= fun first =>
            (values'.mapM fun value => value.2) >>= fun others => pure (first :: others)))
          (ClosedMultipleParser.new p) := by
  apply Proofs.Parser.Category.Multiple.closedMultiple_waits_inner <;> assumption

/--
info: 'BSmtLib.Facts.Parser.closedMultiple_parser_waits_inner' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms closedMultiple_parser_waits_inner

/-- The list parser enclosed in `(` and `)` on a `(`, its values and the `)`. -/
theorem parenMultiple_parser_parses {version : Token.Version} {p : P}
    {values : List (List Parser.Internal.Input × PM H R)}
    (hvalues : ∀ value ∈ values, Finishes version p value.1 value.2 p ∧
      ∃ token tokens, value.1 = token :: tokens ∧ token ≠ .parenClose) :
    Finishes version (ParenMultipleParser.new (ClosedMultipleParser.new (H := H) p))
      (.parenOpen :: (values.flatMap (·.1) ++ [.parenClose]))
      ((fun results => results.toArray) <$> values.mapM fun value => value.2)
      (ParenMultipleParser.new (ClosedMultipleParser.new p)) := by
  apply Proofs.Parser.Category.Multiple.parenMultiple_parses <;> assumption

/--
info: 'BSmtLib.Facts.Parser.parenMultiple_parser_parses' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms parenMultiple_parser_parses

/-- The list parser enclosed in `(` and `)` on a first token that is not `(`. -/
theorem parenMultiple_parser_rejects_open {version : Token.Version} {p : P}
    {token : Parser.Internal.Input} (htoken : token ≠ .parenOpen) :
    Rejects version (ParenMultipleParser.new (ClosedMultipleParser.new (H := H) p))
      [token] (pure () : PM H Unit)
      (.expectedToken #[.parenOpen]) := by
  apply Proofs.Parser.Category.Multiple.parenMultiple_rejects_open <;> assumption

/--
info: 'BSmtLib.Facts.Parser.parenMultiple_parser_rejects_open' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms parenMultiple_parser_rejects_open

/-- The list parser enclosed in `(` and `)` on a `(`, values and then tokens that its inner
parser rejects, not starting with `)`. -/
theorem parenMultiple_parser_rejects_inner {version : Token.Version} {p : P}
    {values : List (List Parser.Internal.Input × PM H R)}
    (hvalues : ∀ value ∈ values, Finishes version p value.1 value.2 p ∧
      ∃ token tokens, value.1 = token :: tokens ∧ token ≠ .parenClose)
    {tokens : List Parser.Internal.Input} {program : PM H Unit} {kind : SyntaxErrorKind}
    (h : Rejects version p tokens program kind)
    (hfirst : ∃ token tokens', tokens = token :: tokens' ∧ token ≠ .parenClose) :
    Rejects version (ParenMultipleParser.new (ClosedMultipleParser.new (H := H) p))
      (.parenOpen :: (values.flatMap (·.1) ++ tokens))
      (do let _ ← values.mapM fun value => value.2; program) kind := by
  apply Proofs.Parser.Category.Multiple.parenMultiple_rejects_inner <;> assumption

/--
info: 'BSmtLib.Facts.Parser.parenMultiple_parser_rejects_inner' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms parenMultiple_parser_rejects_inner

/-- The list parser enclosed in `(` and `)` on its `(` and no more: it wants more, as a parser
that finishes on values and the `)`. -/
theorem parenMultiple_parser_waits_open {version : Token.Version} {p : P} :
    ∃ after : Unit → ParenMultipleParser H P,
      Waits version (ParenMultipleParser.new (ClosedMultipleParser.new (H := H) p)) [.parenOpen]
        (pure () : PM H Unit) after ∧
      ∀ {values : List (List Parser.Internal.Input × PM H R)},
        (∀ value ∈ values, Finishes version p value.1 value.2 p ∧
          ∃ token tokens, value.1 = token :: tokens ∧ token ≠ .parenClose) →
        Finishes version (after ()) (values.flatMap (·.1) ++ [.parenClose])
          ((fun results => results.toArray) <$> values.mapM fun value => value.2)
          (ParenMultipleParser.new (ClosedMultipleParser.new p)) := by
  apply Proofs.Parser.Category.Multiple.parenMultiple_waits_open <;> assumption

/--
info: 'BSmtLib.Facts.Parser.parenMultiple_parser_waits_open' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms parenMultiple_parser_waits_open

/-- The list parser enclosed in `(` and `)` on its `(` and values, at least one, and no more:
it wants more, as a parser that finishes on further values and the `)`. -/
theorem parenMultiple_parser_waits_between {version : Token.Version} {p : P}
    {values : List (List Parser.Internal.Input × PM H R)}
    (hvalues : ∀ value ∈ values, Finishes version p value.1 value.2 p ∧
      ∃ token tokens, value.1 = token :: tokens ∧ token ≠ .parenClose)
    (hne : values ≠ []) :
    ∃ after : List R → ParenMultipleParser H P,
      Waits version (ParenMultipleParser.new (ClosedMultipleParser.new (H := H) p))
        (.parenOpen :: values.flatMap (·.1)) (values.mapM fun value => value.2) after ∧
      ∀ found {values' : List (List Parser.Internal.Input × PM H R)},
        (∀ value ∈ values', Finishes version p value.1 value.2 p ∧
          ∃ token tokens, value.1 = token :: tokens ∧ token ≠ .parenClose) →
        Finishes version (after found) (values'.flatMap (·.1) ++ [.parenClose])
          ((fun results => (found ++ results).toArray) <$> values'.mapM fun value => value.2)
          (ParenMultipleParser.new (ClosedMultipleParser.new p)) := by
  apply Proofs.Parser.Category.Multiple.parenMultiple_waits_between <;> assumption

/--
info: 'BSmtLib.Facts.Parser.parenMultiple_parser_waits_between' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms parenMultiple_parser_waits_between

/-- The closed list parser with a maximum on at most the maximum of values and the `)` after
them. -/
theorem closedMaximum_parser_parses {version : Token.Version} {p : P} {maximum : Nat}
    {values : List (List Parser.Internal.Input × PM H R)}
    (hvalues : ∀ value ∈ values, Finishes version p value.1 value.2 p ∧
      ∃ token tokens, value.1 = token :: tokens ∧ token ≠ .parenClose)
    (hlength : values.length ≤ maximum) :
    Finishes version (ClosedMaximumParser.new (H := H) p maximum)
      (values.flatMap (·.1) ++ [.parenClose])
      ((fun results => results.toArray) <$> values.mapM fun value => value.2)
      (ClosedMaximumParser.new p maximum) := by
  apply Proofs.Parser.Category.Maximum.closedMaximum_parses <;> assumption

/--
info: 'BSmtLib.Facts.Parser.closedMaximum_parser_parses' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms closedMaximum_parser_parses

/-- The closed list parser with a maximum on the maximum of values and a token after them that
is not `)`: it rejects that token. -/
theorem closedMaximum_parser_rejects_beyond {version : Token.Version} {p : P} {maximum : Nat}
    {values : List (List Parser.Internal.Input × PM H R)}
    (hvalues : ∀ value ∈ values, Finishes version p value.1 value.2 p ∧
      ∃ token tokens, value.1 = token :: tokens ∧ token ≠ .parenClose)
    (hlength : values.length = maximum) {token : Parser.Internal.Input}
    (htoken : token ≠ .parenClose) :
    Rejects version (ClosedMaximumParser.new (H := H) p maximum)
      (values.flatMap (·.1) ++ [token])
      (do let _ ← values.mapM fun value => value.2; pure ()) (.expectedToken #[.parenClose]) := by
  apply Proofs.Parser.Category.Maximum.closedMaximum_rejects_beyond <;> assumption

/--
info: 'BSmtLib.Facts.Parser.closedMaximum_parser_rejects_beyond' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms closedMaximum_parser_rejects_beyond

/-- The closed list parser with a maximum on fewer values than the maximum and then tokens that
its inner parser rejects, not starting with `)`. -/
theorem closedMaximum_parser_rejects_inner {version : Token.Version} {p : P} {maximum : Nat}
    {values : List (List Parser.Internal.Input × PM H R)}
    (hvalues : ∀ value ∈ values, Finishes version p value.1 value.2 p ∧
      ∃ token tokens, value.1 = token :: tokens ∧ token ≠ .parenClose)
    (hlength : values.length < maximum) {tokens : List Parser.Internal.Input}
    {program : PM H Unit} {kind : SyntaxErrorKind}
    (h : Rejects version p tokens program kind)
    (hfirst : ∃ token tokens', tokens = token :: tokens' ∧ token ≠ .parenClose) :
    Rejects version (ClosedMaximumParser.new (H := H) p maximum)
      (values.flatMap (·.1) ++ tokens)
      (do let _ ← values.mapM fun value => value.2; program) kind := by
  apply Proofs.Parser.Category.Maximum.closedMaximum_rejects_inner <;> assumption

/--
info: 'BSmtLib.Facts.Parser.closedMaximum_parser_rejects_inner' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms closedMaximum_parser_rejects_inner

/--
The closed list parser with a maximum on at most the maximum of values and no more: it wants
more, as a parser that holds the maximum and the results so far. A maximum set on it applies to
the values after them: it finishes on as many further values as the maximum leaves and the `)`,
and rejects a token not `)` after values that reach the maximum.
-/
theorem closedMaximum_parser_waits_between {version : Token.Version} {p : P}
    {values : List (List Parser.Internal.Input × PM H R)}
    (hvalues : ∀ value ∈ values, Finishes version p value.1 value.2 p ∧
      ∃ token tokens, value.1 = token :: tokens ∧ token ≠ .parenClose) :
    ∃ after : Nat → List R → ClosedMaximumParser H P,
      (∀ maximum found n, (after maximum found).setMaximum n = after n found) ∧
      (∀ maximum, values.length ≤ maximum →
        Waits version (ClosedMaximumParser.new (H := H) p maximum) (values.flatMap (·.1))
          (values.mapM fun value => value.2) (after maximum)) ∧
      (∀ maximum found {values' : List (List Parser.Internal.Input × PM H R)},
        (∀ value ∈ values', Finishes version p value.1 value.2 p ∧
          ∃ token tokens, value.1 = token :: tokens ∧ token ≠ .parenClose) →
        found.length + values'.length ≤ maximum →
        Finishes version (after maximum found) (values'.flatMap (·.1) ++ [.parenClose])
          ((fun results => (found ++ results).toArray) <$> values'.mapM fun value => value.2)
          (ClosedMaximumParser.new p maximum)) ∧
      (∀ maximum found {values' : List (List Parser.Internal.Input × PM H R)}
        {token : Parser.Internal.Input},
        (∀ value ∈ values', Finishes version p value.1 value.2 p ∧
          ∃ token tokens, value.1 = token :: tokens ∧ token ≠ .parenClose) →
        found.length + values'.length = maximum →
        token ≠ .parenClose →
        Rejects version (after maximum found) (values'.flatMap (·.1) ++ [token])
          (do let _ ← values'.mapM fun value => value.2; pure ())
          (.expectedToken #[.parenClose])) := by
  apply Proofs.Parser.Category.Maximum.closedMaximum_waits_between <;> assumption

/--
info: 'BSmtLib.Facts.Parser.closedMaximum_parser_waits_between' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms closedMaximum_parser_waits_between

omit [Monad m] [LawfulMonad m] in
/-- Setting the maximum of a closed list parser with a maximum before its first value: the
parser with the new maximum. -/
theorem closedMaximum_parser_setMaximum_new (p : P) (maximum n : Nat) :
    (ClosedMaximumParser.new (H := H) p maximum).setMaximum n =
      ClosedMaximumParser.new (H := H) p n := by
  apply Proofs.Parser.Category.Maximum.closedMaximum_setMaximum_new <;> assumption

/--
info: 'BSmtLib.Facts.Parser.closedMaximum_parser_setMaximum_new' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms closedMaximum_parser_setMaximum_new

omit [Monad m] [LawfulMonad m] in
/-- The maximum of a closed list parser with a maximum. -/
theorem closedMaximum_parser_maxElements_new (p : P) (maximum : Nat) :
    (ClosedMaximumParser.new (H := H) p maximum).maxElements = maximum := by
  apply Proofs.Parser.Category.Maximum.closedMaximum_maxElements_new <;> assumption

/--
info: 'BSmtLib.Facts.Parser.closedMaximum_parser_maxElements_new' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms closedMaximum_parser_maxElements_new

/-- The list parser with a maximum and its own `(` on the `(`, at most the maximum of values
and the `)`. -/
theorem parenMaximum_parser_parses {version : Token.Version} {p : P} {maximum : Nat}
    {values : List (List Parser.Internal.Input × PM H R)}
    (hvalues : ∀ value ∈ values, Finishes version p value.1 value.2 p ∧
      ∃ token tokens, value.1 = token :: tokens ∧ token ≠ .parenClose)
    (hlength : values.length ≤ maximum) :
    Finishes version (ParenMaximumParser.new (H := H) p maximum)
      (.parenOpen :: (values.flatMap (·.1) ++ [.parenClose]))
      ((fun results => results.toArray) <$> values.mapM fun value => value.2)
      (ParenMaximumParser.new p maximum) := by
  apply Proofs.Parser.Category.Maximum.parenMaximum_parses <;> assumption

/--
info: 'BSmtLib.Facts.Parser.parenMaximum_parser_parses' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms parenMaximum_parser_parses

/-- The list parser with a maximum and its own `(` on a first token that is not `(`. -/
theorem parenMaximum_parser_rejects_open {version : Token.Version} {p : P} {maximum : Nat}
    {token : Parser.Internal.Input} (htoken : token ≠ .parenOpen) :
    Rejects version (ParenMaximumParser.new (H := H) p maximum) [token]
      (pure () : PM H Unit) (.expectedToken #[.parenOpen]) := by
  apply Proofs.Parser.Category.Maximum.parenMaximum_rejects_open <;> assumption

/--
info: 'BSmtLib.Facts.Parser.parenMaximum_parser_rejects_open' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms parenMaximum_parser_rejects_open

/-- The list parser with a maximum and its own `(` on the `(`, the maximum of values and a token
after them that is not `)`: it rejects that token. -/
theorem parenMaximum_parser_rejects_beyond {version : Token.Version} {p : P} {maximum : Nat}
    {values : List (List Parser.Internal.Input × PM H R)}
    (hvalues : ∀ value ∈ values, Finishes version p value.1 value.2 p ∧
      ∃ token tokens, value.1 = token :: tokens ∧ token ≠ .parenClose)
    (hlength : values.length = maximum) {token : Parser.Internal.Input}
    (htoken : token ≠ .parenClose) :
    Rejects version (ParenMaximumParser.new (H := H) p maximum)
      (.parenOpen :: (values.flatMap (·.1) ++ [token]))
      (do let _ ← values.mapM fun value => value.2; pure ()) (.expectedToken #[.parenClose]) := by
  apply Proofs.Parser.Category.Maximum.parenMaximum_rejects_beyond <;> assumption

/--
info: 'BSmtLib.Facts.Parser.parenMaximum_parser_rejects_beyond' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms parenMaximum_parser_rejects_beyond

/-- The list parser with a maximum and its own `(` on the `(`, fewer values than the maximum and
then tokens that its inner parser rejects, not starting with `)`. -/
theorem parenMaximum_parser_rejects_inner {version : Token.Version} {p : P} {maximum : Nat}
    {values : List (List Parser.Internal.Input × PM H R)}
    (hvalues : ∀ value ∈ values, Finishes version p value.1 value.2 p ∧
      ∃ token tokens, value.1 = token :: tokens ∧ token ≠ .parenClose)
    (hlength : values.length < maximum) {tokens : List Parser.Internal.Input}
    {program : PM H Unit} {kind : SyntaxErrorKind}
    (h : Rejects version p tokens program kind)
    (hfirst : ∃ token tokens', tokens = token :: tokens' ∧ token ≠ .parenClose) :
    Rejects version (ParenMaximumParser.new (H := H) p maximum)
      (.parenOpen :: (values.flatMap (·.1) ++ tokens))
      (do let _ ← values.mapM fun value => value.2; program) kind := by
  apply Proofs.Parser.Category.Maximum.parenMaximum_rejects_inner <;> assumption

/--
info: 'BSmtLib.Facts.Parser.parenMaximum_parser_rejects_inner' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms parenMaximum_parser_rejects_inner

omit [Monad m] [LawfulMonad m] in
/-- Setting the maximum of a list parser with a maximum and its own `(` before its `(`: the
parser with the new maximum. -/
theorem parenMaximum_parser_setMaximum_new (p : P) (maximum n : Nat) :
    (ParenMaximumParser.new (H := H) p maximum).setMaximum n =
      ParenMaximumParser.new (H := H) p n := by
  apply Proofs.Parser.Category.Maximum.parenMaximum_setMaximum_new <;> assumption

/--
info: 'BSmtLib.Facts.Parser.parenMaximum_parser_setMaximum_new' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms parenMaximum_parser_setMaximum_new

omit [Monad m] [LawfulMonad m] in
/-- The maximum of a list parser with a maximum and its own `(`. -/
theorem parenMaximum_parser_maxElements_new (p : P) (maximum : Nat) :
    (ParenMaximumParser.new (H := H) p maximum).maxElements = maximum := by
  apply Proofs.Parser.Category.Maximum.parenMaximum_maxElements_new <;> assumption

/--
info: 'BSmtLib.Facts.Parser.parenMaximum_parser_maxElements_new' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms parenMaximum_parser_maxElements_new

/--
The closed list parser with a maximum on fewer values than the maximum and then tokens on which
its inner parser wants more, not starting with `)`: it wants more, as a parser that holds the
maximum, the results so far and the inner parser within its value. A maximum set on it applies
to the values after that value; it finishes once the inner parser finishes the value and as many
further values as the maximum leaves and the `)` follow.
-/
theorem closedMaximum_parser_waits_inner {version : Token.Version} {p : P}
    {values : List (List Parser.Internal.Input × PM H R)}
    (hvalues : ∀ value ∈ values, Finishes version p value.1 value.2 p ∧
      ∃ token tokens, value.1 = token :: tokens ∧ token ≠ .parenClose)
    {tokens : List Parser.Internal.Input} {α : Type} {program : PM H α} {after : α → P}
    (h : Waits version p tokens program after)
    (hfirst : ∃ token tokens', tokens = token :: tokens' ∧ token ≠ .parenClose) :
    ∃ after' : Nat → List R × α → ClosedMaximumParser H P,
      (∀ maximum x n, (after' maximum x).setMaximum n = after' n x) ∧
      (∀ maximum, values.length < maximum →
        Waits version (ClosedMaximumParser.new (H := H) p maximum)
          (values.flatMap (·.1) ++ tokens)
          (do let found ← values.mapM fun value => value.2; let a ← program; pure (found, a))
          (after' maximum)) ∧
      ∀ maximum found a {tokens' : List Parser.Internal.Input} {program' : PM H R}
        {values' : List (List Parser.Internal.Input × PM H R)},
        Finishes version (after a) tokens' program' p → tokens' ≠ [] →
        (∀ value ∈ values', Finishes version p value.1 value.2 p ∧
          ∃ token tokens, value.1 = token :: tokens ∧ token ≠ .parenClose) →
        found.length + 1 + values'.length ≤ maximum →
        Finishes version (after' maximum (found, a))
          (tokens' ++ values'.flatMap (·.1) ++ [.parenClose])
          ((fun results => (found ++ results).toArray) <$> (program' >>= fun first =>
            (values'.mapM fun value => value.2) >>= fun others => pure (first :: others)))
          (ClosedMaximumParser.new p maximum) := by
  apply Proofs.Parser.Category.Maximum.closedMaximum_waits_inner <;> assumption

/--
info: 'BSmtLib.Facts.Parser.closedMaximum_parser_waits_inner' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms closedMaximum_parser_waits_inner

/-- The list parser with a maximum and its own `(` on no token: it wants more, as it is. -/
theorem parenMaximum_parser_waits_open {version : Token.Version} {p : P} {maximum : Nat} :
    Waits version (ParenMaximumParser.new (H := H) p maximum) [] (pure () : PM H Unit)
      fun _ => ParenMaximumParser.new p maximum := by
  apply Proofs.Parser.Category.Maximum.parenMaximum_waits_open <;> assumption

/--
info: 'BSmtLib.Facts.Parser.parenMaximum_parser_waits_open' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms parenMaximum_parser_waits_open

/--
The list parser with a maximum and its own `(` on its `(` and no more: it wants more, as a parser
that holds the maximum, which a maximum set on it replaces. It finishes on at most the maximum
of values and the `)`, and rejects a token not `)` after the maximum of values.
-/
theorem parenMaximum_parser_waits_after_open {version : Token.Version} {p : P} :
    ∃ after : Nat → ParenMaximumParser H P,
      (∀ maximum n, (after maximum).setMaximum n = after n) ∧
      (∀ maximum, Waits version (ParenMaximumParser.new (H := H) p maximum) [.parenOpen]
        (pure () : PM H Unit) fun _ => after maximum) ∧
      (∀ maximum {values : List (List Parser.Internal.Input × PM H R)},
        (∀ value ∈ values, Finishes version p value.1 value.2 p ∧
          ∃ token tokens, value.1 = token :: tokens ∧ token ≠ .parenClose) →
        values.length ≤ maximum →
        Finishes version (after maximum) (values.flatMap (·.1) ++ [.parenClose])
          ((fun results => results.toArray) <$> values.mapM fun value => value.2)
          (ParenMaximumParser.new p maximum)) ∧
      (∀ maximum {values : List (List Parser.Internal.Input × PM H R)}
        {token : Parser.Internal.Input},
        (∀ value ∈ values, Finishes version p value.1 value.2 p ∧
          ∃ token tokens, value.1 = token :: tokens ∧ token ≠ .parenClose) →
        values.length = maximum → token ≠ .parenClose →
        Rejects version (after maximum) (values.flatMap (·.1) ++ [token])
          (do let _ ← values.mapM fun value => value.2; pure ())
          (.expectedToken #[.parenClose])) := by
  apply Proofs.Parser.Category.Maximum.parenMaximum_waits_after_open <;> assumption

/--
info: 'BSmtLib.Facts.Parser.parenMaximum_parser_waits_after_open' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms parenMaximum_parser_waits_after_open

/--
The list parser with a maximum and its own `(` on its `(` and at most the maximum of values, at
least one, and no more: it wants more, as a parser that holds the maximum and the results so
far. A maximum set on it applies to the values after them.
-/
theorem parenMaximum_parser_waits_between {version : Token.Version} {p : P}
    {values : List (List Parser.Internal.Input × PM H R)}
    (hvalues : ∀ value ∈ values, Finishes version p value.1 value.2 p ∧
      ∃ token tokens, value.1 = token :: tokens ∧ token ≠ .parenClose)
    (hne : values ≠ []) :
    ∃ after : Nat → List R → ParenMaximumParser H P,
      (∀ maximum found n, (after maximum found).setMaximum n = after n found) ∧
      (∀ maximum, values.length ≤ maximum →
        Waits version (ParenMaximumParser.new (H := H) p maximum)
          (.parenOpen :: values.flatMap (·.1)) (values.mapM fun value => value.2)
          (after maximum)) ∧
      (∀ maximum found {values' : List (List Parser.Internal.Input × PM H R)},
        (∀ value ∈ values', Finishes version p value.1 value.2 p ∧
          ∃ token tokens, value.1 = token :: tokens ∧ token ≠ .parenClose) →
        found.length + values'.length ≤ maximum →
        Finishes version (after maximum found) (values'.flatMap (·.1) ++ [.parenClose])
          ((fun results => (found ++ results).toArray) <$> values'.mapM fun value => value.2)
          (ParenMaximumParser.new p maximum)) ∧
      (∀ maximum found {values' : List (List Parser.Internal.Input × PM H R)}
        {token : Parser.Internal.Input},
        (∀ value ∈ values', Finishes version p value.1 value.2 p ∧
          ∃ token tokens, value.1 = token :: tokens ∧ token ≠ .parenClose) →
        found.length + values'.length = maximum →
        token ≠ .parenClose →
        Rejects version (after maximum found) (values'.flatMap (·.1) ++ [token])
          (do let _ ← values'.mapM fun value => value.2; pure ())
          (.expectedToken #[.parenClose])) := by
  apply Proofs.Parser.Category.Maximum.parenMaximum_waits_between <;> assumption

/--
info: 'BSmtLib.Facts.Parser.parenMaximum_parser_waits_between' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms parenMaximum_parser_waits_between

/--
The list parser with a maximum and its own `(` on its `(`, fewer values than the maximum and then
tokens on which its inner parser wants more, not starting with `)`: it wants more, as a parser
that holds the maximum, the results so far and the inner parser within its value. A maximum set
on it applies to the values after that value; it finishes once the inner parser finishes the
value and as many further values as the maximum leaves and the `)` follow.
-/
theorem parenMaximum_parser_waits_inner {version : Token.Version} {p : P}
    {values : List (List Parser.Internal.Input × PM H R)}
    (hvalues : ∀ value ∈ values, Finishes version p value.1 value.2 p ∧
      ∃ token tokens, value.1 = token :: tokens ∧ token ≠ .parenClose)
    {tokens : List Parser.Internal.Input} {α : Type} {program : PM H α} {after : α → P}
    (h : Waits version p tokens program after)
    (hfirst : ∃ token tokens', tokens = token :: tokens' ∧ token ≠ .parenClose) :
    ∃ after' : Nat → List R × α → ParenMaximumParser H P,
      (∀ maximum x n, (after' maximum x).setMaximum n = after' n x) ∧
      (∀ maximum, values.length < maximum →
        Waits version (ParenMaximumParser.new (H := H) p maximum)
          (.parenOpen :: (values.flatMap (·.1) ++ tokens))
          (do let found ← values.mapM fun value => value.2; let a ← program; pure (found, a))
          (after' maximum)) ∧
      ∀ maximum found a {tokens' : List Parser.Internal.Input} {program' : PM H R}
        {values' : List (List Parser.Internal.Input × PM H R)},
        Finishes version (after a) tokens' program' p → tokens' ≠ [] →
        (∀ value ∈ values', Finishes version p value.1 value.2 p ∧
          ∃ token tokens, value.1 = token :: tokens ∧ token ≠ .parenClose) →
        found.length + 1 + values'.length ≤ maximum →
        Finishes version (after' maximum (found, a))
          (tokens' ++ values'.flatMap (·.1) ++ [.parenClose])
          ((fun results => (found ++ results).toArray) <$> (program' >>= fun first =>
            (values'.mapM fun value => value.2) >>= fun others => pure (first :: others)))
          (ParenMaximumParser.new p maximum) := by
  apply Proofs.Parser.Category.Maximum.parenMaximum_waits_inner <;> assumption

/--
info: 'BSmtLib.Facts.Parser.parenMaximum_parser_waits_inner' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms parenMaximum_parser_waits_inner

end

section

open BSmtLib.Parser.Category BSmtLib.Parser.Category.Combinator BSmtLib.Parser.Category.Ident
open BSmtLib.Parser.Category.SortedVar BSmtLib.Parser.Category.QualifiedIdent
open BSmtLib.Parser.Category.Pattern BSmtLib.Parser.Category.Attribute
open BSmtLib.Parser (SyntaxErrorKind)
open BSmtLib.Parser.Internal (PM)
open Adapters.Outcome (Finishes Waits Rejects)
open Adapters.Bridge
open Adapters.Run (adaptRun)
open Adapters.Cursor (noPoints)

variable {H : Type} {m : Type → Type} [Monad m] [LawfulMonad m] [Traits.Handler H m]
variable {version : Token.Version}
variable {h : Traversal.Handler (StateT H m) (Traits.Handler.Error H) (valuesOf H)}

/-- The identifier parser from its start on the tokens of a valid identifier. -/
theorem ident_parser_parses {version : Token.Version} (ident : Tree.Identifier)
    (hvalid : ident.Valid (Bridge.version version)) {tokens : List Parser.Internal.Input}
    (hs : Stands tokens ident.tokens) :
    ∃ result : Nodes.Ident, Bridge.identifier result = ident ∧
      Finishes version IdentParser.new tokens (pure result.intoOwned : PM H Nodes.IdentBuf)
        IdentParser.new := by
  apply Proofs.Parser.Category.Ident.ident_parses <;> assumption

/--
info: 'BSmtLib.Facts.Parser.ident_parser_parses' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms ident_parser_parses

/-- The identifier parser on a first token that is neither a symbol nor `(`. -/
theorem ident_parser_rejects_first {version : Token.Version} {token : Parser.Internal.Input}
    (hsymbol : ∀ symbol, token ≠ .symbol symbol) (hopen : token ≠ .parenOpen) :
    Rejects version IdentParser.new [token] (pure () : PM H Unit) .expectedIdent := by
  apply Proofs.Parser.Category.Ident.ident_rejects_first <;> assumption

/--
info: 'BSmtLib.Facts.Parser.ident_parser_rejects_first' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms ident_parser_rejects_first

/-- The identifier parser on `(` and a token that is not `_`. -/
theorem ident_parser_rejects_underscore {version : Token.Version} {token : Parser.Internal.Input}
    (htoken : token ≠ .reserved (.general .underscore)) :
    Rejects version IdentParser.new [.parenOpen, token] (pure () : PM H Unit)
      .expectedUnderscore := by
  apply Proofs.Parser.Category.Ident.ident_rejects_underscore <;> assumption

/--
info: 'BSmtLib.Facts.Parser.ident_parser_rejects_underscore' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms ident_parser_rejects_underscore

/-- The identifier parser on `(` `_` and a token that is not a symbol. -/
theorem ident_parser_rejects_symbol {version : Token.Version} {token : Parser.Internal.Input}
    (htoken : ∀ symbol, token ≠ .symbol symbol) :
    Rejects version IdentParser.new [.parenOpen, .reserved (.general .underscore), token]
      (pure () : PM H Unit) .expectedSymbol := by
  apply Proofs.Parser.Category.Ident.ident_rejects_symbol <;> assumption

/--
info: 'BSmtLib.Facts.Parser.ident_parser_rejects_symbol' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms ident_parser_rejects_symbol

/-- The identifier parser on `(` `_`, a symbol and `)`, an identifier without indices. -/
theorem ident_parser_rejects_empty {version : Token.Version} (symbol : Plain.Symbol) :
    Rejects version IdentParser.new
      [.parenOpen, .reserved (.general .underscore), .symbol symbol, .parenClose]
      (pure () : PM H Unit) .emptyIdentIndices := by
  apply Proofs.Parser.Category.Ident.ident_rejects_empty <;> assumption

/--
info: 'BSmtLib.Facts.Parser.ident_parser_rejects_empty' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms ident_parser_rejects_empty

/-- The identifier parser on `(` `_`, a symbol, indices of the version and a token that is
neither an index of the version nor `)`. -/
theorem ident_parser_rejects_index {version : Token.Version} (symbol : Plain.Symbol)
    {indices : List Parser.Internal.Input}
    (hindices : ∀ index ∈ indices, (∃ digits, index = .constant (.numeral digits)) ∨
      ((∃ symbol, index = .symbol symbol) ∧ version ≥ .v2_5))
    {token : Parser.Internal.Input}
    (htoken : ¬ ((∃ digits, token = .constant (.numeral digits)) ∨
      ((∃ symbol, token = .symbol symbol) ∧ version ≥ .v2_5)))
    (hclose : token ≠ .parenClose) :
    Rejects version IdentParser.new
      ([.parenOpen, .reserved (.general .underscore), .symbol symbol] ++ indices ++ [token])
      (pure () : PM H Unit) .expectedIndexOrCloseParen := by
  apply Proofs.Parser.Category.Ident.ident_rejects_index <;> assumption

/--
info: 'BSmtLib.Facts.Parser.ident_parser_rejects_index' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms ident_parser_rejects_index

/-- The sorted variable parser from its start on the tokens of a valid sorted variable: it
finishes with its symbol, through the bridge, and the handled sort, making the traversal's calls
for its sort. -/
theorem sortedVar_parser_parses {version : Token.Version}
    {h : Handler (StateT H m) (Traits.Handler.Error H) (valuesOf H)} (hA : TermAgrees h)
    (sortedVar : Tree.SortedVar) (hvalid : sortedVar.Valid (Bridge.version version))
    {tokens : List Parser.Internal.Input} (hs : Stands tokens sortedVar.tokens) :
    ∃ symbol : Plain.Symbol, Bridge.symbol symbol = sortedVar.symbol ∧
      Finishes version (SortedVarParser.new (H := H)) tokens
        ((fun sort => (symbol.intoOwned, sort)) <$>
          adaptRun (Traversal.sort noPoints h sortedVar.sort))
        SortedVarParser.new := by
  apply Proofs.Parser.Category.SortedVar.sortedVar_parses <;> assumption

/--
info: 'BSmtLib.Facts.Parser.sortedVar_parser_parses' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms sortedVar_parser_parses

/-- The sorted variable parser on a first token that is not `(`. -/
theorem sortedVar_parser_rejects_open {version : Token.Version} {token : Parser.Internal.Input}
    (htoken : token ≠ .parenOpen) :
    Rejects version (SortedVarParser.new (H := H)) [token] (pure () : PM H Unit)
      (.expectedToken #[.parenOpen]) := by
  apply Proofs.Parser.Category.SortedVar.sortedVar_rejects_open <;> assumption

/--
info: 'BSmtLib.Facts.Parser.sortedVar_parser_rejects_open' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms sortedVar_parser_rejects_open

/-- The sorted variable parser on `(` and a token that is not a symbol. -/
theorem sortedVar_parser_rejects_symbol {version : Token.Version} {token : Parser.Internal.Input}
    (htoken : ∀ symbol, token ≠ .symbol symbol) :
    Rejects version (SortedVarParser.new (H := H)) [.parenOpen, token] (pure () : PM H Unit)
      .expectedSymbol := by
  apply Proofs.Parser.Category.SortedVar.sortedVar_rejects_symbol <;> assumption

/--
info: 'BSmtLib.Facts.Parser.sortedVar_parser_rejects_symbol' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms sortedVar_parser_rejects_symbol

/-- The sorted variable parser on `(`, a symbol and a token that starts no sort: neither a
symbol nor `(`. -/
theorem sortedVar_parser_rejects_sort {version : Token.Version} (symbol : Plain.Symbol)
    {token : Parser.Internal.Input} (hsymbol : ∀ symbol, token ≠ .symbol symbol)
    (hopen : token ≠ .parenOpen) :
    Rejects version (SortedVarParser.new (H := H)) [.parenOpen, .symbol symbol, token]
      (pure () : PM H Unit) .expectedSort := by
  apply Proofs.Parser.Category.SortedVar.sortedVar_rejects_sort <;> assumption

/--
info: 'BSmtLib.Facts.Parser.sortedVar_parser_rejects_sort' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms sortedVar_parser_rejects_sort

/-- The sorted variable parser on `(`, a symbol, the tokens of a valid sort and a token that is
not `)`: it rejects that token with `expectedToken [)]`, having made the traversal's calls for
the sort. -/
theorem sortedVar_parser_rejects_close {version : Token.Version}
    {h : Handler (StateT H m) (Traits.Handler.Error H) (valuesOf H)} (hA : TermAgrees h)
    (symbol : Plain.Symbol) {sort : Tree.«Sort»} (hvalid : sort.Valid (Bridge.version version))
    {sortTokens : List Parser.Internal.Input} (hs : Stands sortTokens sort.tokens)
    {token : Parser.Internal.Input} (htoken : token ≠ .parenClose) :
    Rejects version (SortedVarParser.new (H := H))
      (.parenOpen :: .symbol symbol :: (sortTokens ++ [token]))
      ((fun _ => ()) <$> adaptRun (Traversal.sort noPoints h sort))
      (.expectedToken #[.parenClose]) := by
  apply Proofs.Parser.Category.SortedVar.sortedVar_rejects_close <;> assumption

/--
info: 'BSmtLib.Facts.Parser.sortedVar_parser_rejects_close' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms sortedVar_parser_rejects_close

/-- The sorted variable parser on `(`, a symbol, `(` and a token that starts no head of a
sort. -/
theorem sortedVar_parser_rejects_sortInner {version : Token.Version} (symbol : Plain.Symbol)
    {token : Parser.Internal.Input} (hsymbol : ∀ symbol, token ≠ .symbol symbol)
    (hopen : token ≠ .parenOpen) (hunderscore : token ≠ .reserved (.general .underscore)) :
    Rejects version (SortedVarParser.new (H := H))
      [.parenOpen, .symbol symbol, .parenOpen, token] (pure () : PM H Unit)
      .expectedSortInner := by
  apply Proofs.Parser.Category.SortedVar.sortedVar_rejects_sortInner <;> assumption

/--
info: 'BSmtLib.Facts.Parser.sortedVar_parser_rejects_sortInner' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms sortedVar_parser_rejects_sortInner

/-- The sorted variable parser on `(`, a symbol, and `(`, a symbol and `)`: a sort application
without arguments. -/
theorem sortedVar_parser_rejects_sortEmpty {version : Token.Version}
    (symbol head : Plain.Symbol) :
    Rejects version (SortedVarParser.new (H := H))
      [.parenOpen, .symbol symbol, .parenOpen, .symbol head, .parenClose] (pure () : PM H Unit)
      .emptySortApplication := by
  apply Proofs.Parser.Category.SortedVar.sortedVar_rejects_sortEmpty <;> assumption

/--
info: 'BSmtLib.Facts.Parser.sortedVar_parser_rejects_sortEmpty' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms sortedVar_parser_rejects_sortEmpty

/-- The sorted variable parser on `(`, a symbol, `(`, the tokens of a valid identifier and of
valid sorts and a token that neither starts another argument of the sort nor ends it: it rejects
that token with `expectedSort`, having made the traversal's calls for the sorts. -/
theorem sortedVar_parser_rejects_sortArgument {version : Token.Version}
    {h : Handler (StateT H m) (Traits.Handler.Error H) (valuesOf H)} (hA : TermAgrees h)
    (symbol : Plain.Symbol) {head : Tree.Identifier}
    (hhead : head.Valid (Bridge.version version))
    {headTokens : List Parser.Internal.Input} (hsHead : Stands headTokens head.tokens)
    {sorts : List Tree.«Sort»} (hsorts : Tree.«Sort».ValidAll (Bridge.version version) sorts)
    {sortTokens : List Parser.Internal.Input}
    (hsSorts : Stands sortTokens (Tree.«Sort».tokensAll sorts))
    {token : Parser.Internal.Input} (hsymbol : ∀ symbol, token ≠ .symbol symbol)
    (hopen : token ≠ .parenOpen) (hclose : token ≠ .parenClose) :
    Rejects version (SortedVarParser.new (H := H))
      (.parenOpen :: .symbol symbol :: .parenOpen :: (headTokens ++ (sortTokens ++ [token])))
      ((fun _ => ()) <$> adaptRun (Traversal.sorts noPoints h sorts)) .expectedSort := by
  apply Proofs.Parser.Category.SortedVar.sortedVar_rejects_sortArgument <;> assumption

/--
info: 'BSmtLib.Facts.Parser.sortedVar_parser_rejects_sortArgument' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms sortedVar_parser_rejects_sortArgument

/-- The qualified identifier parser on the tokens of a valid identifier, unqualified: it
finishes with the identifier, through the bridge, and no sort, making no call. -/
theorem qualifiedIdent_parser_parses_plain {version : Token.Version} (identifier : Tree.Identifier)
    (hvalid : identifier.Valid (Bridge.version version)) {tokens : List Parser.Internal.Input}
    (hs : Stands tokens identifier.tokens) :
    ∃ result : Nodes.Ident, Bridge.identifier result = identifier ∧
      Finishes version (QualifiedIdentParser.new (H := H)) tokens
        (pure { ident := result.intoOwned, sort := none } :
          PM H (Nodes.QualifiedIdentBuf (Traits.Handler.«Sort» H)))
        QualifiedIdentParser.new := by
  apply Proofs.Parser.Category.QualifiedIdent.qualifiedIdent_parses_plain <;> assumption

/--
info: 'BSmtLib.Facts.Parser.qualifiedIdent_parser_parses_plain' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms qualifiedIdent_parser_parses_plain

/-- The qualified identifier parser on the tokens of a valid identifier qualified by `as` with a
valid sort: it finishes with the identifier, through the bridge, and the handled sort, making the
traversal's calls for the sort. -/
theorem qualifiedIdent_parser_parses_as {version : Token.Version}
    {h : Traversal.Handler (StateT H m) (Traits.Handler.Error H) (valuesOf H)}
    (hA : TermAgrees h) (identifier : Tree.Identifier) (sort : Tree.«Sort»)
    (hvalid : (Tree.QualIdentifier.as identifier sort).Valid (Bridge.version version))
    {tokens : List Parser.Internal.Input}
    (hs : Stands tokens (Tree.QualIdentifier.as identifier sort).tokens) :
    ∃ result : Nodes.Ident, Bridge.identifier result = identifier ∧
      Finishes version (QualifiedIdentParser.new (H := H)) tokens
        ((fun handled => ({ ident := result.intoOwned, sort := some handled } :
            Nodes.QualifiedIdentBuf _)) <$>
          adaptRun (Traversal.sort noPoints h sort))
        QualifiedIdentParser.new := by
  apply Proofs.Parser.Category.QualifiedIdent.qualifiedIdent_parses_as <;> assumption

/--
info: 'BSmtLib.Facts.Parser.qualifiedIdent_parser_parses_as' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms qualifiedIdent_parser_parses_as

/-- The qualified identifier parser on a first token that is neither a symbol nor `(`. -/
theorem qualifiedIdent_parser_rejects_first {version : Token.Version}
    {token : Parser.Internal.Input}
    (hsymbol : ∀ symbol, token ≠ .symbol symbol) (hopen : token ≠ .parenOpen) :
    Rejects version (QualifiedIdentParser.new (H := H)) [token] (pure () : PM H Unit)
      .expectedIdent := by
  apply Proofs.Parser.Category.QualifiedIdent.qualifiedIdent_rejects_first <;> assumption

/--
info: 'BSmtLib.Facts.Parser.qualifiedIdent_parser_rejects_first' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms qualifiedIdent_parser_rejects_first

/-- The qualified identifier parser on `(` and a token that is neither `_` nor `as`. -/
theorem qualifiedIdent_parser_rejects_opened {version : Token.Version}
    {token : Parser.Internal.Input}
    (hunderscore : token ≠ .reserved (.general .underscore))
    (has : token ≠ .reserved (.general .as)) :
    Rejects version (QualifiedIdentParser.new (H := H)) [.parenOpen, token]
      (pure () : PM H Unit) .expectedUnderscoreOrAs := by
  apply Proofs.Parser.Category.QualifiedIdent.qualifiedIdent_rejects_opened <;> assumption

/--
info: 'BSmtLib.Facts.Parser.qualifiedIdent_parser_rejects_opened' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms qualifiedIdent_parser_rejects_opened

/--
The qualified identifier parser on `(` `as`, the tokens of a valid identifier and of a valid sort,
and a token that is not `)`: it rejects that token with `expectedToken [)]`, having made the
traversal's calls for the sort.
-/
theorem qualifiedIdent_parser_rejects_close {version : Token.Version}
    {h : Traversal.Handler (StateT H m) (Traits.Handler.Error H) (valuesOf H)}
    (hA : TermAgrees h) {identifier : Tree.Identifier} {sort : Tree.«Sort»}
    (hvalid : (Tree.QualIdentifier.as identifier sort).Valid (Bridge.version version))
    {identTokens sortTokens : List Parser.Internal.Input}
    (hident : Stands identTokens identifier.tokens) (hsort : Stands sortTokens sort.tokens)
    {token : Parser.Internal.Input} (htoken : token ≠ .parenClose) :
    Rejects version (QualifiedIdentParser.new (H := H))
      (.parenOpen :: .reserved (.general .as) :: (identTokens ++ (sortTokens ++ [token])))
      ((fun _ => ()) <$> adaptRun (Traversal.sort noPoints h sort))
      (.expectedToken #[.parenClose]) := by
  apply Proofs.Parser.Category.QualifiedIdent.qualifiedIdent_rejects_close <;> assumption

/--
info: 'BSmtLib.Facts.Parser.qualifiedIdent_parser_rejects_close' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms qualifiedIdent_parser_rejects_close

/-- The qualified identifier parser on `(` `as`, the tokens of a valid identifier, `(` and a
token that starts no head of a sort. -/
theorem qualifiedIdent_parser_rejects_sortInner {version : Token.Version}
    {identifier : Tree.Identifier}
    (hvalid : identifier.Valid (Bridge.version version))
    {identTokens : List Parser.Internal.Input} (hident : Stands identTokens identifier.tokens)
    {token : Parser.Internal.Input} (hsymbol : ∀ symbol, token ≠ .symbol symbol)
    (hopen : token ≠ .parenOpen) (hunderscore : token ≠ .reserved (.general .underscore)) :
    Rejects version (QualifiedIdentParser.new (H := H))
      (.parenOpen :: .reserved (.general .as) :: (identTokens ++ [.parenOpen, token]))
      (pure () : PM H Unit) .expectedSortInner := by
  apply Proofs.Parser.Category.QualifiedIdent.qualifiedIdent_rejects_sortInner <;> assumption

/--
info: 'BSmtLib.Facts.Parser.qualifiedIdent_parser_rejects_sortInner' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms qualifiedIdent_parser_rejects_sortInner

/-- The qualified identifier parser on `(` `as`, the tokens of a valid identifier, and `(`, a
symbol and `)`: a sort application without arguments. -/
theorem qualifiedIdent_parser_rejects_sortEmpty {version : Token.Version}
    {identifier : Tree.Identifier}
    (hvalid : identifier.Valid (Bridge.version version))
    {identTokens : List Parser.Internal.Input} (hident : Stands identTokens identifier.tokens)
    (head : Plain.Symbol) :
    Rejects version (QualifiedIdentParser.new (H := H))
      (.parenOpen :: .reserved (.general .as) ::
        (identTokens ++ [.parenOpen, .symbol head, .parenClose]))
      (pure () : PM H Unit) .emptySortApplication := by
  apply Proofs.Parser.Category.QualifiedIdent.qualifiedIdent_rejects_sortEmpty <;> assumption

/--
info: 'BSmtLib.Facts.Parser.qualifiedIdent_parser_rejects_sortEmpty' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms qualifiedIdent_parser_rejects_sortEmpty

/-- The qualified identifier parser on `(` `as`, the tokens of a valid identifier, `(`, the
tokens of a valid identifier and of valid sorts and a token that neither starts another argument
of the sort nor ends it: it rejects that token with `expectedSort`, having made the traversal's
calls for the sorts. -/
theorem qualifiedIdent_parser_rejects_sortArgument {version : Token.Version}
    {h : Traversal.Handler (StateT H m) (Traits.Handler.Error H) (valuesOf H)}
    (hA : TermAgrees h) {identifier : Tree.Identifier}
    (hvalid : identifier.Valid (Bridge.version version))
    {identTokens : List Parser.Internal.Input} (hident : Stands identTokens identifier.tokens)
    {head : Tree.Identifier} (hhead : head.Valid (Bridge.version version))
    {headTokens : List Parser.Internal.Input} (hsHead : Stands headTokens head.tokens)
    {sorts : List Tree.«Sort»} (hsorts : Tree.«Sort».ValidAll (Bridge.version version) sorts)
    {sortTokens : List Parser.Internal.Input}
    (hsSorts : Stands sortTokens (Tree.«Sort».tokensAll sorts))
    {token : Parser.Internal.Input} (hsymbol : ∀ symbol, token ≠ .symbol symbol)
    (hopen : token ≠ .parenOpen) (hclose : token ≠ .parenClose) :
    Rejects version (QualifiedIdentParser.new (H := H))
      (.parenOpen :: .reserved (.general .as) ::
        (identTokens ++ .parenOpen :: (headTokens ++ (sortTokens ++ [token]))))
      ((fun _ => ()) <$> adaptRun (Traversal.sorts noPoints h sorts)) .expectedSort := by
  exact Proofs.Parser.Category.QualifiedIdent.qualifiedIdent_rejects_sortArgument hA hvalid hident
    hhead hsHead hsorts hsSorts hsymbol hopen hclose

/--
info: 'BSmtLib.Facts.Parser.qualifiedIdent_parser_rejects_sortArgument' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms qualifiedIdent_parser_rejects_sortArgument

/-- The parser of sorted variables in parentheses on the tokens of valid sorted variables in
parentheses: it finishes with their symbols, through the bridge, and their handled sorts, making
the traversal's calls for the sorts. -/
theorem parenSortedVars_parser_parses (hA : TermAgrees h) (variables : List Tree.SortedVar)
    (hvalid : ∀ variable_ ∈ variables, variable_.Valid (Bridge.version version))
    {tokens : List Parser.Internal.Input}
    (hs : Stands tokens (paren (variables.flatMap Tree.SortedVar.tokens))) :
    ∃ symbols : List Plain.Symbol, symbols.map Bridge.symbol = variables.map (·.symbol) ∧
      Finishes version
        (ParenSortedVarsParser.new (ClosedMultipleParser.new (SortedVarParser.new (H := H))) :
          ParenSortedVarsParser H) tokens
        ((fun pairs => ((symbols.map Plain.Symbol.intoOwned).zip (pairs.map (·.2))).toArray) <$>
          adaptRun (Traversal.sortedVars noPoints h variables))
        (ParenSortedVarsParser.new (ClosedMultipleParser.new SortedVarParser.new)) := by
  apply Proofs.Parser.Category.SortedVars.parenSortedVars_parses <;> assumption

/--
info: 'BSmtLib.Facts.Parser.parenSortedVars_parser_parses' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms parenSortedVars_parser_parses

/-- The pattern parser from its start on the tokens of a valid pattern: it finishes with it,
through the bridge, making no call. -/
theorem pattern_parser_parses {version : Token.Version} (pattern : Tree.Pattern)
    (hvalid : pattern.Valid (Bridge.version version)) {tokens : List Parser.Internal.Input}
    (hs : Stands tokens pattern.tokens) :
    ∃ result : Nodes.Pattern, Bridge.pattern result = pattern ∧
      Finishes version (PatternParser.new (H := H)) tokens
        (pure result.intoOwned : PM H Nodes.PatternBuf)
        PatternParser.new := by
  apply Proofs.Parser.Category.Pattern.pattern_parses <;> assumption

/--
info: 'BSmtLib.Facts.Parser.pattern_parser_parses' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms pattern_parser_parses

/-- The pattern parser on a first token that is neither `(` nor a symbol, nor the wildcard `_`
from 2.7 on; the error names the wildcard from 2.7 on. -/
theorem pattern_parser_rejects_first {version : Token.Version} {token : Parser.Internal.Input}
    (hopen : token ≠ .parenOpen) (hsymbol : ∀ symbol, token ≠ .symbol symbol)
    (hwildcard : version ≥ .v2_7 → token ≠ .reserved (.general .underscore)) :
    Rejects version (PatternParser.new (H := H)) [token] (pure () : PM H Unit)
      (if version ≥ .v2_7 then .expectedSymbolUnderscoreOrParenOpen
        else .expectedSymbolOrParenOpen) := by
  apply Proofs.Parser.Category.Pattern.pattern_rejects_first <;> assumption

/--
info: 'BSmtLib.Facts.Parser.pattern_parser_rejects_first' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms pattern_parser_rejects_first

/-- The pattern parser on `(` and a token that is not a symbol. -/
theorem pattern_parser_rejects_constructor {version : Token.Version} {token : Parser.Internal.Input}
    (htoken : ∀ symbol, token ≠ .symbol symbol) :
    Rejects version (PatternParser.new (H := H)) [.parenOpen, token] (pure () : PM H Unit)
      .expectedSymbol := by
  apply Proofs.Parser.Category.Pattern.pattern_rejects_constructor <;> assumption

/--
info: 'BSmtLib.Facts.Parser.pattern_parser_rejects_constructor' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms pattern_parser_rejects_constructor

/-- The pattern parser on `(`, a constructor and `)`, a constructor pattern without
arguments. -/
theorem pattern_parser_rejects_empty {version : Token.Version} (constructor : Plain.Symbol) :
    Rejects version (PatternParser.new (H := H)) [.parenOpen, .symbol constructor, .parenClose]
      (pure () : PM H Unit) .emptyPatternArguments := by
  apply Proofs.Parser.Category.Pattern.pattern_rejects_empty <;> assumption

/--
info: 'BSmtLib.Facts.Parser.pattern_parser_rejects_empty' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms pattern_parser_rejects_empty

/-- The pattern parser on `(`, a constructor, arguments of the version and a token that is
neither an argument of the version nor `)`; the error names the wildcard from 2.7 on. -/
theorem pattern_parser_rejects_argument {version : Token.Version} (constructor : Plain.Symbol)
    {arguments : List Parser.Internal.Input}
    (harguments : ∀ argument ∈ arguments, (∃ symbol, argument = .symbol symbol) ∨
      (version ≥ .v2_7 ∧ argument = .reserved (.general .underscore)))
    {token : Parser.Internal.Input}
    (htoken : ¬ ((∃ symbol, token = .symbol symbol) ∨
      (version ≥ .v2_7 ∧ token = .reserved (.general .underscore))))
    (hclose : token ≠ .parenClose) :
    Rejects version (PatternParser.new (H := H))
      ([.parenOpen, .symbol constructor] ++ arguments ++ [token]) (pure () : PM H Unit)
      (if version ≥ .v2_7 then .expectedSymbolOrUnderscore else .expectedSymbol) := by
  apply Proofs.Parser.Category.Pattern.pattern_rejects_argument <;> assumption

/--
info: 'BSmtLib.Facts.Parser.pattern_parser_rejects_argument' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms pattern_parser_rejects_argument

/-- The parser of one attribute from its start on the tokens of a valid attribute and the `)`
after it: it finishes with the handled attribute, making the traversal's calls. -/
theorem closedAttribute_parser_parses {version : Token.Version}
    {h : Traversal.Handler (StateT H m) (Traits.Handler.Error H) (valuesOf H)}
    (hA : TermAgrees h) (attr : Tree.Attribute)
    (hvalid : attr.Valid (Bridge.version version)) {tokens : List Parser.Internal.Input}
    (hs : Stands tokens (attr.tokens ++ [.parenClose])) :
    Finishes version (ClosedAttributeParser.new (H := H)) tokens
      (adaptRun (do
        take noPoints (.keyword attr.keyword)
        attributeThen noPoints h attr.keyword .parenClose attr.value) :
        PM H (Traits.Handler.Attribute H))
      ClosedAttributeParser.new := by
  apply Proofs.Parser.Category.Attribute.closedAttribute_parses <;> assumption

/--
info: 'BSmtLib.Facts.Parser.closedAttribute_parser_parses' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms closedAttribute_parser_parses

/-- The parser of attributes up to a `)` from its start on the tokens of valid attributes, at
least one, and the `)` after them: it finishes with the handled attributes, making the
traversal's calls. -/
theorem closedMultipleAttribute_parser_parses {version : Token.Version}
    {h : Traversal.Handler (StateT H m) (Traits.Handler.Error H) (valuesOf H)}
    (hA : TermAgrees h) (first : Tree.Attribute) (rest : List Tree.Attribute)
    (hvalid : ∀ attr ∈ first :: rest, attr.Valid (Bridge.version version))
    {tokens : List Parser.Internal.Input}
    (hs : Stands tokens ((first :: rest).flatMap Tree.Attribute.tokens ++ [.parenClose])) :
    Finishes version (ClosedMultipleAttributeParser.new (H := H)) tokens
      ((fun handled : List (Traits.Handler.Attribute H) => handled.toArray) <$> adaptRun (do
        take noPoints (.keyword first.keyword)
        attributesThen noPoints h first.keyword first.value rest))
      ClosedMultipleAttributeParser.new := by
  apply Proofs.Parser.Category.Attribute.closedMultipleAttribute_parses <;> assumption

/--
info: 'BSmtLib.Facts.Parser.closedMultipleAttribute_parser_parses' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms closedMultipleAttribute_parser_parses

/-- The parser of attributes up to a `)` from its start on the `)`: it finishes with no
attribute, making no call. -/
theorem closedMultipleAttribute_parser_parses_none {version : Token.Version} :
    Finishes version (ClosedMultipleAttributeParser.new (H := H)) [.parenClose]
      (pure #[] : PM H (Array (Traits.Handler.Attribute H)))
      ClosedMultipleAttributeParser.new := by
  apply Proofs.Parser.Category.Attribute.closedMultipleAttribute_parses_none <;> assumption

/--
info: 'BSmtLib.Facts.Parser.closedMultipleAttribute_parser_parses_none' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms closedMultipleAttribute_parser_parses_none

/-- The parser of one attribute on a first token that is not a keyword: no attribute starts
there, and a `)` would close an empty attribute. -/
theorem closedAttribute_parser_rejects_first {version : Token.Version}
    {token : Parser.Internal.Input}
    (htoken : ∀ name, token ≠ .keyword name) :
    Rejects version (ClosedAttributeParser.new (H := H)) [token] (pure () : PM H Unit)
      .expectedAttribute := by
  apply Proofs.Parser.Category.Attribute.closedAttribute_rejects_first <;> assumption

/--
info: 'BSmtLib.Facts.Parser.closedAttribute_parser_rejects_first' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms closedAttribute_parser_rejects_first

/-- The parser of attributes up to a `)` on a first token that is neither a keyword nor `)`. -/
theorem closedMultipleAttribute_parser_rejects_first {version : Token.Version}
    {token : Parser.Internal.Input} (htoken : ∀ name, token ≠ .keyword name)
    (hclose : token ≠ .parenClose) :
    Rejects version (ClosedMultipleAttributeParser.new (H := H)) [token] (pure () : PM H Unit)
      .expectedAttribute := by
  apply Proofs.Parser.Category.Attribute.closedMultipleAttribute_rejects_first <;> assumption

/--
info: 'BSmtLib.Facts.Parser.closedMultipleAttribute_parser_rejects_first' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms closedMultipleAttribute_parser_rejects_first

/-- The parser of one attribute on a keyword and a token that neither starts a value nor ends
the attribute. -/
theorem closedAttribute_parser_rejects_value {version : Token.Version}
    (name : BSmtLib.Plain.Keyword)
    {token : Parser.Internal.Input}
    (htoken : ¬ ((∃ symbol, token = .symbol symbol) ∨ (∃ constant, token = .constant constant) ∨
      token = .parenOpen ∨ token = .parenClose ∨ (∃ name, token = .keyword name))) :
    Rejects version (ClosedAttributeParser.new (H := H)) [.keyword name, token]
      (pure () : PM H Unit) .expectedAttribute := by
  apply Proofs.Parser.Category.Attribute.closedAttribute_rejects_value <;> assumption

/--
info: 'BSmtLib.Facts.Parser.closedAttribute_parser_rejects_value' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms closedAttribute_parser_rejects_value

/-- The parser of attributes up to a `)` on a keyword and a token that neither starts a value
nor ends the attribute. -/
theorem closedMultipleAttribute_parser_rejects_value {version : Token.Version}
    (name : BSmtLib.Plain.Keyword)
    {token : Parser.Internal.Input}
    (htoken : ¬ ((∃ symbol, token = .symbol symbol) ∨ (∃ constant, token = .constant constant) ∨
      token = .parenOpen ∨ token = .parenClose ∨ (∃ name, token = .keyword name))) :
    Rejects version (ClosedMultipleAttributeParser.new (H := H)) [.keyword name, token]
      (pure () : PM H Unit) .expectedAttribute := by
  apply Proofs.Parser.Category.Attribute.closedMultipleAttribute_rejects_value <;> assumption

/--
info: 'BSmtLib.Facts.Parser.closedMultipleAttribute_parser_rejects_value' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms closedMultipleAttribute_parser_rejects_value

/-- The parser of one attribute on a keyword and a keyword after it: the attribute would be
followed by another, where its `)` is due. -/
theorem closedAttribute_parser_rejects_keyword {version : Token.Version}
    (name name' : BSmtLib.Plain.Keyword) :
    Rejects version (ClosedAttributeParser.new (H := H)) [.keyword name, .keyword name']
      (pure () : PM H Unit) (.expectedToken #[.parenClose]) := by
  apply Proofs.Parser.Category.Attribute.closedAttribute_rejects_keyword <;> assumption

/--
info: 'BSmtLib.Facts.Parser.closedAttribute_parser_rejects_keyword' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms closedAttribute_parser_rejects_keyword

/-- The parser of one attribute on the tokens of a valid attribute with a value and a token
that is not `)`: it rejects that token with `expectedToken [)]`, having made the traversal's
calls for the attribute. -/
theorem closedAttribute_parser_rejects_close {version : Token.Version}
    {h : Traversal.Handler (StateT H m) (Traits.Handler.Error H) (valuesOf H)}
    (hA : TermAgrees h) (keyword : BSmtLibSpec.Regex.Chars) (value : Tree.AttributeValue)
    (hvalid : (⟨keyword, some value⟩ : Tree.Attribute).Valid (Bridge.version version))
    {tokens : List Parser.Internal.Input}
    (hs : Stands tokens (Tree.Attribute.tokens ⟨keyword, some value⟩))
    {token : Parser.Internal.Input} (htoken : token ≠ .parenClose) :
    Rejects version (ClosedAttributeParser.new (H := H)) (tokens ++ [token])
      ((fun _ => ()) <$> adaptRun (do
        let node ← attributeValue noPoints h value
        Traversal.call h (.handleAttribute keyword (some node))))
      (.expectedToken #[.parenClose]) := by
  apply Proofs.Parser.Category.Attribute.closedAttribute_rejects_close <;> assumption

/--
info: 'BSmtLib.Facts.Parser.closedAttribute_parser_rejects_close' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms closedAttribute_parser_rejects_close

/-- The parser of attributes up to a `)` on the tokens of a valid attribute with a value and a
token that neither starts another attribute nor is `)`: it rejects that token, having made the
traversal's calls for the attribute. -/
theorem closedMultipleAttribute_parser_rejects_after {version : Token.Version}
    {h : Traversal.Handler (StateT H m) (Traits.Handler.Error H) (valuesOf H)}
    (hA : TermAgrees h) (keyword : BSmtLibSpec.Regex.Chars) (value : Tree.AttributeValue)
    (hvalid : (⟨keyword, some value⟩ : Tree.Attribute).Valid (Bridge.version version))
    {tokens : List Parser.Internal.Input}
    (hs : Stands tokens (Tree.Attribute.tokens ⟨keyword, some value⟩))
    {token : Parser.Internal.Input} (hkeyword : ∀ name, token ≠ .keyword name)
    (hclose : token ≠ .parenClose) :
    Rejects version (ClosedMultipleAttributeParser.new (H := H)) (tokens ++ [token])
      ((fun _ => ()) <$> adaptRun (do
        let node ← attributeValue noPoints h value
        Traversal.call h (.handleAttribute keyword (some node)))) .expectedAttribute := by
  apply Proofs.Parser.Category.Attribute.closedMultipleAttribute_rejects_after <;> assumption

/--
info: 'BSmtLib.Facts.Parser.closedMultipleAttribute_parser_rejects_after' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms closedMultipleAttribute_parser_rejects_after


/-- The sorted variable parser on `(`, a symbol, the tokens of open sort applications and a
token that neither starts another argument nor ends an application: it rejects that token with
`expectedSort`, having made the traversal's calls for the applications' argument sorts. -/
theorem sortedVar_parser_rejects_sortDeepArgument {version : Token.Version}
    {h : Handler (StateT H m) (Traits.Handler.Error H) (valuesOf H)} (hA : TermAgrees h)
    (symbol : Plain.Symbol) {frames : List (Tree.Identifier × List Tree.«Sort»)}
    (hvalid : ∀ frame ∈ frames, frame.1.Valid (Bridge.version version) ∧
      Tree.«Sort».ValidAll (Bridge.version version) frame.2)
    {tokens : List Parser.Internal.Input} (hs : Stands tokens (frames.flatMap fun frame =>
      .parenOpen :: (frame.1.tokens ++ Tree.«Sort».tokensAll frame.2)))
    {token : Parser.Internal.Input} (hsymbol : ∀ symbol, token ≠ .symbol symbol)
    (hopen : token ≠ .parenOpen) (hclose : token ≠ .parenClose) :
    Rejects version (SortedVarParser.new (H := H))
      (.parenOpen :: .symbol symbol :: (tokens ++ [token]))
      ((fun _ => ()) <$> adaptRun (frames.mapM fun frame => Traversal.sorts noPoints h frame.2))
      .expectedSort := by
  apply Proofs.Parser.Category.SortedVar.sortedVar_rejects_sortDeepArgument <;> assumption

/--
info: 'BSmtLib.Facts.Parser.sortedVar_parser_rejects_sortDeepArgument' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms sortedVar_parser_rejects_sortDeepArgument

/-- The sorted variable parser on `(`, a symbol, the tokens of open sort applications, `(` and
a token that starts no head: it rejects that token with `expectedSortInner`, having made the
traversal's calls for the applications' argument sorts. -/
theorem sortedVar_parser_rejects_sortDeepInner {version : Token.Version}
    {h : Handler (StateT H m) (Traits.Handler.Error H) (valuesOf H)} (hA : TermAgrees h)
    (symbol : Plain.Symbol) {frames : List (Tree.Identifier × List Tree.«Sort»)}
    (hvalid : ∀ frame ∈ frames, frame.1.Valid (Bridge.version version) ∧
      Tree.«Sort».ValidAll (Bridge.version version) frame.2)
    {tokens : List Parser.Internal.Input} (hs : Stands tokens (frames.flatMap fun frame =>
      .parenOpen :: (frame.1.tokens ++ Tree.«Sort».tokensAll frame.2)))
    {token : Parser.Internal.Input} (hsymbol : ∀ symbol, token ≠ .symbol symbol)
    (hopen : token ≠ .parenOpen) (hunderscore : token ≠ .reserved (.general .underscore)) :
    Rejects version (SortedVarParser.new (H := H))
      (.parenOpen :: .symbol symbol :: (tokens ++ [.parenOpen, token]))
      ((fun _ => ()) <$> adaptRun (frames.mapM fun frame => Traversal.sorts noPoints h frame.2))
      .expectedSortInner := by
  apply Proofs.Parser.Category.SortedVar.sortedVar_rejects_sortDeepInner <;> assumption

/--
info: 'BSmtLib.Facts.Parser.sortedVar_parser_rejects_sortDeepInner' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms sortedVar_parser_rejects_sortDeepInner

/-- The sorted variable parser on `(`, a symbol, the tokens of open sort applications, and `(`,
a symbol and `)`: it rejects the `)` with `emptySortApplication`, having made the traversal's
calls for the applications' argument sorts. -/
theorem sortedVar_parser_rejects_sortDeepEmpty {version : Token.Version}
    {h : Handler (StateT H m) (Traits.Handler.Error H) (valuesOf H)} (hA : TermAgrees h)
    (symbol : Plain.Symbol) {frames : List (Tree.Identifier × List Tree.«Sort»)}
    (hvalid : ∀ frame ∈ frames, frame.1.Valid (Bridge.version version) ∧
      Tree.«Sort».ValidAll (Bridge.version version) frame.2)
    {tokens : List Parser.Internal.Input} (hs : Stands tokens (frames.flatMap fun frame =>
      .parenOpen :: (frame.1.tokens ++ Tree.«Sort».tokensAll frame.2)))
    (head : Plain.Symbol) :
    Rejects version (SortedVarParser.new (H := H))
      (.parenOpen :: .symbol symbol :: (tokens ++ [.parenOpen, .symbol head, .parenClose]))
      ((fun _ => ()) <$> adaptRun (frames.mapM fun frame => Traversal.sorts noPoints h frame.2))
      .emptySortApplication := by
  apply Proofs.Parser.Category.SortedVar.sortedVar_rejects_sortDeepEmpty <;> assumption

/--
info: 'BSmtLib.Facts.Parser.sortedVar_parser_rejects_sortDeepEmpty' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms sortedVar_parser_rejects_sortDeepEmpty

/-- The qualified identifier parser on `(` `as`, the tokens of a valid identifier, of open sort
applications and a token that neither starts another argument nor ends an application: it
rejects that token with `expectedSort`, having made the traversal's calls for the applications'
argument sorts. -/
theorem qualifiedIdent_parser_rejects_sortDeepArgument {version : Token.Version}
    {h : Traversal.Handler (StateT H m) (Traits.Handler.Error H) (valuesOf H)}
    (hA : TermAgrees h) {identifier : Tree.Identifier}
    (hvalid : identifier.Valid (Bridge.version version))
    {identTokens : List Parser.Internal.Input} (hident : Stands identTokens identifier.tokens)
    {frames : List (Tree.Identifier × List Tree.«Sort»)}
    (hframes : ∀ frame ∈ frames, frame.1.Valid (Bridge.version version) ∧
      Tree.«Sort».ValidAll (Bridge.version version) frame.2)
    {tokens : List Parser.Internal.Input} (hs : Stands tokens (frames.flatMap fun frame =>
      .parenOpen :: (frame.1.tokens ++ Tree.«Sort».tokensAll frame.2)))
    {token : Parser.Internal.Input} (hsymbol : ∀ symbol, token ≠ .symbol symbol)
    (hopen : token ≠ .parenOpen) (hclose : token ≠ .parenClose) :
    Rejects version (QualifiedIdentParser.new (H := H))
      (.parenOpen :: .reserved (.general .as) :: (identTokens ++ (tokens ++ [token])))
      ((fun _ => ()) <$> adaptRun (frames.mapM fun frame => Traversal.sorts noPoints h frame.2))
      .expectedSort := by
  apply Proofs.Parser.Category.QualifiedIdent.qualifiedIdent_rejects_sortDeepArgument <;> assumption

/--
info: 'BSmtLib.Facts.Parser.qualifiedIdent_parser_rejects_sortDeepArgument' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms qualifiedIdent_parser_rejects_sortDeepArgument

/-- The qualified identifier parser on `(` `as`, the tokens of a valid identifier, of open sort
applications, `(` and a token that starts no head: it rejects that token with
`expectedSortInner`, having made the traversal's calls for the applications' argument sorts. -/
theorem qualifiedIdent_parser_rejects_sortDeepInner {version : Token.Version}
    {h : Traversal.Handler (StateT H m) (Traits.Handler.Error H) (valuesOf H)}
    (hA : TermAgrees h) {identifier : Tree.Identifier}
    (hvalid : identifier.Valid (Bridge.version version))
    {identTokens : List Parser.Internal.Input} (hident : Stands identTokens identifier.tokens)
    {frames : List (Tree.Identifier × List Tree.«Sort»)}
    (hframes : ∀ frame ∈ frames, frame.1.Valid (Bridge.version version) ∧
      Tree.«Sort».ValidAll (Bridge.version version) frame.2)
    {tokens : List Parser.Internal.Input} (hs : Stands tokens (frames.flatMap fun frame =>
      .parenOpen :: (frame.1.tokens ++ Tree.«Sort».tokensAll frame.2)))
    {token : Parser.Internal.Input} (hsymbol : ∀ symbol, token ≠ .symbol symbol)
    (hopen : token ≠ .parenOpen) (hunderscore : token ≠ .reserved (.general .underscore)) :
    Rejects version (QualifiedIdentParser.new (H := H))
      (.parenOpen :: .reserved (.general .as) :: (identTokens ++ (tokens ++ [.parenOpen, token])))
      ((fun _ => ()) <$> adaptRun (frames.mapM fun frame => Traversal.sorts noPoints h frame.2))
      .expectedSortInner := by
  apply Proofs.Parser.Category.QualifiedIdent.qualifiedIdent_rejects_sortDeepInner <;> assumption

/--
info: 'BSmtLib.Facts.Parser.qualifiedIdent_parser_rejects_sortDeepInner' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms qualifiedIdent_parser_rejects_sortDeepInner

/-- The qualified identifier parser on `(` `as`, the tokens of a valid identifier, of open sort
applications, and `(`, a symbol and `)`: it rejects the `)` with `emptySortApplication`, having
made the traversal's calls for the applications' argument sorts. -/
theorem qualifiedIdent_parser_rejects_sortDeepEmpty {version : Token.Version}
    {h : Traversal.Handler (StateT H m) (Traits.Handler.Error H) (valuesOf H)}
    (hA : TermAgrees h) {identifier : Tree.Identifier}
    (hvalid : identifier.Valid (Bridge.version version))
    {identTokens : List Parser.Internal.Input} (hident : Stands identTokens identifier.tokens)
    {frames : List (Tree.Identifier × List Tree.«Sort»)}
    (hframes : ∀ frame ∈ frames, frame.1.Valid (Bridge.version version) ∧
      Tree.«Sort».ValidAll (Bridge.version version) frame.2)
    {tokens : List Parser.Internal.Input} (hs : Stands tokens (frames.flatMap fun frame =>
      .parenOpen :: (frame.1.tokens ++ Tree.«Sort».tokensAll frame.2)))
    (head : Plain.Symbol) :
    Rejects version (QualifiedIdentParser.new (H := H))
      (.parenOpen :: .reserved (.general .as) ::
        (identTokens ++ (tokens ++ [.parenOpen, .symbol head, .parenClose])))
      ((fun _ => ()) <$> adaptRun (frames.mapM fun frame => Traversal.sorts noPoints h frame.2))
      .emptySortApplication := by
  apply Proofs.Parser.Category.QualifiedIdent.qualifiedIdent_rejects_sortDeepEmpty <;> assumption

/--
info: 'BSmtLib.Facts.Parser.qualifiedIdent_parser_rejects_sortDeepEmpty' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms qualifiedIdent_parser_rejects_sortDeepEmpty

/-- The qualified identifier parser from its start on the tokens of a valid qualified
identifier: it finishes with an identifier that is, through the bridge, the one the qualified
identifier names, plain or qualified by `as` with a sort, and the handled sort if any, making the
traversal's calls for that sort. -/
theorem qualifiedIdent_parser_parses {version : Token.Version}
    {h : Traversal.Handler (StateT H m) (Traits.Handler.Error H) (valuesOf H)}
    (hA : TermAgrees h) (qualified : Tree.QualIdentifier)
    (hvalid : qualified.Valid (Bridge.version version)) {tokens : List Parser.Internal.Input}
    (hs : Stands tokens qualified.tokens) :
    ∃ identifier : Nodes.Ident,
      (qualified = .plain (Bridge.identifier identifier) ∨
        ∃ sort, qualified = .as (Bridge.identifier identifier) sort) ∧
      Finishes version (QualifiedIdentParser.new (H := H)) tokens
        ((fun result => ({ ident := identifier.intoOwned, sort := result.2 } :
            Nodes.QualifiedIdentBuf _)) <$>
          adaptRun (Traversal.qualIdentifier noPoints h qualified))
        QualifiedIdentParser.new := by
  apply Proofs.Parser.Category.QualifiedIdent.qualifiedIdent_parses_any <;> assumption

/--
info: 'BSmtLib.Facts.Parser.qualifiedIdent_parser_parses' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms qualifiedIdent_parser_parses

/--
The parser of one attribute on a keyword, `(`, the tokens of valid items, of open lists of
s-expressions and a token that starts no s-expression and does not end a list: it rejects that
token with `expectedSExpr`, having made the traversal's calls for the items.
-/
theorem closedAttribute_parser_rejects_sExpr {version : Token.Version}
    {h : Traversal.Handler (StateT H m) (Traits.Handler.Error H) (valuesOf H)}
    (hA : TermAgrees h) (name : BSmtLib.Plain.Keyword) {items : List Tree.SExpr}
    (hitems : Tree.SExpr.ValidAll (Bridge.version version) items)
    {itemTokens : List Parser.Internal.Input}
    (hsItems : Stands itemTokens (Tree.SExpr.tokensAll items))
    {frames : List (List Tree.SExpr)}
    (hframes : ∀ items ∈ frames, Tree.SExpr.ValidAll (Bridge.version version) items)
    {tokens : List Parser.Internal.Input} (hs : Stands tokens (frames.flatMap fun items =>
      .parenOpen :: Tree.SExpr.tokensAll items))
    {token : Parser.Internal.Input}
    (hopen : token ≠ .parenOpen) (hclose : token ≠ .parenClose)
    (hconstant : ∀ constant, token ≠ .constant constant)
    (hsymbol : ∀ symbol, token ≠ .symbol symbol) (hkeyword : ∀ name, token ≠ .keyword name)
    (hreserved : ∀ word, token = .reserved word → ¬ version ≥ .v2_6) :
    Rejects version (ClosedAttributeParser.new (H := H))
      (.keyword name :: .parenOpen :: (itemTokens ++ (tokens ++ [token])))
      ((fun _ => ()) <$> (adaptRun (Traversal.sExprs noPoints h items) >>= fun _ =>
        adaptRun (frames.mapM fun items => Traversal.sExprs noPoints h items)))
      .expectedSExpr := by
  apply Proofs.Parser.Category.Attribute.closedAttribute_rejects_sExpr <;> assumption

/--
info: 'BSmtLib.Facts.Parser.closedAttribute_parser_rejects_sExpr' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms closedAttribute_parser_rejects_sExpr

/--
The parser of attributes up to a `)` on a keyword, `(`, the tokens of valid items, of open lists
of s-expressions and a token that starts no s-expression and does not end a list: it rejects that
token with `expectedSExpr`, having made the traversal's calls for the items.
-/
theorem closedMultipleAttribute_parser_rejects_sExpr {version : Token.Version}
    {h : Traversal.Handler (StateT H m) (Traits.Handler.Error H) (valuesOf H)}
    (hA : TermAgrees h) (name : BSmtLib.Plain.Keyword) {items : List Tree.SExpr}
    (hitems : Tree.SExpr.ValidAll (Bridge.version version) items)
    {itemTokens : List Parser.Internal.Input}
    (hsItems : Stands itemTokens (Tree.SExpr.tokensAll items))
    {frames : List (List Tree.SExpr)}
    (hframes : ∀ items ∈ frames, Tree.SExpr.ValidAll (Bridge.version version) items)
    {tokens : List Parser.Internal.Input} (hs : Stands tokens (frames.flatMap fun items =>
      .parenOpen :: Tree.SExpr.tokensAll items))
    {token : Parser.Internal.Input}
    (hopen : token ≠ .parenOpen) (hclose : token ≠ .parenClose)
    (hconstant : ∀ constant, token ≠ .constant constant)
    (hsymbol : ∀ symbol, token ≠ .symbol symbol) (hkeyword : ∀ name, token ≠ .keyword name)
    (hreserved : ∀ word, token = .reserved word → ¬ version ≥ .v2_6) :
    Rejects version (ClosedMultipleAttributeParser.new (H := H))
      (.keyword name :: .parenOpen :: (itemTokens ++ (tokens ++ [token])))
      ((fun _ => ()) <$> (adaptRun (Traversal.sExprs noPoints h items) >>= fun _ =>
        adaptRun (frames.mapM fun items => Traversal.sExprs noPoints h items)))
      .expectedSExpr := by
  apply Proofs.Parser.Category.Attribute.closedMultipleAttribute_rejects_sExpr <;> assumption

/--
info: 'BSmtLib.Facts.Parser.closedMultipleAttribute_parser_rejects_sExpr' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms closedMultipleAttribute_parser_rejects_sExpr
end

/-! ## What is trusted

A reader of the theorems above trusts the specification (`BSmtLibSpec`), the statements in this
file, and the definitions in `BSmtLib.Facts.Parser.Adapters` and the modules below it, which put
the parser and its handlers into the spec's shapes: the adapters. Everything else Lean checks.
The check below lists the adapters, every definition that the statements of the theorems in this
file rest on outside the specification, the library and Lean (`BSmtLib.Facts.Trusted`), and fails
the build if one of them is declared outside `BSmtLib.Facts.Parser.Adapters`.
-/

/--
info: 123 theorems, stated with 71 adapters:
BSmtLib.Facts.Parser.Adapters.Bridge:
  BSmtLib.Facts.Parser.Adapters.Bridge.Agrees
  BSmtLib.Facts.Parser.Adapters.Bridge.Bridge.attributeValue
  BSmtLib.Facts.Parser.Adapters.Bridge.Bridge.callAttribute
  BSmtLib.Facts.Parser.Adapters.Bridge.Bridge.callSExpr
  BSmtLib.Facts.Parser.Adapters.Bridge.Bridge.callScope
  BSmtLib.Facts.Parser.Adapters.Bridge.Bridge.callSort
  BSmtLib.Facts.Parser.Adapters.Bridge.Bridge.callTerm
  BSmtLib.Facts.Parser.Adapters.Bridge.Bridge.callUnit
  BSmtLib.Facts.Parser.Adapters.Bridge.Bridge.chars
  BSmtLib.Facts.Parser.Adapters.Bridge.Bridge.constant
  BSmtLib.Facts.Parser.Adapters.Bridge.Bridge.constructor
  BSmtLib.Facts.Parser.Adapters.Bridge.Bridge.identifier
  BSmtLib.Facts.Parser.Adapters.Bridge.Bridge.index
  BSmtLib.Facts.Parser.Adapters.Bridge.Bridge.keyword
  BSmtLib.Facts.Parser.Adapters.Bridge.Bridge.libVersion
  BSmtLib.Facts.Parser.Adapters.Bridge.Bridge.pairs
  BSmtLib.Facts.Parser.Adapters.Bridge.Bridge.pattern
  BSmtLib.Facts.Parser.Adapters.Bridge.Bridge.quantifier
  BSmtLib.Facts.Parser.Adapters.Bridge.Bridge.received
  BSmtLib.Facts.Parser.Adapters.Bridge.Bridge.reserved
  BSmtLib.Facts.Parser.Adapters.Bridge.Bridge.sExprNode
  BSmtLib.Facts.Parser.Adapters.Bridge.Bridge.signature
  BSmtLib.Facts.Parser.Adapters.Bridge.Bridge.symbol
  BSmtLib.Facts.Parser.Adapters.Bridge.Bridge.symbolOrWildcard
  BSmtLib.Facts.Parser.Adapters.Bridge.Bridge.termNode
  BSmtLib.Facts.Parser.Adapters.Bridge.Bridge.version
  BSmtLib.Facts.Parser.Adapters.Bridge.NoLayout
  BSmtLib.Facts.Parser.Adapters.Bridge.Rejection.rcv
  BSmtLib.Facts.Parser.Adapters.Bridge.Stands
  BSmtLib.Facts.Parser.Adapters.Bridge.TermAgrees
  BSmtLib.Facts.Parser.Adapters.Bridge.causeOf
  BSmtLib.Facts.Parser.Adapters.Bridge.outcomeOf
  BSmtLib.Facts.Parser.Adapters.Bridge.policyOf
  BSmtLib.Facts.Parser.Adapters.Bridge.valuesOf
BSmtLib.Facts.Parser.Adapters.Cursor:
  BSmtLib.Facts.Parser.Adapters.Cursor.Reads
  BSmtLib.Facts.Parser.Adapters.Cursor.Takes
  BSmtLib.Facts.Parser.Adapters.Cursor.noPoints
BSmtLib.Facts.Parser.Adapters.Handler:
  BSmtLib.Facts.Parser.Adapters.Handler.Bridged
  BSmtLib.Facts.Parser.Adapters.Handler.attributeValueOf
  BSmtLib.Facts.Parser.Adapters.Handler.bridgedCall
  BSmtLib.Facts.Parser.Adapters.Handler.instCommandHandlerBridged
  BSmtLib.Facts.Parser.Adapters.Handler.instHandlerBridged
  BSmtLib.Facts.Parser.Adapters.Handler.liftCall
  BSmtLib.Facts.Parser.Adapters.Handler.liftHandler
  BSmtLib.Facts.Parser.Adapters.Handler.recordingCall
  BSmtLib.Facts.Parser.Adapters.Handler.recordingLibrary
  BSmtLib.Facts.Parser.Adapters.Handler.recordingLibraryTerms
  BSmtLib.Facts.Parser.Adapters.Handler.sExprNodeOf
  BSmtLib.Facts.Parser.Adapters.Handler.termNodeOf
BSmtLib.Facts.Parser.Adapters.Outcome:
  BSmtLib.Facts.Parser.Adapters.Outcome.Finishes
  BSmtLib.Facts.Parser.Adapters.Outcome.HandlerOnly
  BSmtLib.Facts.Parser.Adapters.Outcome.Outcome
  BSmtLib.Facts.Parser.Adapters.Outcome.Rejects
  BSmtLib.Facts.Parser.Adapters.Outcome.Waits
  BSmtLib.Facts.Parser.Adapters.Outcome.answer
  BSmtLib.Facts.Parser.Adapters.Outcome.outcome
BSmtLib.Facts.Parser.Adapters.Run:
  BSmtLib.Facts.Parser.Adapters.Run.Rejection.LibItem
  BSmtLib.Facts.Parser.Adapters.Run.Rejection.libEnding
  BSmtLib.Facts.Parser.Adapters.Run.Rejection.libraryParser
  BSmtLib.Facts.Parser.Adapters.Run.adaptRun
  BSmtLib.Facts.Parser.Adapters.Run.arrivalTick
  BSmtLib.Facts.Parser.Adapters.Run.arriveAt
  BSmtLib.Facts.Parser.Adapters.Run.drive
  BSmtLib.Facts.Parser.Adapters.Run.driveInput
  BSmtLib.Facts.Parser.Adapters.Run.driveParse
  BSmtLib.Facts.Parser.Adapters.Run.noArrival
  BSmtLib.Facts.Parser.Adapters.Run.parserRecord
  BSmtLib.Facts.Parser.Adapters.Run.processAt
  BSmtLib.Facts.Parser.Adapters.Run.recordedRun
  BSmtLib.Facts.Parser.Adapters.Run.startEvents
  BSmtLib.Facts.Parser.Adapters.Run.unrestrictedPosture
-/
#guard_msgs in
#adapters within BSmtLib.Facts.Parser.Adapters

end BSmtLib.Facts.Parser
