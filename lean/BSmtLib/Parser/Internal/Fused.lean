module

public import BSmtLib.Parser.Internal.Fused.Category

public section

/-!
# The fused script reader

The script parser with the same state (`Parser.Script.ScriptParser`), run by one tail-recursive
loop over a batch cursor that holds the state of the term parser of `assert` and of definitions
in arguments of its own while the term is read: the command around the term (`TermContext`), the
term's mode and its levels. The parser's state is put back together from them when the loop
stops (`assemble`). Each step takes the loop's continuation and calls it with its outcome, so
that after inlining every outcome is a tail call in the loop, in every monad.

Fused: terms (without `match`, annotations and `as`), indexed identifiers, and the commands
`assert`, `declare-fun`, `declare-const`, `define-fun`, `define-fun-rec`, `define-const`, `push`,
`pop` and every command's last `)`; sorts, sorted variables and signatures by the functions of
`Parser.Internal.Fused.Category`. Every other state is stepped by the port's own steps.

The script parser's `parse` (`Fused.parse`) runs this loop on a batch cursor of the library's
lexer, which the cursor gives through `Token.Produce.asBatch?`, and the parser's loop over single
tokens on every other producer.
-/

namespace BSmtLib.Parser.Internal.Fused

open BSmtLib.Nodes BSmtLib.Traits
open BSmtLib.Token.BatchCursor.Internal (remaining)
open BSmtLib.Parser.Category.Combinator.Internal (ListState)
open BSmtLib.Parser.Category.Term.Internal (TermLevel TermLevelOf TermStateOf)
open BSmtLib.Parser.Command.Internal (CommandStateOf)
open BSmtLib.Parser.Command.Internal.Definition (DefinitionEnd)
open BSmtLib.Parser.Command.Internal.Standard (FinalCall Payload)
open BSmtLib.Parser.Internal.Fused.Basic
open BSmtLib.Parser.Script (ScriptParser)
open BSmtLib.Parser.Script.ScriptParser.Internal renaming mk → scriptParser, posture → postureOf,
  command → commandOf, declarations → declarationsOf
open BSmtLib.Plain (SymbolView NumeralView)
open BSmtLib.Token (BatchTag BatchCursor VersionPosture)

section

variable {H : Type} {m : Type → Type} [Monad m] [CommandHandler H m]

/-- The command state of a command around a term, with the term's state. -/
@[inline]
def withTerm (context : TermContext (Handler.«Sort» H)) (term : TermStateOf H) :
    CommandStateOf H :=
  match context with
  | .assert => .payload (.assert term)
  | .definition definition => .payload (.defineBody definition term)

/-- The command state before the `)` of a command, whose last call it makes. -/
@[inline]
def closing (final : FinalCall (Handler.Attribute H) (Handler.«Sort» H) (Handler.Term H)) :
    CommandStateOf H :=
  .payload (.closing final)

/-- The command state after the command's term. -/
@[inline]
def finishTerm (context : TermContext (Handler.«Sort» H)) (term : Handler.Term H) :
    CommandStateOf H :=
  match context with
  | .assert => closing (.assert term)
  | .definition definition =>
    closing (match definition with
      | .defineConst symbol sort => .defineConst symbol sort term
      | .defineFun => .endDefineFun term
      | .defineFunRec => .endDefineFunRec term)

/-- A term is complete: it goes to the innermost level's construct, or completes the command's
term. As `Parser.Category.Term.Internal.termComplete`. -/
@[inline]
def termComplete {batch : BatchTag} (posture : VersionPosture) (next : BatchCursor batch)
    (h : H) (declarations : Nat) (context : TermContext (Handler.«Sort» H))
    (levels : List (TermLevelOf H)) (term : Handler.Term H) {β : Type}
    (k : OutcomeOf H next → m β) : m β :=
  match levels with
  | [] => k <| .command h declarations (finishTerm context term)
  | .application function sort arguments :: outer =>
    k <| .term h declarations context .start
      (.application function sort (arguments.push term) :: outer)
  | .letBinding bindings symbol :: outer =>
    k <| .term h declarations context (.letBindingClose (bindings.push (symbol, term))) outer
  | .binder kind scope :: outer =>
    k <| .term h declarations context (.binderClose kind scope term) outer
  | .annotation :: outer => k <| .term h declarations context (.annotating term .init) outer
  | .matchScrutinee :: outer => do
    match ← runHandler (Handler.startMatch term) h with
    | (.error e, h) => fail posture next h (.handler e) k
    | (.ok (), h) => k <| .term h declarations context (.matchCasesOpen term) outer
  | .matchCase scrutinee cases pattern scope :: outer =>
    k <| .term h declarations context (.matchCaseClose scrutinee cases pattern scope term) outer

/-- A term without binders handed to the handler, then complete. -/
@[inline]
def handleTerm {batch : BatchTag} (posture : VersionPosture) (next : BatchCursor batch)
    (h : H) (declarations : Nat) (context : TermContext (Handler.«Sort» H))
    (levels : List (TermLevelOf H)) (node : TermNode (Handler.«Sort» H) (Handler.Term H))
    {β : Type} (k : OutcomeOf H next → m β) : m β := do
  match ← runHandler (Handler.handleTerm node) h with
  | (.error e, h) => fail posture next h (.handler e) k
  | (.ok term, h) => termComplete posture next h declarations context levels term k

/-- The step of the port's term parser, for the modes the fused step does not cover. -/
@[inline]
def portTermStep {batch : BatchTag} (posture : VersionPosture) (h : H) (declarations : Nat)
    (context : TermContext (Handler.«Sort» H)) (term : TermStateOf H) (token : Token batch)
    (next : BatchCursor batch) {β : Type} (k : OutcomeOf H next → m β) : m β := do
  let input := Internal.Input.ofSyntax (Token.Produce.«syntax» next token)
  match ← runParser (Category.Term.Internal.termStep next.version term input) h with
  | (.error e, h) => fail posture next h e k
  | (.ok (.more term), h) => k <| .term h declarations context term.mode term.levels
  | (.ok (.done term), h) => k <| .command h declarations (finishTerm context term)

/--
A step of the term parser of the command, in the mode with the levels, fused for its common
modes; the others go through the port's term step. `context` is the command around the term.
-/
@[inline]
def termStep {batch : BatchTag} (posture : VersionPosture) (h : H) (declarations : Nat)
    (context : TermContext (Handler.«Sort» H)) (mode : TermModeOf H)
    (levels : List (TermLevelOf H)) (token : Token batch) (next : BatchCursor batch) {β : Type}
    (k : OutcomeOf H next → m β) : m β := do
  let version := next.version
  let category := next.category token
  match mode with
  | .start =>
    match category with
    | .parenOpen => k <| .term h declarations context .opened levels
    | .parenClose =>
      match levels with
      | .application function sort arguments :: outer =>
        if arguments.isEmpty then fail posture next h (.syntax .emptyTermApplication) k
        else
          handleTerm posture next h declarations context outer
            (.application function sort (.new arguments)) k
      | _ => fail posture next h (.syntax .expectedTerm) k
    | .unquotedSymbol =>
      let content := contentOf next token
      match reservedAt? version next token with
      | none =>
        handleTerm posture next h declarations context levels
          (.identifier ⟨SymbolView.Internal.newUnchecked false content, #[]⟩ none) k
      | some _ => fail posture next h (.syntax .expectedTerm) k
    | .quotedSymbol =>
      handleTerm posture next h declarations context levels
        (.identifier ⟨SymbolView.Internal.newUnchecked true (contentOf next token), #[]⟩ none) k
    | .numeral | .decimal | .hexadecimal | .binary | .string =>
      handleTerm posture next h declarations context levels
        (.constant (constantOf category (contentOf next token))) k
    | _ => fail posture next h (.syntax .expectedTerm) k
  | .opened =>
    match category with
    | .unquotedSymbol =>
      let content := contentOf next token
      match reservedAt? version next token with
      | none =>
        let level :=
          TermLevel.application ⟨SymbolView.Internal.newUnchecked false content, #[]⟩ none #[]
        k <| .term h declarations context .start (level :: levels)
      | some (.general word) =>
        match word with
        | .let => k <| .term h declarations context .letBindingsOpen levels
        | .lambda =>
          k <| .term h declarations context (.sortedVars .lambda (ListState.paren .start))
            levels
        | .forall =>
          k <| .term h declarations context
            (.sortedVars (.quantifier .forall) (ListState.paren .start)) levels
        | .exists =>
          k <| .term h declarations context
            (.sortedVars (.quantifier .exists) (ListState.paren .start)) levels
        | .match => k <| .term h declarations context .start (.matchScrutinee :: levels)
        | .exclamationMark => k <| .term h declarations context .start (.annotation :: levels)
        | .underscore =>
          k <| .term h declarations context (.qualIdent (.indexed .afterUnderscore)) levels
        | .as => k <| .term h declarations context (.qualIdent (.qualifiedIdent .start)) levels
        | _ => fail posture next h (.syntax .expectedOperator) k
      | some (.commandName _) => fail posture next h (.syntax .expectedOperator) k
    | .quotedSymbol =>
      let level := TermLevel.application
        ⟨SymbolView.Internal.newUnchecked true (contentOf next token), #[]⟩ none #[]
      k <| .term h declarations context .start (level :: levels)
    | .parenOpen => k <| .term h declarations context (.applicationHead .opened) levels
    | _ => fail posture next h (.syntax .expectedOperator) k
  | .qualIdent state =>
    match Category.qualIdentStep version state category next token with
    | some (.more state) => k <| .term h declarations context (.qualIdent state) levels
    | some (.done identifier) =>
      handleTerm posture next h declarations context levels (.identifier identifier none) k
    | some (.error kind) => fail posture next h (.syntax kind) k
    | none => portTermStep posture h declarations context { mode, levels } token next k
  | .applicationHead state =>
    match Category.qualIdentStep version state category next token with
    | some (.more state) => k <| .term h declarations context (.applicationHead state) levels
    | some (.done function) =>
      k <| .term h declarations context .start (.application function none #[] :: levels)
    | some (.error kind) => fail posture next h (.syntax kind) k
    | none => portTermStep posture h declarations context { mode, levels } token next k
  | .letBindingsOpen =>
    match category with
    | .parenOpen => k <| .term h declarations context (.letBindingOpen #[]) levels
    | _ => fail posture next h (.syntax (.expectedToken #[.parenOpen])) k
  | .letBindingOpen bindings =>
    match category with
    | .parenOpen => k <| .term h declarations context (.letBindingSymbol bindings) levels
    | .parenClose =>
      if bindings.isEmpty then fail posture next h (.syntax .emptyLetBindings) k
      else
        match ← runHandler (Handler.startLet (Multiple.NamedView.Internal.new bindings)) h with
        | (.error e, h) => fail posture next h (.handler e) k
        | (.ok scope, h) =>
          k <| .term h declarations context .start (.binder .let scope :: levels)
    | _ => fail posture next h (.syntax (.expectedToken #[.parenOpen, .parenClose])) k
  | .letBindingSymbol bindings =>
    match Category.symbolOf? version category next token with
    | some symbol =>
      k <| .term h declarations context .start (.letBinding bindings symbol :: levels)
    | none => fail posture next h (.syntax .expectedSymbol) k
  | .letBindingClose bindings =>
    match category with
    | .parenClose => k <| .term h declarations context (.letBindingOpen bindings) levels
    | _ => fail posture next h (.syntax (.expectedToken #[.parenClose])) k
  | .sortedVars binder state =>
    match ← Category.sortedVarsStepOutlined version h state category next token with
    | .more h state => k <| .term h declarations context (.sortedVars binder state) levels
    | .done h variables =>
      if variables.isEmpty then
        fail posture next h (.syntax (match binder with
          | .lambda => .emptyLambdaBindings
          | _ => .emptyQuantifierBindings)) k
      else
        let started := match binder with
          | .quantifier quantifier =>
            Handler.startQuantifier quantifier (Multiple.NamedView.Internal.new variables)
          | .lambda => Handler.startLambda (Multiple.NamedView.Internal.new variables)
        match ← runHandler started h with
        | (.error e, h) => fail posture next h (.handler e) k
        | (.ok scope, h) =>
          k <| .term h declarations context .start (.binder (.sorted binder) scope :: levels)
    | .error h cause => fail posture next h cause k
  | .binderClose kind scope body =>
    match category with
    | .parenClose =>
      let ended := match kind with
        | .let => Handler.endLet scope body
        | .sorted (.quantifier quantifier) => Handler.endQuantifier quantifier scope body
        | .sorted .lambda => Handler.endLambda scope body
      match ← runHandler ended h with
      | (.error e, h) => fail posture next h (.handler e) k
      | (.ok term, h) => termComplete posture next h declarations context levels term k
    | _ => fail posture next h (.syntax (.expectedToken #[.parenClose])) k
  | _ => portTermStep posture h declarations context { mode, levels } token next k

/-- The step of a command's last `)`. -/
@[inline]
def closingStep {batch : BatchTag} (posture : VersionPosture) (h : H) (declarations : Nat)
    (final : FinalCall (Handler.Attribute H) (Handler.«Sort» H) (Handler.Term H))
    (token : Token batch) (next : BatchCursor batch) {β : Type} (k : OutcomeOf H next → m β) :
    m β := do
  match next.category token with
  | .parenClose =>
    match ← runParser (Command.Internal.Standard.finalCall final) h with
    | (.error e, h) => fail posture next h e k
    | (.ok (), h) =>
      match final with
      | .exit =>
        -- the cursor discards the rest of the input, and the script goes on to its end
        k <| .resume h (scriptParser posture .awaiting declarations) next.discardRest
          (BatchCursor.discardRest_follows next)
      | _ => k <| .command h declarations .awaiting
  | _ => fail posture next h (.syntax (.expectedToken #[.parenClose])) k

/-- A command named by a symbol, a non-standard one: the handler gives its parser, which the
port's step then hands the payload to. -/
@[inline]
def startNonstandard {batch : BatchTag} (posture : VersionPosture) (h : H) (declarations : Nat)
    (name : SymbolView) (next : BatchCursor batch) {β : Type} (k : OutcomeOf H next → m β) :
    m β := do
  match ← runHandler (CommandHandler.nonstandardCommand name) h with
  | (.error e, h) => fail posture next h (.handler e) k
  | (.ok parser, h) => k <| .command h declarations (.nonstandard parser)

/-- The command around a term that starts. -/
@[inline]
def startTerm {batch : BatchTag} {next : BatchCursor batch} (h : H) (declarations : Nat)
    (context : TermContext (Handler.«Sort» H)) : OutcomeOf H next :=
  .term h declarations context .start []

/-- The step of the token at the command level, fused for the common states. -/
@[inline]
def commandStep {batch : BatchTag} (posture : VersionPosture) (h : H) (declarations : Nat)
    (command : CommandStateOf H) (token : Token batch) (next : BatchCursor batch) {β : Type}
    (k : OutcomeOf H next → m β) : m β := do
  match command with
  | .awaiting =>
    match next.category token with
    | .parenOpen => k <| .command h declarations .opened
    | .endOfFile => k <| .stop (.ok (.break ())) (ScriptParser.new posture) next (.refl _) h
    | _ => fail posture next h (.syntax .expectedCommand) k
  | .opened =>
    match next.category token with
    | .unquotedSymbol =>
      match reservedAt? next.version next token with
      | some (.commandName name) =>
        match name with
        | .assert => k <| startTerm h declarations .assert
        | name => k <| .command h declarations (.payload (Payload.init name next.version))
      | some (.general _) => fail posture next h (.syntax .expectedCommandName) k
      | none =>
        startNonstandard posture h declarations
          (SymbolView.Internal.newUnchecked false (contentOf next token)) next k
    | .quotedSymbol =>
      startNonstandard posture h declarations
        (SymbolView.Internal.newUnchecked true (contentOf next token)) next k
    | _ => fail posture next h (.syntax .expectedCommandName) k
  | .payload (.closing final) => closingStep posture h declarations final token next k
  | .payload (.named named) =>
    match Category.symbolOf? next.version (next.category token) next token with
    | none => fail posture next h (.syntax .expectedSymbol) k
    | some symbol =>
      k <| .command h declarations (match named with
        | .declareConst => .payload (.declareConst symbol .init)
        | .declareDatatype => .payload (.declareDatatype symbol .start)
        | .declareFun => .payload (.declareFunParameters symbol (ListState.paren .init))
        | .declareSort => .payload (.declareSort symbol)
        | .declareSortParameter => closing (.declareSortParameter symbol)
        | .defineConst => .payload (.defineConstSort symbol .init)
        | .defineSort => .payload (.defineSortParameters symbol (ListState.paren ()))
        | .setLogic => closing (.setLogic symbol))
  | .payload (.declareConst symbol state) =>
    match ← Category.sortStepOutlined next.version h state (next.category token) next token with
    | .more h state => k <| .command h declarations (.payload (.declareConst symbol state))
    | .done h sort => k <| .command h declarations (closing (.declareConst symbol sort))
    | .error h cause => fail posture next h cause k
  | .payload (.declareFunParameters symbol state) =>
    match ← Category.sortsStepOutlined next.version h state (next.category token) next token
        with
    | .more h state =>
      k <| .command h declarations (.payload (.declareFunParameters symbol state))
    | .done h parameters =>
      k <| .command h declarations (.payload (.declareFunResult symbol parameters .init))
    | .error h cause => fail posture next h cause k
  | .payload (.declareFunResult symbol parameters state) =>
    match ← Category.sortStepOutlined next.version h state (next.category token) next token with
    | .more h state =>
      k <| .command h declarations (.payload (.declareFunResult symbol parameters state))
    | .done h result =>
      k <| .command h declarations (closing (.declareFun symbol parameters result))
    | .error h cause => fail posture next h cause k
  | .payload (.defineConstSort symbol state) =>
    match ← Category.sortStepOutlined next.version h state (next.category token) next token with
    | .more h state => k <| .command h declarations (.payload (.defineConstSort symbol state))
    | .done h sort => k <| startTerm h declarations (.definition (.defineConst symbol sort))
    | .error h cause => fail posture next h cause k
  | .payload (.defineSignature definition state) =>
    match ← Category.signatureStepOutlined next.version h state (next.category token) next
        token with
    | .more h state =>
      k <| .command h declarations (.payload (.defineSignature definition state))
    | .done h signature =>
      let started := match definition with
        | .defineFunRec => CommandHandler.startDefineFunRec signature
        | _ => CommandHandler.startDefineFun signature
      match ← runHandler started h with
      | (.error e, h) => fail posture next h (.handler e) k
      | (.ok (), h) => k <| startTerm h declarations (.definition definition)
    | .error h cause => fail posture next h cause k
  | .payload .push =>
    match next.category token with
    | .numeral =>
      k <| .command h declarations
        (closing (.push (NumeralView.Internal.newUnchecked (contentOf next token))))
    | _ => fail posture next h (.syntax (.expectedToken #[.numeral])) k
  | .payload .pop =>
    match next.category token with
    | .numeral =>
      k <| .command h declarations
        (closing (.pop (NumeralView.Internal.newUnchecked (contentOf next token))))
    | _ => fail posture next h (.syntax (.expectedToken #[.numeral])) k
  | _ => portStep posture h declarations command token next k

/-- The step of the token: in the command's term, or at the command level. -/
@[inline]
def step {batch : BatchTag} (posture : VersionPosture) (h : H) (declarations : Nat)
    (command : CommandStateOf H) (inTerm : Bool) (context : TermContext (Handler.«Sort» H))
    (mode : TermModeOf H) (levels : List (TermLevelOf H)) (token : Token batch)
    (next : BatchCursor batch) {β : Type} (k : OutcomeOf H next → m β) : m β :=
  if inTerm then termStep posture h declarations context mode levels token next k
  else commandStep posture h declarations command token next k

/-- The parser the loop's arguments stand for: the command state, or, in a term, the command
around it with the term's state. -/
@[inline]
def assemble (posture : VersionPosture) (declarations : Nat) (command : CommandStateOf H)
    (inTerm : Bool) (context : TermContext (Handler.«Sort» H)) (mode : TermModeOf H)
    (levels : List (TermLevelOf H)) : ScriptParser H :=
  scriptParser posture
    (if inTerm then withTerm context { mode, levels } else command) declarations

/--
Has the parser take `token`, taken from a cursor that leaves `next`, which has consumed from
`origin`, then the tokens after it, until there are none or the parser stops. The parser is the
one `assemble` makes of the arguments.
-/
@[specialize]
def loop {batch : BatchTag} (posture : VersionPosture) (origin : BatchCursor batch) (h : H)
    (declarations : Nat) (command : CommandStateOf H) (inTerm : Bool)
    (context : TermContext (Handler.«Sort» H)) (mode : TermModeOf H)
    (levels : List (TermLevelOf H)) (token : Token batch) (next : BatchCursor batch)
    (consumed : next.Consumed origin) : m (LoopResult H origin) :=
  step posture h declarations command inTerm context mode levels token next fun outcome =>
  match outcome with
  | .command h declarations command =>
    if hn : next.HasNext then
      let (token', ⟨after, taken⟩) := next.next hn
      have : remaining after < remaining next := taken.remaining_lt
      -- a command state that reads a term goes on with the term in the loop's arguments
      match command with
      | .payload (.assert term) =>
        loop posture origin h declarations .awaiting true .assert term.mode term.levels token'
          after (taken.trans consumed)
      | .payload (.defineBody definition term) =>
        loop posture origin h declarations .awaiting true (.definition definition) term.mode
          term.levels token' after (taken.trans consumed)
      | command =>
        loop posture origin h declarations command false .assert .start [] token' after
          (taken.trans consumed)
    else
      return (.ok .continue, scriptParser posture command declarations, ⟨next, consumed⟩, h)
  | .term h declarations context mode levels =>
    if hn : next.HasNext then
      let (token', ⟨after, taken⟩) := next.next hn
      have : remaining after < remaining next := taken.remaining_lt
      loop posture origin h declarations .awaiting true context mode levels token' after
        (taken.trans consumed)
    else
      return (.ok .continue, assemble posture declarations .awaiting true context mode levels,
        ⟨next, consumed⟩, h)
  | .resume h parser cursor follows =>
    if hn : cursor.HasNext then
      let (token', ⟨after, taken⟩) := cursor.next hn
      have : remaining after < remaining next := (taken.trans_follows follows).remaining_lt
      -- a command state that reads a term goes on with the term in the loop's arguments
      match commandOf parser with
      | .payload (.assert term) =>
        loop (postureOf parser) origin h (declarationsOf parser) .awaiting true .assert term.mode
          term.levels token' after ((taken.trans_follows follows).trans consumed)
      | .payload (.defineBody definition term) =>
        loop (postureOf parser) origin h (declarationsOf parser) .awaiting true
          (.definition definition) term.mode term.levels token' after
          ((taken.trans_follows follows).trans consumed)
      | command =>
        loop (postureOf parser) origin h (declarationsOf parser) command false .assert .start []
          token' after ((taken.trans_follows follows).trans consumed)
    else
      return (.ok .continue, parser, ⟨cursor, follows.trans_consumed consumed⟩, h)
  | .stop answer parser cursor follows h =>
    return (answer, parser, ⟨cursor, follows.trans_consumed consumed⟩, h)
termination_by remaining next

/-- The loop from the first token of a hand-over, with the parser's state in its arguments. -/
@[inline]
def start {batch : BatchTag} (parser : ScriptParser H) (h : H) (token : Token batch)
    (producer next : BatchCursor batch) (consumed : next.Consumed producer) :
    m (LoopResult H producer) :=
  -- a command state that reads a term goes on with the term in the loop's arguments
  match commandOf parser with
  | .payload (.assert term) =>
    loop (postureOf parser) producer h (declarationsOf parser) .awaiting true .assert term.mode
      term.levels token next consumed
  | .payload (.defineBody definition term) =>
    loop (postureOf parser) producer h (declarationsOf parser) .awaiting true
      (.definition definition) term.mode term.levels token next consumed
  | command =>
    loop (postureOf parser) producer h (declarationsOf parser) command false .assert .start []
      token next consumed

/--
Parses the cursor with the script parser: the fused loop if the cursor is a batch cursor of the
library's lexer, else the loop over single tokens.
-/
@[inline]
def parse {Z : Type} [Token.Produce Z] (parser : ScriptParser H) (state : ParseState H)
    (cursor : Z) :
    StateT H m (Except (ParseError (Handler.Error H)) (ControlFlow Unit) × ScriptParser H ×
      ParseState H ×
      { next : Z // Token.Produce.HasNext cursor → Token.Produce.Consumed next cursor }) :=
  match Token.Produce.asBatch? cursor with
  | none => Parser.Internal.parseByToken parser state cursor
  | some view => fun h => do
    if hn : view.cursor.HasNext then
      let (token, ⟨next, consumed⟩) := view.cursor.next hn
      let (answer, parser, ⟨done, taken⟩, h) ← start parser h token view.cursor next consumed
      return ((answer, parser, state, ⟨view.back done, fun _ => view.consumed taken⟩), h)
    else
      return ((.ok .continue, parser, state,
        ⟨view.back view.cursor, fun hc => absurd (view.hasNext hc) hn⟩), h)

end

/- LEAN: Rust's `impl SmtParse<H> for SmtScriptParser<H>` is in `script.rs`. Here it is declared
in this module, which needs the script parser's module, as its `parse` runs the fused loop; it is
named where the script parser is. -/
instance _root_.BSmtLib.Parser.Script.instParseScriptParser {H : Type} {m : Type → Type}
    [Monad m] [CommandHandler H m] : Parse (ScriptParser H) H m (Handler.Error H) Unit where
  parse := Fused.parse

end BSmtLib.Parser.Internal.Fused
