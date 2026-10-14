import BSmtLib.Parser.Script
import BSmtLib.Token.Produce
import BSmtLib.Token.ConsumeFrom

/-!
# The parse adapter

The token consumer that runs a parser over the tokens a producer hands over: at the start of
every input, before anything else, it tells the handler the producer's version; for each token, it
tells the parser of the token's arrival, then has it take the token, viewed under the producer's
version, and acts on the producer as the parser asks. It is the only part of the parser that
reads a producer.
-/

open BSmtLib.Traits

namespace BSmtLib.Parser.Adapter

/- LEAN: Rust's `SmtParseAdapter`. It holds the handler, which is read back from the adapter
after a run, also after a failure. The adapter is never concrete: it does not take whitespace
and comments. -/
/-- A parser with its handler, as the token consumer of a lexer (`SmtParseAdapter`). -/
structure ParseAdapter (H P : Type) where
  handler : H
  parser : P
  /-- Whether the handler was told the version of the input being read. -/
  versionSet : Bool

namespace ParseAdapter

variable {H P R E : Type} {m : Type → Type} [Monad m] [Parse P H m E R]

/-- The adapter of the parser over the handler. -/
def new (handler : H) (parser : P) : ParseAdapter H P :=
  { handler, parser, versionSet := false }

/-- What the parser did with a token. -/
inductive After (P R E : Type) where
  /-- It goes on: take the next token. -/
  | goOn (parser : P)
  /-- The hand-over stops with the answer to the producer, the parser to go on from after. -/
  | stop (answer : Except (ParseErrorCause E) (ControlFlow R)) (parser : P)

/-- What the parser's step asks after the producer did what the step asked. A parser that
finished goes on from `fresh`, its reset. -/
def resumed (fresh : P) : Step P R → After P R E
  | .more parser => .stop (.ok .continue) parser
  | .done result => .stop (.ok (.break result)) fresh

variable {Z : Type} [Token.Produce Z]

/- LEAN: Rust's parsers act on the producer themselves; here the step asks, and the adapter acts.
After an action on the producer the hand-over stops, so that the producer hands the rest over
anew under what the action changed. An action stands when the step fails after it, as in Rust,
where the producer is changed in place.

The reset parser is made before the step, and the parser is not used after it: the step then
holds the only reference to the parser's state, so that the state is updated in place and not
copied at every token. A failed parser goes on from its reset too, as a consumer that failed is
in no state it promises. -/
/--
Has the parser take the token, taken from `cursor` and leaving `next`: its arrival, its step, and
what the step asks of the producer. A refused switch of the version fails with
`unsupportedVersion`.
-/
@[inline]
def takeOne (parser : P) (cursor : Z) (token : Token.Produce.Token Z) (next : Z)
    (consumed : Token.Produce.Consumed next cursor) :
    StateT H m (After P R E × { z : Z // Token.Produce.Consumed z cursor }) := do
  let fresh := Parse.reset parser
  let input := Input.ofSyntax (Token.Produce.«syntax» next token)
  match ← (do Parse.arrive parser input; Parse.step (Token.Produce.version next) parser input).run
      with
  | .error error => return (.stop (.error error) fresh, ⟨next, consumed⟩)
  | .ok (.more parser) => return (.goOn parser, ⟨next, consumed⟩)
  | .ok (.done result) =>
    return (.stop (.ok (.break result)) fresh, ⟨next, consumed⟩)
  | .ok (.switchVersion declared resume) =>
    match switch : Token.Produce.setVersion next declared with
    | .error _ => return (.stop (.error (.syntax .unsupportedVersion)) fresh, ⟨next, consumed⟩)
    | .ok switched =>
      let after := Token.Produce.setVersion_consumed consumed switch
      match ← resume.run with
      | .error error => return (.stop (.error error) fresh, ⟨switched, after⟩)
      | .ok step => return (resumed fresh step, ⟨switched, after⟩)
  | .ok (.discardRest resume) =>
    let after := Token.Produce.discardRest_consumed consumed
    match ← resume.run with
    | .error error => return (.stop (.error error) fresh, ⟨Token.Produce.discardRest next, after⟩)
    | .ok step => return (resumed fresh step, ⟨Token.Produce.discardRest next, after⟩)

/- LEAN: the loop is the recursion, which ends as every token taken is consumed, by the
producer's well-founded consumption. -/
/-- A producer, ordered by its consumption: the loop over its tokens descends by it. -/
structure Consuming (Z : Type) where
  producer : Z

instance : WellFoundedRelation (Consuming Z) :=
  invImage Consuming.producer ⟨Token.Produce.Consumed, Token.Produce.consumed_wf⟩

/--
Has the parser take the tokens of `cursor`, which comes from `origin` with tokens consumed, one
by one, until there are none or the hand-over stops.
-/
def rest (origin : Z) (parser : P) (cursor : Z) (consumed : Token.Produce.Consumed cursor origin) :
    StateT H m (Except (ParseErrorCause E) (ControlFlow R) × P ×
      { z : Z // Token.Produce.Consumed z origin }) :=
  match Token.Produce.next? cursor with
  | none => return (.ok .continue, parser, ⟨cursor, consumed⟩)
  | some (token, ⟨next, step⟩) => do
    match ← takeOne parser cursor token next step with
    | (.goOn parser, ⟨later, taken⟩) =>
      rest origin parser later (Token.Produce.consumed_trans taken consumed)
    | (.stop answer parser, ⟨later, taken⟩) =>
      return (answer, parser, ⟨later, Token.Produce.consumed_trans taken consumed⟩)
termination_by (⟨cursor⟩ : Consuming Z)
decreasing_by exact taken

/-- The first token of a producer that has one. -/
def first (producer : Z) (h : Token.Produce.HasNext producer) :
    Token.Produce.Token Z × { next : Z // Token.Produce.Consumed next producer } :=
  match taken : Token.Produce.next? producer with
  | some first => first
  | none => absurd (Token.Produce.next?_isSome h) (by rw [taken]; exact Bool.false_ne_true)

end ParseAdapter

variable {H P R E : Type}

instance {m : Type → Type} [Monad m] [Parse P H m E R] :
    Token.Consume (ParseAdapter H P) R (ParseErrorCause E) where
  isConcrete := false

/-- Whether the parser is to be told the version before the next hand-over: after its answer,
unless it broke, it is not, as the next hand-over continues the same input. -/
def ParseAdapter.versionSetAfter {R E : Type} : Except (ParseErrorCause E) (ControlFlow R) → Bool
  | .ok (.break _) => false
  | _ => true

/- LEAN: Rust's `impl SmtConsumeFrom<Z> for SmtParseAdapter`, for every producer. -/
instance {m : Type → Type} [Monad m] [Handler H m] [Parse P H m E R] {Z : Type} [Token.Produce Z] :
    Token.ConsumeFrom (ParseAdapter H P) Z m where
  consume producer h := do
    let adapter ← get
    -- the handler is told the version in force before the first token of every input
    let ((), handler) ← (show StateT H m Unit from
      if adapter.versionSet then pure () else Handler.setVersion
          (Token.Produce.version producer)).run
        adapter.handler
    let (token, ⟨next, consumed⟩) := ParseAdapter.first producer h
    let ((after, ⟨later, taken⟩), handler) ←
      (ParseAdapter.takeOne adapter.parser producer token next consumed).run handler
    match after with
    | .stop answer parser =>
      set ({ handler, parser, versionSet := ParseAdapter.versionSetAfter answer } :
        ParseAdapter H P)
      return (answer, ⟨later, taken⟩)
    | .goOn parser =>
      let ((answer, parser, done), handler) ←
        (ParseAdapter.rest producer parser later taken).run handler
      set ({ handler, parser, versionSet := ParseAdapter.versionSetAfter answer } :
        ParseAdapter H P)
      return (answer, done)

end BSmtLib.Parser.Adapter
