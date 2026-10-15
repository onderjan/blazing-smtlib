module

public import BSmtLib.Parser.Category.Token

public section

/-!
# Lists

The parser of a list of elements, each parsed by an inner parser, up to a `)`, with or without
its own `(` and with a maximum number of elements or none.
-/

namespace BSmtLib.Parser.Category.Combinator

open BSmtLib.Traits BSmtLib.Parser.Category.Token
open BSmtLib.Parser.Category.Token.Internal
open BSmtLib.Parser.Internal (PM call syntaxError)

namespace Internal

/--
The state of a list of elements, each parsed by an inner parser, up to a `)`: whether the `(`
that opens the list is consumed (always, for a list whose `(` belongs to someone else), whether
the parser is between elements, the inner parser's state, and the elements so far.
-/
structure ListState (σ ρ : Type) where
  opened : Bool
  outside : Bool
  inner : σ
  items : Array ρ

namespace ListState

variable {σ ρ : Type}

/-- A list whose `(` is still to come, with the inner parser at its initial state. -/
def paren (init : σ) : ListState σ ρ :=
  { opened := false, outside := true, inner := init, items := #[] }

/-- A list whose `(` is already consumed. -/
def closed (init : σ) : ListState σ ρ :=
  { opened := true, outside := true, inner := init, items := #[] }

variable {H : Type} {m : Type → Type} [Monad m] [Handler H m]

/--
A step of the list: the `(` first, if the list opens with one; between elements, a `)` ends the
list, and with a maximum reached, nothing else may come; any other token goes to the inner
parser, which starts the next element.
-/
/- LEAN: Rust's `SmtParenMultipleParser`, `SmtClosedMultipleParser` and the maximum parsers,
in one. -/
@[specialize inner]
def step (init : σ) (inner : σ → Internal.Input → PM H (Internal.Step σ ρ)) (maximum : Option Nat)
    (self : ListState σ ρ) (token : Internal.Input) : PM H (Internal.Step (ListState σ ρ)
        (Array ρ)) := do
  if !self.opened then
    expectOpen token
    return .more { self with opened := true }
  if self.outside then
    if let .parenClose := token then
      return .done self.items
    if let some limit := maximum then
      if limit ≤ self.items.size then
        syntaxError (.expectedToken #[.parenClose])
  match ← inner self.inner token with
  | .more state => return .more { self with inner := state, outside := false }
  | .done item =>
    return .more { self with inner := init, outside := true, items := self.items.push item }

end ListState

end Internal

/-! ## The combinators (`SmtParse`)

Parsers built of other parsers, each having its inner parsers parse the cursor it is handed, in
turn. An inner parser that finishes is back in its initial state, as every parser is, so a
combinator that finishes is back in its initial state too. -/

namespace Internal

open BSmtLib.Token (Produce)

section

variable {Z : Type} [Produce Z]

/-- The first token of a producer that has one, and the producer after it. -/
def firstToken (producer : Z) (h : Produce.HasNext producer) :
    Produce.Token Z × { next : Z // Produce.Consumed next producer } :=
  match taken : Produce.next? producer with
  | some first => first
  | none => absurd (Produce.next?_isSome h) (by rw [taken]; exact Bool.false_ne_true)

end

/-- The answer of a parse, with the result of a parser that finished changed by `f`. -/
def mapBreak {ε α β : Type} (f : α → β) : Except ε (ControlFlow α) → Except ε (ControlFlow β)
  | .ok (.break value) => .ok (.break (f value))
  | .ok .continue => .ok .continue
  | .error error => .error error

section

variable {H S R E : Type} {m : Type → Type} [Monad m] {Z : Type} [Produce Z]

/-- A turn of a combinator's loop on a cursor with a token: it takes at least one token, and
gives the combinator's answer if it stops, `none` if it goes on. -/
abbrev Turn (H S R E Z : Type) (m : Type → Type) [Produce Z] :=
  S → ParseState H → (cursor : Z) → Produce.HasNext cursor →
    StateT H m (Option (Except (ParseErrorCause E) (ControlFlow R)) × S × ParseState H ×
      { next : Z // Produce.Consumed next cursor })

/-- Has the combinator take turns on `cursor`, which comes from `origin` with tokens consumed,
while the cursor has a token and the combinator goes on. -/
@[specialize turn]
def repeatTurns (turn : Turn H S R E Z m) (origin : Z) (self : S) (state : ParseState H)
    (cursor : Z) (consumed : Produce.Consumed cursor origin) :
    StateT H m (Except (ParseErrorCause E) (ControlFlow R) × S × ParseState H ×
      { next : Z // Produce.Consumed next origin }) :=
  match Produce.decideHasNext cursor with
  | .isFalse _ => return (.ok .continue, self, state, ⟨cursor, consumed⟩)
  | .isTrue h => do
    match ← turn self state cursor h with
    | (some answer, self, state, ⟨next, taken⟩) =>
      return (answer, self, state, ⟨next, Produce.consumed_trans taken consumed⟩)
    | (none, self, state, ⟨next, taken⟩) =>
      repeatTurns turn origin self state next (Produce.consumed_trans taken consumed)
termination_by (⟨cursor⟩ : Parser.Internal.Consuming Z)
decreasing_by exact taken

/-- Has the combinator take turns on the cursor while it has a token and the combinator goes on:
the `parse` of a combinator that loops. -/
@[inline]
def parseByTurns (turn : Turn H S R E Z m) (self : S) (state : ParseState H) (cursor : Z) :
    StateT H m (Except (ParseErrorCause E) (ControlFlow R) × S × ParseState H ×
      { next : Z // Produce.HasNext cursor → Produce.Consumed next cursor }) :=
  match Produce.decideHasNext cursor with
  | .isFalse h => return (.ok .continue, self, state, ⟨cursor, fun hn => absurd hn h⟩)
  | .isTrue h => do
    match ← turn self state cursor h with
    | (some answer, self, state, ⟨next, taken⟩) =>
      return (answer, self, state, ⟨next, fun _ => taken⟩)
    | (none, self, state, ⟨next, taken⟩) =>
      let (answer, self, state, ⟨done, consumed⟩) ← repeatTurns turn cursor self state next taken
      return (answer, self, state, ⟨done, fun _ => consumed⟩)

end

end Internal

open BSmtLib.Token (Produce)

/--
A parser that parses with the first parser, then with the second, and finishes with both results
(`SmtPairParser`).
-/
structure PairParser (H P₁ P₂ : Type) {m : Type → Type} {E R₁ : Type} [Parse P₁ H m E R₁] where
  private mk ::
  private first : P₁
  private second : P₂
  /-- The first parser's result, once it finished. -/
  private firstResult : Option R₁

section

variable {H P₁ P₂ : Type} {m : Type → Type} {E R₁ : Type} [Parse P₁ H m E R₁]

/-- The pair of the parsers, before the first value. -/
def PairParser.new (first : P₁) (second : P₂) : PairParser H P₁ P₂ :=
  { first, second, firstResult := none }

instance [Inhabited P₁] [Inhabited P₂] : Inhabited (PairParser H P₁ P₂) := ⟨.new default default⟩

end

section

variable {H P₁ P₂ R₁ R₂ : Type} {m : Type → Type} [Monad m] [Handler H m]
  [Parse P₁ H m (Handler.Error H) R₁] [Parse P₂ H m (Handler.Error H) R₂]
  {Z : Type} [Produce Z]

/-- Has the second parser parse the cursor, the first having finished with `first`. -/
private def PairParser.parseSecond (self : PairParser H P₁ P₂) (first : R₁)
    (state : ParseState H) (cursor : Z) :
    StateT H m (Except (ParseErrorCause (Handler.Error H)) (ControlFlow (R₁ × R₂)) ×
      PairParser H P₁ P₂ × ParseState H ×
      { next : Z // Produce.HasNext cursor → Produce.Consumed next cursor }) := do
  let (answer, second, state, next) ← Parse.parse self.second state cursor
  match answer with
  | .ok (.break result) =>
    return (.ok (.break (first, result)), { self with second, firstResult := none }, state, next)
  | .ok .continue => return (.ok .continue, { self with second, firstResult := some first }, state,
      next)
  | .error error => return (.error error, { self with second, firstResult := some first }, state,
      next)

/- LEAN: Rust's pair has the second parser parse the cursor after the first finished, empty or
not. A parser handed an empty cursor gives no proof of what it did with it, so here the second
parser is not handed an empty cursor: it parses from the next cursor on. -/
@[no_expose] instance : Parse (PairParser H P₁ P₂) H m (Handler.Error H) (R₁ × R₂) where
  parse self state cursor := do
    match self.firstResult with
    | some first => self.parseSecond first state cursor
    | none =>
      let (answer, first, state, ⟨next, consumed⟩) ← Parse.parse self.first state cursor
      let self := { self with first }
      match answer with
      | .error error => return (.error error, self, state, ⟨next, consumed⟩)
      | .ok .continue => return (.ok .continue, self, state, ⟨next, consumed⟩)
      | .ok (.break result) =>
        match Produce.decideHasNext next with
        | .isFalse _ =>
          return (.ok .continue, { self with firstResult := some result }, state,
            ⟨next, consumed⟩)
        | .isTrue h =>
          let (answer, self, state, ⟨later, taken⟩) ← self.parseSecond result state next
          return (answer, self, state,
            ⟨later, fun hn => Produce.consumed_trans (taken h) (consumed hn)⟩)

end

/-- A parser that parses with the inner parser, then takes a `)`, and finishes with the inner
result (`SmtClosedParser`). -/
structure ClosedParser (H P : Type) {m : Type → Type} {E R : Type} [Parse P H m E R] where
  private mk ::
  private inner : PairParser H P CloseParenParser

/-- A parser that takes a `(`, then parses with the inner parser, and finishes with its result
(`SmtOpenedParser`). -/
structure OpenedParser (H P : Type) {m : Type → Type} [Monad m] [Handler H m] where
  private mk ::
  private inner : PairParser H OpenParenParser P

section

variable {H P : Type} {m : Type → Type} {E R : Type} [Parse P H m E R]

/-- The parser before the inner value. -/
def ClosedParser.new (inner : P) : ClosedParser H P := ⟨.new inner .new⟩

instance [Inhabited P] : Inhabited (ClosedParser H P) := ⟨.new default⟩

end

section

variable {H P : Type} {m : Type → Type} [Monad m] [Handler H m]

/-- The parser before the `(`. -/
def OpenedParser.new (inner : P) : OpenedParser H P := ⟨.new .new inner⟩

instance [Inhabited P] : Inhabited (OpenedParser H P) := ⟨.new default⟩

end

section

variable {H P R : Type} {m : Type → Type} [Monad m] [Handler H m]
  [Parse P H m (Handler.Error H) R]

@[no_expose] instance : Parse (ClosedParser H P) H m (Handler.Error H) R where
  parse self state cursor := do
    let (answer, inner, state, next) ← Parse.parse self.inner state cursor
    return (Internal.mapBreak (fun (result, ()) => result) answer, ⟨inner⟩, state, next)

@[no_expose] instance : Parse (OpenedParser H P) H m (Handler.Error H) R where
  parse self state cursor := do
    let (answer, inner, state, next) ← Parse.parse self.inner state cursor
    return (Internal.mapBreak (fun ((), result) => result) answer, ⟨inner⟩, state, next)

end

/-- A parser of the inner parser's value enclosed in `(` and `)` (`SmtParenParser`). -/
abbrev ParenParser (H P : Type) {m : Type → Type} [Monad m] [Handler H m] {E R : Type}
    [Parse P H m E R] :=
  OpenedParser H (ClosedParser H P)

/-- The parser before the `(`. -/
/- LEAN: Rust's `SmtParenParser` is a type alias, made with `SmtOpenedParser::new` and
`SmtClosedParser::new`; this does both. -/
def ParenParser.new {H P : Type} {m : Type → Type} [Monad m] [Handler H m] {E R : Type}
    [Parse P H m E R] (inner : P) : ParenParser H P :=
  OpenedParser.new (ClosedParser.new inner)

/--
A parser of values of the inner parser up to a `)`, which finishes with their results
(`SmtClosedMultipleParser`). It does not take the `(` that the `)` closes; `ParenMultipleParser`
does.
-/
structure ClosedMultipleParser (H P : Type) {m : Type → Type} {E R : Type} [Parse P H m E R]
    where
  private mk ::
  private inner : P
  /-- Whether the parser is between values, where a `)` ends the list. -/
  private outside : Bool
  private items : Array R

section

variable {H P : Type} {m : Type → Type} {E R : Type} [Parse P H m E R]

/-- The parser before the first value. -/
def ClosedMultipleParser.new (inner : P) : ClosedMultipleParser H P :=
  { inner, outside := true, items := #[] }

instance [Inhabited P] : Inhabited (ClosedMultipleParser H P) := ⟨.new default⟩

end

section

variable {H P R : Type} {m : Type → Type} [Monad m] [Handler H m]
  [Parse P H m (Handler.Error H) R] {Z : Type} [Produce Z]

/-- A turn of the list: between values, a `)` ends the list; any other token goes to the inner
parser, which parses the next value. -/
private def ClosedMultipleParser.turn :
    Internal.Turn H (ClosedMultipleParser H P) (Array R) (Handler.Error H) Z m :=
  fun self state cursor h => do
    let (token, ⟨next, consumed⟩) := Internal.firstToken cursor h
    if self.outside then
      if let .parenClose := Produce.syntax next token then
        return (some (.ok (.break self.items)), { self with items := #[] }, state,
          ⟨next, consumed⟩)
    let (answer, inner, state, ⟨later, taken⟩) ← Parse.parse self.inner state cursor
    let self := { self with inner, outside := false }
    match answer with
    | .error error => return (some (.error error), self, state, ⟨later, taken h⟩)
    | .ok .continue => return (some (.ok .continue), self, state, ⟨later, taken h⟩)
    | .ok (.break item) =>
      return (none, { self with outside := true, items := self.items.push item }, state,
        ⟨later, taken h⟩)

@[no_expose] instance : Parse (ClosedMultipleParser H P) H m (Handler.Error H) (Array R) where
  parse self state cursor := Internal.parseByTurns ClosedMultipleParser.turn self state cursor

end

/-- A parser of values of the inner parser enclosed in `(` and `)`, which finishes with their
results (`SmtParenMultipleParser`). -/
abbrev ParenMultipleParser (H P : Type) {m : Type → Type} [Monad m] [Handler H m] {E R : Type}
    [Parse P H m E R] :=
  OpenedParser H (ClosedMultipleParser H P)

/-- The parser before the `(`. -/
/- LEAN: Rust's `SmtParenMultipleParser` is a type alias, made with `SmtOpenedParser::new` and
`SmtClosedMultipleParser::new`; this does both. -/
def ParenMultipleParser.new {H P : Type} {m : Type → Type} [Monad m] [Handler H m] {E R : Type}
    [Parse P H m E R] (inner : P) : ParenMultipleParser H P :=
  OpenedParser.new (ClosedMultipleParser.new inner)

/--
A parser of at most a maximum number of values of the inner parser up to a `)`, which finishes
with their results (`SmtClosedMaximumParser`). A value beyond the maximum is a syntax error at
its first token, which expected the `)`.
-/
structure ClosedMaximumParser (H P : Type) {m : Type → Type} {E R : Type} [Parse P H m E R]
    where
  private mk ::
  private maximum : Nat
  private outside : Bool
  private results : Array R
  private inner : P

section

variable {H P : Type} {m : Type → Type} {E R : Type} [Parse P H m E R]

/-- The parser before the first value, allowing at most `maxElements` values. -/
def ClosedMaximumParser.new (inner : P) (maxElements : Nat) : ClosedMaximumParser H P :=
  { maximum := maxElements, outside := true, results := #[], inner }

/--
Sets the maximum number of values.

The maximum is only applied when deciding whether a next value is allowed: it does not affect
the values parsed before or the value being parsed, so the parser may finish with more values
than the maximum set while it parses.
-/
def ClosedMaximumParser.setMaximum (self : ClosedMaximumParser H P) (maxElements : Nat) :
    ClosedMaximumParser H P :=
  { self with maximum := maxElements }

/-- The maximum number of values. -/
def ClosedMaximumParser.maxElements (self : ClosedMaximumParser H P) : Nat :=
  self.maximum

end

section

variable {H P R : Type} {m : Type → Type} [Monad m] [Handler H m]
  [Parse P H m (Handler.Error H) R] {Z : Type} [Produce Z]

/-- A turn of the list: between values, a `)` ends the list, and with the maximum reached any
other token is an error; any other token goes to the inner parser, which parses the next
value. -/
private def ClosedMaximumParser.turn :
    Internal.Turn H (ClosedMaximumParser H P) (Array R) (Handler.Error H) Z m :=
  fun self state cursor h => do
    let (token, ⟨next, consumed⟩) := Internal.firstToken cursor h
    if self.outside then
      if let .parenClose := Produce.syntax next token then
        return (some (.ok (.break self.results)), { self with results := #[] }, state,
          ⟨next, consumed⟩)
      if self.maximum ≤ self.results.size then
        return (some (.error (.syntax (.expectedToken #[.parenClose]))), self, state,
          ⟨next, consumed⟩)
    let (answer, inner, state, ⟨later, taken⟩) ← Parse.parse self.inner state cursor
    let self := { self with inner, outside := false }
    match answer with
    | .error error => return (some (.error error), self, state, ⟨later, taken h⟩)
    | .ok .continue => return (some (.ok .continue), self, state, ⟨later, taken h⟩)
    | .ok (.break item) =>
      return (none, { self with outside := true, results := self.results.push item }, state,
        ⟨later, taken h⟩)

@[no_expose] instance : Parse (ClosedMaximumParser H P) H m (Handler.Error H) (Array R) where
  parse self state cursor := Internal.parseByTurns ClosedMaximumParser.turn self state cursor

end

/--
A parser of at most a maximum number of values of the inner parser enclosed in `(` and `)`, which
finishes with their results (`SmtParenMaximumParser`).
-/
structure ParenMaximumParser (H P : Type) {m : Type → Type} {E R : Type} [Parse P H m E R] where
  private mk ::
  private isOpened : Bool
  private inner : ClosedMaximumParser H P

section

variable {H P : Type} {m : Type → Type} {E R : Type} [Parse P H m E R]

/-- The parser before the `(`, allowing at most `maxElements` values. -/
def ParenMaximumParser.new (inner : P) (maxElements : Nat) : ParenMaximumParser H P :=
  { isOpened := false, inner := .new inner maxElements }

/--
Sets the maximum number of values.

The maximum is only applied when deciding whether a next value is allowed: it does not affect
the values parsed before or the value being parsed, so the parser may finish with more values
than the maximum set while it parses.
-/
def ParenMaximumParser.setMaximum (self : ParenMaximumParser H P) (maxElements : Nat) :
    ParenMaximumParser H P :=
  { self with inner := self.inner.setMaximum maxElements }

/-- The maximum number of values. -/
def ParenMaximumParser.maxElements (self : ParenMaximumParser H P) : Nat :=
  self.inner.maxElements

end

section

variable {H P R : Type} {m : Type → Type} [Monad m] [Handler H m]
  [Parse P H m (Handler.Error H) R] {Z : Type} [Produce Z]

/-- Has the list parse the cursor, the `(` taken. -/
private def ParenMaximumParser.parseInner (self : ParenMaximumParser H P) (state : ParseState H)
    (cursor : Z) :
    StateT H m (Except (ParseErrorCause (Handler.Error H)) (ControlFlow (Array R)) ×
      ParenMaximumParser H P × ParseState H ×
      { next : Z // Produce.HasNext cursor → Produce.Consumed next cursor }) := do
  let (answer, inner, state, next) ← Parse.parse self.inner state cursor
  match answer with
  | .ok (.break results) => return (.ok (.break results), { isOpened := false, inner }, state, next)
  | answer => return (answer, { self with inner }, state, next)

/- LEAN: as in the pair, the list is not handed an empty cursor after the `(`. -/
@[no_expose] instance : Parse (ParenMaximumParser H P) H m (Handler.Error H) (Array R) where
  parse self state cursor :=
    if self.isOpened then self.parseInner state cursor
    else
      match taken : Produce.next? cursor with
      | none => return (.ok .continue, self, state,
          ⟨cursor, fun hn => absurd hn (Parser.Internal.not_hasNext taken)⟩)
      | some (token, ⟨next, consumed⟩) =>
        match Produce.syntax next token with
        | .parenOpen =>
          let self := { self with isOpened := true }
          match Produce.decideHasNext next with
          | .isFalse _ => return (.ok .continue, self, state, ⟨next, fun _ => consumed⟩)
          | .isTrue h => do
            let (answer, self, state, ⟨later, taken⟩) ← self.parseInner state next
            return (answer, self, state,
              ⟨later, fun _ => Produce.consumed_trans (taken h) consumed⟩)
        | _ => return (.error (.syntax (.expectedToken #[.parenOpen])), self, state,
            ⟨next, fun _ => consumed⟩)

end

end BSmtLib.Parser.Category.Combinator
