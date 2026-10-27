module

public import BSmtLib.Parser.Category.Token

public section

/-!
# Lists

The parser of a list of elements, each parsed by an inner parser, up to a `)`, with or without
its own `(` and with a maximum number of elements or none.
-/

namespace BSmtLib.Parser.Category.Combinator

open BSmtLib.Handler BSmtLib.Parser.Category.Token
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
        syntaxError (.expected #[.token .parenClose])
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

open BSmtLib.Token (Cursor)

section

variable {Z : Type} [Cursor Z]

/-- The first token of a producer that has one, and the producer after it. -/
def firstToken (cursor : Z) (h : Cursor.HasNext cursor) :
    Cursor.Token Z × { next : Z // Cursor.Consumed next cursor } :=
  match taken : Cursor.next? cursor with
  | some first => first
  | none => absurd (Cursor.next?_isSome h) (by rw [taken]; exact Bool.false_ne_true)

end

/-- The answer of a parse, with the result of a parser that finished changed by `f`. -/
def mapBreak {ε α β : Type} (f : α → β) : Except ε (ControlFlow α) → Except ε (ControlFlow β)
  | .ok (.break value) => .ok (.break (f value))
  | .ok .continue => .ok .continue
  | .error error => .error error

section

variable {H S R E : Type} {m : Type → Type} [Monad m] {Z : Type} [Cursor Z]

/-- A turn of a combinator's loop on a cursor with a token: it takes at least one token, and
gives the combinator's answer if it stops, `none` if it goes on. -/
abbrev Turn (H S R E Z : Type) (m : Type → Type) [Cursor Z] :=
  S → ParseState H → (cursor : Z) → Cursor.HasNext cursor →
    StateT H m (Option (Except (ParseError E) (ControlFlow R)) × S × ParseState H ×
      { next : Z // Cursor.Consumed next cursor })

/-- Has the combinator take turns on `cursor`, which comes from `origin` with tokens consumed,
while the cursor has a token and the combinator goes on. -/
@[specialize turn]
def repeatTurns (turn : Turn H S R E Z m) (origin : Z) (self : S) (state : ParseState H)
    (cursor : Z) (consumed : Cursor.Consumed cursor origin) :
    StateT H m (Except (ParseError E) (ControlFlow R) × S × ParseState H ×
      { next : Z // Cursor.Consumed next origin }) :=
  match Cursor.decideHasNext cursor with
  | .isFalse _ => return (.ok .continue, self, state, ⟨cursor, consumed⟩)
  | .isTrue h => do
    match ← turn self state cursor h with
    | (some answer, self, state, ⟨next, taken⟩) =>
      return (answer, self, state, ⟨next, Cursor.consumed_trans taken consumed⟩)
    | (none, self, state, ⟨next, taken⟩) =>
      repeatTurns turn origin self state next (Cursor.consumed_trans taken consumed)
termination_by (⟨cursor⟩ : Parser.Internal.Consuming Z)
decreasing_by exact taken

/-- Has the combinator take turns on the cursor while it has a token and the combinator goes on:
the `parse` of a combinator that loops. -/
@[inline]
def parseByTurns (turn : Turn H S R E Z m) (self : S) (state : ParseState H) (cursor : Z) :
    StateT H m (Except (ParseError E) (ControlFlow R) × S × ParseState H ×
      { next : Z // Cursor.HasNext cursor → Cursor.Consumed next cursor }) :=
  match Cursor.decideHasNext cursor with
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

open BSmtLib.Token (Cursor)

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
  {Z : Type} [Cursor Z]

/-- Has the second parser parse the cursor, the first having finished with `first`. -/
private def PairParser.parseSecond (self : PairParser H P₁ P₂) (first : R₁)
    (state : ParseState H) (cursor : Z) :
    StateT H m (Except (ParseError (Handler.Error H)) (ControlFlow (R₁ × R₂)) ×
      PairParser H P₁ P₂ × ParseState H ×
      { next : Z // Cursor.HasNext cursor → Cursor.Consumed next cursor }) := do
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
        match Cursor.decideHasNext next with
        | .isFalse _ =>
          return (.ok .continue, { self with firstResult := some result }, state,
            ⟨next, consumed⟩)
        | .isTrue h =>
          let (answer, self, state, ⟨later, taken⟩) ← self.parseSecond result state next
          return (answer, self, state,
            ⟨later, fun hn => Cursor.consumed_trans (taken h) (consumed hn)⟩)

end

/-! ## The tuple combinators

The pair parsers nested to the right over three to eight parsers. A Lean tuple is pairs nested to
the right, `R₁ × R₂ × R₃` being `R₁ × (R₂ × R₃)`, so the nested result is the tuple of the
results. -/

/- LEAN: Rust's `SmtTuple3Parser` … `SmtTuple8Parser` are structures over the nested pair
parsers that flatten the nested result when the last parser finishes. Here each is the nested
pair parsers themselves, whose result is already the flat tuple, so it parses as they do. -/

/-- Parses using each parser in turn, then returns the result tuple (`SmtTuple3Parser`).

Preserves self-reset: if the inner parsers are self-resetting, moves back into the default state
before returning `ControlFlow.break`. -/
abbrev Tuple3Parser (H P₁ P₂ P₃ : Type) {m : Type → Type} {E R₁ R₂ : Type}
    [Parse P₁ H m E R₁] [Parse P₂ H m E R₂] :=
  PairParser H P₁ (PairParser H P₂ P₃)

/-- Parses using each parser in turn, then returns the result tuple (`SmtTuple4Parser`).

Preserves self-reset: if the inner parsers are self-resetting, moves back into the default state
before returning `ControlFlow.break`. -/
abbrev Tuple4Parser (H P₁ P₂ P₃ P₄ : Type) {m : Type → Type} {E R₁ R₂ R₃ : Type}
    [Parse P₁ H m E R₁] [Parse P₂ H m E R₂] [Parse P₃ H m E R₃] :=
  PairParser H P₁ (Tuple3Parser H P₂ P₃ P₄)

/-- Parses using each parser in turn, then returns the result tuple (`SmtTuple5Parser`).

Preserves self-reset: if the inner parsers are self-resetting, moves back into the default state
before returning `ControlFlow.break`. -/
abbrev Tuple5Parser (H P₁ P₂ P₃ P₄ P₅ : Type) {m : Type → Type} {E R₁ R₂ R₃ R₄ : Type}
    [Parse P₁ H m E R₁] [Parse P₂ H m E R₂] [Parse P₃ H m E R₃] [Parse P₄ H m E R₄] :=
  PairParser H P₁ (Tuple4Parser H P₂ P₃ P₄ P₅)

/-- Parses using each parser in turn, then returns the result tuple (`SmtTuple6Parser`).

Preserves self-reset: if the inner parsers are self-resetting, moves back into the default state
before returning `ControlFlow.break`. -/
abbrev Tuple6Parser (H P₁ P₂ P₃ P₄ P₅ P₆ : Type) {m : Type → Type} {E R₁ R₂ R₃ R₄ R₅ : Type}
    [Parse P₁ H m E R₁] [Parse P₂ H m E R₂] [Parse P₃ H m E R₃] [Parse P₄ H m E R₄]
    [Parse P₅ H m E R₅] :=
  PairParser H P₁ (Tuple5Parser H P₂ P₃ P₄ P₅ P₆)

/-- Parses using each parser in turn, then returns the result tuple (`SmtTuple7Parser`).

Preserves self-reset: if the inner parsers are self-resetting, moves back into the default state
before returning `ControlFlow.break`. -/
abbrev Tuple7Parser (H P₁ P₂ P₃ P₄ P₅ P₆ P₇ : Type) {m : Type → Type}
    {E R₁ R₂ R₃ R₄ R₅ R₆ : Type} [Parse P₁ H m E R₁] [Parse P₂ H m E R₂] [Parse P₃ H m E R₃]
    [Parse P₄ H m E R₄] [Parse P₅ H m E R₅] [Parse P₆ H m E R₆] :=
  PairParser H P₁ (Tuple6Parser H P₂ P₃ P₄ P₅ P₆ P₇)

/-- Parses using each parser in turn, then returns the result tuple (`SmtTuple8Parser`).

Preserves self-reset: if the inner parsers are self-resetting, moves back into the default state
before returning `ControlFlow.break`. -/
abbrev Tuple8Parser (H P₁ P₂ P₃ P₄ P₅ P₆ P₇ P₈ : Type) {m : Type → Type}
    {E R₁ R₂ R₃ R₄ R₅ R₆ R₇ : Type} [Parse P₁ H m E R₁] [Parse P₂ H m E R₂]
    [Parse P₃ H m E R₃] [Parse P₄ H m E R₄] [Parse P₅ H m E R₅] [Parse P₆ H m E R₆]
    [Parse P₇ H m E R₇] :=
  PairParser H P₁ (Tuple7Parser H P₂ P₃ P₄ P₅ P₆ P₇ P₈)

section

variable {H P₁ P₂ P₃ P₄ P₅ P₆ P₇ P₈ : Type} {m : Type → Type}
  {E R₁ R₂ R₃ R₄ R₅ R₆ R₇ : Type} [Parse P₁ H m E R₁] [Parse P₂ H m E R₂] [Parse P₃ H m E R₃]
  [Parse P₄ H m E R₄] [Parse P₅ H m E R₅] [Parse P₆ H m E R₆] [Parse P₇ H m E R₇]

/-- The parsers in turn, before the first value. -/
def Tuple3Parser.new (p₁ : P₁) (p₂ : P₂) (p₃ : P₃) : Tuple3Parser H P₁ P₂ P₃ :=
  PairParser.new p₁ (PairParser.new p₂ p₃)

/-- The parsers in turn, before the first value. -/
def Tuple4Parser.new (p₁ : P₁) (p₂ : P₂) (p₃ : P₃) (p₄ : P₄) : Tuple4Parser H P₁ P₂ P₃ P₄ :=
  PairParser.new p₁ (Tuple3Parser.new p₂ p₃ p₄)

/-- The parsers in turn, before the first value. -/
def Tuple5Parser.new (p₁ : P₁) (p₂ : P₂) (p₃ : P₃) (p₄ : P₄) (p₅ : P₅) :
    Tuple5Parser H P₁ P₂ P₃ P₄ P₅ :=
  PairParser.new p₁ (Tuple4Parser.new p₂ p₃ p₄ p₅)

/-- The parsers in turn, before the first value. -/
def Tuple6Parser.new (p₁ : P₁) (p₂ : P₂) (p₃ : P₃) (p₄ : P₄) (p₅ : P₅) (p₆ : P₆) :
    Tuple6Parser H P₁ P₂ P₃ P₄ P₅ P₆ :=
  PairParser.new p₁ (Tuple5Parser.new p₂ p₃ p₄ p₅ p₆)

/-- The parsers in turn, before the first value. -/
def Tuple7Parser.new (p₁ : P₁) (p₂ : P₂) (p₃ : P₃) (p₄ : P₄) (p₅ : P₅) (p₆ : P₆) (p₇ : P₇) :
    Tuple7Parser H P₁ P₂ P₃ P₄ P₅ P₆ P₇ :=
  PairParser.new p₁ (Tuple6Parser.new p₂ p₃ p₄ p₅ p₆ p₇)

/-- The parsers in turn, before the first value. -/
def Tuple8Parser.new (p₁ : P₁) (p₂ : P₂) (p₃ : P₃) (p₄ : P₄) (p₅ : P₅) (p₆ : P₆) (p₇ : P₇)
    (p₈ : P₈) : Tuple8Parser H P₁ P₂ P₃ P₄ P₅ P₆ P₇ P₈ :=
  PairParser.new p₁ (Tuple7Parser.new p₂ p₃ p₄ p₅ p₆ p₇ p₈)

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
structure ParenParser (H P : Type) {m : Type → Type} [Monad m] [Handler H m] {E R : Type}
    [Parse P H m E R] where
  private mk ::
  private inner : OpenedParser H (ClosedParser H P)

section

variable {H P : Type} {m : Type → Type} [Monad m] [Handler H m] {E R : Type} [Parse P H m E R]

/-- The parser before the `(`. -/
def ParenParser.new (inner : P) : ParenParser H P := ⟨.new (.new inner)⟩

instance [Inhabited P] : Inhabited (ParenParser H P) := ⟨.new default⟩

end

section

variable {H P R : Type} {m : Type → Type} [Monad m] [Handler H m]
  [Parse P H m (Handler.Error H) R]

@[no_expose] instance : Parse (ParenParser H P) H m (Handler.Error H) R where
  parse self state cursor := do
    let (answer, inner, state, next) ← Parse.parse self.inner state cursor
    return (answer, ⟨inner⟩, state, next)

end

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
  [Parse P H m (Handler.Error H) R] {Z : Type} [Cursor Z]

/-- A turn of the list: between values, a `)` ends the list; any other token goes to the inner
parser, which parses the next value. -/
private def ClosedMultipleParser.turn :
    Internal.Turn H (ClosedMultipleParser H P) (Array R) (Handler.Error H) Z m :=
  fun self state cursor h => do
    let (token, ⟨next, consumed⟩) := Internal.firstToken cursor h
    if self.outside then
      if let .parenClose := Cursor.syntax next token then
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
structure ParenMultipleParser (H P : Type) {m : Type → Type} [Monad m] [Handler H m]
    {E R : Type} [Parse P H m E R] where
  private mk ::
  private inner : OpenedParser H (ClosedMultipleParser H P)

section

variable {H P : Type} {m : Type → Type} [Monad m] [Handler H m] {E R : Type} [Parse P H m E R]

/-- The parser before the `(`. -/
def ParenMultipleParser.new (inner : P) : ParenMultipleParser H P := ⟨.new (.new inner)⟩

instance [Inhabited P] : Inhabited (ParenMultipleParser H P) := ⟨.new default⟩

end

section

variable {H P R : Type} {m : Type → Type} [Monad m] [Handler H m]
  [Parse P H m (Handler.Error H) R]

@[no_expose] instance : Parse (ParenMultipleParser H P) H m (Handler.Error H) (Array R) where
  parse self state cursor := do
    let (answer, inner, state, next) ← Parse.parse self.inner state cursor
    return (answer, ⟨inner⟩, state, next)

end

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

/-- The parser before the first value, allowing at most `maxItems` values. -/
def ClosedMaximumParser.new (inner : P) (maxItems : Nat) : ClosedMaximumParser H P :=
  { maximum := maxItems, outside := true, results := #[], inner }

/--
Sets the maximum number of values.

The maximum is only applied when deciding whether a next value is allowed: it does not affect
the values parsed before or the value being parsed, so the parser may finish with more values
than the maximum set while it parses.
-/
def ClosedMaximumParser.setMaxItems (self : ClosedMaximumParser H P) (maxItems : Nat) :
    ClosedMaximumParser H P :=
  { self with maximum := maxItems }

/-- The maximum number of values. -/
def ClosedMaximumParser.maxItems (self : ClosedMaximumParser H P) : Nat :=
  self.maximum

end

section

variable {H P R : Type} {m : Type → Type} [Monad m] [Handler H m]
  [Parse P H m (Handler.Error H) R] {Z : Type} [Cursor Z]

/-- A turn of the list: between values, a `)` ends the list, and with the maximum reached any
other token is an error; any other token goes to the inner parser, which parses the next
value. -/
private def ClosedMaximumParser.turn :
    Internal.Turn H (ClosedMaximumParser H P) (Array R) (Handler.Error H) Z m :=
  fun self state cursor h => do
    let (token, ⟨next, consumed⟩) := Internal.firstToken cursor h
    if self.outside then
      if let .parenClose := Cursor.syntax next token then
        return (some (.ok (.break self.results)), { self with results := #[] }, state,
          ⟨next, consumed⟩)
      if self.maximum ≤ self.results.size then
        return (some (.error (ParseError.Internal.new (.syntax (.expected #[.token .parenClose])))),
          self, state, ⟨next, consumed⟩)
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

/-- The parser before the `(`, allowing at most `maxItems` values. -/
def ParenMaximumParser.new (inner : P) (maxItems : Nat) : ParenMaximumParser H P :=
  { isOpened := false, inner := .new inner maxItems }

/--
Sets the maximum number of values.

The maximum is only applied when deciding whether a next value is allowed: it does not affect
the values parsed before or the value being parsed, so the parser may finish with more values
than the maximum set while it parses.
-/
def ParenMaximumParser.setMaxItems (self : ParenMaximumParser H P) (maxItems : Nat) :
    ParenMaximumParser H P :=
  { self with inner := self.inner.setMaxItems maxItems }

/-- The maximum number of values. -/
def ParenMaximumParser.maxItems (self : ParenMaximumParser H P) : Nat :=
  self.inner.maxItems

end

section

variable {H P R : Type} {m : Type → Type} [Monad m] [Handler H m]
  [Parse P H m (Handler.Error H) R] {Z : Type} [Cursor Z]

/-- Has the list parse the cursor, the `(` taken. -/
private def ParenMaximumParser.parseInner (self : ParenMaximumParser H P) (state : ParseState H)
    (cursor : Z) :
    StateT H m (Except (ParseError (Handler.Error H)) (ControlFlow (Array R)) ×
      ParenMaximumParser H P × ParseState H ×
      { next : Z // Cursor.HasNext cursor → Cursor.Consumed next cursor }) := do
  let (answer, inner, state, next) ← Parse.parse self.inner state cursor
  match answer with
  | .ok (.break results) => return (.ok (.break results), { isOpened := false, inner }, state, next)
  | answer => return (answer, { self with inner }, state, next)

/- LEAN: as in the pair, the list is not handed an empty cursor after the `(`. -/
@[no_expose] instance : Parse (ParenMaximumParser H P) H m (Handler.Error H) (Array R) where
  parse self state cursor :=
    if self.isOpened then self.parseInner state cursor
    else
      match taken : Cursor.next? cursor with
      | none => return (.ok .continue, self, state,
          ⟨cursor, fun hn => absurd hn (Parser.Internal.not_hasNext taken)⟩)
      | some (token, ⟨next, consumed⟩) =>
        match Cursor.syntax next token with
        | .parenOpen =>
          let self := { self with isOpened := true }
          match Cursor.decideHasNext next with
          | .isFalse _ => return (.ok .continue, self, state, ⟨next, fun _ => consumed⟩)
          | .isTrue h => do
            let (answer, self, state, ⟨later, taken⟩) ← self.parseInner state next
            return (answer, self, state,
              ⟨later, fun _ => Cursor.consumed_trans (taken h) consumed⟩)
        | _ => return (.error (ParseError.Internal.new (.syntax (.expected #[.token .parenOpen]))),
            self, state, ⟨next, fun _ => consumed⟩)

end

end BSmtLib.Parser.Category.Combinator
