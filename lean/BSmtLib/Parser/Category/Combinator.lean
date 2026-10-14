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
def step (init : σ) (inner : σ → Input → PM H (Step σ ρ)) (maximum : Option Nat)
    (self : ListState σ ρ) (token : Input) : PM H (Step (ListState σ ρ) (Array ρ)) := do
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

end BSmtLib.Parser.Category.Combinator
