module

public import BSmtLib.Parser.Category.SExpr
public import BSmtLib.Parser.Category.Token

public section

/-!
# Attributes

The parser of an attribute, a keyword with its value if it has one, alone or in a list.
-/

namespace BSmtLib.Parser.Category.Attribute

open BSmtLib.Nodes BSmtLib.Traits BSmtLib.Parser.Category.Token BSmtLib.Parser.Category.SExpr
open BSmtLib.Plain (KeywordView)
open BSmtLib.Token (Version)

/-- What the attribute parser is doing. -/
inductive AttributeMode (HandledSExpr : Type) where
  /-- Before an attribute's keyword, or the `)` after the attributes. -/
  | start
  /-- After an attribute's keyword: its value, the next keyword or the `)` follows. -/
  | afterName (keyword : KeywordView)
  /-- In the list value of an attribute: its items so far, and whether the parser is between
  them. -/
  | inside (keyword : KeywordView) (items : Array HandledSExpr) (sExpr : SExprState HandledSExpr)
      (outside : Bool)

/-- The state of the attribute parser: its mode, and the attributes handled so far. -/
structure AttributeState (HandledSExpr HandledAttribute : Type) where
  mode : AttributeMode HandledSExpr
  attributes : Array HandledAttribute

/-- The attribute parser before the attributes. -/
def AttributeState.init {HandledSExpr HandledAttribute : Type} :
    AttributeState HandledSExpr HandledAttribute :=
  { mode := .start, attributes := #[] }

section

variable {H : Type} {m : Type → Type} [Monad m] [Handler H m]

/--
A step of the attribute parser, for attributes up to the `)` after them; with `single`, for
exactly one. An attribute is handled when the tokens determine it: an attribute with a value
at the value's last token; one without, at the token after its keyword, the next keyword or the
`)`. A list value is handed over as its items.
-/
def attributeStep (single : Bool) (version : Version)
    (self : AttributeState (Handler.SExpr H) (Handler.Attribute H)) (token : Input) :
    PM H (Step (AttributeState (Handler.SExpr H) (Handler.Attribute H))
      (Array (Handler.Attribute H))) := do
  let finish (attributes : Array (Handler.Attribute H)) :
      PM H (Step (AttributeState (Handler.SExpr H) (Handler.Attribute H))
        (Array (Handler.Attribute H))) :=
    if single && attributes.isEmpty then syntaxError .expectedAttribute
    else pure (.done attributes)
  match self.mode with
  | .start =>
    if single && !self.attributes.isEmpty then
      expectClose token
      return ← finish self.attributes
    match token with
    | .parenClose => finish self.attributes
    | .keyword name => return .more { self with mode := .afterName name }
    | _ => syntaxError .expectedAttribute
  | .afterName keyword =>
    let valued (value : AttributeValueNode (Handler.SExpr H)) := do
      let handled ← call (Handler.handleAttribute keyword (some value))
      return .more { mode := .start, attributes := self.attributes.push handled }
    match token with
    | .symbol symbol => valued (.symbol symbol)
    | .constant constant => valued (.constant constant)
    | .parenOpen => return .more { self with mode := .inside keyword #[] [] true }
    | .parenClose =>
      let handled ← call (Handler.handleAttribute keyword none)
      finish (self.attributes.push handled)
    | .keyword name =>
      -- a single attribute is followed by the `)`: reject the keyword before handing over
      if single then syntaxError (.expectedToken #[.parenClose])
      let handled ← call (Handler.handleAttribute keyword none)
      return .more { mode := .afterName name, attributes := self.attributes.push handled }
    | _ => syntaxError .expectedAttribute
  | .inside keyword items sExpr outside =>
    if outside then
      if let .parenClose := token then
        let handled ← call (Handler.handleAttribute keyword (some (.list items)))
        return .more { mode := .start, attributes := self.attributes.push handled }
    match ← sExprStep version sExpr token with
    | .more sExpr => return .more { self with mode := .inside keyword items sExpr false }
    | .done item => return .more { self with mode := .inside keyword (items.push item) [] true }

end

end BSmtLib.Parser.Category.Attribute
