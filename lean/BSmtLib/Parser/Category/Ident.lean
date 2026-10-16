module

public import BSmtLib.Parser

public section

/-!
# Identifiers

The parser of an identifier: a symbol, or an indexed identifier `(` `_` ⟨symbol⟩ ⟨index⟩+ `)`.
-/

namespace BSmtLib.Parser.Category.Ident

open BSmtLib.Plain (Symbol)
open BSmtLib.Nodes BSmtLib.Traits
open BSmtLib.Token (Version)
open BSmtLib.Parser.Internal (PM call syntaxError)

namespace Internal

/-- The state of the identifier parser. -/
inductive IdentState where
  /-- Before the identifier. -/
  | start
  /-- After its `(`, before the `_`. -/
  | opened
  /-- After `(` `_`, before its symbol. -/
  | afterUnderscore
  /-- After its symbol, reading its indices up to the `)`. -/
  | indices (symbol : Symbol) (indices : Array Index)

namespace IdentState

variable {H : Type} {m : Type → Type} [Monad m] [Handler H m]

/--
A step of the identifier parser: a symbol is an identifier by itself; `(` `_` ⟨symbol⟩
⟨index⟩+ `)` an indexed one. A symbol is an index from 2.5 on.
-/
def step (version : Version) (self : IdentState) (token : Internal.Input) :
    PM H (Internal.Step IdentState Ident) :=
  match self, token with
  | .start, .symbol symbol => pure (.done ⟨symbol, #[]⟩)
  | .start, .parenOpen => pure (.more .opened)
  | .start, _ => syntaxError (.expected #[.ident])
  | .opened, token =>
    if token.isWord .underscore then pure (.more .afterUnderscore)
    else syntaxError (.expected #[.reserved (.general .underscore)])
  | .afterUnderscore, .symbol symbol => pure (.more (.indices symbol #[]))
  | .afterUnderscore, _ => syntaxError (.expected #[.symbol])
  | .indices symbol found, .parenClose =>
    if found.isEmpty then syntaxError (.empty .identIndices)
    else pure (.done ⟨symbol, found⟩)
  | .indices symbol found, .constant (.numeral digits) =>
    pure (.more (.indices symbol (found.push (.numeral digits))))
  | .indices symbol found, .symbol index =>
    if version ≥ .v2_5 then pure (.more (.indices symbol (found.push (.symbol index))))
    else syntaxError (.expected #[.index, .token .parenClose])
  | .indices _ _, _ => syntaxError (.expected #[.index, .token .parenClose])

end IdentState

end Internal

/-- The parser of one identifier (`SmtIdentParser`). -/
structure IdentParser where
  private mk ::
  private state : Internal.IdentState

/-- The identifier parser before an identifier. -/
def IdentParser.new : IdentParser := ⟨.start⟩

instance : Inhabited IdentParser := ⟨.new⟩

namespace Internal

/- LEAN: as the parsers of single tokens, the identifier parser names no handler, so its steps
are a definition for each handler. -/
/-- The steps of the identifier parser, with the handler `H`. -/
@[instance_reducible]
def identByToken (H : Type) {m : Type → Type} [Monad m] [Handler H m] :
    Parser.Internal.ParseByToken IdentParser H m (Handler.Error H) IdentBuf where
  arrive _ _ := pure ()
  step version parser token := do
    match ← parser.state.step version token with
    | .more state => return .more ⟨state⟩
    | .done result => return .done result.intoOwned
  reset _ := .new

end Internal

section

variable {H : Type} {m : Type → Type} [Monad m] [Handler H m]

instance : Parse IdentParser H m (Handler.Error H) IdentBuf where
  parse parser state cursor :=
    letI := Internal.identByToken H
    Parser.Internal.parseByToken parser state cursor

end

end BSmtLib.Parser.Category.Ident
