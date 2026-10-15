module

public import BSmtLib.Parser.Category.Sort
public import BSmtLib.Parser.Category.Token

public section

/-!
# Qualified identifiers

The parser of a qualified identifier: an identifier, or one qualified by its sort with `as`.
-/

namespace BSmtLib.Parser.Category.QualifiedIdent

open BSmtLib.Nodes BSmtLib.Traits BSmtLib.Parser.Category.Token BSmtLib.Parser.Category.Ident
    BSmtLib.Parser.Category.Sort
open BSmtLib.Token (Version)

/-- The state of the qualified identifier parser. -/
inductive QualIdentState (HandledSort : Type) where
  | start
  /-- After its `(`: `_` or `as` follows. -/
  | opened
  /-- Reading an indexed identifier, unqualified. -/
  | indexed (ident : IdentState)
  /-- After `(` `as`, reading the identifier. -/
  | qualifiedIdent (ident : IdentState)
  /-- After the identifier of `(as`, reading its sort. -/
  | sort (identifier : Identifier) (sort : SortState HandledSort)
  /-- After the sort, before the `)`. -/
  | close (identifier : Identifier) (sort : HandledSort)

section

variable {H : Type} {m : Type → Type} [Monad m] [Handler H m]

/--
A step of the qualified identifier parser: ⟨identifier⟩ | `(` `as` ⟨identifier⟩ ⟨sort⟩ `)`. Its
sort is handled at the sort's last token; the identifier is not handled.
-/
def qualIdentStep (version : Version) (self : QualIdentState (Handler.«Sort» H))
    (token : Internal.Input) :
    PM H (Internal.Step (QualIdentState (Handler.«Sort» H)) (Identifier × Option
        (Handler.«Sort» H))) := do
  match self with
  | .start =>
    match token with
    | .symbol symbol => return .done (⟨symbol, #[]⟩, none)
    | .parenOpen => return .more .opened
    | _ => syntaxError .expectedIdent
  | .opened =>
    if token.isWord .underscore then return .more (.indexed .afterUnderscore)
    else if token.isWord .as then return .more (.qualifiedIdent .start)
    else syntaxError .expectedUnderscoreOrAs
  | .indexed ident =>
    match ← ident.step version token with
    | .more ident => return .more (.indexed ident)
    | .done identifier => return .done (identifier, none)
  | .qualifiedIdent ident =>
    match ← ident.step version token with
    | .more ident => return .more (.qualifiedIdent ident)
    | .done identifier => return .more (.sort identifier .init)
  | .sort identifier sort =>
    match ← sortStep version sort token with
    | .more sort => return .more (.sort identifier sort)
    | .done sort => return .more (.close identifier sort)
  | .close identifier sort =>
    expectClose token
    return .done (identifier, some sort)

end

end BSmtLib.Parser.Category.QualifiedIdent
