module

public import BSmtLib.Facts.Parser.Adapters.Run

@[expose] public section

/-!
# A cursor against a list of tokens

A parser of the library parses a cursor, an instance of `Token.Produce`; what it does is stated
against the tokens the cursor gives, as the parser takes them (`Parser.Internal.Input`).

- `Takes version cursor tokens next`: taking the tokens one by one from `cursor`, each in the
  version, leaves `next`. `Reads version cursor tokens`: the cursor gives exactly the tokens, each
  in the version.
- `noPoints`: the token points that mark nothing, as a parse of a cursor marks no point: the spec's
  traversal with them is its handler calls alone.

What a parser does on such a cursor is in `Adapters.Outcome`.

These definitions are adapters: the root theorems of `BSmtLib.Facts.Parser` about the category
parsers and the combinators are stated with them, so they are trusted, and are to be read with the
spec.
-/

namespace BSmtLib.Facts.Parser.Adapters.Cursor

open BSmtLib.Token (Produce)

section

variable {Z : Type} [Produce Z]

/--
`Takes version cursor tokens next`: the cursor has the tokens first, each viewed in the version
in force after it is taken, which is `version`, and taking them leaves `next`.
-/
inductive Takes (version : Token.Version) : Z → List Parser.Internal.Input → Z → Prop where
  | nil (cursor : Z) : Takes version cursor [] cursor
  | cons {cursor after next : Z} {token : Produce.Token Z} {consumed : Produce.Consumed after cursor}
      {tokens : List Parser.Internal.Input} :
      Produce.HasNext cursor → Produce.next? cursor = some (token, ⟨after, consumed⟩) →
      Produce.version after = version → Takes version after tokens next →
      Takes version cursor (Parser.Internal.Input.ofSyntax (Produce.syntax after token) :: tokens)
        next

/-- The cursor gives exactly the tokens, each in the version. -/
def Reads (version : Token.Version) (cursor : Z) (tokens : List Parser.Internal.Input) : Prop :=
  ∃ last, Takes version cursor tokens last ∧ Produce.next? last = none

end

/-- The token points that mark nothing. -/
def noPoints {m : Type → Type} [Monad m] : BSmtLibSpec.Parser.Traversal.Points m :=
  ⟨fun _ => pure (), fun _ => pure ()⟩

end BSmtLib.Facts.Parser.Adapters.Cursor
