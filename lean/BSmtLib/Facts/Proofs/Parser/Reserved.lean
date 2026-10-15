module

public import BSmtLib.Facts.Proofs.Parser.Tokens
import all BSmtLib.Parser
import all BSmtLib.Token.Reserved

@[expose] public section

/-!
# Reserved words as the spec spells them

Two reserved words that the spec spells alike are the same word, so a token that stands for a
reserved word of the spec is that word.
-/

namespace BSmtLib.Facts.Proofs.Parser.Reserved

open BSmtLib.Facts.Parser.Adapters.Bridge BSmtLib.Facts.Proofs.Parser.Tokens

theorem decodeReserved_reserved (r : Token.Reserved) : decodeReserved
    (Bridge.reserved r) = some r := by
  cases r with
  | general w => cases w <;> rfl
  | commandName w => cases w <;> rfl

theorem Bridge.reserved_injective {r r' : Token.Reserved}
    (h : Bridge.reserved r = Bridge.reserved r') :
    r = r' := by
  have := decodeReserved_reserved r
  rw [h, decodeReserved_reserved] at this
  exact (Option.some.inj this).symm

/-- A token that stands for a reserved word is that word. -/
theorem Parser.Internal.Input.received_word {token : Parser.Internal.Input} {word : Token.Reserved}
    (h : Bridge.received token = some (.token (.reserved (Bridge.reserved word)))) :
    token = .reserved word := by
  obtain ⟨reserved, rfl, hreserved⟩ := Parser.Internal.Input.received_reserved h
  rw [Bridge.reserved_injective hreserved]

@[simp]
theorem Parser.Internal.Input.isWord_general (word : Token.Reserved.GeneralReserved) :
    (Parser.Internal.Input.reserved (.general word)).isWord word = true := by
  cases word <;> rfl

end BSmtLib.Facts.Proofs.Parser.Reserved
