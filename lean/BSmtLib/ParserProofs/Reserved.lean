import BSmtLib.ParserProofs.Tokens

/-!
# Reserved words as the spec spells them

Two reserved words that the spec spells alike are the same word, so a token that stands for a
reserved word of the spec is that word.
-/

namespace BSmtLib.ParserProofs

open BSmtLib.Spec.Grammar
open BSmtLib.Parser (Input)

theorem decodeReserved_reserved (r : Reserved) : decodeReserved (Bridge.reserved r) = some r := by
  cases r with
  | general w => cases w <;> rfl
  | commandName w => cases w <;> rfl

theorem Bridge.reserved_injective {r r' : Reserved} (h : Bridge.reserved r = Bridge.reserved r') :
    r = r' := by
  have := decodeReserved_reserved r
  rw [h, decodeReserved_reserved] at this
  exact (Option.some.inj this).symm

/-- A token that stands for a reserved word is that word. -/
theorem Input.received_word {token : Input} {word : Reserved}
    (h : Bridge.received token = some (.token (.reserved (Bridge.reserved word)))) :
    token = .reserved word := by
  obtain ⟨reserved, rfl, hreserved⟩ := Input.received_reserved h
  rw [Bridge.reserved_injective hreserved]

@[simp]
theorem Input.isWord_general (word : GeneralReserved) :
    (Input.reserved (.general word)).isWord word = true := by
  cases word <;> rfl

end BSmtLib.ParserProofs
