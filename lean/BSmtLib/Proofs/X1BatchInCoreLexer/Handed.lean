import BSmtLib.Proofs.X1BatchInCoreLexer.Top
import BSmtLib.Proofs.X1BatchInCoreLexer.Chunks

/-!
# The constructed lexers

The lexer with the batch kept in its state is constructed as the library's lexer is, with its
state mapped (`new_eq`, `newRecovering_eq`), so the constructed lexers are related
(`lexerRel_new`, `lexerRel_newRecovering`). The slice of the bytes of a list shorter than
`USize.size` ends below it (`stop_toByteSlice_lt`).
-/

namespace BSmtLib.Proofs.X1BatchInCoreLexer

open BSmtLib.Lexer.Internal (handler core ofParts)

theorem new_eq {H R E : Type} [Consume H R E] (consumer : H) (version : Version) :
    Lexer.WRustPort.Lexer.new consumer version =
      { handler := handler (BSmtLib.Lexer.new consumer version)
        core := coreMap 0 (core (BSmtLib.Lexer.new consumer version))
        held := BSmtLib.Lexer.Internal.held (BSmtLib.Lexer.new consumer version) } :=
  rfl

theorem newRecovering_eq {H R E : Type} [Consume H R E] {m : Type → Type} [Recover H m]
    (consumer : H) (version : Version) :
    Lexer.WRustPort.Lexer.newRecovering (m := m) consumer version =
      { handler := handler (BSmtLib.Lexer.newRecovering (m := m) consumer version)
        core := coreMap 0 (core (BSmtLib.Lexer.newRecovering (m := m) consumer version))
        held := BSmtLib.Lexer.Internal.held
          (BSmtLib.Lexer.newRecovering (m := m) consumer version) } :=
  rfl

theorem lexerRel_new {H R E : Type} [Consume H R E] (consumer : H) (version : Version) :
    LexerRel (BSmtLib.Lexer.new consumer version) (Lexer.WRustPort.Lexer.new consumer version) :=
  ⟨rfl, rel_coreMap 0 _, rfl⟩

theorem lexerRel_newRecovering {H R E : Type} [Consume H R E] {m : Type → Type} [Recover H m]
    (consumer : H) (version : Version) :
    LexerRel (BSmtLib.Lexer.newRecovering (m := m) consumer version)
      (Lexer.WRustPort.Lexer.newRecovering (m := m) consumer version) :=
  ⟨rfl, rel_coreMap 0 _, rfl⟩

/-- The slice of the bytes of a list of characters ends below `USize.size` if the list is that
short. -/
theorem stop_toByteSlice_lt {s : BSmtLibSpec.Regex.Chars} (h : s.length < USize.size) :
    (s.toByteArray.toByteSlice).stop < USize.size := by
  unfold ByteArray.toByteSlice
  simp only [Nat.le_refl, dite_true, Nat.zero_le]
  show s.toByteArray.size < USize.size
  rw [List.size_toByteArray]
  exact h

end BSmtLib.Proofs.X1BatchInCoreLexer
