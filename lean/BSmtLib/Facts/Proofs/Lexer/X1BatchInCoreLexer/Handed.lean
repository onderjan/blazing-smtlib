module

public import BSmtLib.Facts.Proofs.Lexer.X1BatchInCoreLexer.Top
public import BSmtLib.Facts.Proofs.Lexer.X1BatchInCoreLexer.Chunks
import all BSmtLib.Lexer
import all BSmtLib.Lexer.Internal.WRustPort

@[expose] public section

/-!
# The constructed lexers

The lexer with the batch kept in its state is constructed as the library's lexer is, with its
state mapped (`new_eq`, `newRecovering_eq`), so the constructed lexers are related
(`lexerRel_new`, `lexerRel_newRecovering`). The slice of the bytes of a list shorter than
`USize.size` ends below it (`stop_toByteSlice_lt`).
-/

namespace BSmtLib.Facts.Proofs.Lexer.X1BatchInCoreLexer.Handed

open BSmtLib.Facts.Proofs.Lexer.X1BatchInCoreLexer.Core
open BSmtLib.Facts.Proofs.Lexer.X1BatchInCoreLexer.Outer
open BSmtLib.Facts.Proofs.Lexer.X1BatchInCoreLexer.Top

theorem new_eq {H R E : Type} [Token.Consume H R E] (consumer : H) (version : Version) :
    Lexer.Internal.WRustPort.Lexer.new consumer version =
      { handler := BSmtLib.Lexer.Internal.handler (BSmtLib.Lexer.new consumer version)
        core := coreMap 0 (BSmtLib.Lexer.Internal.core (BSmtLib.Lexer.new consumer version))
        held := BSmtLib.Lexer.Internal.held (BSmtLib.Lexer.new consumer version) } :=
  (rfl)

theorem newRecovering_eq {H R E : Type} [Token.Consume H R E] {m : Type → Type} [Lexer.Recovery.Recover H m]
    (consumer : H) (version : Version) :
    Lexer.Internal.WRustPort.Lexer.newRecovering (m := m) consumer version =
      { handler := BSmtLib.Lexer.Internal.handler (BSmtLib.Lexer.newRecovering
          (m := m) consumer version)
        core := coreMap 0 (BSmtLib.Lexer.Internal.core
            (BSmtLib.Lexer.newRecovering (m := m) consumer version))
        held := BSmtLib.Lexer.Internal.held
          (BSmtLib.Lexer.newRecovering (m := m) consumer version) } :=
  (rfl)

theorem lexerRel_new {H R E : Type} [Token.Consume H R E] (consumer : H) (version : Version) :
    LexerRel (BSmtLib.Lexer.new consumer version) (Lexer.Internal.WRustPort.Lexer.new consumer
        version) :=
  ⟨rfl, rel_coreMap 0 _, rfl⟩

theorem lexerRel_newRecovering {H R E : Type} [Token.Consume H R E]
    {m : Type → Type} [Lexer.Recovery.Recover H m]
    (consumer : H) (version : Version) :
    LexerRel (BSmtLib.Lexer.newRecovering (m := m) consumer version)
      (Lexer.Internal.WRustPort.Lexer.newRecovering (m := m) consumer version) :=
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

end BSmtLib.Facts.Proofs.Lexer.X1BatchInCoreLexer.Handed
