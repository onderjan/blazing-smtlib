module

public import BSmtLib.Facts.Proofs.Lexer.WRustPortX1BatchInCore.Api
import all BSmtLib.Lexer.Internal.WRustPort

@[expose] public section

/-!
# The constructed lexers

A lexer corresponds to itself as constructed (`new_rel`, `newRecovering_rel`), as the two lexers
have the same constructors.
-/

namespace BSmtLib.Facts.Proofs.Lexer.WRustPortX1BatchInCore.Handed

open BSmtLib.Facts.Proofs.Lexer.Simulation.Batch
open BSmtLib.Facts.Proofs.Lexer.WRustPortX1BatchInCore.Calls

/-- The fields of two lexer states as constructed correspond. -/
theorem coreRel_new (version : Token.Version) (recovers : Bool) :
    Core.CoreRel
      { version, initialVersion := version, state := .normal, discardedFrom := none,
        holding := false, recovers, consumedDepth := 0, lexedDepth := 0, recoveryState := none,
        tokenStart := Span.Location.initial, tokenContent := Lexer.Helpers.ContentBuffer.empty,
            offset := 0,
        base := 0, line := 0, lineStart := 0, batch := Token.TokenBatch.empty Lexer.BATCH_CAPACITY,
        tokenStarted := .inl rfl, batchEnded := Nat.zero_le _ }
      { version, initialVersion := version, state := .normal, discardedFrom := none,
        holding := false, recovers, consumedDepth := 0, lexedDepth := 0, recoveryState := none,
        tokenStart := Span.Location.initial, tokenContent := Lexer.Helpers.ContentBuffer.empty,
            offset := 0,
        base := 0, line := 0, lineStart := 0, batch := Token.TokenBatch.empty Lexer.BATCH_CAPACITY,
        tokenStarted := .inl rfl, batchEnded := Nat.zero_le _ } where
  initialVersion := rfl
  state := rfl
  discardedFrom := rfl
  holding := rfl
  recovers := rfl
  consumedDepth := rfl
  lexedDepth := rfl
  recoveryState := rfl
  tokenStart := rfl
  tokenContent := rfl
  offset := rfl
  base := rfl
  line := rfl
  lineStart := rfl
  version := rfl
  batch := agree_of_len_zero rfl rfl
  capacity := Core.zero_lt_capacity

theorem new_rel {H R E : Type} [Token.Consume H R E] (consumer : H) (version : Token.Version) :
    LexRel (Lexer.Internal.WRustPort.Lexer.new consumer version)
      (Lexer.Internal.WRustPort.Lexer.new consumer version) :=
  ⟨rfl, ⟨coreRel_new version false, rfl⟩, rfl⟩

theorem newRecovering_rel {H R E : Type} [Token.Consume H R E] {m : Type → Type} [Token.Recover H m]
    (consumer : H) (version : Token.Version) :
    LexRel (Lexer.Internal.WRustPort.Lexer.newRecovering (m := m) consumer version)
      (Lexer.Internal.WRustPort.Lexer.newRecovering (m := m) consumer version) :=
  ⟨rfl, ⟨coreRel_new version true, rfl⟩, rfl⟩

end BSmtLib.Facts.Proofs.Lexer.WRustPortX1BatchInCore.Handed
