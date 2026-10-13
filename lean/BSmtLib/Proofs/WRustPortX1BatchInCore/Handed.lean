import BSmtLib.Proofs.WRustPortX1BatchInCore.Api

/-!
# The constructed lexers

A lexer corresponds to itself as constructed (`new_rel`, `newRecovering_rel`), as the two lexers
have the same constructors.
-/

namespace BSmtLib.Proofs.WRustPortX1BatchInCore

open BSmtLib.Proofs.Simulation

/-- The fields of two lexer states as constructed correspond. -/
theorem coreRel_new (version : Version) (recovers : Bool) :
    CoreRel
      { version, initialVersion := version, state := .normal, discardedFrom := none,
        holding := false, recovers, consumedDepth := 0, lexedDepth := 0, recoveryState := none,
        tokenStart := Location.initial, tokenContent := Lexer.ContentBuffer.empty, offset := 0,
        base := 0, line := 0, lineStart := 0, batch := TokenBatch.empty Lexer.BATCH_CAPACITY,
        tokenStarted := .inl rfl, batchEnded := Nat.zero_le _ }
      { version, initialVersion := version, state := .normal, discardedFrom := none,
        holding := false, recovers, consumedDepth := 0, lexedDepth := 0, recoveryState := none,
        tokenStart := Location.initial, tokenContent := Lexer.ContentBuffer.empty, offset := 0,
        base := 0, line := 0, lineStart := 0, batch := TokenBatch.empty Lexer.BATCH_CAPACITY,
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
  capacity := zero_lt_capacity

theorem new_rel {H R E : Type} [Consume H R E] (consumer : H) (version : Version) :
    LexRel (Lexer.WRustPort.Lexer.new consumer version)
      (Lexer.WRustPort.Lexer.new consumer version) :=
  ⟨rfl, ⟨coreRel_new version false, rfl⟩, rfl⟩

theorem newRecovering_rel {H R E : Type} [Consume H R E] {m : Type → Type} [Recover H m]
    (consumer : H) (version : Version) :
    LexRel (Lexer.WRustPort.Lexer.newRecovering (m := m) consumer version)
      (Lexer.WRustPort.Lexer.newRecovering (m := m) consumer version) :=
  ⟨rfl, ⟨coreRel_new version true, rfl⟩, rfl⟩

end BSmtLib.Proofs.WRustPortX1BatchInCore
