import BSmtLib.Proofs.WRustPortX1BatchInCore.Api
import BSmtLib.Proofs.WRustPortX1BatchInCore.Collector

/-!
# The constructed lexers

A lexer corresponds to itself as constructed (`new_rel`, `newRecovering_rel`), as the two lexers
have the same constructors.
-/

namespace BSmtLib.Proofs.WRustPortX1BatchInCore

open BSmtLib.Proofs.Adapter
open BSmtLib.Proofs.Simulation

theorem new_rel {H : Type} (consumer : H) (version : Version) :
    LexRel (Lexer.WRustPort.Lexer.new consumer version)
      (Lexer.WRustPort.Lexer.new consumer version) :=
  ⟨rfl, { initialVersion := rfl, state := rfl, discard := rfl, recovers := rfl
          consumedDepth := rfl, lexedDepth := rfl, recoveryState := rfl, tokenStart := rfl
          tokenContent := rfl, offset := rfl, base := rfl, line := rfl, lineStart := rfl
          version := rfl, batch := agree_of_len_zero rfl rfl, capacity := zero_lt_capacity }, rfl⟩

theorem newRecovering_rel {H : Type} {m : Type → Type} [Recover H m] (consumer : H)
    (version : Version) :
    LexRel (Lexer.WRustPort.Lexer.newRecovering (m := m) consumer version)
      (Lexer.WRustPort.Lexer.newRecovering (m := m) consumer version) :=
  ⟨rfl, { initialVersion := rfl, state := rfl, discard := rfl, recovers := rfl
          consumedDepth := rfl, lexedDepth := rfl, recoveryState := rfl, tokenStart := rfl
          tokenContent := rfl, offset := rfl, base := rfl, line := rfl, lineStart := rfl
          version := rfl, batch := agree_of_len_zero rfl rfl, capacity := zero_lt_capacity }, rfl⟩

end BSmtLib.Proofs.WRustPortX1BatchInCore
