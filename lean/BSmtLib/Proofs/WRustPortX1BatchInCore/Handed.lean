import BSmtLib.Proofs.WRustPortX1BatchInCore.Api
import BSmtLib.Proofs.WRustPortX1BatchInCore.Collector

/-!
# The constructed lexers, and what the adapter records

A lexer corresponds to itself as constructed (`new_rel`, `newRecovering_rel`), as the two lexers
have the same constructors; fed the same slices, with the adapter's consumer, lexers that
correspond record the same tokens (`feed_eq`, `handed_eq`).
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

/-- Lexers that correspond, fed the same slices and then the end of the input with the adapter's
consumer, record the same tokens. -/
theorem feed_eq (slices : List Spec.Lexicon.Chars) :
    ∀ (a : WRustPort.ops.Lexer) (b : X1BatchInCore.ops.Lexer), LexRel a b →
      feedAll WRustPort.ops a slices = feedAll X1BatchInCore.ops b slices := by
  induction slices with
  | nil =>
    intro a b h
    obtain ⟨y, h1, h2⟩ := lexEof_couple collector_consumesAlike a b h
    have e1 : WRustPort.ops.lexEof a = y.val.1 := h1
    have e2 : X1BatchInCore.ops.lexEof b = y.val.2 := h2
    rw [feedAll, feedAll, e1, e2]
    obtain ⟨⟨r, r'⟩, hr⟩ := y
    dsimp only
    rcases r with ⟨e, x⟩ | ⟨f, l⟩ <;> rcases r' with ⟨e', x'⟩ | ⟨g, l'⟩
    · rfl
    · exact hr.elim
    · exact hr.elim
    · obtain ⟨e, hl⟩ := hr
      subst e
      cases f with
      | «continue» => exact congrArg (some ·.handed) hl.1
      | «break» fin => exact fin.value.elim
  | cons slice slices ih =>
    intro a b h
    obtain ⟨y, h1, h2⟩ := lexSlice_couple collector_consumesAlike a b h
      slice.toByteArray.toByteSlice
    have e1 : WRustPort.ops.lexSlice a slice.toByteArray.toByteSlice = y.val.1 := h1
    have e2 : X1BatchInCore.ops.lexSlice b slice.toByteArray.toByteSlice = y.val.2 := h2
    rw [feedAll, feedAll, e1, e2]
    obtain ⟨⟨r, r'⟩, hr⟩ := y
    dsimp only
    rcases r with ⟨e, x⟩ | ⟨f, l⟩ <;> rcases r' with ⟨e', x'⟩ | ⟨g, l'⟩
    · rfl
    · exact hr.elim
    · exact hr.elim
    · obtain ⟨e, hl⟩ := hr
      subst e
      cases f with
      | «continue» => exact ih l l' hl
      | «break» fin => exact fin.value.elim

/-- The two lexers, run by the adapter, hand over the same tokens. -/
theorem handed_eq (version : Spec.Lexicon.Version) (slices : List Spec.Lexicon.Chars) :
    handed WRustPort.ops version slices = handed X1BatchInCore.ops version slices :=
  feed_eq slices _ _ (new_rel _ _)

end BSmtLib.Proofs.WRustPortX1BatchInCore
