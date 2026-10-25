module

public import BSmtLib.Facts.Proofs.PublicApi.Lexing
import all BSmtLib.Lexer.Internal.VNaive
import all BSmtLib.Span

@[expose] public section

/-!
# The naive lexer's pure run, with whitespace and comments, tiles its input

With whitespace and comments taken, every byte is in a lexeme: the lexemes of the pure run
follow each other without a gap from where it starts to where the token in progress starts, or
to where it is idle (`front`) (`lexBytesF_tiles`). Where the run fails, they reach at most to
where the failure's span starts. At the end of the input the token in progress and the
end-of-file token close the tiling at the end of the input (`stream_tiles`).
-/

namespace BSmtLib.Facts.Proofs.PublicApi.Tiling

open BSmtLib.Facts.PublicApi.Adapters
open BSmtLib.Facts.Proofs.PublicApi.Lexing
open BSmtLib.Facts.Proofs.Lexer.Consumers.Pure BSmtLib.Facts.Proofs.Lexer.Consumers.Stream
open BSmtLib.Facts.Proofs.Lexer.VNaive.Facts BSmtLib.Facts.Proofs.Lexer.VNaive.Prefix
open BSmtLib.Facts.Proofs.Lexer.VNaive.Run
open BSmtLib.Lexer.Internal.VNaive

theorem tiles_append : ∀ (a b : List Entry) (s e : Nat),
    Tiles (a ++ b) s e ↔ ∃ m, Tiles a s m ∧ Tiles b m e
  | [], b, s, e => by
    simp only [List.nil_append, Tiles]
    exact ⟨fun h => ⟨s, rfl, h⟩, fun ⟨m, h1, h2⟩ => h1 ▸ h2⟩
  | (c, f, l) :: a, b, s, e => by
    simp only [List.cons_append, Tiles]
    rw [tiles_append a b l e]
    exact ⟨fun ⟨h1, m, h2, h3⟩ => ⟨m, ⟨h1, h2⟩, h3⟩, fun ⟨m, ⟨h1, h2⟩, h3⟩ => ⟨h1, m, h2, h3⟩⟩

theorem tiles_trans {a b : List Entry} {s m e : Nat} (h₁ : Tiles a s m) (h₂ : Tiles b m e) :
    Tiles (a ++ b) s e :=
  (tiles_append a b s e).mpr ⟨m, h₁, h₂⟩

theorem tiles_one (l : Lexeme) : Tiles [lexEntry l] l.start.offset l.end.offset :=
  ⟨rfl, rfl⟩

/-- Where the lexemes of a run reach: where the token in progress starts, or where the run is
idle. -/
def front : St → Span.Location → Nat
  | .idle, location => location.offset
  | .token p, _ => p.start.offset

theorem start_ne_idle (v : Version) (location : Span.Location) (c : UInt8) :
    start v true location c ≠ .idle := by
  intro h
  simp only [start] at h
  repeat' split at h
  all_goals (cases h <;> simp_all)

theorem advance_ne_idle (p : Pending) (location : Span.Location) (c : UInt8) :
    advance true p location c ≠ .idle := by
  intro h
  simp only [advance, legacyStringByte] at h
  repeat' split at h
  all_goals (cases h <;> simp_all)

theorem finish_ne_none (p : Pending) (location : Span.Location) :
    finish true p location ≠ .none := by
  intro h
  simp only [finish] at h
  repeat' split at h
  all_goals (cases h <;> simp_all)

theorem start_error_start {v : Version} {ws : Bool} {location : Span.Location} {c : UInt8}
    {f : LexFailure} (h : start v ws location c = .error f) :
    f.span.start.offset = location.offset := by
  simp only [start] at h
  repeat' split at h
  all_goals cases h
  rfl

theorem advance_error_start {ws : Bool} {p : Pending} {location : Span.Location} {c : UInt8}
    {f : LexFailure} (h : advance ws p location c = .error f) :
    f.span.start.offset = p.start.offset := by
  simp only [advance, legacyStringByte] at h
  repeat' split at h
  all_goals first | (cases h; rfl) | cases h

theorem finish_error_start {ws : Bool} {p : Pending} {location : Span.Location}
    {f : LexFailure} (h : finish ws p location = .error f) :
    f.span.start.offset = p.start.offset := by
  simp only [finish] at h
  repeat' split at h
  all_goals first | (cases h; rfl) | cases h

/-- A step from no token in progress tiles from where it starts. -/
theorem startStep_tiles {v : Version} {location : Span.Location} {c : UInt8} {st' : St}
    {ls : List Lexeme} (h : startStepW v true location c = some (st', ls)) :
    Tiles (ls.map lexEntry) location.offset (front st' (location.afterByte c)) := by
  unfold startStepW at h
  cases hs : start v true location c with
  | idle => exact absurd hs (start_ne_idle v location c)
  | pending q =>
    rw [hs] at h
    cases h
    exact (congrArg Span.Location.offset (start_pending hs)).symm
  | token l =>
    rw [hs] at h
    cases h
    obtain ⟨h1, h2⟩ := start_token_span hs
    exact ⟨by rw [h1], by rw [h2]; rfl⟩
  | error f => rw [hs] at h; cases h

/-- A step of the pure run tiles from its front to the next one. -/
theorem byteStep_tiles {v : Version} {st st' : St} {location : Span.Location} {c : UInt8}
    {ls : List Lexeme} (h : byteStepW v true st location c = some (st', ls)) :
    Tiles (ls.map lexEntry) (front st location) (front st' (location.afterByte c)) := by
  cases st with
  | idle => exact startStep_tiles h
  | token p =>
    simp only [byteStepW] at h
    cases ha : advance true p location c with
    | pending q =>
      rw [ha] at h
      cases h
      exact (congrArg Span.Location.offset (advance_pending ha)).symm
    | idle => exact absurd ha (advance_ne_idle p location c)
    | tokenWith l =>
      rw [ha] at h
      cases h
      obtain ⟨h1, h2⟩ := advance_tokenWith ha
      exact ⟨by rw [h1]; rfl, by rw [h2]; rfl⟩
    | tokenBefore l =>
      rw [ha] at h
      obtain ⟨⟨st'', ls''⟩, hs, he⟩ := Option.map_eq_some_iff.mp h
      cases he
      obtain ⟨h1, h2⟩ := advance_tokenBefore ha
      have := startStep_tiles hs
      rw [List.map_cons, show lexEntry l :: ls''.map lexEntry = [lexEntry l] ++ ls''.map lexEntry
        from rfl]
      refine tiles_trans (m := location.offset) ⟨by rw [h1]; rfl, by rw [h2]; rfl⟩ this
    | error f => rw [ha] at h; cases h

/-- Where a step fails, the lexemes it finishes before tile from its front up to where the
failure's span starts, at most. -/
theorem byteStep_fail_tiles {v : Version} {st : St} {location : Span.Location} {c : UInt8}
    (h : byteStepW v true st location c = none) :
    ∃ X, Tiles ((failedBeforeW true st location c).map lexEntry) (front st location) X ∧
      X ≤ (failW v true st location c).span.start.offset := by
  cases st with
  | idle =>
    simp only [byteStepW, startStepW] at h
    cases hs : start v true location c with
    | error f =>
      refine ⟨location.offset, rfl, ?_⟩
      simp only [failW, startFail, hs]
      exact Nat.le_of_eq (start_error_start hs).symm
    | idle => rw [hs] at h; cases h
    | pending _ => rw [hs] at h; cases h
    | token _ => rw [hs] at h; cases h
  | token p =>
    simp only [byteStepW] at h
    cases ha : advance true p location c with
    | error f =>
      refine ⟨p.start.offset, ?_, ?_⟩
      · simp only [failedBeforeW, ha]; rfl
      · simp only [failW, ha]
        exact Nat.le_of_eq (advance_error_start ha).symm
    | tokenBefore l =>
      rw [ha] at h
      have hs : startStepW v true location c = none := by
        cases hs : startStepW v true location c with
        | none => rfl
        | some r => rw [hs] at h; cases h
      cases hst : start v true location c with
      | error f =>
        obtain ⟨h1, h2⟩ := advance_tokenBefore ha
        refine ⟨location.offset, ?_, ?_⟩
        · simp only [failedBeforeW, ha, List.map_cons, List.map_nil]
          exact ⟨by rw [h1]; rfl, by rw [h2]; rfl⟩
        · simp only [failW, ha, startFail, hst]
          exact Nat.le_of_eq (start_error_start hst).symm
      | idle => simp only [startStepW, hst] at hs; cases hs
      | pending _ => simp only [startStepW, hst] at hs; cases hs
      | token _ => simp only [startStepW, hst] at hs; cases hs
    | pending _ => rw [ha] at h; cases h
    | idle => rw [ha] at h; cases h
    | tokenWith _ => rw [ha] at h; cases h

theorem advanceLoc_cons (location : Span.Location) (c : UInt8) (cs : List UInt8) :
    advanceLoc location (c :: cs) = advanceLoc (location.afterByte c) cs := rfl

/-- The pure run with whitespace and comments tiles from its front: to the front where it ends,
at the location after the bytes, or up to where its failure's span starts, at most. -/
theorem lexBytesF_tiles (v : Version) : ∀ (bs : List UInt8) (st : St)
    (location : Span.Location),
    match lexBytesF v true st location bs with
    | .ok (st', location', ls) =>
      Tiles (ls.map lexEntry) (front st location) (front st' location') ∧
        location' = advanceLoc location bs
    | .error (ls, f) =>
      ∃ X, Tiles (ls.map lexEntry) (front st location) X ∧ X ≤ f.span.start.offset
  | [], st, location => ⟨rfl, rfl⟩
  | c :: cs, st, location => by
    simp only [lexBytesF]
    cases hb : byteStepW v true st location c with
    | none => exact byteStep_fail_tiles hb
    | some r =>
      obtain ⟨st', ls⟩ := r
      have h1 := byteStep_tiles hb
      have ih := lexBytesF_tiles v cs st' (location.afterByte c)
      dsimp only
      revert ih
      cases lexBytesF v true st' (location.afterByte c) cs with
      | ok x =>
        obtain ⟨st'', location'', ls'⟩ := x
        rintro ⟨h2, h3⟩
        refine ⟨?_, by rw [h3]; rfl⟩
        simp only [List.map_append]
        exact tiles_trans h1 h2
      | error x =>
        obtain ⟨ls', f⟩ := x
        rintro ⟨X, h2, h3⟩
        refine ⟨X, ?_, h3⟩
        simp only [List.map_append]
        exact tiles_trans h1 h2

/-- The end of the input after the pure run closes the tiling at the location. -/
theorem endStep_tiles {st : St} {location : Span.Location} {ls : List Lexeme}
    (h : endStepW true st location = some ls) :
    Tiles (ls.map lexEntry) (front st location) location.offset := by
  cases st with
  | idle =>
    simp only [endStepW, Option.some.injEq] at h
    subst h
    exact ⟨rfl, rfl⟩
  | token p =>
    simp only [endStepW] at h
    cases hf : finish true p location with
    | none => exact absurd hf (finish_ne_none p location)
    | token l =>
      rw [hf] at h
      cases h
      obtain ⟨h1, h2⟩ := finish_token hf
      exact ⟨by rw [h1]; rfl, by rw [h2]; rfl, rfl⟩
    | error f => rw [hf] at h; cases h

end BSmtLib.Facts.Proofs.PublicApi.Tiling
