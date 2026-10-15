module

public import BSmtLib.Facts.Proofs.Parser.Canon.Chain
public import BSmtLib.Facts.Proofs.Parser.Canon.Link
import all BSmtLib.Lexer

@[expose] public section

/-!
# A lexer fed an input to its end

`lexThrough` feeds a library's lexer in `Id` the slices by the steps of its call on a slice,
then the end of the input by the step of its call there, as a reader feeds its lexer. Lexers
related through one Rust port's lexer read alike (`lexThrough_zRel`), and so do the lexer with
the parse adapter and the lexer with the canonical adapter from states whose canonicalisations
agree (`lexThrough_link`).
-/

namespace BSmtLib.Facts.Proofs.Parser.Canon.Through

open BSmtLib.Lexer BSmtLib.Lexer.Error
open BSmtLib.Lexer.Internal (BATCH_CAPACITY Stop Interrupted Failure LexerCore InnerM StepM LexM)
open BSmtLib.Facts.PublicApi.Adapters (ByteList)
open BSmtLib.Facts.Proofs.Lexer.Simulation.Batch
open Chain
open BSmtLib.Facts.Proofs.Reader.Param.Basic (ERel)

section

variable {H R E : Type} [Token.Consume H R E] [∀ b, Token.ConsumeFrom H (Token.BatchCursor b) Id]

/-- The result to return at the end of the input: the one held, else the one the consumer broke
with. -/
def eofResultT (held : Option (Span.Located R)) (flow : ControlFlow (Span.Located R)) :
    Option (Span.Located R) :=
  match held, flow with
  | some held, _ => some held
  | none, .break located => some located
  | none, .continue => none

/-- The lexer fed the slices by the step of its call on a slice: the lexer after the last, or the
first error. -/
def lexFeed : BSmtLib.Lexer H → List ByteList → Except (LexError E) (BSmtLib.Lexer H)
  | l, [] => .ok l
  | l, slice :: slices =>
    match Internal.run l (Internal.lexSliceStep (R := R) (E := E) abandonI recoverI
        slice.toByteArray.toByteSlice) with
    | (.ok held, l') => lexFeed (Internal.withHeld l' (held.or (Internal.held l'))) slices
    | (.error e, _) => .error e

/-- The lexer fed the slices and then the end of the input: the result, the lexer before the end
of the input and after it, or the first error. -/
def lexThrough (l : BSmtLib.Lexer H) (slices : List ByteList) :
    Except (LexError E) (Option (Span.Located R) × BSmtLib.Lexer H × BSmtLib.Lexer H) :=
  match lexFeed l slices with
  | .error e => .error e
  | .ok before =>
    match Internal.run before (Internal.lexEofStep (R := R) (E := E) abandonI recoverI) with
    | (.ok flow, l') =>
      .ok (eofResultT (Internal.held l') flow, before, Internal.withHeld l' none)
    | (.error e, _) => .error e

/-- Two reads through to the end that end alike: the same error, or the same result with lexers
related before and after the end of the input. -/
def ThroughRel (Rel : BSmtLib.Lexer H → BSmtLib.Lexer H → Prop) :
    Except (LexError E) (Option (Span.Located R) × BSmtLib.Lexer H × BSmtLib.Lexer H) →
      Except (LexError E) (Option (Span.Located R) × BSmtLib.Lexer H × BSmtLib.Lexer H) → Prop
  | .error e, .error e' => e = e'
  | .ok (r, b, a), .ok (r', b', a') => r = r' ∧ Rel b b' ∧ Rel a a'
  | _, _ => False

variable (hcons : ConsumesAlike H Id R E)
include hcons

theorem lexFeed_zRel : ∀ (slices : List ByteList) {l₁ l₂ : BSmtLib.Lexer H}, ZRelG l₁ l₂ →
    ERel (· = ·) ZRelG (lexFeed (R := R) (E := E) l₁ slices) (lexFeed l₂ slices)
  | [], l₁, l₂, h => h
  | slice :: slices, l₁, l₂, h => by
    obtain ⟨e1, hz⟩ := step_slice hcons h slice.toByteArray.toByteSlice
    simp only [lexFeed]
    generalize Internal.run l₁ (Internal.lexSliceStep (R := R) (E := E) abandonI recoverI
      slice.toByteArray.toByteSlice) = A at e1 hz ⊢
    generalize Internal.run l₂ (Internal.lexSliceStep (R := R) (E := E) abandonI recoverI
      slice.toByteArray.toByteSlice) = B at e1 hz ⊢
    obtain ⟨r₁, l₁'⟩ := A
    obtain ⟨r₂, l₂'⟩ := B
    dsimp only at e1 hz ⊢
    subst e1
    cases r₁ with
    | ok held =>
      have hz' : ZRelG (Internal.withHeld l₁' (held.or (Internal.held l₁')))
          (Internal.withHeld l₂' (held.or (Internal.held l₂'))) := by
        rw [← hz.held]
        exact hz.withHeld _
      exact lexFeed_zRel slices hz'
    | error e => exact (rfl : e = e)

theorem lexThrough_zRel (slices : List ByteList) {l₁ l₂ : BSmtLib.Lexer H} (h : ZRelG l₁ l₂) :
    ThroughRel ZRelG (lexThrough (R := R) (E := E) l₁ slices) (lexThrough l₂ slices) := by
  have hf := lexFeed_zRel hcons slices h
  unfold lexThrough
  generalize lexFeed (R := R) (E := E) l₁ slices = F₁ at hf ⊢
  generalize lexFeed (R := R) (E := E) l₂ slices = F₂ at hf ⊢
  rcases F₁ with e₁ | b₁ <;> rcases F₂ with e₂ | b₂ <;> simp only [ERel] at hf
  · subst hf; exact (rfl : e₁ = e₁)
  · obtain ⟨e1, hz⟩ := step_eof hcons hf
    dsimp only
    generalize Internal.run b₁ (Internal.lexEofStep (R := R) (E := E) abandonI recoverI) = A
      at e1 hz ⊢
    generalize Internal.run b₂ (Internal.lexEofStep (R := R) (E := E) abandonI recoverI) = B
      at e1 hz ⊢
    obtain ⟨r₁, l₁'⟩ := A
    obtain ⟨r₂, l₂'⟩ := B
    dsimp only at e1 hz ⊢
    subst e1
    cases r₁ with
    | ok flow =>
      refine ⟨?_, hf, hz.withHeld none⟩
      rw [hz.held]
    | error e => exact (rfl : e = e)

end

/-! ## The parse adapter and the canonical adapter -/

section

open BSmtLib.Parser
open BSmtLib.Facts.Reader.Adapters (RecAdapter)
open BSmtLib.Facts.Proofs.Reader.Param.Basic BSmtLib.Facts.Proofs.Reader.Param.Calls
open BSmtLib.Facts.Proofs.Parser.Canon.Adapter BSmtLib.Facts.Proofs.Parser.Canon.Canonical
open BSmtLib.Facts.Proofs.Parser.Canon.Link

/-- A lexer with the parse adapter and one with the canonical adapter between calls: the same
fields and held result, and the parse adapter's state canonicalised in the other. -/
def LinkRel (l₁ : BSmtLib.Lexer RecAdapter) (l₂ : BSmtLib.Lexer CanonAdapter) : Prop :=
  Internal.core l₁ = Internal.core l₂ ∧ Internal.held l₁ = Internal.held l₂ ∧
    canonA (Internal.handler l₁) = (Internal.handler l₂).adapter

theorem run_eq {H : Type} {R E α : Type} [Token.Consume H R E] (l : BSmtLib.Lexer H)
    (x : InnerM H Id α) :
    Internal.run l x =
      (((x.run (Internal.core l)).run (Internal.handler l)).1.1,
        Internal.ofParts ((x.run (Internal.core l)).run (Internal.handler l)).2
          ((x.run (Internal.core l)).run (Internal.handler l)).1.2 (Internal.held l)) := (rfl)

theorem lexErrRel_eq {e₁ e₂ : LexError (ParseErrorCause Unit)} (h : LexErrRel link.re e₁ e₂) :
    e₁ = e₂ := by
  obtain ⟨c₁, s₁, f₁⟩ := e₁
  obtain ⟨c₂, s₂, f₂⟩ := e₂
  obtain ⟨hc, hs, hf⟩ := h
  dsimp only at hc hs hf
  subst hs hf
  cases c₁ <;> cases c₂ <;> simp only [CauseRel] at hc
  · subst hc; rfl
  · subst hc; rfl

theorem locRel_eq {a b : Span.Located Unit} (h : LocRel link.rr a b) : a = b := by
  obtain ⟨⟨⟩, l₁⟩ := a
  obtain ⟨⟨⟩, l₂⟩ := b
  obtain ⟨-, h⟩ := h
  dsimp only at h
  rw [h]

theorem oRel_eq {a b : Option (Span.Located Unit)} (h : ORel (LocRel link.rr) a b) : a = b := by
  cases a <;> cases b <;> simp only [ORel] at h
  · rfl
  · rw [locRel_eq h]

theorem flowRel_eq {a b : ControlFlow (Span.Located Unit)} (h : FlowRel (LocRel link.rr) a b) :
    a = b := by
  cases a <;> cases b <;> simp only [FlowRel] at h
  · rfl
  · rw [locRel_eq h]

theorem habandon (l : Span.Location) :
    link.rc.rel (· = ·) (abandonI (H := RecAdapter) l) (abandonI (H := CanonAdapter) l) :=
  link.rc.pure rfl

theorem hrecover (l : Span.Location) :
    link.rc.rel (· = ·) (recoverI (H := RecAdapter) l) (recoverI (H := CanonAdapter) l) :=
  link.rc.pure rfl

theorem lexFeed_link : ∀ (slices : List ByteList) {l₁ : BSmtLib.Lexer RecAdapter}
    {l₂ : BSmtLib.Lexer CanonAdapter}, LinkRel l₁ l₂ →
    ERel (· = ·) LinkRel (lexFeed (R := Unit) (E := ParseErrorCause Unit) l₁ slices)
      (lexFeed (R := Unit) (E := ParseErrorCause Unit) l₂ slices)
  | [], l₁, l₂, h => h
  | slice :: slices, l₁, l₂, ⟨hc, hh, ha⟩ => by
    have hsim := lexSliceStep_sim consumers abandonI recoverI abandonI recoverI habandon
      hrecover slice.toByteArray.toByteSlice (Internal.core l₂) (Internal.handler l₁)
      (Internal.handler l₂) ha
    simp only [lexFeed]
    rw [run_eq, run_eq, hc, hh]
    generalize ((Internal.lexSliceStep (R := Unit) (E := ParseErrorCause Unit) abandonI recoverI
      slice.toByteArray.toByteSlice).run (Internal.core l₂)).run (Internal.handler l₁) = A
      at hsim ⊢
    generalize ((Internal.lexSliceStep (R := Unit) (E := ParseErrorCause Unit) abandonI recoverI
      slice.toByteArray.toByteSlice).run (Internal.core l₂)).run (Internal.handler l₂) = B
      at hsim ⊢
    obtain ⟨⟨r₁, c₁⟩, h₁⟩ := A
    obtain ⟨⟨r₂, c₂⟩, h₂⟩ := B
    obtain ⟨⟨hr, hcc⟩, hha⟩ := hsim
    dsimp only at hr hcc hha ⊢
    subst hcc
    rcases r₁ with e₁ | o₁ <;> rcases r₂ with e₂ | o₂ <;> simp only [ERel] at hr
    · exact lexErrRel_eq hr
    · rw [oRel_eq hr]
      exact lexFeed_link slices ⟨rfl, rfl, hha⟩

/-- A read with the parse adapter and one with the canonical adapter that end alike: the same
error, or the same result with lexers related before and after the end of the input. -/
def ThroughLink :
    Except (LexError (ParseErrorCause Unit))
        (Option (Span.Located Unit) × BSmtLib.Lexer RecAdapter × BSmtLib.Lexer RecAdapter) →
      Except (LexError (ParseErrorCause Unit))
        (Option (Span.Located Unit) × BSmtLib.Lexer CanonAdapter ×
          BSmtLib.Lexer CanonAdapter) → Prop
  | .error e, .error e' => e = e'
  | .ok (r, b, a), .ok (r', b', a') => r = r' ∧ LinkRel b b' ∧ LinkRel a a'
  | _, _ => False

theorem lexThrough_link (slices : List ByteList) {l₁ : BSmtLib.Lexer RecAdapter}
    {l₂ : BSmtLib.Lexer CanonAdapter} (h : LinkRel l₁ l₂) :
    ThroughLink (lexThrough (R := Unit) (E := ParseErrorCause Unit) l₁ slices)
      (lexThrough (R := Unit) (E := ParseErrorCause Unit) l₂ slices) := by
  have hf := lexFeed_link slices h
  unfold lexThrough
  generalize lexFeed (R := Unit) (E := ParseErrorCause Unit) l₁ slices = F₁ at hf ⊢
  generalize lexFeed (R := Unit) (E := ParseErrorCause Unit) l₂ slices = F₂ at hf ⊢
  rcases F₁ with e₁ | b₁ <;> rcases F₂ with e₂ | b₂ <;> simp only [ERel] at hf
  · subst hf; exact (rfl : e₁ = e₁)
  · obtain ⟨hc, hh, ha⟩ := hf
    have hsim := lexEofStep_sim consumers abandonI recoverI abandonI recoverI habandon
      hrecover (Internal.core b₂) (Internal.handler b₁) (Internal.handler b₂) ha
    dsimp only
    rw [run_eq, run_eq, hc]
    generalize ((Internal.lexEofStep (R := Unit) (E := ParseErrorCause Unit) abandonI
      recoverI).run (Internal.core b₂)).run (Internal.handler b₁) = A at hsim ⊢
    generalize ((Internal.lexEofStep (R := Unit) (E := ParseErrorCause Unit) abandonI
      recoverI).run (Internal.core b₂)).run (Internal.handler b₂) = B at hsim ⊢
    obtain ⟨⟨r₁, c₁⟩, h₁⟩ := A
    obtain ⟨⟨r₂, c₂⟩, h₂⟩ := B
    obtain ⟨⟨hr, hcc⟩, hha⟩ := hsim
    dsimp only at hr hcc hha ⊢
    subst hcc
    rcases r₁ with e₁ | f₁ <;> rcases r₂ with e₂ | f₂ <;> simp only [ERel] at hr
    · exact lexErrRel_eq hr
    · rw [flowRel_eq hr]
      refine ⟨?_, ⟨hc, hh, ha⟩, ⟨rfl, rfl, hha⟩⟩
      show eofResultT (Internal.held b₁) f₂ = eofResultT (Internal.held b₂) f₂
      rw [hh]

end

end BSmtLib.Facts.Proofs.Parser.Canon.Through
