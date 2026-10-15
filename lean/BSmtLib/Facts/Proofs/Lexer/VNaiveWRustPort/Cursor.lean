module

public import BSmtLib.Facts.Proofs.Lexer.VNaiveWRustPort.Model
public import BSmtLib.Facts.Proofs.Lexer.VNaiveWRustPort.Batch
public import BSmtLib.Facts.Proofs.Lexer.Simulation.Batch
import all BSmtLib.Span
import all BSmtLib.Token
import all BSmtLib.Token.SyntaxToken

@[expose] public section

/-!
# Cursors over a batch that holds lexemes

A cursor is observed by the index of its next token (`cNext`) and the index after the last token
it yields (`cStop`) in its batch. Over a batch that holds lexemes, the token at an index is
reported as the naive lexer reports the lexeme at that index alone (`toHanded_at`), and the end of
the last token consumed is that of the lexeme before the next index (`consumedEndOf_at`).
-/

open BSmtLib.Facts.Proofs.Lexer.Simulation.Batch BSmtLib.Facts.Proofs.Lexer.Simulation.Bytes
open BSmtLib.Token.BatchCursor.Internal
    (discardRequested resetConsumed relexRequested consumedEndOf)
open BSmtLib.Facts.Proofs.Lexer.VNaive.Run BSmtLib.Facts.Proofs.Lexer.VNaive.Streaming
open BSmtLib.Facts.Proofs.Lexer.VNaiveWRustPort.Batch
open BSmtLib.Facts.Proofs.Lexer.VNaiveWRustPort.Bytes
open BSmtLib.Facts.Proofs.Lexer.VNaiveWRustPort.Model BSmtLib.Lexer.Internal.VNaive

namespace BSmtLib.Facts.Proofs.Lexer.VNaiveWRustPort.Cursor

open BSmtLib.Facts.Lexer.Adapters

variable {g : Token.BatchTag}

theorem cNext_next (c : Token.BatchCursor g) (h : c.HasNext) : cNext
    (c.next h).2.1 = cNext c + 1 := by
  cases c; rfl

theorem cStop_next (c : Token.BatchCursor g) (h : c.HasNext) : cStop (c.next h).2.1 = cStop c := by
  cases c; rfl

theorem cNext_resetConsumed (c : Token.BatchCursor g) : cNext (resetConsumed c) = cNext c := by
  cases c; rfl

theorem cStop_resetConsumed (c : Token.BatchCursor g) : cStop (resetConsumed c) = cStop c := by
  cases c; rfl

theorem relex_resetConsumed (c : Token.BatchCursor g) :
    (relexRequested (resetConsumed c)) = relexRequested c := by
  cases c; rfl

theorem discard_resetConsumed (c : Token.BatchCursor g) :
    (discardRequested (resetConsumed c)) = discardRequested c := by
  cases c; rfl

theorem cNext_new (v : Token.Version) (b : Token.Internal.TokenBatch) :
    cNext (Token.BatchCursor.Internal.new v b) = 0 := (rfl)

theorem cStop_new (v : Token.Version) (b : Token.Internal.TokenBatch) :
    cStop (Token.BatchCursor.Internal.new v b) = b.len := (rfl)

theorem relex_new (v : Token.Version) (b : Token.Internal.TokenBatch) :
    (relexRequested (Token.BatchCursor.Internal.new v b)) = false := (rfl)

theorem discard_new (v : Token.Version) (b : Token.Internal.TokenBatch) :
    (discardRequested (Token.BatchCursor.Internal.new v b)) = false := (rfl)

theorem version_new (v : Token.Version) (b : Token.Internal.TokenBatch) :
    (Token.BatchCursor.Internal.new v b).version = v := (rfl)

theorem cNext_discardRest (c : Token.BatchCursor g) : cNext c.discardRest = cNext c := by
  cases c; rfl

theorem cStop_discardRest (c : Token.BatchCursor g) : cStop c.discardRest = cNext c := by
  cases c; rfl

theorem discard_discardRest (c : Token.BatchCursor g) : discardRequested c.discardRest = true := by
  cases c; rfl

theorem relex_discardRest (c : Token.BatchCursor g) :
    (relexRequested c.discardRest) = relexRequested c := by
  cases c; rfl

theorem version_discardRest (c : Token.BatchCursor g) : c.discardRest.version = c.version := by
  cases c; rfl

/-- A switch of the version: the version, and, if the lexical rules change, a request to relex
and no token left. -/
theorem setVersion_eq (c : Token.BatchCursor g) (v : Token.Version) :
    ∃ c', c.setVersion v = .ok c' ∧ c'.version = v ∧ cNext c' = cNext c ∧
      (discardRequested c') = discardRequested c ∧
      (crosses c.version v = true → relexRequested c' = true ∧ cStop c' = cNext c) ∧
      (crosses c.version v = false → relexRequested c' = relexRequested c ∧
        cStop c' = cStop c) := by
  cases c
  simp only [Token.BatchCursor.setVersion, crosses]
  split
  · rename_i h
    refine ⟨_, rfl, rfl, rfl, rfl, fun _ => ⟨rfl, rfl⟩, fun h' => ?_⟩
    rw [h] at h'
    cases h'
  · rename_i h
    refine ⟨_, rfl, rfl, rfl, rfl, fun h' => ?_, fun _ => ⟨rfl, rfl⟩⟩
    exact absurd h' h

/-- A batch that holds the lexemes has their entries at their indices. -/
theorem holds_categoryAt {T : Token.Internal.TokenBatch} {ls : List Lexeme} (h : Holds T ls)
    {i : Nat}
    (hi : i < ls.length) : categoryAt T i = ls[i].category := by
  obtain ⟨e1, -⟩ := h.entry i hi
  simp only [Simulation.Batch.categoryAt, e1, ofUInt8_toUInt8]

theorem holds_spanAt_start {T : Token.Internal.TokenBatch} {ls : List Lexeme} (h : Holds T ls)
    {i : Nat}
    (hi : i < ls.length) : (spanAt T i).start = ls[i].start := by
  obtain ⟨-, -, -, -, e5, e6, e7, -⟩ := h.entry i hi
  simp only [Simulation.Batch.spanAt, Span.Internal.ofNumbers, Span.start, e5, e6, e7,
    Span.Location.Internal.new_eta]

theorem holds_spanAt_end {T : Token.Internal.TokenBatch} {ls : List Lexeme} (h : Holds T ls)
    {i : Nat}
    (hi : i < ls.length) : (spanAt T i).end = ls[i].end := by
  obtain ⟨-, -, -, -, -, -, -, e8, e9, e10⟩ := h.entry i hi
  simp only [Simulation.Batch.spanAt, Span.Internal.ofNumbers, Span.«end», e8, e9, e10,
    Span.Location.Internal.new_eta]

theorem holds_contentAt {T : Token.Internal.TokenBatch} {ls : List Lexeme} (h : Holds T ls)
    {i : Nat}
    (hi : i < ls.length) : (contentAt T i).toByteArray = ls[i].content := by
  obtain ⟨-, e2, e3, e4, -⟩ := h.entry i hi
  simp only [Simulation.Batch.contentAt]
  rw [toByteArray_toByteSlice_range _ e2 e3, e4]

/-- The next token of a cursor over a batch that holds the lexemes is reported as the naive
lexer reports the lexeme at its index alone. -/
theorem toHanded_at {ls : List Lexeme} (c : Token.BatchCursor g) (h : c.HasNext)
    (hb : Holds (BSmtLib.Lexer.Internal.intoBatch c) ls) (hj : cNext c < ls.length) :
    toHanded c (c.next h).1 = lexemeHanded c.version ls[cNext c] := by
  rw [lexemeHanded_eq]
  have hcontent : (c.content (c.next h).1).toByteArray = ls[cNext c].content := by
    rw [Simulation.Batch.content_eq, tokenIndex_next, holds_contentAt hb hj]
  have hcat : c.category (c.next h).1 = ls[cNext c].category := by
    rw [Simulation.Batch.category_eq, tokenIndex_next, holds_categoryAt hb hj]
  have hstart : (c.span (c.next h).1).start = ls[cNext c].start := by
    rw [Simulation.Batch.span_eq, tokenIndex_next, holds_spanAt_start hb hj]
  have hend : (c.span (c.next h).1).end = ls[cNext c].end := by
    rw [Simulation.Batch.span_eq, tokenIndex_next, holds_spanAt_end hb hj]
  unfold toHanded
  simp only [Token.BatchCursor.«syntax», Token.SyntaxToken.fromToken,
      Token.SyntaxToken.Internal.fromParts,
      hcat, hstart, hend,
    toContent, hcontent, byteArray_toList]
  cases hc : ls[cNext c].category <;> simp [toTokenType, lexemeReserved, toReservedKind]
  · rw [← hcontent, fromBytes_toByteArray]
    cases Token.Reserved.fromBytes? (c.content (c.next h).1) c.version <;> rfl

/-- The next token of a cursor over a batch that holds the lexemes is taken as the entry the naive
lexer reports for the lexeme at its index alone. -/
theorem entry_at (C : BSmtLibSpec.Lexer.Consumer) {ls : List Lexeme} (c : Token.BatchCursor g)
    (h : c.HasNext)
    (hb : Holds (BSmtLib.Lexer.Internal.intoBatch c) ls) (hj : cNext c < ls.length) :
    Answering.entry C c (c.next h).1 = lexemeEntry C.concrete c.version ls[cNext c] := by
  have hcontent : (c.content (c.next h).1).toByteArray = ls[cNext c].content := by
    rw [Simulation.Batch.content_eq, tokenIndex_next, holds_contentAt hb hj]
  have hcat : c.category (c.next h).1 = ls[cNext c].category := by
    rw [Simulation.Batch.category_eq, tokenIndex_next, holds_categoryAt hb hj]
  have hstart : (c.span (c.next h).1).start = ls[cNext c].start := by
    rw [Simulation.Batch.span_eq, tokenIndex_next, holds_spanAt_start hb hj]
  have hend : (c.span (c.next h).1).end = ls[cNext c].end := by
    rw [Simulation.Batch.span_eq, tokenIndex_next, holds_spanAt_end hb hj]
  unfold Answering.entry lexemeEntry
  rw [toHanded_at c h hb hj]
  cases lexemeHanded c.version ls[cNext c] with
  | some _ => rfl
  | none =>
    simp only [toLayout, lexemeLayout, hcat, hstart, hend, toContent, hcontent,
      Simulation.Bytes.toByteArray_toByteSlice]

/-- The span of the next token of a cursor over a batch that holds the lexemes starts where the
lexeme at its index starts. -/
theorem span_peek_start {ls : List Lexeme} (c : Token.BatchCursor g) (h : c.HasNext)
    (hb : Holds (BSmtLib.Lexer.Internal.intoBatch c) ls) (hj : cNext c < ls.length) :
    (c.span (c.peek h)).start = ls[cNext c].start := by
  rw [Simulation.Batch.span_eq, tokenIndex_peek, holds_spanAt_start hb hj]

/-- The end of the last token consumed from a cursor over a batch that holds the lexemes. -/
theorem consumedEndOf_at {ls : List Lexeme} {c c₀ : Token.BatchCursor g} (hc : c.Consumed c₀)
    (hb : Holds (BSmtLib.Lexer.Internal.intoBatch c) ls) (hj : cNext c - 1 < ls.length) :
    (consumedEndOf c) hc = ls[cNext c - 1].end := by
  rw [consumedEndOf_eq, holds_spanAt_end hb hj]

/-- The span of a lexeme, from its start to its end. -/
def lexSpan (l : Lexeme) : Span :=
  Span.Internal.newUnchecked l.start l.end

theorem lexSpan_start (l : Lexeme) : (lexSpan l).start = l.start := by
  simp only [lexSpan, Span.Internal.newUnchecked, Span.start, Span.Location.Internal.new_eta]

theorem lexSpan_end (l : Lexeme) : (lexSpan l).end = l.end := by
  simp only [lexSpan, Span.Internal.newUnchecked, Span.«end», Span.Location.Internal.new_eta]

/-- A location of the library for one of the spec. -/
def ofLocation (l : BSmtLibSpec.Lexer.Location) : Span.Location :=
  Span.Location.Internal.new l.offset l.line l.column

theorem ofLocation_toLocation (l : Span.Location) :
    ofLocation (BSmtLib.Facts.Lexer.Adapters.toLocation l) = l := by
  simp only [ofLocation, BSmtLib.Facts.Lexer.Adapters.toLocation, Span.Location.Internal.new_eta]

/-- The span of the last token taken, from its start to its end. -/
def handedSpan (t : List BSmtLibSpec.Lexer.Handed) : Span :=
  match t.getLast? with
  | some h => Span.Internal.newUnchecked (ofLocation h.start) (ofLocation h.end)
  | none => Span.Internal.newZero

theorem handedSpan_eq {t : List BSmtLibSpec.Lexer.Handed} {x : BSmtLibSpec.Lexer.Handed}
    {l : Lexeme} (h : t.getLast? = some x)
    (hs : x.start = BSmtLib.Facts.Lexer.Adapters.toLocation l.start)
    (he : x.end = BSmtLib.Facts.Lexer.Adapters.toLocation l.end) : handedSpan t = lexSpan l := by
  unfold handedSpan lexSpan
  rw [h]
  dsimp only
  rw [hs, he, ofLocation_toLocation, ofLocation_toLocation]

theorem span_eq_lexSpan {s : Span} {l : Lexeme} (h₁ : s.start = l.start) (h₂ : s.end = l.end) :
    s = lexSpan l := by
  unfold lexSpan
  rw [← h₁, ← h₂]
  rfl

/-- The span of the next token of a cursor over a batch that holds the lexemes is that of the
lexeme at its index. -/
theorem span_peek {ls : List Lexeme} (c : Token.BatchCursor g) (h : c.HasNext)
    (hb : Holds (BSmtLib.Lexer.Internal.intoBatch c) ls) (hj : cNext c < ls.length) :
    c.span (c.peek h) = lexSpan ls[cNext c] := by
  apply span_eq_lexSpan
  · rw [Simulation.Batch.span_eq, tokenIndex_peek, holds_spanAt_start hb hj]
  · rw [Simulation.Batch.span_eq, tokenIndex_peek, holds_spanAt_end hb hj]

/-- The span of the last token consumed from a cursor over a batch that holds the lexemes. -/
theorem consumedSpanOf_at {ls : List Lexeme} {c c₀ : Token.BatchCursor g} (hc : c.Consumed c₀)
    (hb : Holds (BSmtLib.Lexer.Internal.intoBatch c) ls) (hj : cNext c - 1 < ls.length) :
    Token.BatchCursor.Internal.consumedSpanOf c hc = lexSpan ls[cNext c - 1] := by
  rw [Simulation.Batch.consumedSpanOf_eq]
  exact span_eq_lexSpan (holds_spanAt_start hb hj) (holds_spanAt_end hb hj)

end BSmtLib.Facts.Proofs.Lexer.VNaiveWRustPort.Cursor

namespace BSmtLib.Facts.Proofs.Lexer.VNaiveWRustPort.Cursor

open BSmtLib.Facts.Lexer.Adapters

variable {g : Token.BatchTag} (C : BSmtLibSpec.Lexer.Consumer)

/-- The cursor after the switch the consumer asks for at the last of the tokens `taken`. -/
theorem switched_eq (taken : List BSmtLibSpec.Lexer.Handed) (c : Token.BatchCursor g) :
    (Answering.switched C taken c).val.version = switchedTo c.version (C.switchTo taken) ∧
      cNext (Answering.switched C taken c).val = cNext c ∧
      (discardRequested (Answering.switched C taken c).val) = discardRequested c ∧
      (crosses c.version (switchedTo c.version (C.switchTo taken)) = true →
        (relexRequested (Answering.switched C taken c).val) = true ∧
        cStop (Answering.switched C taken c).val = cNext c) ∧
      (crosses c.version (switchedTo c.version (C.switchTo taken)) = false →
        (relexRequested (Answering.switched C taken c).val) = relexRequested c ∧
        cStop (Answering.switched C taken c).val = cStop c) := by
  unfold Answering.switched
  split
  · rename_i hs
    rw [hs]
    simp [switchedTo, crosses]
  · rename_i v hs
    obtain ⟨c', hc', h1, h2, h3, h4, h5⟩ := setVersion_eq c (toVersion v)
    simp only [hs, switchedTo]
    split
    · rename_i next hn
      rw [hc'] at hn
      cases hn
      exact ⟨h1, h2, h3, h4, h5⟩
    · rename_i hn
      rw [hc'] at hn
      cases hn

end BSmtLib.Facts.Proofs.Lexer.VNaiveWRustPort.Cursor
