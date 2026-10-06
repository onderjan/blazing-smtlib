import BSmtLib.Proofs.VNaiveWRustPort.HandOver

/-!
# The Rust port's state against the naive lexer's pure state

The correspondence of the Rust port's lexer state `WRustPort.LexerCore` with the naive lexer's
pure state `VNaive.St` and its location, under the version, when the adapter's consumer runs
the Rust port: it never switches the version, never finishes and does not take whitespace and
comments, and the lexer stops at its first error.

- `Fixed`: the version is the one in force, the lexer does not recover, does not discard and is
  not recovering.
- `StAgrees`: the lexer state `normal` is `St.idle`; any other state is a token in progress
  (`TokenAgrees`), which starts at `tokenStart`, with the content of the content buffer
  `tokenContent` (`contentBytes`), whose length is within its array (`Fits`), in the mode
  that the state stands for under the version: `numeralOrDecimal` is a numeral, which is the
  single digit `0` exactly when the content is; `fraction` is a fraction, with a digit after
  the dot exactly when the content does not end with the dot; `baseSelection` is the `#`;
  `hexadecimal` and `binary` are the digits of the base; `stringLiteral`,
  `stringLiteralDoubleQuote` and `stringLiteralBackslashEscape` are a string, a string and its
  quote, and (under version 2.0 only) a string and its backslash, in the modes of version 2.0 or
  of the later versions; `simpleSymbol`, `quotedSymbol`, `keyword` and `quotedSymbolClosed` are
  the modes of their names; `comment` is a comment, whose content the Rust port does not keep
  for a consumer that does not take comments, and the naive lexer keeps but never hands over.
  The state `whitespace` is never reached, as the consumer does not take whitespace.
- `LocAt`: the location of the index of the slice is the one the Rust port computes from the
  offset `offset` of the index `base`, on its line, from the offset where the line starts.
- the batch of the lexer state holds lexemes (`Holds`) not yet handed over, which the
  consumer will record before those still to come (`outcome`).
-/

namespace BSmtLib.Proofs.Lexer.VNaiveWRustPort

open BSmtLib.Proofs.Adapter VNaive BSmtLib.Proofs.Simulation
open BSmtLib.Lexer (LexerState)

/-- The Rust port's lexer state is fixed as the adapter's consumer runs it, under the version. -/
structure Fixed (v : Version) (c : WCore) : Prop where
  version : c.version = v
  recovers : c.recovers = false
  discard : c.discard = false
  recoveryState : c.recoveryState = none

/-- The last byte of the content, if any. -/
def lastOf (content : ByteArray) : Option UInt8 :=
  if content.size == 0 then none else some (content.get! (content.size - 1))

/-- The last byte of the content buffer is that of its content. -/
theorem last?_stored {buf : BSmtLib.Lexer.ContentBuffer} (h : Fits buf) :
    BSmtLib.Lexer.Content.stored.last? buf = lastOf (contentBytes buf) := by
  unfold BSmtLib.Lexer.Content.last? lastOf
  rw [size_contentBytes h]
  by_cases h0 : buf.len = 0
  · simp [h0]
  · have h1 : buf.len - 1 < buf.len := by omega
    simp [h0, get!_eq_getElem!, get!_contentBytes h h1]

/-- The Rust port's token in progress, in the state `state` from `start` with the content
`content`, is the naive lexer's token in progress `p`, under the version. -/
def TokenAgrees (v : Version) (state : LexerState) (start : Location) (content : ByteArray)
    (p : Pending) : Prop :=
  p.start = start ∧
    match state with
    | .normal => False
    | .numeralOrDecimal =>
      p.mode = .numeral (content.size == 1 && content.get! 0 == byte! '0') ∧ p.content = content ∧
        content.size ≠ 0
    | .fraction =>
      p.mode = .fraction !((lastOf content).isNone || lastOf content == some (byte! '.')) ∧
        p.content = content
    | .baseSelection => p.mode = .hash ∧ p.content = content
    | .hexadecimal => p.mode = .digits .hexadecimal ∧ p.content = content
    | .binary => p.mode = .digits .binary ∧ p.content = content
    | .stringLiteral =>
      p.mode = (if v == .v2_0 then .legacyString else .string) ∧ p.content = content
    | .stringLiteralDoubleQuote =>
      p.mode = (if v == .v2_0 then .legacyQuote else .stringQuote) ∧ p.content = content
    | .stringLiteralBackslashEscape => v = .v2_0 ∧ p.mode = .legacyEscape ∧ p.content = content
    | .simpleSymbol => p.mode = .simpleSymbol ∧ p.content = content
    | .quotedSymbol => p.mode = .quotedSymbol ∧ p.content = content
    | .keyword => p.mode = .keyword ∧ p.content = content
    | .comment => p.mode = .comment
    | .whitespace => False
    | .quotedSymbolClosed => p.mode = .quotedSymbolClosed ∧ p.content = content

/-- The Rust port's lexer state is the naive lexer's pure state, under the version. -/
def StAgrees (v : Version) : St → WCore → Prop
  | .idle, c => c.state = .normal
  | .token p, c =>
    TokenAgrees v c.state c.tokenStart (contentBytes c.tokenContent) p ∧ Fits c.tokenContent

/-- The location is that of the index `index` of the slice, from the offset `offset` of the
index `base`, on the lexer's line. -/
def LocAt (c : WCore) (offset base index : Nat) (location : Location) : Prop :=
  location.offset = offset + (index - base) ∧ location.line = c.line ∧
    c.lineStart + location.column = location.offset

theorem LocAt.congr {c c' : WCore} {offset base index : Nat} {location : Location}
    (h : LocAt c offset base index location) (hl : c'.line = c.line)
    (hs : c'.lineStart = c.lineStart) : LocAt c' offset base index location := by
  obtain ⟨h1, h2, h3⟩ := h
  exact ⟨h1, by rw [hl]; exact h2, by rw [hs]; exact h3⟩

theorem fixed_of_key {v : Version} {c c' : WCore} (h : Fixed v c) (hk : key c' = key c) :
    Fixed v c' := by
  simp only [key, Prod.mk.injEq] at hk
  obtain ⟨e1, -, e3, e4, e5, -⟩ := hk
  exact ⟨e1.trans h.1, e4.trans h.2, e3.trans h.3, e5.trans h.4⟩

theorem fixed_of_key' {v : Version} {c c' : WCore} (hk : key c' = key c) (h : Fixed v c) :
    Fixed v c' :=
  fixed_of_key h hk

theorem stAgrees_of_key {v : Version} {st : St} {c c' : WCore} (h : StAgrees v st c)
    (hk : key c' = key c) : StAgrees v st c' := by
  simp only [key, Prod.mk.injEq] at hk
  obtain ⟨-, e2, -, -, -, e6, e7, -⟩ := hk
  cases st with
  | idle => exact e2.trans h
  | token p =>
    show TokenAgrees v c'.state c'.tokenStart (contentBytes c'.tokenContent) p ∧
      Fits c'.tokenContent
    rw [e2, e6, e7]
    exact h

theorem locAt_of_key {c c' : WCore} {offset base index : Nat} {location : Location}
    (h : LocAt c offset base index location) (hk : key c' = key c) :
    LocAt c' offset base index location := by
  simp only [key, Prod.mk.injEq] at hk
  exact h.congr hk.2.2.2.2.2.2.2.2.2.1 hk.2.2.2.2.2.2.2.2.2.2

end BSmtLib.Proofs.Lexer.VNaiveWRustPort
