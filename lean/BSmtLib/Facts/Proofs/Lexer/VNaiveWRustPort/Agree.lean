import BSmtLib.Facts.Proofs.Lexer.VNaiveWRustPort.HandOver

/-!
# The Rust port's state against the naive lexer's pure state

The correspondence of the Rust port's lexer state with the naive lexer's pure state, for a
consumer that takes whitespace and comments if `ws`, while the Rust port lexes under a version
with the lexical rules of `v`, holds a result if `hd`, and was created with the version `iv`.

- `Fixed`: the version has the lexical rules of `v`, the lexer does not recover, does not
  discard, holds a result exactly if `hd`, is not recovering, and was created with `iv`.
- `TokenAgreesNoWs`: a lexer state other than `normal` and `whitespace` is a token in progress,
  which starts at `start`, with the content `content`, in the mode that the state stands for under
  the version: `numeralOrDecimal` is a numeral, which is the single digit `0` exactly when the
  content is; `fraction` is a fraction, with a digit after the dot exactly when the content does
  not end with the dot; `baseSelection` is the `#`; `hexadecimal` and `binary` are the digits of
  the base; `stringLiteral`, `stringLiteralDoubleQuote` and `stringLiteralBackslashEscape` are a
  string, a string and its quote, and (under version 2.0 only) a string and its backslash, in the
  modes of version 2.0 or of the later versions; `simpleSymbol`, `quotedSymbol`, `keyword` and
  `quotedSymbolClosed` are the modes of their names; `comment` is a comment, whose content is not
  compared.
- `TokenAgrees`, `StAgrees`: as `TokenAgreesNoWs`, and in addition for a consumer that takes
  whitespace and comments: `whitespace` is whitespace, with its content, and `comment` keeps the
  content. The lexer state `normal` is `St.idle`; any other state is a token in progress, with the
  content of the content buffer `tokenContent` (`contentBytes`), whose length is within its array
  (`Fits`).
- `LocAt`: the location of the index of the slice is the one the Rust port computes from the
  offset `offset` of the index `base`, on its line, from the offset where the line starts.
-/

namespace BSmtLib.Facts.Proofs.Lexer.VNaiveWRustPort.Agree

open BSmtLib.Facts.Proofs.Lexer.Simulation.Bytes
open BSmtLib.Lexer.Helpers (LexerState)
open BSmtLib.Facts.Proofs.Lexer.VNaive.Run BSmtLib.Facts.Proofs.Lexer.VNaiveWRustPort.HandOver
open BSmtLib.Lexer.Internal.VNaive

/-- The last byte of the content, if any. -/
def lastOf (content : ByteArray) : Option UInt8 :=
  if content.size == 0 then none else some (content.get! (content.size - 1))

/-- The last byte of the content buffer is that of its content. -/
theorem last?_stored {buf : Lexer.Helpers.ContentBuffer} (h : Fits buf) :
    Lexer.Helpers.Content.stored.last? buf = lastOf (contentBytes buf) := by
  unfold Lexer.Helpers.Content.last? lastOf
  rw [size_contentBytes h]
  by_cases h0 : buf.len = 0
  · simp [h0]
  · have h1 : buf.len - 1 < buf.len := by omega
    have h2 : buf.len - 1 < buf.bytes.size := by have := buf.fits; omega
    simp only [h0, get!_eq_getElem!, get!_contentBytes h h1, beq_iff_eq, ↓reduceDIte, ↓reduceIte]
    exact congrArg some (getElem!_pos buf.bytes (buf.len - 1) h2).symm

/-- The Rust port's token in progress, in the state `state` from `start` with the content
`content`, is the naive lexer's token in progress `p`, under the version, for a consumer that does
not take whitespace and comments. -/
def TokenAgreesNoWs (v : Token.Version) (state : LexerState) (start : Span.Location)
    (content : ByteArray)
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

/-- The location is that of the index `index` of the slice, from the offset `offset` of the
index `base`, on the lexer's line. -/
def LocAt (c : WP.WCore) (offset base index : Nat) (location : Span.Location) : Prop :=
  location.offset = offset + (index - base) ∧ location.line = c.line ∧
    c.lineStart + location.column = location.offset

theorem LocAt.congr {c c' : WP.WCore} {offset base index : Nat} {location : Span.Location}
    (h : LocAt c offset base index location) (hl : c'.line = c.line)
    (hs : c'.lineStart = c.lineStart) : LocAt c' offset base index location := by
  obtain ⟨h1, h2, h3⟩ := h
  exact ⟨h1, by rw [hl]; exact h2, by rw [hs]; exact h3⟩

/-- The Rust port's lexer state is fixed while it lexes a slice. -/
structure Fixed (v : Token.Version) (hd : Bool) (iv : Token.Version) (c : WP.WCore) : Prop where
  version : (c.version == .v2_0) = (v == .v2_0)
  recovers : c.recovers = false
  discardedFrom : c.discardedFrom = none
  holding : c.holding = hd
  recoveryState : c.recoveryState = none
  initial : c.initialVersion = iv

/-- The Rust port's token in progress, in the state `state` from `start` with the content
`content`, is the naive lexer's token in progress `p`, under the version, for a consumer that
takes whitespace and comments if `ws`. -/
def TokenAgrees (v : Token.Version) (ws : Bool) (state : LexerState) (start : Span.Location)
    (content : ByteArray) (p : Pending) : Prop :=
  match state with
  | .whitespace => p.start = start ∧ ws = true ∧ p.mode = .whitespace ∧ p.content = content
  | .comment => p.start = start ∧ p.mode = .comment ∧ (ws = true → p.content = content)
  | _ => TokenAgreesNoWs v state start content p

/-- The Rust port's lexer state is the naive lexer's pure state, under the version. -/
def StAgrees (v : Token.Version) (ws : Bool) : St → WP.WCore → Prop
  | .idle, c => c.state = .normal
  | .token p, c =>
    TokenAgrees v ws c.state c.tokenStart (contentBytes c.tokenContent) p ∧ Fits c.tokenContent

/-- The fields of the lexer state that are kept determine its correspondence. -/
theorem key_fields {c c' : WP.WCore} (hk : key c' = key c) :
    ((c'.version == .v2_0) = (c.version == .v2_0) ∧ c'.initialVersion = c.initialVersion) ∧
      c'.state = c.state ∧
      (c'.discardedFrom, c'.holding) = (c.discardedFrom, c.holding) ∧
      c'.recovers = c.recovers ∧ c'.recoveryState = c.recoveryState ∧
      c'.tokenStart = c.tokenStart ∧ c'.tokenContent = c.tokenContent ∧ c'.offset = c.offset ∧
      c'.base = c.base ∧ c'.line = c.line ∧ c'.lineStart = c.lineStart := by
  unfold key at hk
  injection hk with e1 hk
  injection e1 with e1 e1'
  injection hk with e2 hk
  injection hk with e3 hk
  injection hk with e4 hk
  injection hk with e5 hk
  injection hk with e6 hk
  injection hk with e7 hk
  injection hk with e8 hk
  injection hk with e9 hk
  injection hk with e10 e11
  exact ⟨⟨e1, e1'⟩, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11⟩

theorem fixed_of_key {v : Token.Version} {hd : Bool} {iv : Token.Version} {c c' : WP.WCore}
    (h : Fixed v hd iv c) (hk : key c' = key c) : Fixed v hd iv c' := by
  obtain ⟨⟨e1, e1'⟩, -, e3, e4, e5, -⟩ := key_fields hk
  simp only [Prod.mk.injEq] at e3
  exact ⟨e1.trans h.1, e4.trans h.2, e3.1.trans h.3, e3.2.trans h.4, e5.trans h.5, e1'.trans h.6⟩

theorem fixed_of_key' {v : Token.Version} {hd : Bool} {iv : Token.Version} {c c' : WP.WCore}
    (hk : key c' = key c) (h : Fixed v hd iv c) : Fixed v hd iv c' :=
  fixed_of_key h hk

theorem stAgrees_of_key {v : Token.Version} {ws : Bool} {st : St} {c c' : WP.WCore}
    (h : StAgrees v ws st c) (hk : key c' = key c) : StAgrees v ws st c' := by
  obtain ⟨-, e2, -, -, -, e6, e7, -⟩ := key_fields hk
  cases st with
  | idle => exact e2.trans h
  | token p =>
    show TokenAgrees v ws c'.state c'.tokenStart (contentBytes c'.tokenContent) p ∧
      Fits c'.tokenContent
    rw [e2, e6, e7]
    exact h

theorem locAt_of_key {c c' : WP.WCore} {offset base index : Nat} {location : Span.Location}
    (h : LocAt c offset base index location) (hk : key c' = key c) :
    LocAt c' offset base index location := by
  obtain ⟨-, -, -, -, -, -, -, -, -, e10, e11⟩ := key_fields hk
  exact h.congr e10 e11

end BSmtLib.Facts.Proofs.Lexer.VNaiveWRustPort.Agree
