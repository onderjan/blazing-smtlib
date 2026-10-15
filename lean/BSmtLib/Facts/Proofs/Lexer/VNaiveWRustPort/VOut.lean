module

public import BSmtLib.Facts.Proofs.Lexer.VNaiveWRustPort.VHand
public import BSmtLib.Facts.Proofs.Lexer.Consumers.VHold
import all BSmtLib.Lexer.Internal.VNaive
import all BSmtLib.Span
import all BSmtLib.Lexer.Error

@[expose] public section

/-!
# What the naive lexer does with the bytes, as the outcome says

`VOut` states what the naive lexer does with bytes, from a lexer state holding a result with the
tokens taken, as an outcome of the pure run (`outcome`) says: where the run ends, the naive lexer
ends in the pure run's state; where the run fails, it fails with the lexical error; where the
consumer stops, it fails, holds the result, discards or starts again after the lexeme of the
stop (`Restarts`).
-/

namespace BSmtLib.Facts.Proofs.Lexer.VNaiveWRustPort.VOut

open BSmtLibSpec.Lexer (Handed)
open BSmtLib.Facts.Proofs.Lexer.Consumers.Pure BSmtLib.Facts.Proofs.Lexer.Consumers.VSession
open BSmtLib.Facts.Proofs.Lexer.Consumers.VSteps BSmtLib.Facts.Proofs.Lexer.VNaive.Facts
open BSmtLib.Facts.Proofs.Lexer.VNaiveWRustPort.Model BSmtLib.Lexer.Error
open BSmtLib.Lexer.Internal.VNaive

theorem start_legacy {v1 v2 : Token.Version} (hv : (v1 == .v2_0) = (v2 == .v2_0)) :
    start v1 = start v2 := by
  funext ws loc c
  simp only [start, hv]

theorem startStepW_legacy {v1 v2 : Token.Version} (hv : (v1 == .v2_0) = (v2 == .v2_0)) :
    startStepW v1 = startStepW v2 := by
  funext ws loc c
  simp only [startStepW, start_legacy hv]

theorem byteStepW_legacy {v1 v2 : Token.Version} (hv : (v1 == .v2_0) = (v2 == .v2_0)) :
    byteStepW v1 = byteStepW v2 := by
  funext ws st loc c
  cases st <;> simp only [byteStepW, startStepW_legacy hv]

theorem lexBytesW_legacy {v1 v2 : Token.Version} (hv : (v1 == .v2_0) = (v2 == .v2_0)) :
    lexBytesW v1 = lexBytesW v2 := by
  funext ws st loc bs
  induction bs generalizing st loc with
  | nil => rfl
  | cons c bs ih => simp only [lexBytesW, byteStepW_legacy hv, ih]

variable (C : BSmtLibSpec.Lexer.Consumer)

/-- The lexer state `c'` is the naive lexer's state at the end of a run that went on: the
activity, the version, holding and the version it was created with. -/
structure VEnd' (core c' : Core) (act : Activity) (ver : Token.Version) (hold : Bool) : Prop where
  activity : c'.activity = act
  version : c'.version = ver
  holding : c'.holding = hold
  initial : c'.initialVersion = core.initialVersion

/-- The naive lexer, from `core` holding `held` with the tokens `taken`, fed the bytes, starts
again after the lexeme `l` in the state `c''`, holding `held'`, with the tokens `taken'`: the
bytes after `l` are those after the first `k`. -/
def Restarts (core : Core) (held : Option (Span.Located C.Result)) (bs : List UInt8)
    (taken : List Handed) (l : Lexeme) (ver : Token.Version) (hold : Bool)
    (held' : Option (Span.Located C.Result)) (taken' : List Handed) : Prop :=
  ∃ k c'', l.end = advanceLoc core.location (bs.take k) ∧ c''.activity = .idle ∧
    c''.location = l.end ∧ c''.version = ver ∧ c''.holding = hold ∧
    c''.initialVersion = core.initialVersion ∧
    vBytes C core held bs taken = vBytes C c'' held' (bs.drop k) taken'

/-- The naive lexer, from `core` holding `held` with the tokens `taken`, fed the bytes, fails
with the lexeme `l` as trailing input, with the consumer having done `p`. -/
def VTrailing (core : Core) (held : Option (Span.Located C.Result)) (bs : List UInt8)
    (taken : List Handed) (l : Lexeme) (p : Prog) : Prop :=
  ∃ c', vBytes C core held bs taken =
    ((.error ⟨.lexical .unexpectedTrailingToken, trailingSpan l, l.start⟩, c'), p.taken) ∧
    c'.version = p.ver ∧
    c'.initialVersion = core.initialVersion ∧ ∀ s, c'.activity ≠ .discarding s

/-- What the naive lexer does with the bytes, from `core` holding `held` with the tokens
`taken`, as the outcome of the pure run says. -/
def _root_.BSmtLib.Facts.Proofs.Lexer.VNaiveWRustPort.VOut (core : Core)
    (held : Option (Span.Located C.Result)) (bs : List UInt8)
    (taken : List Handed) : Out C → Prop
  | .endOk st loc p => ∃ c', vBytes C core held bs taken = ((.ok held, c'), p.taken) ∧
      VOut.VEnd' core c' st.activity p.ver core.holding ∧ c'.location = loc
  | .endErr f p => ∃ c' : Core,
      vBytes C core held bs taken = ((.error ⟨.lexical f.kind, f.span, f.location⟩, c'), p.taken) ∧
      f.kind ≠ .unexpectedTrailingToken ∧ c'.version = p.ver ∧
      c'.initialVersion = core.initialVersion ∧ ∀ s, c'.activity ≠ .discarding s
  | .stopped s p =>
    match s with
    | .trailing l => VOut.VTrailing C core held bs taken l p
    | .fail e d l => ∃ c' span loc, vBytes C core held bs taken =
        ((.error ⟨.consumer (some e), span, loc⟩, c'), p.taken) ∧ c'.version = p.ver ∧
        c'.initialVersion = core.initialVersion ∧
        discardedOf c' = (Stop.fail (C := C) e d l).discards
    | .layout _ => ∃ c' span loc, vBytes C core held bs taken =
        ((.error ⟨.consumer none, span, loc⟩, c'), p.taken) ∧ c'.version = p.ver ∧
        c'.initialVersion = core.initialVersion ∧ ∀ s, c'.activity ≠ .discarding s
    | .brk v l nx =>
      VOut.Restarts C core held bs taken l p.ver true (some (Span.Located.Internal.new v l.end))
        p.taken ∧
        ∀ l2, nx = some l2 → VOut.VTrailing C core held bs taken l2 p
    | .brkX v l =>
      VOut.Restarts C core held bs taken l p.ver true (some (Span.Located.Internal.new v l.end))
        p.taken
    | .discard v l => ∃ c', vBytes C core held bs taken =
        ((.ok ((v.map (Span.Located.Internal.new · l.end)).or held), c'), p.taken) ∧
        VOut.VEnd' core c' (.discarding l.end) p.ver (v.isSome || core.holding) ∧
        c'.location = l.end ∧
        ∃ k, l.end = advanceLoc core.location (bs.take k)
    | .relex l => VOut.Restarts C core held bs taken l p.ver core.holding held p.taken

variable {C}

/-- What the naive lexer does after a byte it lexed without a hand-over or after a hand-over that
went on is what it does from there. -/
theorem cons {core c' : Core} {held : Option (Span.Located C.Result)} {c : UInt8}
    {rest : List UInt8} {taken taken' : List Handed} (O : Out C)
    (hv : vBytes C core held (c :: rest) taken = vBytes C c' held rest taken')
    (hh : c'.holding = core.holding) (hi : c'.initialVersion = core.initialVersion)
    (hl : c'.location = core.location.afterByte c) (h : VOut C c' held rest taken' O) :
    VOut C core held (c :: rest) taken O := by
  have hr : ∀ {l ver hold held' tk}, Restarts C c' held rest taken' l ver hold held' tk →
      Restarts C core held (c :: rest) taken l ver hold held' tk := by
    intro l ver hold held' tk ⟨k, c'', h1, h2, h3, h4, h5, h6, h7⟩
    refine ⟨k + 1, c'', ?_, h2, h3, h4, h5, h6.trans hi, by rw [hv, h7]; rfl⟩
    rw [h1, hl]
    rfl
  have ht : ∀ {l p}, VTrailing C c' held rest taken' l p →
      VTrailing C core held (c :: rest) taken l p := by
    intro l p ⟨c2, e, a1, a2, a3⟩
    exact ⟨c2, hv.trans e, a1, a2.trans hi, a3⟩
  rcases O with ⟨st, loc, p⟩ | ⟨f, p⟩ | ⟨s, p⟩
  · obtain ⟨c2, e, ⟨a1, a2, a3, a4⟩, a5⟩ := h
    exact ⟨c2, hv.trans e, ⟨a1, a2, a3.trans hh, a4.trans hi⟩, a5⟩
  · obtain ⟨c2, e, a1, a2, a3, a4⟩ := h
    exact ⟨c2, hv.trans e, a1, a2, a3.trans hi, a4⟩
  · cases s with
    | trailing l => exact ht h
    | fail e d l =>
      obtain ⟨c2, span, loc, e, a1, a2, a3⟩ := h
      exact ⟨c2, span, loc, hv.trans e, a1, a2.trans hi, a3⟩
    | layout l =>
      obtain ⟨c2, span, loc, e, a1, a2, a3⟩ := h
      exact ⟨c2, span, loc, hv.trans e, a1, a2.trans hi, a3⟩
    | brk v l nx => exact ⟨hr h.1, fun l2 hl2 => ht (h.2 l2 hl2)⟩
    | brkX v l => exact hr h
    | discard v l =>
      obtain ⟨c2, e, ⟨a1, a2, a3, a4⟩, a5, k, a6⟩ := h
      refine ⟨c2, hv.trans e, ⟨a1, a2, by rw [a3, hh], a4.trans hi⟩, a5, k + 1, ?_⟩
      rw [a6, hl]
      rfl
    | relex l =>
      have := hr h
      rw [hh] at this
      exact this

/-- What the naive lexer does from a state at the same location, over the same bytes. -/
theorem same {core c' : Core} {held : Option (Span.Located C.Result)} {bs : List UInt8}
    {taken taken' : List Handed} (O : Out C)
    (hv : vBytes C core held bs taken = vBytes C c' held bs taken')
    (hh : c'.holding = core.holding) (hi : c'.initialVersion = core.initialVersion)
    (hl : c'.location = core.location) (h : VOut C c' held bs taken' O) :
    VOut C core held bs taken O := by
  have hr : ∀ {l ver hold held' tk}, Restarts C c' held bs taken' l ver hold held' tk →
      Restarts C core held bs taken l ver hold held' tk := by
    intro l ver hold held' tk ⟨k, c'', h1, h2, h3, h4, h5, h6, h7⟩
    exact ⟨k, c'', by rw [h1, hl], h2, h3, h4, h5, h6.trans hi, by rw [hv, h7]⟩
  have ht : ∀ {l p}, VTrailing C c' held bs taken' l p →
      VTrailing C core held bs taken l p := by
    intro l p ⟨c2, e, a1, a2, a3⟩
    exact ⟨c2, hv.trans e, a1, a2.trans hi, a3⟩
  rcases O with ⟨st, loc, p⟩ | ⟨f, p⟩ | ⟨s, p⟩
  · obtain ⟨c2, e, ⟨a1, a2, a3, a4⟩, a5⟩ := h
    exact ⟨c2, hv.trans e, ⟨a1, a2, a3.trans hh, a4.trans hi⟩, a5⟩
  · obtain ⟨c2, e, a1, a2, a3, a4⟩ := h
    exact ⟨c2, hv.trans e, a1, a2, a3.trans hi, a4⟩
  · cases s with
    | trailing l => exact ht h
    | fail e d l =>
      obtain ⟨c2, span, loc, e, a1, a2, a3⟩ := h
      exact ⟨c2, span, loc, hv.trans e, a1, a2.trans hi, a3⟩
    | layout l =>
      obtain ⟨c2, span, loc, e, a1, a2, a3⟩ := h
      exact ⟨c2, span, loc, hv.trans e, a1, a2.trans hi, a3⟩
    | brk v l nx => exact ⟨hr h.1, fun l2 hl2 => ht (h.2 l2 hl2)⟩
    | brkX v l => exact hr h
    | discard v l =>
      obtain ⟨c2, e, ⟨a1, a2, a3, a4⟩, a5, k, a6⟩ := h
      exact ⟨c2, hv.trans e, ⟨a1, a2, by rw [a3, hh], a4.trans hi⟩, a5, k,
        by rw [a6, hl]⟩
    | relex l =>
      have := hr h
      rw [hh] at this
      exact this

end BSmtLib.Facts.Proofs.Lexer.VNaiveWRustPort.VOut
