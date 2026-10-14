import BSmtLib.Facts.Proofs.Lexer.Consumers.Pure

/-!
# The pure run for a consumer that takes whitespace and comments

The naive lexer's pure run for a consumer that takes whitespace and comments finishes the same
lexemes as the run for one that does not, and between them the lexemes of whitespace and
comments: the run with the flag on, with those lexemes left out, is the run with the flag off
(`lexBytes_plain`, `endStep_plain`), step by step (`byteStep_plain`).
-/

namespace BSmtLib.Facts.Proofs.Lexer.Consumers.Layout

open BSmtLib.Facts.Lexer.Adapters
open BSmtLib.Facts.Proofs.Lexer.Consumers.Pure BSmtLib.Facts.Proofs.Lexer.VNaive.Prefix
open BSmtLib.Facts.Proofs.Lexer.VNaive.Prefix.Lexeme BSmtLib.Facts.Proofs.Lexer.VNaive.Run
open BSmtLib.Lexer.Internal.VNaive

theorem start_ws_eq {version : Token.Version} {location : Span.Location} {c : UInt8}
    (h : isWhitespace c = false) :
    start version true location c = start version false location c := by
  simp only [start, h, Bool.false_eq_true, ite_false]

theorem start_ws_true {version : Token.Version} {location : Span.Location} {c : UInt8}
    (h : isWhitespace c = true) :
    start version true location c =
      .pending { mode := .whitespace, start := location, content := ByteArray.empty.push c } ∧
    start version false location c = .idle := by
  simp [start, h]

theorem advance_ws_eq {p : Pending} {location : Span.Location} {c : UInt8}
    (hc : p.mode ≠ .comment) :
    advance true p location c = advance false p location c := by
  cases hm : p.mode <;> simp only [advance, hm] <;> simp_all

/-- The comment that the line break `c` ends. -/
def commentLexeme (p : Pending) (location : Span.Location) (c : UInt8) : Lexeme :=
  { category := .comment, content := p.content.push c, start := p.start,
    «end» := location.afterByte c }

theorem advance_ws_comment {p : Pending} {location : Span.Location} {c : UInt8}
    (hc : p.mode = .comment) :
    (advance true p location c = advance false p location c) ∨
    ((c == byte! '\n' || c == byte! '\r') = true ∧
      advance true p location c = .tokenWith (commentLexeme p location c) ∧
      advance false p location c = .idle) := by
  by_cases h : (c == byte! '\n' || c == byte! '\r') = true
  · right
    simp only [advance, hc, h, ite_true]
    exact ⟨trivial, rfl, rfl⟩
  · left
    simp only [advance, hc, h, Bool.false_eq_true, ite_false]

theorem finish_ws_eq {p : Pending} {location : Span.Location} (hc : p.mode ≠ .comment) :
    finish true p location = finish false p location := by
  cases hm : p.mode <;> simp only [finish, hm] <;> simp_all

/-- The lexemes of the lexemes that a consumer that does not take whitespace and comments is
handed: all but whitespace and comments. -/
def plainOf (ls : List Lexeme) : List Lexeme :=
  ls.filter fun l => (toTokenType l.category).isSome

theorem plainOf_append (a b : List Lexeme) : plainOf (a ++ b) = plainOf a ++ plainOf b :=
  List.filter_append _ _

theorem plainOf_of_taken {ls : List Lexeme} (h : ∀ l ∈ ls, (Taken l)) : plainOf ls = ls :=
  List.filter_eq_self.mpr h

/-- The state of the run for a consumer that takes whitespace and comments, and the state of
the run for one that does not, at the same byte: the same, except that whitespace in progress in
the first is nothing in progress in the second. -/
def PlainOf : St → St → Prop
  | .idle, .idle => True
  | .token p, .idle => p.mode = .whitespace
  | .token p, .token q => p = q ∧ p.mode ≠ .whitespace
  | .idle, .token _ => False

/-- The outcomes of the two pure steps, related as `PlainOf` relates their states. -/
def StepPlain : Option (St × List Lexeme) → Option (St × List Lexeme) → Prop
  | none, none => True
  | some (stW, lsW), some (stP, lsP) => PlainOf stW stP ∧ plainOf lsW = lsP
  | _, _ => False

theorem startStep_plain (version : Token.Version) (location : Span.Location) (c : UInt8) :
    StepPlain (startStepW version true location c) (startStepW version false location c) := by
  cases hw : isWhitespace c with
  | true =>
    obtain ⟨h1, h2⟩ := start_ws_true (version := version) (location := location) hw
    simp only [startStepW, h1, h2, StepPlain, PlainOf, plainOf, List.filter_nil, and_self]
  | false =>
    simp only [startStepW, start_ws_eq hw]
    cases hs : start version false location c with
    | idle => exact ⟨trivial, rfl⟩
    | pending p => exact ⟨⟨rfl, start_taken hs⟩, rfl⟩
    | token l => exact ⟨trivial, plainOf_of_taken (by simpa using (start_paren hs).1)⟩
    | error f => trivial

theorem stepPlain_cons {l : Lexeme} {a b : Option (St × List Lexeme)} (h : StepPlain a b)
    (hl : (Taken l)) :
    StepPlain (a.map fun (st, ls) => (st, l :: ls)) (b.map fun (st, ls) => (st, l :: ls)) := by
  have hl' : (toTokenType l.category).isSome = true := hl
  cases a with
  | none => cases b with
    | none => trivial
    | some _ => exact h.elim
  | some x => cases b with
    | none => exact h.elim
    | some y =>
      obtain ⟨stW, lsW⟩ := x
      obtain ⟨stP, lsP⟩ := y
      obtain ⟨h1, h2⟩ := h
      refine ⟨h1, ?_⟩
      simp only [plainOf, List.filter_cons, hl', ite_true] at h2 ⊢
      rw [h2]

theorem stepPlain_layout {l : Lexeme} {a b : Option (St × List Lexeme)} (h : StepPlain a b)
    (hl : (toTokenType l.category).isSome = false) :
    StepPlain (a.map fun (st, ls) => (st, l :: ls)) b := by
  cases a with
  | none => cases b with
    | none => trivial
    | some _ => exact h.elim
  | some x => cases b with
    | none => exact h.elim
    | some y =>
      obtain ⟨h1, h2⟩ := h
      refine ⟨h1, ?_⟩
      simp only [plainOf, List.filter_cons, hl, Bool.false_eq_true, ite_false] at h2 ⊢
      exact h2

theorem byteStep_plain (version : Token.Version) {stW stP : St} (h : PlainOf stW stP)
    (location : Span.Location) (c : UInt8) :
    StepPlain (byteStepW version true stW location c) (byteStepW version false stP location c) := by
  cases stW with
  | idle =>
    cases stP with
    | idle => exact startStep_plain version location c
    | token q => exact h.elim
  | token p =>
    cases stP with
    | idle =>
      -- whitespace in progress for the first, nothing for the second
      have hm : p.mode = .whitespace := h
      cases hw : isWhitespace c with
      | true =>
        have h2 := (start_ws_true (version := version) (location := location) hw).2
        simp only [byteStepW, startStepW, advance, hm, hw, ite_true, h2]
        exact ⟨rfl, rfl⟩
      | false =>
        simp only [byteStepW, advance, hm, hw, Bool.false_eq_true, ite_false]
        have := startStep_plain version location c
        simp only [startStepW, start_ws_eq hw] at this ⊢
        exact stepPlain_layout this rfl
    | token q =>
      obtain ⟨rfl, hp⟩ := h
      by_cases hc : p.mode = .comment
      · rcases advance_ws_comment (location := location) (c := c) hc with he | ⟨_, h1, h2⟩
        · simp only [byteStepW, he]
          cases ha : advance false p location c with
          | pending p' => exact ⟨⟨rfl, advance_taken ha hp⟩, rfl⟩
          | idle => exact ⟨trivial, rfl⟩
          | tokenWith l => exact (advance_not_tokenWith ha).elim
          | tokenBefore l =>
            exact stepPlain_cons (startStep_plain version location c)
              (advance_tokenBefore_taken ha hp).2
          | error f => trivial
        · simp only [byteStepW, h1, h2]
          exact ⟨trivial, rfl⟩
      · simp only [byteStepW, advance_ws_eq hc]
        cases ha : advance false p location c with
        | pending p' => exact ⟨⟨rfl, advance_taken ha hp⟩, rfl⟩
        | idle => exact ⟨trivial, rfl⟩
        | tokenWith l => exact (advance_not_tokenWith ha).elim
        | tokenBefore l =>
          exact stepPlain_cons (startStep_plain version location c)
            (advance_tokenBefore_taken ha hp).2
        | error f => trivial

theorem failedBefore_plain (version : Token.Version) {stW stP : St} (h : PlainOf stW stP)
    (location : Span.Location) (c : UInt8) (hP : byteStepW version false stP location c = none) :
    plainOf (failedBeforeW true stW location c) = failedBeforeW false stP location c := by
  cases stW with
  | idle =>
    cases stP with
    | idle => rfl
    | token q => exact h.elim
  | token p =>
    cases stP with
    | idle =>
      have hm : p.mode = .whitespace := h
      simp only [failedBeforeW, advance, hm]
      cases isWhitespace c <;> simp only [ite_true, ite_false, Bool.false_eq_true] <;> rfl
    | token q =>
      obtain ⟨rfl, hp⟩ := h
      rw [failedBeforeW_false,
        failedBefore_nil (st := .token p) (by rwa [byteStepW_false] at hP) hp]
      simp only [failedBeforeW]
      by_cases hc : p.mode = .comment
      · rcases advance_ws_comment (location := location) (c := c) hc with he | ⟨_, h1, _⟩
        · rw [he]
          cases ha : advance false p location c with
          | tokenBefore l =>
            have hd := (advance_tokenBefore_taken ha hp).1
            simp only [byteStepW_false, byteStep, ha, startStep] at hP
            cases hs : start version false location c with
            | error f => exact absurd hs (start_delimiter hd f)
            | _ => simp [hs] at hP
          | _ => rfl
        · rw [h1]
          rfl
      · rw [advance_ws_eq hc]
        cases ha : advance false p location c with
        | tokenBefore l =>
          have hd := (advance_tokenBefore_taken ha hp).1
          simp only [byteStepW_false, byteStep, ha, startStep] at hP
          cases hs : start version false location c with
          | error f => exact absurd hs (start_delimiter hd f)
          | _ => simp [hs] at hP
        | _ => rfl

/-- The outcomes of the two pure runs, related as `PlainOf` relates their states. -/
def RunPlain : Except (List Lexeme) (St × Span.Location × List Lexeme) →
    Except (List Lexeme) (St × Span.Location × List Lexeme) → Prop
  | .ok (stW, locW, lsW), .ok (stP, locP, lsP) => PlainOf stW stP ∧ locW = locP ∧ plainOf lsW = lsP
  | .error lsW, .error lsP => plainOf lsW = lsP
  | _, _ => False

theorem runPlain_withBefore {lsW lsP : List Lexeme}
    {a b : Except (List Lexeme) (St × Span.Location × List Lexeme)} (h : RunPlain a b)
    (hl : plainOf lsW = lsP) : RunPlain (withBefore lsW a) (withBefore lsP b) := by
  cases a with
  | ok x => cases b with
    | ok y =>
      obtain ⟨stW, locW, lsW'⟩ := x
      obtain ⟨stP, locP, lsP'⟩ := y
      obtain ⟨h1, h2, h3⟩ := h
      exact ⟨h1, h2, by rw [plainOf_append, hl, h3]⟩
    | error _ => exact h.elim
  | error x => cases b with
    | ok _ => exact h.elim
    | error y => show plainOf (lsW ++ x) = lsP ++ y; rw [plainOf_append, hl, h]

theorem lexBytes_plain (version : Token.Version) (bytes : List UInt8) :
    ∀ {stW stP : St} (location : Span.Location), PlainOf stW stP →
      RunPlain (lexBytesW version true stW location bytes)
        (lexBytesW version false stP location bytes) := by
  induction bytes with
  | nil => intro stW stP location h; exact ⟨h, rfl, rfl⟩
  | cons c bytes ih =>
    intro stW stP location h
    have hs := byteStep_plain version h location c
    simp only [lexBytesW]
    cases hW : byteStepW version true stW location c with
    | none =>
      cases hP : byteStepW version false stP location c with
      | none => exact failedBefore_plain version h location c hP
      | some _ => rw [hW, hP] at hs; exact hs.elim
    | some x =>
      cases hP : byteStepW version false stP location c with
      | none => rw [hW, hP] at hs; exact hs.elim
      | some y =>
        rw [hW, hP] at hs
        obtain ⟨stW', lsW⟩ := x
        obtain ⟨stP', lsP⟩ := y
        obtain ⟨h1, h2⟩ := hs
        exact runPlain_withBefore (ih _ h1) h2

theorem endStep_plain {stW stP : St} (h : PlainOf stW stP) (location : Span.Location) :
    match endStepW true stW location, endStepW false stP location with
    | some lsW, some lsP => plainOf lsW = lsP
    | none, none => True
    | _, _ => False := by
  cases stW with
  | idle =>
    cases stP with
    | idle => rfl
    | token q => exact h.elim
  | token p =>
    cases stP with
    | idle =>
      have hm : p.mode = .whitespace := h
      simp only [endStepW, finish, hm]
      rfl
    | token q =>
      obtain ⟨rfl, hp⟩ := h
      by_cases hc : p.mode = .comment
      · simp only [endStepW, finish, hc, ite_true, Bool.false_eq_true, ite_false]
        rfl
      · simp only [endStepW, finish_ws_eq hc]
        cases hf : finish false p location with
        | none => rfl
        | token l =>
          refine plainOf_of_taken (endStep_taken (st := .token p) (location := location) ?_ hp)
          simp only [endStep, hf]
        | error f => trivial

end BSmtLib.Facts.Proofs.Lexer.Consumers.Layout
