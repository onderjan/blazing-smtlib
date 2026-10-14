import BSmtLib.Facts.Proofs.Reader.Lexes.Requests

/-!
# Lexers with consumers that answer alike

`BSmtLibSpec.Lexer.Runs` reads a consumer only through the kind of its answer after each entry, the
switch and the discarding it asks for, and whether it takes whitespace and comments. So with two
consumers that answer alike (`AnswersAlike`), a lexer correct with every consumer takes the same
tokens and finishes alike (`lexing_congr`).
-/

namespace BSmtLib.Facts.Proofs.Reader.Lexes.Congr

open BSmtLibSpec BSmtLibSpec.Lexer
open BSmtLib.Facts.Proofs.Reader.Lexes.Requests

/-- The kind of an answer. -/
def answerKind {α ε : Type} : Answer α ε → Nat
  | .continue => 0
  | .break _ => 1
  | .fail _ => 2

theorem _root_.BSmtLib.Facts.Proofs.Reader.Lexes.Requests.AnswersAlike.kind {c₁ c₂ : Consumer}
    (h : AnswersAlike c₁ c₂) (taken : List Handed) :
    Congr.answerKind (c₁.answer taken) = Congr.answerKind (c₂.answer taken) := by
  cases hc : c₁.answer taken with
  | «continue» => rw [h.cont taken hc]; rfl
  | «break» r =>
    obtain ⟨r', hr'⟩ := h.brk taken r hc
    rw [hr']; rfl
  | fail e =>
    obtain ⟨e', he'⟩ := h.fail taken e hc
    rw [he']; rfl

theorem settle_taken {α ε : Type} (start : Lexicon.Version) (taken : List Handed)
    (outcome : Outcome α ε) (version : Lexicon.Version) (d : Option BSmtLibSpec.Lexer.Location) :
    (settle start taken outcome version d).taken = taken := by
  unfold settle; split <;> rfl

theorem settle_outcome {α ε : Type} (start : Lexicon.Version) (taken : List Handed)
    (outcome : Outcome α ε) (version : Lexicon.Version) (d : Option BSmtLibSpec.Lexer.Location) :
    (settle start taken outcome version d).outcome = outcome := by
  unfold settle; split <;> rfl

/-- What two sessions that `Runs` gives for consumers that answer alike share. -/
def SameRun {α₁ ε₁ α₂ ε₂ : Type} (s₁ : Session α₁ ε₁) (s₂ : Session α₂ ε₂) : Prop :=
  s₁.taken = s₂.taken ∧ s₁.outcome.isFinished = s₂.outcome.isFinished

theorem afterBreak_finished {α ε : Type} {result : α} {location : BSmtLibSpec.Lexer.Location}
    {ready : List Handed}
    {failed : Bool} {outcome : Outcome α ε} (h : AfterBreak result location ready failed outcome) :
    outcome.isFinished = (ready.head?.map (·.type) = some .endOfFile : Bool) := by
  cases h with
  | trailing hne => simp [Outcome.isFinished, hne]
  | ends he => simp [Outcome.isFinished, he]
  | lexical => rfl
  | held => rfl

/-- A lexer that does what `Runs` states with two consumers that answer alike takes the same
tokens with both and finishes alike. -/
theorem runs_congr {feed : Lexicon.Version → List Regex.Chars → Bool → Fed} {c₁ c₂ : Consumer}
    (h : AnswersAlike c₁ c₂) {start : Lexicon.Version} {input : Regex.Chars} {ended : Bool}
    {version : Lexicon.Version} {ready : List Handed} {failed : Bool} {taken : List Handed}
    {s₁ : Session c₁.Result c₁.Error}
    (h₁ : Runs feed c₁ start input ended version ready failed taken s₁) :
    ∀ {s₂ : Session c₂.Result c₂.Error},
      Runs feed c₂ start input ended version ready failed taken s₂ → SameRun s₁ s₂ := by
  induction h₁ with
  | waiting =>
    intro s₂ h₂
    cases h₂
    exact ⟨by simp [settle_taken], by simp [settle_outcome, Outcome.isFinished]⟩
  | lexical =>
    intro s₂ h₂
    cases h₂
    exact ⟨by simp [settle_taken], by simp [settle_outcome, Outcome.isFinished]⟩
  | @fails taken token error version ready failed hf =>
    intro s₂ h₂
    have hk := h.kind (taken ++ [token])
    cases h₂ <;> first
      | (exfalso; simp_all [answerKind]; done)
      | exact ⟨by simp [settle_taken], by simp [settle_outcome, Outcome.isFinished]⟩
  | @ends taken token result version ready failed htype hb =>
    intro s₂ h₂
    have hk := h.kind (taken ++ [token])
    cases h₂ <;> first
      | (exfalso; simp_all [answerKind]; done)
      | exact ⟨by simp [settle_taken], by simp [settle_outcome, Outcome.isFinished]⟩
  | @continues taken token version ready failed session htype hcont hdisc _ ih =>
    intro s₂ h₂
    have hk := h.kind (taken ++ [token])
    have hd := congrFun h.discards (taken ++ [token])
    cases h₂ with
    | continues _ _ _ hrest =>
      rw [← h.switchTo, ← h.concrete] at hrest
      exact ih hrest
    | _ => exfalso; simp_all [answerKind]
  | @breaks taken token result ready failed outcome version htype hb hdisc hafter =>
    intro s₂ h₂
    have hk := h.kind (taken ++ [token])
    have hd := congrFun h.discards (taken ++ [token])
    cases h₂ with
    | breaks _ _ _ hafter₂ =>
      rw [← h.switchTo, ← h.concrete] at hafter₂
      refine ⟨by simp [settle_taken], ?_⟩
      simp only [settle_outcome]
      rw [afterBreak_finished hafter, afterBreak_finished hafter₂]
    | _ => exfalso; simp_all [answerKind]
  | @discardsHeld taken token result version ready failed htype hb hdisc hended =>
    intro s₂ h₂
    have hk := h.kind (taken ++ [token])
    have hd := congrFun h.discards (taken ++ [token])
    cases h₂ <;> first
      | (exfalso; simp_all [answerKind]; done)
      | exact ⟨by simp [settle_taken], by simp [settle_outcome, Outcome.isFinished]⟩
  | @discardsEnds taken token result version ready failed htype hb hdisc hended =>
    intro s₂ h₂
    have hk := h.kind (taken ++ [token])
    have hd := congrFun h.discards (taken ++ [token])
    cases h₂ <;> first
      | (exfalso; simp_all [answerKind]; done)
      | exact ⟨by simp [settle_taken], by simp [settle_outcome, Outcome.isFinished]⟩
  | @discardsWaiting taken token version ready failed htype hc hdisc hended =>
    intro s₂ h₂
    have hk := h.kind (taken ++ [token])
    have hd := congrFun h.discards (taken ++ [token])
    cases h₂ <;> first
      | (exfalso; simp_all [answerKind]; done)
      | exact ⟨by simp [settle_taken], by simp [settle_outcome, Outcome.isFinished]⟩
  | @discardsToEnd taken token result version ready failed htype hc hdisc hended hb =>
    intro s₂ h₂
    have hk := h.kind (taken ++ [token])
    have hk' := h.kind (taken ++ [token, endOfFileAt token.«end»])
    have hd := congrFun h.discards (taken ++ [token])
    cases h₂ <;> first
      | (exfalso; simp_all [answerKind]; done)
      | exact ⟨by simp [settle_taken], by simp [settle_outcome, Outcome.isFinished]⟩
  | @discardsFailsAtEnd taken token error version ready failed htype hc hdisc hended hf =>
    intro s₂ h₂
    have hk := h.kind (taken ++ [token])
    have hk' := h.kind (taken ++ [token, endOfFileAt token.«end»])
    have hd := congrFun h.discards (taken ++ [token])
    cases h₂ <;> first
      | (exfalso; simp_all [answerKind]; done)
      | exact ⟨by simp [settle_taken], by simp [settle_outcome, Outcome.isFinished]⟩

/-- A lexer correct with every consumer takes the same tokens with two consumers that answer
alike and break at the end of the input, and finishes alike. -/
theorem lexing_congr (lexing : Lexing) (hc : CorrectWithConsumers lexing) {c₁ c₂ : Consumer}
    (h : AnswersAlike c₁ c₂) (hb₁ : c₁.BreaksAtEnd) (hb₂ : c₂.BreaksAtEnd)
    (version : Lexicon.Version) (slices : List Regex.Chars) (ended : Bool) :
    SameRun (lexing c₁ version [] slices ended) (lexing c₂ version [] slices ended) := by
  have h₁ := hc.2.1 c₁ version slices ended hb₁
  have h₂ := hc.2.1 c₂ version slices ended hb₂
  rw [← h.concrete] at h₂
  exact runs_congr h h₁ h₂

end BSmtLib.Facts.Proofs.Reader.Lexes.Congr
