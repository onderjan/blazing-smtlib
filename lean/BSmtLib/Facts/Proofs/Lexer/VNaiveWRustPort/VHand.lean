module

public import BSmtLib.Facts.Proofs.Lexer.VNaiveWRustPort.Model
public import BSmtLib.Facts.Proofs.Lexer.Consumers.VEnd

@[expose] public section

/-!
# The naive lexer's hand-over of a lexeme, as `hand1` says

The naive lexer hands each lexeme over alone (`VNaive.handOverAt`). With the adapter's consumer
for `C`, what it does is what `hand1` says the consumer does with the lexeme, from the tokens
taken and the version and holding of the lexer state (`handOverAt_hand1`): where the consumer
goes on, the naive lexer goes on under the version the consumer is in; where it waits after a
break, or breaks with a switch to other lexical rules, the naive lexer holds the result; where it
has the rest discarded, the naive lexer discards; where it fails or the lexeme is trailing
input, the naive lexer fails.
-/

namespace BSmtLib.Facts.Proofs.Lexer.VNaiveWRustPort.VHand

open BSmtLib.Facts.Lexer.Adapters
open BSmtLibSpec.Lexer (Handed)
open BSmtLib.Facts.Proofs.Lexer.Consumers.VSteps BSmtLib.Facts.Proofs.Lexer.VNaive.Run
open BSmtLib.Facts.Proofs.Lexer.VNaiveWRustPort.Model BSmtLib.Lexer.Internal.VNaive

variable (C : BSmtLibSpec.Lexer.Consumer)

/-- The lexer state `c'` after a hand-over from `core`: the location, the activity and the
version it was created with kept, under the version `ver`, holding a result if `hold`. -/
structure VSame (core c' : Core) (ver : Token.Version) (hold : Bool) (act : Activity) : Prop where
  location : c'.location = core.location
  activity : c'.activity = act
  version : c'.version = ver
  holding : c'.holding = hold
  initial : c'.initialVersion = core.initialVersion

/-- What the naive lexer's hand-over of the lexeme gives, as `hand1` says. -/
def HandV (core : Core) (l : Lexeme)
    (r : VRes (Except (Failure (Option C.Error)) (Option (Span.Located C.Result)))) :
    HandOut C → Prop
  | .cont p => ∃ c', r = ((.ok none, c'), p.taken) ∧ VSame core c' p.ver core.holding core.activity
  | .wait v l0 p => l0 = l ∧ ∃ c', r = ((.ok (some ⟨v, l.end⟩), c'), p.taken) ∧
      VSame core c' p.ver true core.activity
  | .stop s p =>
    match s with
    | .trailing l0 => l0 = l ∧ p.ver = core.version ∧
        r = ((.error ⟨.lexical .unexpectedTrailingToken, trailingSpan l, l.start⟩, core), p.taken)
    | .fail e d l0 => l0 = l ∧ ∃ c',
        r = ((.error ⟨.consumer (some e), Span.Internal.newUnchecked l.end l.end, l.end⟩, c'),
            p.taken) ∧
        VSame core c' p.ver core.holding
          (if d then .discarding (core.activity.discardStart l.end) else core.activity)
    | .layout l0 => l0 = l ∧ ∃ c',
        r = ((.error ⟨.consumer none, Span.Internal.newUnchecked l.end l.end, l.end⟩, c'),
            p.taken) ∧
        VSame core c' p.ver core.holding core.activity
    | .brk _ _ _ => False
    | .brkX v l0 => l0 = l ∧ ∃ c', r = ((.ok (some ⟨v, l.end⟩), c'), p.taken) ∧
        VSame core c' p.ver true core.activity
    | .discard v l0 => l0 = l ∧ ∃ c', r = ((.ok (v.map (⟨·, l.end⟩)), c'), p.taken) ∧
        VSame core c' p.ver (v.isSome || core.holding) (.discarding l.end)
    | .relex l0 => l0 = l ∧ ∃ c', r = ((.ok none, c'), p.taken) ∧
        VSame core c' p.ver core.holding core.activity

theorem switchedTo_eq (ver : Token.Version) (o : Option BSmtLibSpec.Lexicon.Version) :
    (o.map toVersion).getD ver = switchedTo ver o := by
  cases o <;> rfl

/-- The naive lexer's hand-over of a lexeme is as `hand1` says. -/
theorem handOverAt_hand1 (core : Core) (l : Lexeme) (hl : l.Valid) (taken : List Handed) :
    HandV C core l (vRun C (handOverAt (H := Answering C) core l hl) taken)
      (hand1 C core.holding (.cont ⟨taken, core.version⟩) l) := by
  cases hh : core.holding with
  | true =>
    rw [handOverAt_holding C core l hl hh]
    simp only [hand1, ite_true, HandV]
    exact ⟨trivial, trivial, trivial⟩
  | false =>
    rw [handOverAt_reply C core l hl hh]
    simp only [hand1, Bool.false_eq_true, ite_false]
    unfold reply
    cases hx : lexemeEntry C.concrete core.version l with
    | none =>
      simp only [HandV]
      exact ⟨trivial, _, rfl, ⟨rfl, rfl, rfl, rfl, rfl⟩⟩
    | some x =>
      dsimp only
      cases ha : C.answer (taken ++ [x]) with
      | fail e =>
        simp only [HandV]
        rw [switchedTo_eq]
        refine ⟨trivial, _, rfl, ⟨?_, ?_, ?_, ?_, ?_⟩⟩ <;> unfold coreAfterError <;>
          split <;> rfl
      | «break» v =>
        dsimp only
        rw [switchedTo_eq]
        cases hd : C.discards (taken ++ [x]) with
        | true =>
          simp only [ite_true, HandV, coreAfter, Option.map_some, Option.isSome_some,
            Bool.true_or]
          first
            | exact ⟨_, rfl, ⟨rfl, rfl, rfl, rfl, rfl⟩⟩
            | exact ⟨trivial, _, rfl, ⟨rfl, rfl, rfl, rfl, rfl⟩⟩
        | false =>
          simp only [Bool.false_eq_true, ite_false, coreAfter]
          cases hcr : crosses core.version (switchedTo core.version (C.switchTo (taken ++ [x])))
          with
          | true =>
            simp only [ite_true, HandV]
            first
              | exact ⟨_, rfl, ⟨rfl, rfl, rfl, rfl, rfl⟩⟩
              | exact ⟨trivial, _, rfl, ⟨rfl, rfl, rfl, rfl, rfl⟩⟩
          | false =>
            simp only [Bool.false_eq_true, ite_false, HandV]
            first
              | exact ⟨_, rfl, ⟨rfl, rfl, rfl, rfl, rfl⟩⟩
              | exact ⟨trivial, _, rfl, ⟨rfl, rfl, rfl, rfl, rfl⟩⟩
      | «continue» =>
        dsimp only
        rw [switchedTo_eq]
        cases hd : C.discards (taken ++ [x]) with
        | true =>
          simp only [ite_true, HandV, coreAfter, Option.map_none, Option.isSome_none,
            Bool.false_or]
          first
            | exact ⟨_, rfl, ⟨rfl, rfl, rfl, rfl, rfl⟩⟩
            | exact ⟨trivial, _, rfl, ⟨rfl, rfl, rfl, rfl, rfl⟩⟩
        | false =>
          simp only [Bool.false_eq_true, ite_false, coreAfter]
          cases hcr : crosses core.version (switchedTo core.version (C.switchTo (taken ++ [x])))
          with
          | true =>
            simp only [ite_true, HandV]
            first
              | exact ⟨_, rfl, ⟨rfl, rfl, rfl, rfl, rfl⟩⟩
              | exact ⟨trivial, _, rfl, ⟨rfl, rfl, rfl, rfl, rfl⟩⟩
          | false =>
            simp only [Bool.false_eq_true, ite_false, HandV]
            first
              | exact ⟨_, rfl, ⟨rfl, rfl, rfl, rfl, rfl⟩⟩
              | exact ⟨trivial, _, rfl, ⟨rfl, rfl, rfl, rfl, rfl⟩⟩

end BSmtLib.Facts.Proofs.Lexer.VNaiveWRustPort.VHand
