module

public import BSmtLib.Facts.Proofs.Reader.Param.Calls
public import BSmtLib.Facts.Proofs.Lexer.Consumers.AlikeF
import all BSmtLib.Lexer

@[expose] public section

/-!
# The adapter's consumer with a record of what went wrong

`Flagged consumer` answers exactly as the adapter's consumer `Answering consumer` does, and keeps
a record in its state:
- whether it has answered an error or been handed a cursor in another version than the one of
  the last cursor it gave back (`errored`), and that version (`version`);
- whether it has been called after something went wrong or handed such a cursor (`spoiled`);
- whether the call at which it went wrong was handed whitespace or a comment (`layout`).

The record is read by nothing but the proofs: another consumer agrees with this one only while
nothing went wrong, and at the call where it went wrong if that call was handed a cursor in its
version.

As both consumers answer alike on every cursor, the library's lexer does with one what it does
with the other (`lexing_flagged`, from the lexer's steps on two consumers,
`Calls.lexSliceStep_sim` and `Calls.lexEofStep_sim`).
-/

open BSmtLib.Lexer.Cursor (LexerCursor)

namespace BSmtLib.Facts.Proofs.Reader.Param.Flagged

open BSmtLib.Lexer
open BSmtLib.Lexer.Internal (BATCH_CAPACITY Stop Interrupted Failure LexerCore InnerM StepM LexM)
open BSmtLib.Facts.Lexer.Adapters BSmtLib.Facts.Proofs.Lexer.Consumers.AlikeF
open BSmtLib.Facts.Proofs.Reader.Param.Basic BSmtLib.Facts.Proofs.Reader.Param.Calls
open BSmtLib.Facts.Proofs.Reader.Param.HandOver BSmtLib.Lexer.Error

/-- The adapter's consumer with a record of what went wrong. -/
structure _root_.BSmtLib.Facts.Proofs.Reader.Param.Flagged
    (consumer : BSmtLibSpec.Lexer.Consumer) : Type where
  /-- Whether the consumer has answered an error, or been handed a cursor in another version than
  the one of the last cursor it gave back. -/
  errored : Bool
  /-- The version of the last cursor it gave back, or the one it started with. -/
  version : Version
  /-- Whether the consumer has been called after something went wrong, or handed a cursor in
  another version than the one of the last cursor it gave back. -/
  spoiled : Bool
  /-- Whether the call at which the consumer went wrong was handed whitespace or a comment, which
  a consumer that does not take them answers with the error `none`. -/
  layout : Bool

/-- Whether the answer is an error. -/
def isError {ε α : Type} : Except ε α → Bool
  | .error _ => true
  | .ok _ => false

/-- Whether the answer is the error `none`, which the adapter's consumer answers when it is handed
whitespace or a comment that it does not take. -/
def isLayoutAnswer {ε α : Type} : Except (Option ε) α → Bool
  | .error none => true
  | _ => false

instance (consumer : BSmtLibSpec.Lexer.Consumer) : Token.Consume (Flagged consumer) consumer.Result
    (Option consumer.Error) where
  isConcrete := consumer.concrete

/-- Takes the tokens as `Answering consumer` does, and records what went wrong. -/
def consume (consumer : BSmtLibSpec.Lexer.Consumer) {batch : Token.BatchTag}
    (cursor : LexerCursor batch) (h : cursor.HasNext) :
    StateT (Flagged consumer) AnswerM
      (Except (Option consumer.Error) (ControlFlow consumer.Result) ×
        {c : LexerCursor batch // c.Consumed cursor}) := do
  let flagged ← get
  let (answer, next) ← (Answering.consume consumer cursor h : AnswerM _)
  set ({ errored := flagged.errored || cursor.version != flagged.version || isError answer
         version := next.val.version
         spoiled := flagged.spoiled || flagged.errored || cursor.version != flagged.version
         layout := if flagged.errored then flagged.layout else isLayoutAnswer answer } :
    Flagged consumer)
  return (answer, next)

instance (consumer : BSmtLibSpec.Lexer.Consumer) {batch : Token.BatchTag} :
    Token.ConsumeFrom (Flagged consumer) (LexerCursor batch) AnswerM where
  consume cursor h := Flagged.consume consumer cursor h

/-! ## Both consumers answer alike -/

section

variable (consumer : BSmtLibSpec.Lexer.Consumer)

/-- The relator of the two consumers: run from the same tokens taken, related values and the same
tokens taken, whatever the states of the consumers. -/
def alikeRelator : Relator (Answering consumer) AnswerM (Flagged consumer) AnswerM where
  rel Q x y := ∀ a f l, Q ((x.run a).run l).1.1 ((y.run f).run l).1.1 ∧
    ((x.run a).run l).2 = ((y.run f).run l).2
  pure h _ _ _ := ⟨h, rfl⟩
  bind {_ _ _ _ _ _ x y f g} hx hk a fl l := by
    obtain ⟨h₁, h₂⟩ := hx a fl l
    have e₁ : ((x >>= f).run a).run l =
        ((f ((x.run a).run l).1.1).run ((x.run a).run l).1.2).run ((x.run a).run l).2 := rfl
    have e₂ : ((y >>= g).run fl).run l =
        ((g ((y.run fl).run l).1.1).run ((y.run fl).run l).1.2).run ((y.run fl).run l).2 := rfl
    rw [e₁, e₂, h₂]
    exact hk _ _ h₁ _ _ _
  mono hQ h a f l := ⟨hQ _ _ (h a f l).1, (h a f l).2⟩

/-- The link of the two consumers: equal results and equal errors. -/
def alikeLink : Link (Answering consumer) AnswerM consumer.Result (Option consumer.Error)
    (Flagged consumer) AnswerM consumer.Result (Option consumer.Error) where
  rc := alikeRelator consumer
  rr := (· = ·)
  re := (· = ·)

theorem eRel_refl {ε α : Type} (r : Except ε (ControlFlow α)) :
    ERel (· = ·) (FlowRel (· = ·)) r r := by
  rcases r with e | (_ | v)
  · rfl
  · trivial
  · rfl

theorem alike_calls : HandOver.Calls (alikeLink consumer) where
  concrete := rfl
  consume cursor h a f l := by
    show _ ∧ (((Answering.consume consumer cursor h : AnswerM _).run l).2) = _
    refine ⟨⟨?_, rfl⟩, rfl⟩
    exact eRel_refl _

theorem alike_consumers : Consumers (alikeLink consumer) :=
  .ofCalls (alike_calls consumer)

end

/-! ## Equal results -/

theorem cause_eq {ε : Type} {a b : LexerErrorCause ε} (h : CauseRel (· = ·) a b) : a = b := by
  rcases a with a | a <;> rcases b with b | b <;> first | exact absurd h id | cases h; rfl

/-- Lexer errors related as `LexErrRel (· = ·)` are the same to the formalism. -/
theorem failureOf_eq_of_rel {ε : Type} {a b : LexerError (Option ε)}
    (h : LexErrRel (· = ·) a b) : failureOf a = failureOf b := by
  unfold failureOf
  rw [cause_eq h.1, h.2.1]

theorem sliceRel_eq {ε α : Type} {a b : Except (LexerError (Option ε)) (Option (Span.Located α))}
    (h : ERel (LexErrRel (· = ·)) (ORel (LocRel (· = ·))) a b) :
    a.mapError failureOf = b.mapError failureOf := by
  rcases a with e | (_ | ⟨v, l⟩) <;> rcases b with e' | (_ | ⟨v', l'⟩) <;>
    first | exact absurd h id | skip
  · simp only [Except.mapError, failureOf_eq_of_rel h]
  · rfl
  · obtain ⟨hv, hl⟩ := h
    simp only at hv hl
    rw [hv, hl]

theorem eofRel_eq {ε α : Type} {a b : Except (LexerError (Option ε)) (ControlFlow (Span.Located α))}
    (h : ERel (LexErrRel (· = ·)) (FlowRel (LocRel (· = ·))) a b) :
    a.mapError failureOf = b.mapError failureOf := by
  rcases a with e | (_ | ⟨v, l⟩) <;> rcases b with e' | (_ | ⟨v', l'⟩) <;>
    first | exact absurd h id | skip
  · simp only [Except.mapError, failureOf_eq_of_rel h]
  · rfl
  · obtain ⟨hv, hl⟩ := h
    simp only at hv hl
    rw [hv, hl]

/-! ## The two lexers as the adapter feeds them -/

/-- The library's lexer with the consumer `Flagged consumer`, which starts with nothing gone
wrong, for every consumer of the formalism. -/
def flaggedOps : LexOps where
  Lexer consumer := BSmtLib.Lexer (Flagged consumer)
  AfterError consumer := BSmtLib.Lexer.AfterError (Flagged consumer) Lexer.Recovery.FailFast
  AfterEofError consumer := BSmtLib.Lexer.AfterEofError (Flagged consumer) Lexer.Recovery.FailFast
  new _ _ version :=
    BSmtLib.Lexer.new { errored := false, version, spoiled := false, layout := false } version
  lexSlice := BSmtLib.Lexer.lexSlice
  lexEof := BSmtLib.Lexer.lexEof
  lexSliceStep lexer slice :=
    BSmtLib.Lexer.Internal.run lexer (BSmtLib.Lexer.Internal.lexSliceStep
      (Recovery.LexerRecovery.abandon Recovery.FailFast)
          (Recovery.LexerRecovery.recover Recovery.FailFast) slice)
  lexEofStep lexer :=
    BSmtLib.Lexer.Internal.run lexer (BSmtLib.Lexer.Internal.lexEofStep
      (Recovery.LexerRecovery.abandon Recovery.FailFast)
          (Recovery.LexerRecovery.recover Recovery.FailFast))
  held := BSmtLib.Lexer.Internal.held
  withHeld := BSmtLib.Lexer.Internal.withHeld
  version := BSmtLib.Lexer.version
  discardedFrom := BSmtLib.Lexer.discardedFrom

section

variable {H : Type} {R E : Type} [Token.Consume H R E] {α : Type}

/-- A run of a step on the library's lexer in the adapter's monad, by the parts of the lexer. -/
theorem run_answerM (lexer : BSmtLib.Lexer H) (step : InnerM H AnswerM α)
    (taken : List BSmtLibSpec.Lexer.Handed) :
    (BSmtLib.Lexer.Internal.run lexer step).run taken =
      let r := ((step.run (Internal.core lexer)).run (Internal.handler lexer)).run taken
      ((r.1.1.1, Internal.ofParts r.1.2 r.1.1.2 (Internal.held lexer)), r.2) := (rfl)

theorem core_ofParts (h : H) (c : LexerCore) (d : Option (Span.Located R)) :
    Internal.core (Internal.ofParts h c d : BSmtLib.Lexer H) = c := (rfl)

theorem held_ofParts (h : H) (c : LexerCore) (d : Option (Span.Located R)) :
    Internal.held (Internal.ofParts h c d : BSmtLib.Lexer H) = d := (rfl)

end

/-- Lexers with the two consumers with the same state and the same held result. -/
def AlikeLexers (consumer : BSmtLibSpec.Lexer.Consumer) (a : Lexer.lexOps.Lexer consumer)
    (b : flaggedOps.Lexer consumer) : Prop :=
  Internal.core a = Internal.core b ∧ Internal.held a = Internal.held b

theorem recovery_alike (consumer : BSmtLibSpec.Lexer.Consumer) (l : Span.Location) :
    (alikeLink consumer).rc.rel (· = ·)
      (Recovery.LexerRecovery.abandon (H := Answering consumer) (m := AnswerM) Recovery.FailFast l)
      (Recovery.LexerRecovery.abandon (H := Flagged consumer) (m := AnswerM) Recovery.FailFast l) :=
  fun _ _ _ => ⟨rfl, rfl⟩

theorem recover_alike (consumer : BSmtLibSpec.Lexer.Consumer) (l : Span.Location) :
    (alikeLink consumer).rc.rel (· = ·)
      (Recovery.LexerRecovery.recover (H := Answering consumer) (m := AnswerM) Recovery.FailFast l)
      (Recovery.LexerRecovery.recover (H := Flagged consumer) (m := AnswerM) Recovery.FailFast l) :=
  fun _ _ _ => ⟨rfl, rfl⟩

/-- The call on a slice does with the two consumers what it does with the other, from lexers
alike. -/
theorem slice_alikeF (consumer : BSmtLibSpec.Lexer.Consumer) (slice : BSmtLibSpec.Regex.Chars) :
    StepsAlikeF Lexer.lexOps flaggedOps (AlikeLexers consumer)
      (fun a b => Internal.core a = Internal.core b)
      (fun a => Lexer.lexOps.lexSliceStep a slice.toByteArray.toByteSlice)
      (fun b => flaggedOps.lexSliceStep b slice.toByteArray.toByteSlice) := by
  intro a b taken hab
  have hsim := lexSliceStep_sim (alike_consumers consumer)
    (Recovery.LexerRecovery.abandon (H := Answering consumer) (m := AnswerM) Recovery.FailFast)
    (Recovery.LexerRecovery.recover (H := Answering consumer) (m := AnswerM) Recovery.FailFast)
    (Recovery.LexerRecovery.abandon (H := Flagged consumer) (m := AnswerM) Recovery.FailFast)
    (Recovery.LexerRecovery.recover (H := Flagged consumer) (m := AnswerM) Recovery.FailFast)
    (recovery_alike consumer) (recover_alike consumer) slice.toByteArray.toByteSlice
        (Internal.core a)
    (Internal.handler a) (Internal.handler b)
    taken
  obtain ⟨⟨hr, hc⟩, ht⟩ := hsim
  simp only [Lexer.lexOps, flaggedOps]
  rw [run_answerM (H := Answering consumer) a, run_answerM (H := Flagged consumer) b,
    ← hab.1]
  exact ⟨sliceRel_eq hr, ht, fun _ => ⟨hc, hab.2⟩, hc⟩

/-- The end of the input does with the two consumers what it does with the other, from lexers
alike. -/
theorem eof_alikeF (consumer : BSmtLibSpec.Lexer.Consumer) :
    StepsAlikeF Lexer.lexOps flaggedOps (AlikeLexers consumer)
      (fun a b => Internal.core a = Internal.core b)
      Lexer.lexOps.lexEofStep flaggedOps.lexEofStep := by
  intro a b taken hab
  have hsim := lexEofStep_sim (alike_consumers consumer)
    (Recovery.LexerRecovery.abandon (H := Answering consumer) (m := AnswerM) Recovery.FailFast)
    (Recovery.LexerRecovery.recover (H := Answering consumer) (m := AnswerM) Recovery.FailFast)
    (Recovery.LexerRecovery.abandon (H := Flagged consumer) (m := AnswerM) Recovery.FailFast)
    (Recovery.LexerRecovery.recover (H := Flagged consumer) (m := AnswerM) Recovery.FailFast)
    (recovery_alike consumer) (recover_alike consumer) (Internal.core a) (Internal.handler a)
        (Internal.handler b) taken
  obtain ⟨⟨hr, hc⟩, ht⟩ := hsim
  simp only [Lexer.lexOps, flaggedOps]
  rw [run_answerM (H := Answering consumer) a, run_answerM (H := Flagged consumer) b,
    ← hab.1]
  exact ⟨eofRel_eq hr, ht, fun _ => ⟨hc, hab.2⟩, hc⟩

/-- The library's lexer does with `Flagged consumer` what it does with `Answering consumer`, for
every consumer of the formalism. -/
theorem lexing_flagged : lexing Lexer.lexOps = lexing flaggedOps :=
  lexing_alikeF Lexer.lexOps flaggedOps AlikeLexers
      (fun _ a b => Internal.core a = Internal.core b)
    (fun _ _ => ⟨rfl, rfl⟩) slice_alikeF eof_alikeF (fun _ _ _ h => h.2)
    (fun _ _ _ _ h => ⟨h.1, rfl⟩)
    (fun _ _ _ h => h.1)
    (fun _ _ _ h => congrArg LexerCore.version h)
    (fun _ _ _ h => congrArg LexerCore.discardedFrom h)

end BSmtLib.Facts.Proofs.Reader.Param.Flagged
