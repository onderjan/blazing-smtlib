module

public import BSmtLib.Facts.Proofs.Parser.Recording
import all BSmtLib.Parser

@[expose] public section

/-!
# The parser's steps write no token points

In a recording run of the library's parser (the handler `recordingLibrary`, whose state is the
log), a step of any parser only adds events to the log, and none of them is a token's arrival or
processing: those are written by the token points alone, around the steps. `Quiet P x` says
this of the action `x`, and that its result satisfies `P`.

`Quiet.Without bad P x` says the same of the events `bad` picks out, for any `bad` that picks out
no call of the handler: `Quiet` is `Quiet.Without isPoint`, and `Quiet.Without isSwitch` says that
the action tells the handler no version. The closure lemmas below hold for every `bad`, and so do
the lemmas of `QuietSteps` for the steps that tell the handler only calls (`Quiet.CallsPass`).

A parser's step is generic in its handler's monad, so it cannot reach the log but through the
handler; Lean does not give that free theorem, so it is proved for each step from how it is
built, by the closure lemmas below and the tactic `quiet`.
-/

namespace BSmtLib.Facts.Proofs.Parser.Quiet

open BSmtLibSpec.Parser.Properties
open BSmtLibSpec.Parser.Traversal
open BSmtLib.Parser (PM Input Step Flow)
open BSmtLib.Facts.Parser.Adapters.Handler

/-- The event is a token's arrival or processing. -/
def isPoint : Event → Bool
  | .arrive _ | .process _ => true
  | _ => false

/-- The event is the handler's switch of the version. -/
def isSwitch : Event → Bool
  | .handlerSwitch _ => true
  | _ => false

/-- The parser's monad in a recording run. -/
abbrev RPM := PM (List Event)

/-- The action adds events to the log, none of them one that `bad` picks out, and its result
satisfies `P`. -/
structure Without (bad : Event → Bool) {α : Type} (P : α → Prop) (x : RPM α) : Prop where
  holds :
  ∀ events, ∃ added, (x.run.run events).2 = added ++ events ∧
    (∀ e ∈ added, bad e = false) ∧ ∀ a, (x.run.run events).1 = .ok a → P a

/-- The action adds events to the log, none of them a token point, and its result satisfies
`P`. -/
abbrev _root_.BSmtLib.Facts.Proofs.Parser.Quiet {α : Type} (P : α → Prop) (x : Quiet.RPM α) :
    Prop :=
  Quiet.Without Quiet.isPoint P x

/-- The action adds events to the log, none of them a token point. -/
abbrev Silent {α : Type} (x : RPM α) : Prop := Quiet (fun _ => True) x

/-- The action adds events to the log, none of them one that `bad` picks out. -/
abbrev Avoids (bad : Event → Bool) {α : Type} (x : RPM α) : Prop := Without bad (fun _ => True) x

/-- `bad` picks out no call of the handler. -/
class CallsPass (bad : Event → Bool) : Prop where
  /-- A call of the handler is not picked out. -/
  call : ∀ returns request, bad (.call returns request) = false

instance : CallsPass isPoint := ⟨fun _ _ => rfl⟩

instance : CallsPass isSwitch := ⟨fun _ _ => rfl⟩

section

variable {bad : Event → Bool} {α β : Type} {P Q : α → Prop}

theorem pure {a : α} (h : P a) : Without bad P (Pure.pure a : RPM α) :=
  ⟨fun events => ⟨[], rfl, by simp, fun a' ha' => by cases ha'; exact h⟩⟩

theorem throw (e : Parser.ParseErrorCause Unit) : Without bad P (MonadExcept.throw e : RPM α) :=
  ⟨fun events => ⟨[], rfl, by simp, fun _ h => by cases h⟩⟩

theorem bind {P : β → Prop} {x : RPM α} {f : α → RPM β} (hx : Without bad Q x)
    (hf : ∀ a, Q a → Without bad P (f a)) : Without bad P (x >>= f) := by
  constructor
  intro events
  obtain ⟨added, hstate, hpoints, hresult⟩ := hx.holds events
  simp only [ExceptT.run_bind, StateT.run_bind]
  rcases hrun : (x.run.run events) with ⟨result, events'⟩
  rw [hrun] at hstate hresult
  cases result with
  | error e => exact ⟨added, hstate, hpoints, fun _ h => by cases h⟩
  | ok a =>
    obtain ⟨added', hstate', hpoints', hresult'⟩ := (hf a (hresult a rfl)).holds events'
    refine ⟨added' ++ added, ?_, ?_, hresult'⟩
    · change ((ExceptT.run (f a)).run events').2 = _
      rw [hstate', show events' = added ++ events from hstate, List.append_assoc]
    · intro e he
      rcases List.mem_append.mp he with he | he
      · exact hpoints' e he
      · exact hpoints e he

theorem bind_silent {P : β → Prop} {x : RPM α} {f : α → RPM β}
    (hx : Avoids bad x) (hf : ∀ a, Without bad P (f a)) :
    Without bad P (x >>= f) :=
  Quiet.bind hx fun a _ => hf a

theorem mono {x : RPM α} (h : Without bad Q x) (himp : ∀ a, Q a → P a) : Without bad P x :=
  ⟨fun events => by
    obtain ⟨added, h₁, h₂, h₃⟩ := h.holds events
    exact ⟨added, h₁, h₂, fun a ha => himp a (h₃ a ha)⟩⟩

theorem silent {x : RPM α} (h : Without bad P x) : Avoids bad x :=
  mono h fun _ _ => trivial

/-- A call of the recording handler is silent. -/
theorem silent_call [CallsPass bad] {returns : Returns} (request : Call Recorded returns) :
    Avoids bad (Parser.call (recordingCall request) : RPM (Recorded.of returns)) := by
  constructor
  intro events
  refine ⟨[.call returns request], ?_, by simp [CallsPass.call], fun _ _ => trivial⟩
  rfl

/-- The handler's switch of the version is silent. -/
theorem silent_handlerSetVersion (version : BSmtLibSpec.Lexicon.Version) :
    Silent (ExceptT.lift (recordingHandler.setVersion version) : RPM Unit) := by
  constructor
  intro events
  exact ⟨[.handlerSwitch version], rfl, by simp [isPoint], fun _ _ => trivial⟩

end

end BSmtLib.Facts.Proofs.Parser.Quiet
