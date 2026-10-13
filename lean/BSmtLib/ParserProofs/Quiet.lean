import BSmtLib.ParserProofs.Recording

/-!
# The parser's steps write no token points

In a recording run of the library's parser (the handler `recordingLibrary`, whose state is the
log), a step of any parser only adds events to the log, and none of them is a token's arrival or
processing: those are written by the token points alone, around the steps. `Quiet P x` says
this of the action `x`, and that its result satisfies `P`.

A parser's step is generic in its handler's monad, so it cannot reach the log but through the
handler; Lean does not give that free theorem, so it is proved for each step from how it is
built, by the closure lemmas below and the tactic `quiet`.
-/

namespace BSmtLib.ParserProofs

open BSmtLib.Spec.Parser
open BSmtLib.Spec.Parser.Traversal
open BSmtLib.Parser (PM Input Step Flow)

/-- The event is a token's arrival or processing. -/
def isPoint : Event → Bool
  | .arrive _ | .process _ => true
  | _ => false

/-- The parser's monad in a recording run. -/
abbrev RPM := PM (List Event)

/-- The action adds events to the log, none of them a token point, and its result satisfies
`P`. -/
structure Quiet {α : Type} (P : α → Prop) (x : RPM α) : Prop where
  holds :
  ∀ events, ∃ added, (x.run.run events).2 = added ++ events ∧
    (∀ e ∈ added, isPoint e = false) ∧ ∀ a, (x.run.run events).1 = .ok a → P a

/-- The action adds events to the log, none of them a token point. -/
abbrev Silent {α : Type} (x : RPM α) : Prop := Quiet (fun _ => True) x

section

variable {α β : Type} {P Q : α → Prop}

theorem Quiet.pure {a : α} (h : P a) : Quiet P (Pure.pure a : RPM α) :=
  ⟨fun events => ⟨[], rfl, by simp, fun a' ha' => by cases ha'; exact h⟩⟩

theorem Quiet.throw (e : Parser.ParseErrorCause Unit) : Quiet P (MonadExcept.throw e : RPM α) :=
  ⟨fun events => ⟨[], rfl, by simp, fun _ h => by cases h⟩⟩

theorem Quiet.bind {P : β → Prop} {x : RPM α} {f : α → RPM β} (hx : Quiet Q x)
    (hf : ∀ a, Q a → Quiet P (f a)) : Quiet P (x >>= f) := by
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

theorem Quiet.bind_silent {P : β → Prop} {x : RPM α} {f : α → RPM β} (hx : Silent x)
    (hf : ∀ a, Quiet P (f a)) : Quiet P (x >>= f) :=
  Quiet.bind hx fun a _ => hf a

theorem Quiet.mono {x : RPM α} (h : Quiet Q x) (himp : ∀ a, Q a → P a) : Quiet P x :=
  ⟨fun events => by
    obtain ⟨added, h₁, h₂, h₃⟩ := h.holds events
    exact ⟨added, h₁, h₂, fun a ha => himp a (h₃ a ha)⟩⟩

theorem Quiet.silent {x : RPM α} (h : Quiet P x) : Silent x := h.mono fun _ _ => trivial

/-- A call of the recording handler is silent. -/
theorem silent_call {returns : Returns} (request : Call Recorded returns) :
    Silent (Parser.call (recordingCall request) : RPM (Recorded.of returns)) := by
  constructor
  intro events
  refine ⟨[.call returns request], ?_, by simp [isPoint], fun _ _ => trivial⟩
  rfl

/-- The handler's switch of the version is silent. -/
theorem silent_handlerSetVersion (version : Spec.Lexicon.Version) :
    Silent (ExceptT.lift (recordingHandler.setVersion version) : RPM Unit) := by
  constructor
  intro events
  exact ⟨[.handlerSwitch version], rfl, by simp [isPoint], fun _ _ => trivial⟩

end

end BSmtLib.ParserProofs
