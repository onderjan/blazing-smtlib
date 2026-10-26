module

public import BSmtLib.Facts.Parser.Adapters

@[expose] public section

/-!
# Running a parser over tokens, with the formalism's token points

`drive` (an adapter, in `Adapters.Run`) runs a parser stepped by single tokens over a list of
tokens, marking each token's arrival and processing with the `Points` of the specification formalism
(`BSmtLibSpec`) before the step that takes it, and making the parser's calls due at the token's
arrival (`arrival`, none by default) between the two. It is the parser's run as the formalism's
traversal sees it.

The framework for proving a parser against the traversal is one predicate and its rules:
`Runs points step state tokens program next` says that the parser, from the state, reads the
tokens with the effects of `program`, and then goes on as `next` says with its result:
`drive` from the state over the tokens and any rest is `program`, then the step `next` gives,
resumed over the rest. A parser with a stack of levels states its lemma in this form for every
stack, with `next` putting the result into the innermost level, so that nested constructs
compose (`Runs.append`). A parser that runs another inside one of its modes takes the inner
parser's lemma over by `Runs.embed`.
-/

open BSmtLib.Facts.Parser.Adapters.Run

namespace BSmtLib.Facts.Proofs.Parser.Drive

open BSmtLib.Parser
open BSmtLib.Parser.Internal (PM call syntaxError)
open BSmtLibSpec.Parser.Traversal

section

variable {H : Type} {m : Type → Type} [Monad m] [Handler H m] {σ ρ τ χ α β : Type}
variable (points : Points (StateT H m))

/-- A token arrives and is processed, with no call due at its arrival. -/
def tick (token : Parser.Internal.Input) : PM H Unit := do
  ExceptT.lift (arriveAt points token)
  ExceptT.lift (processAt points token)

/-- The tokens arrive and are processed, one after another. -/
def ticks : List Parser.Internal.Input → PM H Unit
  | [] => pure ()
  | token :: tokens => do
    tick points token
    ticks tokens

@[simp]
theorem noArrival_apply (state : σ) (token : Parser.Internal.Input) :
    (noArrival : σ → Parser.Internal.Input → PM H Unit) state token = pure () := rfl

/-- What the parser does after a step: goes on over the tokens, or ends with its result. -/
def resume (step : σ → Parser.Internal.Input → PM H (Parser.Internal.Step σ ρ)) (next : PM H
    (Parser.Internal.Step σ ρ))
    (tokens : List Parser.Internal.Input)
        (arrival : σ → Parser.Internal.Input → PM H Unit := noArrival) :
    PM H (Option (ρ × List Parser.Internal.Input)) := do
  match ← next with
  | .more state => drive points step state tokens arrival
  | .done result => pure (some (result, tokens))

/--
`Runs points step state tokens program next`: the parser, from the state, reads the tokens with
the effects of `program`, then goes on as `next` says with its result, whatever tokens follow.
-/
def Runs (step : σ → Parser.Internal.Input → PM H (Parser.Internal.Step σ ρ)) (state : σ)
    (tokens : List Parser.Internal.Input)
    (program : PM H α) (next : α → PM H (Parser.Internal.Step σ ρ))
    (arrival : σ → Parser.Internal.Input → PM H Unit := noArrival) : Prop :=
  ∀ rest, drive points step state (tokens ++ rest) arrival =
    program >>= fun result => resume points step (next result) rest arrival

/-- A step of an inner parser, as a step of the parser it runs in. -/
def Parser.Internal.Step.wrap (wrap : σ → τ) (after : ρ → PM H
    (Parser.Internal.Step τ χ)) : Parser.Internal.Step σ ρ → PM H (Parser.Internal.Step τ χ)
  | .more state => pure (.more (wrap state))
  | .done result => after result

variable {points}

theorem drive_nil (step : σ → Parser.Internal.Input → PM H (Parser.Internal.Step σ ρ)) (state : σ)
    {arrival : σ → Parser.Internal.Input → PM H Unit} :
    drive points step state [] arrival = pure none := rfl

theorem drive_cons' (step : σ → Parser.Internal.Input → PM H (Parser.Internal.Step σ ρ))
    (arrival : σ → Parser.Internal.Input → PM H Unit)
    (state : σ) (token : Parser.Internal.Input) (tokens : List Parser.Internal.Input) :
    drive points step state (token :: tokens) arrival = (do
      arrivalTick points arrival state token
      resume points step (step state token) tokens arrival) := rfl

variable [LawfulMonad m]

@[simp]
theorem arrivalTick_none (state : σ) (token : Parser.Internal.Input) :
    arrivalTick points (noArrival (H := H)) state token = tick points token := by
  simp [arrivalTick, tick]

theorem arrivalTick_pure {arrival : σ → Parser.Internal.Input → PM H Unit} {state : σ}
    {token : Parser.Internal.Input}
    (harr : arrival state token = pure ()) :
    arrivalTick points arrival state token = tick points token := by
  simp [arrivalTick, tick, harr]

theorem drive_cons (step : σ → Parser.Internal.Input → PM H (Parser.Internal.Step σ ρ))
    (state : σ) (token : Parser.Internal.Input)
    (tokens : List Parser.Internal.Input) :
    drive points step state (token :: tokens) = (do
      tick points token
      resume points step (step state token) tokens) := by
  rw [drive_cons', arrivalTick_none]

@[simp]
theorem resume_more (step : σ → Parser.Internal.Input → PM H (Parser.Internal.Step σ ρ))
    (state : σ) (tokens : List Parser.Internal.Input)
    {arrival : σ → Parser.Internal.Input → PM H Unit} :
    resume points step (pure (.more state)) tokens arrival =
      drive points step state tokens arrival := by
  simp [resume]

@[simp]
theorem resume_done (step : σ → Parser.Internal.Input → PM H (Parser.Internal.Step σ ρ))
    (result : ρ) (tokens : List Parser.Internal.Input)
    {arrival : σ → Parser.Internal.Input → PM H Unit} :
    resume points step (pure (.done result)) tokens arrival = pure (some (result, tokens)) := by
  simp [resume]

theorem resume_bind (step : σ → Parser.Internal.Input → PM H (Parser.Internal.Step σ ρ))
    (first : PM H α)
    (next : α → PM H (Parser.Internal.Step σ ρ)) (tokens : List Parser.Internal.Input)
    {arrival : σ → Parser.Internal.Input → PM H Unit} :
    resume points step (first >>= next) tokens arrival =
      first >>= fun a => resume points step (next a) tokens arrival := by
  simp [resume]

omit [LawfulMonad m] in
@[simp]
theorem ticks_nil : (ticks points [] : PM H Unit) = pure () := rfl

omit [LawfulMonad m] in
@[simp]
theorem ticks_cons (token : Parser.Internal.Input) (tokens : List Parser.Internal.Input) :
    (ticks points (token :: tokens) : PM H Unit) = (do tick points token; ticks points tokens) :=
  rfl

theorem ticks_append (first second : List Parser.Internal.Input) :
    (ticks points (first ++ second) : PM H Unit) =
      (do ticks points first; ticks points second) := by
  induction first with
  | nil => simp
  | cons token tokens ih => simp [ih]

theorem ticks_singleton (token : Parser.Internal.Input) :
    (ticks points [token] : PM H Unit) = tick points token := by
  simp

namespace Runs

variable {arrival : σ → Parser.Internal.Input → PM H Unit}

/-- One token, whose step makes the effects of the program, then the next step. -/
theorem tokenA {step : σ → Parser.Internal.Input → PM H
    (Parser.Internal.Step σ ρ)} {state : σ} {token : Parser.Internal.Input}
    {program : PM H α} {next : α → PM H (Parser.Internal.Step σ ρ)}
    (h : step state token = program >>= next)
    (harr : arrival state token = pure () := by intros; rfl) :
    Runs points step state [token] (do tick points token; program) next arrival := by
  intro rest
  simp only [List.singleton_append, drive_cons', arrivalTick_pure harr, h, resume_bind,
    bind_assoc]

/-- One token, at whose arrival calls are made, whose step makes the effects of the program,
then the next step. -/
theorem arriving {step : σ → Parser.Internal.Input → PM H
    (Parser.Internal.Step σ ρ)} {state : σ} {token : Parser.Internal.Input}
    {program : PM H α} {next : α → PM H (Parser.Internal.Step σ ρ)}
    (h : step state token = program >>= next) :
    Runs points step state [token] (do arrivalTick points arrival state token; program) next
      arrival := by
  intro rest
  simp only [List.singleton_append, drive_cons', h, resume_bind, bind_assoc]

/-- One token that only moves the parser to another state. -/
theorem token_moreA {step : σ → Parser.Internal.Input → PM H
    (Parser.Internal.Step σ ρ)} {state state' : σ} {token : Parser.Internal.Input}
    (h : step state token = pure (.more state'))
    (harr : arrival state token = pure () := by intros; rfl) :
    Runs points step state [token] (tick points token) (fun _ => pure (.more state'))
      arrival := by
  intro rest
  simp [drive_cons', arrivalTick_pure harr, h]


/-- One token, whose step makes the effects of the program, then the next step. -/
theorem token {step : σ → Parser.Internal.Input → PM H
    (Parser.Internal.Step σ ρ)} {state : σ} {token : Parser.Internal.Input}
    {program : PM H α} {next : α → PM H (Parser.Internal.Step σ ρ)}
    (h : step state token = program >>= next) :
    Runs points step state [token] (do tick points token; program) next :=
  tokenA h

/-- One token that only moves the parser to another state. -/
theorem token_more {step : σ → Parser.Internal.Input → PM H
    (Parser.Internal.Step σ ρ)} {state state' : σ} {token : Parser.Internal.Input}
    (h : step state token = pure (.more state')) :
    Runs points step state [token] (tick points token) fun _ => pure (.more state') :=
  token_moreA h
/-- Two runs one after the other, the first going on in the state the second starts from. -/
theorem append {step : σ → Parser.Internal.Input → PM H (Parser.Internal.Step σ ρ)} {state : σ}
    {first second : List Parser.Internal.Input} {program : PM H α} {middle : α → σ}
    {following : α → PM H β} {next : β → PM H (Parser.Internal.Step σ ρ)}
    (h₁ : Runs points step state first program (fun a => pure (.more (middle a))) arrival)
    (h₂ : ∀ a, Runs points step (middle a) second (following a) next arrival) :
    Runs points step state (first ++ second) (program >>= following) next arrival := by
  intro rest
  rw [List.append_assoc, h₁, bind_assoc]
  congr 1
  funext a
  rw [resume_more, h₂]

omit [LawfulMonad m] in
/-- A run is the same run with programs and continuations equal to its own. -/
theorem congr {step : σ → Parser.Internal.Input → PM H
    (Parser.Internal.Step σ ρ)} {state : σ} {tokens : List Parser.Internal.Input}
    {program program' : PM H α} {next next' : α → PM H (Parser.Internal.Step σ ρ)}
    (h : Runs points step state tokens program next arrival) (hprogram : program = program')
    (hnext : next = next') : Runs points step state tokens program' next' arrival :=
  hprogram ▸ hnext ▸ h

/-- The run over no tokens: the parser goes on in its state, with the value of the program. -/
theorem nil {step : σ → Parser.Internal.Input → PM H (Parser.Internal.Step σ ρ)} {state : σ}
    (value : α)
    {next : α → PM H (Parser.Internal.Step σ ρ)} (hnext : next value = pure (.more state)) :
    Runs points step state [] (pure value) next arrival := by
  intro rest
  simp [hnext]

/-- A run whose program ends in a pure value goes on with that value. -/
theorem map_program {step : σ → Parser.Internal.Input → PM H
    (Parser.Internal.Step σ ρ)} {state : σ} {tokens : List Parser.Internal.Input}
    {program : PM H α} {f : α → β} {next : β → PM H (Parser.Internal.Step σ ρ)}
    (h : Runs points step state tokens program (fun a => next (f a)) arrival) :
    Runs points step state tokens (f <$> program) next arrival := by
  intro rest
  rw [h, map_eq_pure_bind, bind_assoc]
  simp

/-- Effects at the start of the continuation are effects of the run. -/
theorem bind_next {step : σ → Parser.Internal.Input → PM H
    (Parser.Internal.Step σ ρ)} {state : σ} {tokens : List Parser.Internal.Input}
    {program : PM H α} {following : α → PM H β} {next : β → PM H (Parser.Internal.Step σ ρ)}
    (h : Runs points step state tokens program (fun a => following a >>= next) arrival) :
    Runs points step state tokens (program >>= following) next arrival := by
  intro rest
  rw [h, bind_assoc]
  congr 1
  funext a
  rw [resume_bind]

end Runs

/--
A parser that runs an inner one in its states `wrap state`: the outer parser in such a state
steps as the inner one, staying wrapped while the inner one goes on, and as `after` says when
it ends; the calls due at a token's arrival are the inner one's.
-/
theorem drive_embedA {inner : σ → Parser.Internal.Input → PM H (Parser.Internal.Step σ ρ)}
    {outer : τ → Parser.Internal.Input → PM H
        (Parser.Internal.Step τ χ)} {innerArrival : σ → Parser.Internal.Input → PM H Unit}
    {outerArrival : τ → Parser.Internal.Input → PM H Unit} (wrap : σ → τ) (after : ρ → PM H
        (Parser.Internal.Step τ χ))
    (hstep : ∀ state token, outer (wrap state) token =
      inner state token >>= Parser.Internal.Step.wrap wrap after)
    (harr : ∀ state token, outerArrival (wrap state) token = innerArrival state token)
    (state : σ) (tokens : List Parser.Internal.Input) :
    drive points outer (wrap state) tokens outerArrival =
      drive points inner state tokens innerArrival >>= fun
      | none => pure none
      | some (result, rest) => resume points outer (after result) rest outerArrival := by
  induction tokens generalizing state with
  | nil => simp [drive_nil]
  | cons token tokens ih =>
    simp only [drive_cons', arrivalTick, harr, hstep, bind_assoc, resume]
    congr 1
    funext _
    congr 1
    funext _
    congr 1
    funext _
    congr 1
    funext step
    cases step with
    | more state => simp [Parser.Internal.Step.wrap, ih, resume]
    | done result => simp [Parser.Internal.Step.wrap]

/-- The run of an inner parser, as a run of the parser it runs in (see `drive_embed`). -/
theorem Runs.embedA {inner : σ → Parser.Internal.Input → PM H (Parser.Internal.Step σ ρ)}
    {outer : τ → Parser.Internal.Input → PM H
        (Parser.Internal.Step τ χ)} {innerArrival : σ → Parser.Internal.Input → PM H Unit}
    {outerArrival : τ → Parser.Internal.Input → PM H Unit} (wrap : σ → τ) (after : ρ → PM H
        (Parser.Internal.Step τ χ))
    (hstep : ∀ state token, outer (wrap state) token =
      inner state token >>= Parser.Internal.Step.wrap wrap after)
    {state : σ} {tokens : List Parser.Internal.Input} {program : PM H α} {next : α → PM H
        (Parser.Internal.Step σ ρ)}
    (h : Runs points inner state tokens program next innerArrival)
    (harr : ∀ state token, outerArrival (wrap state) token = innerArrival state token := by
      intros; rfl) :
    Runs points outer (wrap state) tokens program
      (fun a => next a >>= Parser.Internal.Step.wrap wrap after) outerArrival := by
  intro rest
  rw [drive_embedA wrap after hstep harr, h, bind_assoc]
  congr 1
  funext a
  simp only [resume, bind_assoc]
  congr 1
  funext step
  cases step with
  | more state =>
    simp [Parser.Internal.Step.wrap, drive_embedA wrap after hstep harr, resume]
  | done result => simp [Parser.Internal.Step.wrap]


/-- `drive_embedA` with no calls due at any arrival. -/
theorem drive_embed {inner : σ → Parser.Internal.Input → PM H (Parser.Internal.Step σ ρ)}
    {outer : τ → Parser.Internal.Input → PM H (Parser.Internal.Step τ χ)} (wrap : σ → τ)
        (after : ρ → PM H (Parser.Internal.Step τ χ))
    (hstep : ∀ state token, outer (wrap state) token =
      inner state token >>= Parser.Internal.Step.wrap wrap after) (state : σ)
          (tokens : List Parser.Internal.Input) :
    drive points outer (wrap state) tokens = drive points inner state tokens >>= fun
      | none => pure none
      | some (result, rest) => resume points outer (after result) rest :=
  drive_embedA wrap after hstep (fun _ _ => rfl) state tokens

/-- `Runs.embedA` with no calls due at any arrival. -/
theorem Runs.embed {inner : σ → Parser.Internal.Input → PM H (Parser.Internal.Step σ ρ)}
    {outer : τ → Parser.Internal.Input → PM H (Parser.Internal.Step τ χ)} (wrap : σ → τ)
        (after : ρ → PM H (Parser.Internal.Step τ χ))
    (hstep : ∀ state token, outer (wrap state) token =
      inner state token >>= Parser.Internal.Step.wrap wrap after)
    {state : σ} {tokens : List Parser.Internal.Input} {program : PM H α} {next : α → PM H
        (Parser.Internal.Step σ ρ)}
    (h : Runs points inner state tokens program next) :
    Runs points outer (wrap state) tokens program
      (fun a => next a >>= Parser.Internal.Step.wrap wrap after) :=
  Runs.embedA wrap after hstep h
end

end BSmtLib.Facts.Proofs.Parser.Drive

namespace BSmtLib.Facts.Proofs.Parser.Drive

open BSmtLib.Parser
open BSmtLib.Parser.Internal (PM call syntaxError)
open BSmtLibSpec.Parser.Traversal

section

variable {H : Type} {m : Type → Type} [Monad m] [Handler H m] {σ ρ : Type}
variable (points : Points (StateT H m))

/-- A token arrives, the calls `first` are made, and it is processed. -/
def tickFirst (first : PM H Unit) (token : Parser.Internal.Input) : PM H Unit := do
  ExceptT.lift (arriveAt points token)
  first
  ExceptT.lift (processAt points token)

/--
`drive` with calls due at the arrival of the first token: the first token arrives, the calls
are made, then the token is processed and the step takes it; the rest as `drive`.
-/
def driveFirst (first : PM H Unit) (step : σ → Parser.Internal.Input → PM H
    (Parser.Internal.Step σ ρ)) (state : σ) :
    List Parser.Internal.Input → PM H (Option (ρ × List Parser.Internal.Input))
  | [] => pure none
  | token :: tokens => do
    tickFirst points first token
    resume points step (step state token) tokens

/--
`Runs` with the calls `first` due at the arrival of the first token: the parser, from the state,
reads the tokens with the effects of `program`, the calls made at the first token's arrival,
then goes on as `next` says.
-/
def RunsFirst {α : Type} (first : PM H Unit) (step : σ → Parser.Internal.Input → PM H
    (Parser.Internal.Step σ ρ)) (state : σ)
    (tokens : List Parser.Internal.Input) (program : PM H α) (next : α → PM H
        (Parser.Internal.Step σ ρ)) : Prop :=
  ∀ rest, driveFirst points first step state (tokens ++ rest) =
    program >>= fun result => resume points step (next result) rest

variable {points}

variable [LawfulMonad m]

@[simp]
theorem tickFirst_pure (token : Parser.Internal.Input) : tickFirst points (pure
    ()) token = tick points token := by
  simp [tickFirst, tick]

theorem driveFirst_pure (step : σ → Parser.Internal.Input → PM H (Parser.Internal.Step σ ρ))
    (state : σ) (tokens : List Parser.Internal.Input) :
    driveFirst points (pure ()) step state tokens = drive points step state tokens := by
  cases tokens with
  | nil => rfl
  | cons token tokens => simp [driveFirst, drive_cons]

namespace RunsFirst

variable {α β : Type} {first : PM H Unit} {step : σ → Parser.Internal.Input → PM H
    (Parser.Internal.Step σ ρ)} {state : σ}

/-- With no call due at the first arrival, a run as `Runs` states it. -/
theorem runs {tokens : List Parser.Internal.Input} {program : PM H α} {next : α → PM H
    (Parser.Internal.Step σ ρ)}
    (h : RunsFirst points (pure ()) step state tokens program next) :
    Runs points step state tokens program next := by
  intro rest
  rw [← h rest, driveFirst_pure]

/-- One token, whose step makes the effects of the program, then the next step. -/
theorem token {token : Parser.Internal.Input} {program : PM H α} {next : α → PM H
    (Parser.Internal.Step σ ρ)}
    (h : step state token = program >>= next) :
    RunsFirst points first step state [token] (do tickFirst points first token; program) next := by
  intro rest
  simp only [List.singleton_append, driveFirst, h, resume_bind, bind_assoc]

/-- One token that only moves the parser to another state. -/
theorem token_more {token : Parser.Internal.Input} {state' : σ} (h : step state token = pure
    (.more state')) :
    RunsFirst points first step state [token] (tickFirst points first token)
      fun _ => pure (.more state') := by
  intro rest
  simp [driveFirst, h]

/-- A run with calls at its first arrival, then a run with none, going on from where the first
leaves. -/
theorem append {firstTokens second : List Parser.Internal.Input} {program : PM H α} {middle : α → σ}
    {following : α → PM H β} {next : β → PM H (Parser.Internal.Step σ ρ)}
    (h₁ : RunsFirst points first step state firstTokens program
      fun a => pure (.more (middle a)))
    (h₂ : ∀ a, Runs points step (middle a) second (following a) next) :
    RunsFirst points first step state (firstTokens ++ second) (program >>= following) next := by
  intro rest
  rw [List.append_assoc, h₁, bind_assoc]
  congr 1
  funext a
  rw [resume_more, h₂]

omit [LawfulMonad m] in
/-- A run is the same run with programs and continuations equal to its own. -/
theorem congr {tokens : List Parser.Internal.Input} {program program' : PM H α}
    {next next' : α → PM H (Parser.Internal.Step σ ρ)}
        (h : RunsFirst points first step state tokens program next)
    (hprogram : program = program') (hnext : next = next') :
    RunsFirst points first step state tokens program' next' :=
  hprogram ▸ hnext ▸ h

omit [LawfulMonad m] in
/-- A run over tokens equal to its own. -/
theorem tokens_eq {tokens tokens' : List Parser.Internal.Input} {program : PM H α}
    {next : α → PM H (Parser.Internal.Step σ ρ)}
        (h : RunsFirst points first step state tokens program next)
    (heq : tokens = tokens') : RunsFirst points first step state tokens' program next :=
  heq ▸ h


/-- Effects at the start of the continuation are effects of the run. -/
theorem bind_next {tokens : List Parser.Internal.Input} {program : PM H α} {following : α → PM H β}
    {next : β → PM H (Parser.Internal.Step σ ρ)}
    (h : RunsFirst points first step state tokens program fun a => following a >>= next) :
    RunsFirst points first step state tokens (program >>= following) next := by
  intro rest
  rw [h, bind_assoc]
  congr 1
  funext a
  rw [resume_bind]
end RunsFirst

/-- The run of an inner parser with calls due at its first arrival, as a run of the parser it
runs in, which makes the same calls (see `Runs.embed`). -/
theorem RunsFirst.embed {τ χ α : Type} {inner : σ → Parser.Internal.Input → PM H
    (Parser.Internal.Step σ ρ)}
    {outer : τ → Parser.Internal.Input → PM H (Parser.Internal.Step τ χ)} (wrap : σ → τ)
        (after : ρ → PM H (Parser.Internal.Step τ χ))
    (hstep : ∀ state token, outer (wrap state) token =
      inner state token >>= Parser.Internal.Step.wrap wrap after)
    {first : PM H Unit} {state : σ} {tokens : List Parser.Internal.Input} {program : PM H α}
    {next : α → PM H (Parser.Internal.Step σ ρ)}
        (h : RunsFirst points first inner state tokens program next) :
    RunsFirst points first outer (wrap state) tokens program
      (fun a => next a >>= Parser.Internal.Step.wrap wrap after) := by
  let cont : Option (ρ × List Parser.Internal.Input) → PM H (Option
      (χ × List Parser.Internal.Input)) := fun
    | none => pure none
    | some (result, rest) => resume points outer (after result) rest
  have hwrap : ∀ (step : Parser.Internal.Step σ ρ) (tokens : List Parser.Internal.Input),
      resume points outer (Parser.Internal.Step.wrap wrap after step) tokens =
        resume points inner (pure step) tokens >>= cont := by
    intro step tokens
    cases step with
    | more state => simp [Parser.Internal.Step.wrap, drive_embed wrap after hstep, resume, cont]
    | done result => simp [Parser.Internal.Step.wrap, resume, cont]
  have hsplit : ∀ (x : PM H (Parser.Internal.Step σ ρ)) (tokens : List Parser.Internal.Input),
      resume points inner x tokens = x >>= fun step => resume points inner (pure step) tokens := by
    intro x tokens
    simp [resume]
  have hdrive : ∀ tokens, driveFirst points first outer (wrap state) tokens =
      driveFirst points first inner state tokens >>= cont := by
    intro tokens
    cases tokens with
    | nil => simp [driveFirst, cont]
    | cons token tokens =>
      simp only [driveFirst, hstep, resume_bind, hwrap, bind_assoc, hsplit (inner state token)]
  intro rest
  rw [hdrive, h rest, bind_assoc]
  congr 1
  funext a
  rw [resume_bind, hsplit (next a), bind_assoc]
  congr 1
  funext step
  rw [hwrap]

/--
A run of an inner parser with calls due at its first arrival, as a run of the parser it runs in,
from a state that steps on the first token as the inner parser's state and makes those calls at
its arrival; the outer parser's later states are the inner one's, wrapped, with no call due at
an arrival.
-/
theorem Runs.ofFirst {τ χ α : Type} {inner : σ → Parser.Internal.Input → PM H
    (Parser.Internal.Step σ ρ)}
    {outer : τ → Parser.Internal.Input → PM H
        (Parser.Internal.Step τ χ)} {outerArrival : τ → Parser.Internal.Input → PM H Unit}
    (wrap : σ → τ) (after : ρ → PM H
        (Parser.Internal.Step τ χ)) {first : PM H Unit} {start : τ} {state : σ}
    {token : Parser.Internal.Input} {tokens : List Parser.Internal.Input} {program : PM H α}
        {next : α → PM H (Parser.Internal.Step σ ρ)}
    (hstart : outer start token = inner state token >>= Parser.Internal.Step.wrap wrap after)
    (hstep : ∀ state token, outer (wrap state) token =
      inner state token >>= Parser.Internal.Step.wrap wrap after)
    (harrival : outerArrival start token = first)
    (harr : ∀ state token, outerArrival (wrap state) token = noArrival state token)
    (h : RunsFirst points first inner state (token :: tokens) program next) :
    Runs points outer start (token :: tokens) program
      (fun a => next a >>= Parser.Internal.Step.wrap wrap after) outerArrival := by
  intro rest
  -- after the first token's step, the outer parser goes on as the inner one, wrapped
  let cont : Option (ρ × List Parser.Internal.Input) → PM H (Option
      (χ × List Parser.Internal.Input)) := fun
    | none => pure none
    | some (result, rest) => resume points outer (after result) rest outerArrival
  have hwrap : ∀ (step : Parser.Internal.Step σ ρ) (tokens : List Parser.Internal.Input),
      resume points outer (Parser.Internal.Step.wrap wrap after step) tokens outerArrival =
        resume points inner (pure step) tokens >>= cont := by
    intro step tokens
    cases step with
    | more state =>
      simp [Parser.Internal.Step.wrap, drive_embedA wrap after hstep harr, resume, cont]
    | done result => simp [Parser.Internal.Step.wrap, resume, cont]
  have hfirst := h rest
  simp only [List.cons_append, driveFirst] at hfirst
  have hsplit : ∀ (x : PM H (Parser.Internal.Step σ ρ)) (tokens : List Parser.Internal.Input),
      resume points inner x tokens = x >>= fun step => resume points inner (pure step) tokens := by
    intro x tokens
    simp [resume]
  calc drive points outer start (token :: tokens ++ rest) outerArrival
      = (do
          tickFirst points first token
          resume points inner (inner state token) (tokens ++ rest)) >>= cont := by
        simp only [List.cons_append, drive_cons', arrivalTick, harrival, hstart, resume_bind,
          hwrap, tickFirst, bind_assoc, hsplit (inner state token)]
    _ = program >>= fun a => resume points outer
        (next a >>= Parser.Internal.Step.wrap wrap after) rest
          outerArrival := by
        rw [hfirst, bind_assoc]
        congr 1
        funext a
        rw [resume_bind, hsplit (next a), bind_assoc]
        congr 1
        funext step
        rw [hwrap]

end

end BSmtLib.Facts.Proofs.Parser.Drive
