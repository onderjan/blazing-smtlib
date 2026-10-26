module

public import BSmtLib.Facts.Proofs.Parser.Category.Cursor
public import BSmtLib.Facts.Proofs.Parser.Lemmas
import all BSmtLib.Parser

@[expose] public section

/-!
# Runs of a parser's steps that keep where they stopped

`drive` (an adapter) tells what a parser's steps do over a list of tokens, but not where a step
failed, nor in which state the parser is when the tokens run out. `driveS` keeps both: it ends
waiting in a state at the end of the tokens, done with a result and the tokens after, rejected
with a syntax error or a version error and the tokens after the token whose step raised it, or
failed with the handler's error. `RunsS` is `Runs` for `driveS`: its programs are handler-only
(they make calls and fail with the handler's error only), so that a syntax error is where the
continuation raises it. Its rules are those of `Runs`, and the lemmas about the parsers' steps are
proved again with them in the modules beside this one.
-/

namespace BSmtLib.Facts.Proofs.Parser.Category.Steps

open BSmtLib.Parser (ParseErrorCause SyntaxErrorKind VersionErrorKind)
open BSmtLib.Parser.Internal (PM)
open BSmtLib.Facts.Parser.Adapters.Bridge BSmtLib.Facts.Parser.Adapters.Run
open BSmtLib.Facts.Parser.Adapters.Outcome (HandlerOnly)
open BSmtLib.Facts.Proofs.Parser.Drive
open BSmtLibSpec.Parser.Traversal (Points)

/-! ## Handler-only programs -/

section

variable {H E : Type} {m : Type → Type} [Monad m] [LawfulMonad m] {α β : Type}

theorem handlerOnly_pure (a : α) :
    HandlerOnly (pure a : ExceptT (ParseErrorCause E) (StateT H m) α) :=
  ⟨pure a, by
    apply ExceptT.ext
    simp⟩

theorem handlerOnly_lift (x : StateT H m α) :
    HandlerOnly (ExceptT.lift x : ExceptT (ParseErrorCause E) (StateT H m) α) :=
  ⟨ExceptT.lift x, by
    apply ExceptT.ext
    simp [ExceptT.run_lift]⟩

omit [LawfulMonad m] in
theorem handlerOnly_adapt (x : ExceptT E (StateT H m) α) :
    HandlerOnly (ExceptT.adapt ParseErrorCause.handler x) := ⟨x, rfl⟩

theorem handlerOnly_bind {x : ExceptT (ParseErrorCause E) (StateT H m) α}
    {f : α → ExceptT (ParseErrorCause E) (StateT H m) β} (hx : HandlerOnly x)
    (hf : ∀ a, HandlerOnly (f a)) : HandlerOnly (x >>= f) := by
  obtain ⟨y, rfl⟩ := hx
  refine ⟨y >>= fun a => Classical.choose (hf a), ?_⟩
  rw [BSmtLib.Facts.Proofs.Parser.Lemmas.adapt_bind]
  congr 1
  funext a
  exact Classical.choose_spec (hf a)

theorem handlerOnly_map {x : ExceptT (ParseErrorCause E) (StateT H m) α} (f : α → β)
    (hx : HandlerOnly x) : HandlerOnly (f <$> x) := by
  rw [map_eq_pure_bind]
  exact handlerOnly_bind hx fun a => handlerOnly_pure _

omit [LawfulMonad m] in
theorem handlerOnly_congr {x y : ExceptT (ParseErrorCause E) (StateT H m) α} (hx : HandlerOnly x)
    (h : x = y) : HandlerOnly y := h ▸ hx

omit [LawfulMonad m] in
/-- A handler-only program, run: its failures are the handler's. -/
theorem handlerOnly_run_eq {x : ExceptT (ParseErrorCause E) (StateT H m) α} (hx : HandlerOnly x) :
    ∃ calls : ExceptT E (StateT H m) α,
      x.run = (fun e => match e with
        | .ok a => .ok a
        | .error error => .error (.handler error)) <$> calls.run := by
  obtain ⟨calls, rfl⟩ := hx
  refine ⟨calls, ?_⟩
  rw [ExceptT.run_adapt]
  congr 1
  funext e
  cases e <;> rfl

end

section

variable {H : Type} {m : Type → Type} [Monad m] [LawfulMonad m] [Handler H m] {α : Type}
variable {points : Points (StateT H m)}

omit [LawfulMonad m] in
theorem handlerOnly_call (x : ExceptT (Handler.Error H) (StateT H m) α) :
    HandlerOnly (BSmtLib.Parser.Internal.call x : PM H α) := ⟨x, rfl⟩

theorem handlerOnly_tick (token : Parser.Internal.Input) : HandlerOnly (tick points token) :=
  handlerOnly_bind (handlerOnly_lift _) fun _ => handlerOnly_lift _

theorem handlerOnly_ticks (tokens : List Parser.Internal.Input) :
    HandlerOnly (ticks points tokens) := by
  induction tokens with
  | nil => exact handlerOnly_pure ()
  | cons token tokens ih => exact handlerOnly_bind (handlerOnly_tick token) fun _ => ih

end

/-- Proves that a program built of calls, ticks, lifts and pure values is handler-only. -/
syntax "handler_only" : tactic

macro_rules
  | `(tactic| handler_only) => `(tactic| first
    | exact handlerOnly_pure _
    | exact handlerOnly_call _
    | exact handlerOnly_tick _
    | exact handlerOnly_ticks _
    | exact handlerOnly_lift _
    | exact handlerOnly_adapt _
    | (refine handlerOnly_bind ?_ fun _ => ?_ <;> handler_only)
    | (refine handlerOnly_map _ ?_; handler_only))

/-! ## Runs that keep where they stopped -/

/-- Where the steps stopped over a list of tokens. -/
inductive Res (σ ρ E : Type) where
  /-- Every token taken, the parser in the state. -/
  | waits (state : σ)
  /-- Done with the result, the tokens after. -/
  | done (result : ρ) (rest : List Parser.Internal.Input)
  /-- A syntax error of the kind, the tokens after the token whose step raised it. -/
  | rejected (kind : SyntaxErrorKind) (rest : List Parser.Internal.Input)
  /-- A version error of the kind, the tokens after the token whose step raised it. -/
  | rejectedVersion (kind : VersionErrorKind) (rest : List Parser.Internal.Input)
  /-- The handler's error. -/
  | failed (error : E)

section

variable {H : Type} {m : Type → Type} [Monad m] [Handler H m] {σ ρ α β τ χ : Type}
variable (points : Points (StateT H m))

/-- What the step's answer does, with the tokens after it. -/
def onStep (continue_ : σ → StateT H m (Res σ ρ (Handler.Error H)))
    (rest : List Parser.Internal.Input) :
    Except (ParseErrorCause (Handler.Error H)) (Parser.Internal.Step σ ρ) →
    StateT H m (Res σ ρ (Handler.Error H))
  | .ok (.more state) => continue_ state
  | .ok (.done result) => pure (.done result rest)
  | .error (.syntax kind) => pure (.rejected kind rest)
  | .error (.version kind) => pure (.rejectedVersion kind rest)
  | .error (.handler error) => pure (.failed error)

/-- The steps over the tokens, from the state, keeping where they stopped. -/
def driveS (step : σ → Parser.Internal.Input → PM H (Parser.Internal.Step σ ρ)) :
    σ → List Parser.Internal.Input → StateT H m (Res σ ρ (Handler.Error H))
  | state, [] => pure (.waits state)
  | state, token :: tokens => do
    onStep (fun state => driveS step state tokens) tokens
      (← (do tick points token; step state token).run)

/-- What the parser does after a step's program: the continuation, then the tokens. -/
def resumeS (step : σ → Parser.Internal.Input → PM H (Parser.Internal.Step σ ρ))
    (next : PM H (Parser.Internal.Step σ ρ)) (rest : List Parser.Internal.Input) :
    StateT H m (Res σ ρ (Handler.Error H)) := do
  onStep (fun state => driveS points step state rest) rest (← next.run)

/-- What a handler-only program's answer does, then the continuation. -/
def afterProgram (k : α → StateT H m (Res σ ρ (Handler.Error H)))
    (rest : List Parser.Internal.Input) :
    Except (ParseErrorCause (Handler.Error H)) α →
    StateT H m (Res σ ρ (Handler.Error H))
  | .ok a => k a
  | .error (.syntax kind) => pure (.rejected kind rest)
  | .error (.version kind) => pure (.rejectedVersion kind rest)
  | .error (.handler error) => pure (.failed error)

/--
`RunsS points step state tokens program next`: the parser, from the state, reads the tokens with
the effects of the handler-only `program`, then goes on as `next` says with its result, whatever
tokens follow; where it stops is kept.
-/
def RunsS (step : σ → Parser.Internal.Input → PM H (Parser.Internal.Step σ ρ)) (state : σ)
    (tokens : List Parser.Internal.Input) (program : PM H α)
    (next : α → PM H (Parser.Internal.Step σ ρ)) : Prop :=
  HandlerOnly program ∧ ∀ rest, driveS points step state (tokens ++ rest) =
    program.run >>= afterProgram (fun a => resumeS points step (next a) rest) rest

end

section

variable {H : Type} {m : Type → Type} [Monad m] [LawfulMonad m] [Handler H m]
variable {σ ρ α β τ χ : Type} {points : Points (StateT H m)}

omit [LawfulMonad m] in
theorem driveS_nil (step : σ → Parser.Internal.Input → PM H (Parser.Internal.Step σ ρ))
    (state : σ) : driveS points step state [] = pure (.waits state) := rfl

omit [LawfulMonad m] in
theorem driveS_cons (step : σ → Parser.Internal.Input → PM H (Parser.Internal.Step σ ρ))
    (state : σ) (token : Parser.Internal.Input) (tokens : List Parser.Internal.Input) :
    driveS points step state (token :: tokens) =
      (do tick points token; step state token).run >>=
        onStep (fun state => driveS points step state tokens) tokens := rfl

@[simp]
theorem resumeS_more (step : σ → Parser.Internal.Input → PM H (Parser.Internal.Step σ ρ))
    (state : σ) (rest : List Parser.Internal.Input) :
    resumeS points step (pure (.more state)) rest = driveS points step state rest := by
  simp [resumeS, onStep]

@[simp]
theorem resumeS_done (step : σ → Parser.Internal.Input → PM H (Parser.Internal.Step σ ρ))
    (result : ρ) (rest : List Parser.Internal.Input) :
    resumeS points step (pure (.done result)) rest = pure (.done result rest) := by
  simp [resumeS, onStep]

@[simp]
theorem resumeS_throw (step : σ → Parser.Internal.Input → PM H (Parser.Internal.Step σ ρ))
    (kind : SyntaxErrorKind) (rest : List Parser.Internal.Input) :
    resumeS points step (throw (.syntax kind)) rest = pure (.rejected kind rest) := by
  simp [resumeS, onStep, ExceptT.run_throw]

/-- A handler-only program, then a continuation over the step's answer. -/
theorem run_bind_onStep {program : PM H α} (hp : HandlerOnly program)
    (next : α → PM H (Parser.Internal.Step σ ρ))
    (k : σ → StateT H m (Res σ ρ (Handler.Error H))) (rest : List Parser.Internal.Input) :
    (program >>= next).run >>= onStep k rest =
      program.run >>= afterProgram (fun a => (next a).run >>= onStep k rest) rest := by
  obtain ⟨calls, hcalls⟩ := handlerOnly_run_eq hp
  rw [ExceptT.run_bind, hcalls, bind_map_left, bind_map_left, bind_assoc]
  refine bind_congr fun e => ?_
  rcases e with error | a
  · simp [afterProgram, onStep]
  · simp [afterProgram]

namespace RunsS

/-- One token, whose step makes the effects of a handler-only program, then the next step. -/
theorem token {step : σ → Parser.Internal.Input → PM H (Parser.Internal.Step σ ρ)} {state : σ}
    {token : Parser.Internal.Input} {program : PM H α}
    {next : α → PM H (Parser.Internal.Step σ ρ)} (h : step state token = program >>= next)
    (hp : HandlerOnly program := by handler_only) :
    RunsS points step state [token] (do tick points token; program) next := by
  refine ⟨handlerOnly_bind (handlerOnly_tick token) fun _ => hp, fun rest => ?_⟩
  rw [List.singleton_append, driveS_cons, h, ← bind_assoc]
  rw [run_bind_onStep (handlerOnly_bind (handlerOnly_tick token) fun _ => hp)]
  rfl

omit [LawfulMonad m] in
/-- A run is the same run with programs and continuations equal to its own. -/
theorem congr {step : σ → Parser.Internal.Input → PM H (Parser.Internal.Step σ ρ)} {state : σ}
    {tokens : List Parser.Internal.Input} {program program' : PM H α}
    {next next' : α → PM H (Parser.Internal.Step σ ρ)}
    (h : RunsS points step state tokens program next) (hprogram : program = program')
    (hnext : next = next') : RunsS points step state tokens program' next' :=
  hprogram ▸ hnext ▸ h

/-- One token that only moves the parser to another state. -/
theorem token_more {step : σ → Parser.Internal.Input → PM H (Parser.Internal.Step σ ρ)}
    {state state' : σ} {token : Parser.Internal.Input}
    (h : step state token = pure (.more state')) :
    RunsS points step state [token] (tick points token) fun _ => pure (.more state') :=
  (RunsS.token (program := pure ()) (next := fun _ => pure (.more state')) (by simp [h])
    (handlerOnly_pure ())).congr (by simp) rfl

/-- Two runs one after the other, the first going on in the state the second starts from. -/
theorem append {step : σ → Parser.Internal.Input → PM H (Parser.Internal.Step σ ρ)} {state : σ}
    {first second : List Parser.Internal.Input} {program : PM H α} {middle : α → σ}
    {following : α → PM H β} {next : β → PM H (Parser.Internal.Step σ ρ)}
    (h₁ : RunsS points step state first program (fun a => pure (.more (middle a))))
    (h₂ : ∀ a, RunsS points step (middle a) second (following a) next) :
    RunsS points step state (first ++ second) (program >>= following) next := by
  refine ⟨handlerOnly_bind h₁.1 fun a => (h₂ a).1, fun rest => ?_⟩
  rw [List.append_assoc, h₁.2, ExceptT.run_bind, bind_assoc]
  obtain ⟨calls, hcalls⟩ := handlerOnly_run_eq h₁.1
  rw [hcalls, bind_map_left, bind_map_left]
  refine bind_congr fun e => ?_
  rcases e with error | a
  · simp [afterProgram]
  · simp only [afterProgram, resumeS_more]
    exact (h₂ a).2 rest

/-- The run over no tokens: the parser goes on in its state, with the value of the program. -/
theorem nil {step : σ → Parser.Internal.Input → PM H (Parser.Internal.Step σ ρ)} {state : σ}
    (value : α) {next : α → PM H (Parser.Internal.Step σ ρ)}
    (hnext : next value = pure (.more state)) :
    RunsS points step state [] (pure value) next := by
  refine ⟨handlerOnly_pure value, fun rest => ?_⟩
  simp [afterProgram, hnext]

/-- A run whose program ends in a pure value goes on with that value. -/
theorem map_program {step : σ → Parser.Internal.Input → PM H (Parser.Internal.Step σ ρ)}
    {state : σ} {tokens : List Parser.Internal.Input} {program : PM H α} {f : α → β}
    {next : β → PM H (Parser.Internal.Step σ ρ)}
    (h : RunsS points step state tokens program (fun a => next (f a))) :
    RunsS points step state tokens (f <$> program) next := by
  refine ⟨handlerOnly_map f h.1, fun rest => ?_⟩
  rw [h.2, ExceptT.run_map, bind_map_left]
  refine bind_congr fun e => ?_
  rcases e with (kind | kind | error) | a <;> rfl

/-- Effects at the start of the continuation, handler-only, are effects of the run. -/
theorem bind_next {step : σ → Parser.Internal.Input → PM H (Parser.Internal.Step σ ρ)}
    {state : σ} {tokens : List Parser.Internal.Input} {program : PM H α}
    {following : α → PM H β} {next : β → PM H (Parser.Internal.Step σ ρ)}
    (h : RunsS points step state tokens program (fun a => following a >>= next))
    (hf : ∀ a, HandlerOnly (following a) := by intro; handler_only) :
    RunsS points step state tokens (program >>= following) next := by
  refine ⟨handlerOnly_bind h.1 hf, fun rest => ?_⟩
  rw [h.2, ExceptT.run_bind, bind_assoc]
  refine bind_congr fun e => ?_
  rcases e with (kind | kind | error) | a
  · simp [afterProgram]
  · simp [afterProgram]
  · simp [afterProgram]
  · simp only [afterProgram, resumeS]
    exact run_bind_onStep (hf a) next _ rest

end RunsS

/-- A parser that runs an inner one in its states `wrap state`, as `drive_embedA` for `drive`. -/
theorem driveS_embed {inner : σ → Parser.Internal.Input → PM H (Parser.Internal.Step σ ρ)}
    {outer : τ → Parser.Internal.Input → PM H (Parser.Internal.Step τ χ)} (wrap : σ → τ)
    (after : ρ → PM H (Parser.Internal.Step τ χ))
    (hstep : ∀ state token, outer (wrap state) token =
      inner state token >>= Parser.Internal.Step.wrap wrap after)
    (state : σ) (tokens : List Parser.Internal.Input) :
    driveS points outer (wrap state) tokens =
      driveS points inner state tokens >>= fun
        | .waits state => pure (.waits (wrap state))
        | .done result rest => resumeS points outer (after result) rest
        | .rejected kind rest => pure (.rejected kind rest)
        | .rejectedVersion kind rest => pure (.rejectedVersion kind rest)
        | .failed error => pure (.failed error) := by
  induction tokens generalizing state with
  | nil => simp [driveS_nil]
  | cons token tokens ih =>
    simp only [driveS_cons, hstep, bind_assoc]
    rw [ExceptT.run_bind, ExceptT.run_bind, ExceptT.run_bind, bind_assoc, bind_assoc]
    refine bind_congr fun e => ?_
    rcases e with (kind | kind | error) | u
    · simp [onStep]
    · simp [onStep]
    · simp [onStep]
    · rw [bind_assoc]
      apply bind_congr
      intro e
      rcases e with (kind | kind | error) | (state' | result)
      · simp [onStep]
      · simp [onStep]
      · simp [onStep]
      · simp [onStep, Parser.Internal.Step.wrap, ih]
      · simp only [onStep, Parser.Internal.Step.wrap, resumeS, pure_bind]
        refine bind_congr fun e => ?_
        rcases e with (kind | kind | error) | (state' | result) <;> rfl


namespace RunsS

/-- The run of an inner parser, as a run of the parser it runs in (see `driveS_embed`). -/
theorem embed {inner : σ → Parser.Internal.Input → PM H (Parser.Internal.Step σ ρ)}
    {outer : τ → Parser.Internal.Input → PM H (Parser.Internal.Step τ χ)} (wrap : σ → τ)
    (after : ρ → PM H (Parser.Internal.Step τ χ))
    (hstep : ∀ state token, outer (wrap state) token =
      inner state token >>= Parser.Internal.Step.wrap wrap after)
    {state : σ} {tokens : List Parser.Internal.Input} {program : PM H α}
    {next : α → PM H (Parser.Internal.Step σ ρ)}
    (h : RunsS points inner state tokens program next) :
    RunsS points outer (wrap state) tokens program
      (fun a => next a >>= Parser.Internal.Step.wrap wrap after) := by
  refine ⟨h.1, fun rest => ?_⟩
  rw [driveS_embed wrap after hstep, h.2, bind_assoc]
  refine bind_congr fun e => ?_
  rcases e with (kind | kind | error) | a
  · simp [afterProgram]
  · simp [afterProgram]
  · simp [afterProgram]
  · simp only [afterProgram, resumeS, bind_assoc, ExceptT.run_bind]
    refine bind_congr fun e => ?_
    rcases e with (kind | kind | error) | (state' | result)
    · simp [onStep]
    · simp [onStep]
    · simp [onStep]
    · simp [onStep, Parser.Internal.Step.wrap, driveS_embed wrap after hstep]
      rfl
    · simp only [onStep, Parser.Internal.Step.wrap, pure_bind]

omit [LawfulMonad m] in
/-- Two states that step alike on the first token read alike. -/
theorem first {step : σ → Parser.Internal.Input → PM H (Parser.Internal.Step σ ρ)}
    {state state' : σ} {token : Parser.Internal.Input} {tokens : List Parser.Internal.Input}
    {program : PM H α} {next : α → PM H (Parser.Internal.Step σ ρ)}
    (heq : step state token = step state' token)
    (h : RunsS points step state' (token :: tokens) program next) :
    RunsS points step state (token :: tokens) program next := by
  refine ⟨h.1, fun rest => ?_⟩
  have := h.2 rest
  simp only [List.cons_append, driveS_cons, heq] at this ⊢
  exact this

end RunsS

end

end BSmtLib.Facts.Proofs.Parser.Category.Steps
