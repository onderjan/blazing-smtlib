module

public import BSmtLib.Facts.Proofs.Parser.Category.Steps
import all BSmtLib.Parser

@[expose] public section

/-!
# A parser stepped by single tokens, on a cursor, against `driveS`

On a cursor that gives a list of tokens, all in one version, the loop over single tokens
(`Parser.Internal.parseByToken`) does what `driveS` does on that list, with the token points that
mark nothing, read as `outcome` reads a parse (`parseByToken_driveS`): the parser it gives back
when it wants more is the state `driveS` waits in, and where it stops is the cursor after the
tokens `driveS` consumed. So every `RunsS` lemma about a parser's steps gives `Finishes`, `Waits` or
`Rejects` of the parser on cursors.
-/

namespace BSmtLib.Facts.Proofs.Parser.Category.CursorS

open BSmtLib.Token (Produce)
open BSmtLib.Parser (Parse ParseError ParseErrorCause ParseState SyntaxErrorKind)
open BSmtLib.Parser.Internal (PM)
open BSmtLib.Parser.Internal (ParseByToken takeOne rest parseByToken After)
open BSmtLib.Facts.Parser.Adapters.Bridge BSmtLib.Facts.Parser.Adapters.Run
open BSmtLib.Facts.Parser.Adapters.Cursor (Takes Reads noPoints)
open BSmtLib.Facts.Parser.Adapters.Outcome
open BSmtLib.Facts.Proofs.Parser.Category.Cursor BSmtLib.Facts.Proofs.Parser.Category.Steps
open BSmtLib.Facts.Proofs.Parser.Drive

section

variable {H : Type} {m : Type → Type} [Monad m] [LawfulMonad m] [Traits.Handler H m] {σ ρ : Type}
variable {points : BSmtLibSpec.Parser.Traversal.Points (StateT H m)}

/-- The result with the tokens after it made a suffix of `tokens` of the same length, if it can
be: what `driveS` gives back anyway. -/
def projS (tokens : List Parser.Internal.Input) :
    Res σ ρ (Traits.Handler.Error H) → Res σ ρ (Traits.Handler.Error H)
  | .done result rest => .done result (tokens.drop (tokens.length - rest.length))
  | .rejected kind rest => .rejected kind (tokens.drop (tokens.length - rest.length))
  | other => other

omit [Monad m] [LawfulMonad m] in
theorem projS_cons (token : Parser.Internal.Input) (tokens : List Parser.Internal.Input)
    (result : Res σ ρ (Traits.Handler.Error H)) :
    projS (token :: tokens) (projS tokens result) = projS tokens result := by
  have key : ∀ rest : List Parser.Internal.Input,
      (token :: tokens).drop ((token :: tokens).length -
        (tokens.drop (tokens.length - rest.length)).length) =
      tokens.drop (tokens.length - rest.length) := by
    intro rest
    simp only [List.length_drop, List.length_cons]
    rw [show tokens.length + 1 - (tokens.length - (tokens.length - rest.length)) =
      (tokens.length - rest.length) + 1 by omega]
    rfl
  rcases result with state | ⟨r, rest⟩ | ⟨kind, rest⟩ | error
  · rfl
  · simp only [projS, key]
  · simp only [projS, key]
  · rfl

theorem driveS_proj (step : σ → Parser.Internal.Input → PM H (Parser.Internal.Step σ ρ))
    (tokens : List Parser.Internal.Input) (state : σ) :
    driveS points step state tokens = projS tokens <$> driveS points step state tokens := by
  induction tokens generalizing state with
  | nil => simp [driveS_nil, projS]
  | cons token tokens ih =>
    rw [driveS_cons, map_bind]
    refine bind_congr fun e => ?_
    rcases e with (kind | error) | (state' | result)
    · simp [onStep, projS]
    · simp [onStep, projS]
    · simp only [onStep]
      conv => rhs; rw [ih state']
      conv => lhs; rw [ih state']
      rw [Functor.map_map]
      congr 1
      funext result
      exact (projS_cons token tokens result).symm
    · simp [onStep, projS]

end

section

variable {H P R σ : Type} {m : Type → Type} [Monad m] [LawfulMonad m] [Traits.Handler H m]
variable [ParseByToken P H m (Traits.Handler.Error H) R]
variable {version : Token.Version} {mk : σ → P}
  {step : σ → Parser.Internal.Input → PM H (Parser.Internal.Step σ R)} {fresh : P}
variable {Z : Type} [Produce Z]

/-- What the loop gave, read as `outcome` reads a parse. -/
def outcomeRest {origin : Z} :
    Except (ParseError (Traits.Handler.Error H)) (ControlFlow R) × P ×
      { z : Z // Produce.Consumed z origin } →
    Outcome R P Z (Traits.Handler.Error H)
  | (.ok (.break result), parser, next) => .finished result parser next.val
  | (.ok .continue, parser, _) => .waits parser
  | (.error error, _, next) =>
    match error.cause with
    | .syntax kind => .rejected kind next.val
    | .handler error => .failed error

/-- What `driveS` gave back, as the loop on the cursor gives it. -/
def convS (mk : σ → P) (fresh : P) (cursor : Z) (tokens : List Parser.Internal.Input) :
    Res σ R (Traits.Handler.Error H) → Outcome R P Z (Traits.Handler.Error H)
  | .waits state => .waits (mk state)
  | .done result rest => .finished result fresh (advance (tokens.length - rest.length) cursor)
  | .rejected kind rest => .rejected kind (advance (tokens.length - rest.length) cursor)
  | .failed error => .failed error

omit [Monad m] [LawfulMonad m] [ParseByToken P H m (Traits.Handler.Error H) R] in
theorem convS_proj {cursor after : Z} {raw : Produce.Token Z}
    {consumed : Produce.Consumed after cursor}
    (hnext : Produce.next? cursor = some (raw, ⟨after, consumed⟩))
    (token : Parser.Internal.Input) (tokens : List Parser.Internal.Input)
    (result : Res σ R (Traits.Handler.Error H)) :
    convS mk fresh after tokens (projS tokens result) =
      convS mk fresh cursor (token :: tokens) (projS tokens result) := by
  have key : ∀ rest : List Parser.Internal.Input,
      advance (tokens.length - (tokens.drop (tokens.length - rest.length)).length) after =
      advance ((token :: tokens).length -
        (tokens.drop (tokens.length - rest.length)).length) cursor := by
    intro rest
    simp only [List.length_drop, List.length_cons]
    rw [show tokens.length + 1 - (tokens.length - (tokens.length - rest.length)) =
      (tokens.length - (tokens.length - (tokens.length - rest.length))) + 1 by omega,
      advance_succ hnext]
  rcases result with state | ⟨r, rest⟩ | ⟨kind, rest⟩ | error
  · rfl
  · simp only [projS, convS, key]
  · simp only [projS, convS, key]
  · rfl

omit [ParseByToken P H m (Traits.Handler.Error H) R] in
/-- The step on the first token, then what the loop does after it, against `driveS`. -/
theorem step_afterS (state : σ) {cursor after : Z}
    {raw : Produce.Token Z} {consumed : Produce.Consumed after cursor}
    (hnext : Produce.next? cursor = some (raw, ⟨after, consumed⟩))
    {β : Type} (g : β → Outcome R P Z (Traits.Handler.Error H))
    (k : After P R (Traits.Handler.Error H) × { z : Z // Produce.Consumed z cursor } →
      StateT H m β)
    (tokens : List Parser.Internal.Input)
    (hstop : ∀ answer z, g <$> k (.stop answer fresh, z) =
      pure (outcomeRest (origin := cursor) (answer, fresh, z)))
    (hgo : ∀ state' z, z.val = after → g <$> k (.goOn (mk state'), z) =
      convS mk fresh after tokens <$> driveS noPoints step state' tokens)
    (token : Parser.Internal.Input) :
    ((fun e => (afterOf mk fresh e, (⟨after, consumed⟩ : { z : Z // Produce.Consumed z cursor })))
        <$> (step state token).run) >>= (fun x => g <$> k x) =
      convS mk fresh cursor (token :: tokens) <$>
        driveS noPoints step state (token :: tokens) := by
  rw [driveS_cons, tick_noPoints, pure_bind, bind_map_left, map_bind]
  refine bind_congr fun e => ?_
  rcases e with (kind | error) | (state' | result)
  · simp only [afterOf, hstop, outcomeRest, onStep, map_pure, convS, List.length_cons,
      Parser.ParseError.Internal.cause_new]
    rw [show tokens.length + 1 - tokens.length = 0 + 1 by omega, advance_succ hnext]
    rfl
  · simp only [afterOf, hstop, outcomeRest, onStep, map_pure, convS,
      Parser.ParseError.Internal.cause_new]
  · simp only [afterOf, onStep]
    rw [hgo state' _ rfl, driveS_proj step tokens state', Functor.map_map, Functor.map_map]
    congr 1
    funext x
    exact convS_proj hnext token tokens x
  · simp only [afterOf, hstop, outcomeRest, onStep, map_pure, convS, List.length_cons]
    rw [show tokens.length + 1 - tokens.length = 0 + 1 by omega, advance_succ hnext]
    rfl

theorem rest_driveS (sim : Simulates version mk step fresh) :
    (tokens : List Parser.Internal.Input) → (state : σ) → (origin cursor : Z) →
    (hc : Produce.Consumed cursor origin) → Reads version cursor tokens →
    outcomeRest <$> rest origin (mk state) cursor hc =
      convS mk fresh cursor tokens <$> driveS noPoints step state tokens
  | [], state, origin, cursor, hc, ⟨last, hlast, hnone⟩ => by
    rw [Takes.nil_inv hlast] at hnone
    rw [rest, hnone]
    simp [driveS_nil, outcomeRest, convS]
  | token :: tokens, state, origin, cursor, hc, ⟨last, hlast, hnone⟩ => by
    obtain ⟨after, raw, consumed, _, hnext, hver, rfl, htail⟩ := Takes.cons_inv hlast
    rw [rest, hnext]
    simp only
    rw [takeOne_sim sim state cursor raw after consumed hver, map_bind]
    refine step_afterS state hnext outcomeRest _ tokens ?_ ?_ _
    · intro answer z
      obtain ⟨z, hz⟩ := z
      simp only [map_pure]
      rcases answer with (_ | _) | (_ | _) <;> rfl
    · intro state' z hz
      obtain ⟨z, hz'⟩ := z
      dsimp only at hz
      subst hz
      exact rest_driveS sim tokens state' origin z _ ⟨last, htail, hnone⟩

/-- On a cursor that gives the tokens, all in the version, the loop over single tokens does
what `driveS` does on them. -/
theorem parseByToken_driveS (sim : Simulates version mk step fresh) (state : σ)
    (parseState : ParseState H) {cursor : Z} {tokens : List Parser.Internal.Input}
    (hreads : Reads version cursor tokens) :
    outcome <$> parseByToken (mk state) parseState cursor =
      convS mk fresh cursor tokens <$> driveS noPoints step state tokens := by
  obtain ⟨last, hlast, hnone⟩ := hreads
  cases tokens with
  | nil =>
    rw [Takes.nil_inv hlast] at hnone
    unfold parseByToken
    split
    · simp [driveS_nil, outcome, convS]
    · rename_i heq
      rw [hnone] at heq
      cases heq
  | cons token tokens =>
    obtain ⟨after, raw, consumed, _, hnext, hver, rfl, htail⟩ := Takes.cons_inv hlast
    unfold parseByToken
    split
    · rename_i heq
      rw [hnext] at heq
      cases heq
    · rename_i raw' after' consumed' heq
      rw [hnext] at heq
      cases heq
      rw [takeOne_sim sim state cursor raw after consumed hver, map_bind]
      refine step_afterS state hnext outcome _ tokens ?_ ?_ _
      · intro answer z
        obtain ⟨z, hz⟩ := z
        rcases answer with (_ | _) | (_ | _) <;> simp only [map_pure] <;> rfl
      · intro state' z hz
        obtain ⟨z, hz'⟩ := z
        dsimp only at hz
        subst hz
        rw [← rest_driveS sim tokens state' cursor z hz' ⟨last, htail, hnone⟩]
        simp only [map_bind]
        conv => rhs; rw [← bind_pure (rest cursor (mk state') z hz'), map_bind]
        refine bind_congr fun x => ?_
        obtain ⟨answer, parser, ⟨done, hd⟩⟩ := x
        rcases answer with (_ | _) | (_ | _) <;> simp only [map_pure] <;> rfl

/-- `driveS` over the tokens and anything after, as `RunsS` gives it, read on the cursor. -/
theorem outcome_of_runsS [Parse P H m (Traits.Handler.Error H) R]
    (hparse : ∀ {Z : Type} [Produce Z] (parser : P) (parseState : ParseState H) (cursor : Z),
      Parse.parse parser parseState cursor = parseByToken parser parseState cursor)
    {state : σ} (sim : Simulates version mk step fresh) {tokens : List Parser.Internal.Input}
    {α : Type} {program : PM H α} {next : α → PM H (Parser.Internal.Step σ R)}
    (h : RunsS noPoints step state tokens program next) (parseState : ParseState H)
    {cursor last : Z} {rest : List Parser.Internal.Input}
    (htakes : Takes version cursor tokens last) (hreads : Reads version last rest) :
    outcome <$> Parse.parse (mk state) parseState cursor =
      program.run >>= fun e => convS mk fresh cursor (tokens ++ rest) <$>
        afterProgram (fun a => resumeS noPoints step (next a) rest) rest e := by
  rw [hparse, parseByToken_driveS sim state parseState (Reads.of_takes htakes hreads), h.2 rest,
    map_bind]

theorem advance_rest {cursor last : Z} {tokens rest : List Parser.Internal.Input}
    (htakes : Takes version cursor tokens last) :
    advance ((tokens ++ rest).length - rest.length) cursor = last := by
  rw [List.length_append, show tokens.length + rest.length - rest.length = tokens.length by
    omega, advance_takes htakes]

/-- A parser whose steps run over the tokens and finish parses them on every cursor. -/
theorem parses_of_runsS [Parse P H m (Traits.Handler.Error H) R]
    (hparse : ∀ {Z : Type} [Produce Z] (parser : P) (parseState : ParseState H) (cursor : Z),
      Parse.parse parser parseState cursor = parseByToken parser parseState cursor)
    {state : σ} (sim : Simulates version mk step fresh)
    {tokens : List Parser.Internal.Input} {program : PM H R}
    (h : RunsS noPoints step state tokens program fun r => pure (.done r)) :
    Finishes version (mk state) tokens program fresh := by
  refine ⟨h.1, fun parseState cursor next rest htakes hreads => ?_⟩
  rw [outcome_of_runsS @hparse sim h parseState htakes hreads, map_eq_pure_bind]
  refine bind_congr fun e => ?_
  rcases e with (kind | error) | result
  · simp [afterProgram, convS, answer, advance_takes htakes]
  · simp [afterProgram, convS, answer]
  · simp [afterProgram, convS, answer, advance_takes htakes]

/-- A parser whose steps run over the tokens and stay in a state wants more on every cursor that
has exactly the tokens. -/
theorem waits_of_runsS [Parse P H m (Traits.Handler.Error H) R]
    (hparse : ∀ {Z : Type} [Produce Z] (parser : P) (parseState : ParseState H) (cursor : Z),
      Parse.parse parser parseState cursor = parseByToken parser parseState cursor)
    {state : σ} (sim : Simulates version mk step fresh)
    {tokens : List Parser.Internal.Input} {α : Type} {program : PM H α} {after : α → σ}
    (h : RunsS noPoints step state tokens program fun a => pure (.more (after a))) :
    Waits version (mk state) tokens program (fun a => mk (after a)) := by
  refine ⟨h.1, fun parseState cursor last htakes hnone => ?_⟩
  have hreads : Reads version last [] := ⟨last, .nil last, hnone⟩
  rw [outcome_of_runsS @hparse sim h parseState htakes hreads, map_eq_pure_bind]
  refine bind_congr fun e => ?_
  rcases e with (kind | error) | a
  · simp [afterProgram, convS, answer, advance_takes htakes]
  · simp [afterProgram, convS, answer]
  · simp [afterProgram, convS, answer, driveS_nil]

/-- A parser whose steps run over the tokens and then fail with a syntax error rejects them on
every cursor. -/
theorem rejects_of_runsS [Parse P H m (Traits.Handler.Error H) R]
    (hparse : ∀ {Z : Type} [Produce Z] (parser : P) (parseState : ParseState H) (cursor : Z),
      Parse.parse parser parseState cursor = parseByToken parser parseState cursor)
    {state : σ} (sim : Simulates version mk step fresh)
    {tokens : List Parser.Internal.Input} {α : Type} {program : PM H α}
    {kind : SyntaxErrorKind}
    (h : RunsS noPoints step state tokens program fun _ => throw (.syntax kind)) :
    Rejects version (mk state) tokens ((fun _ => ()) <$> program) kind := by
  refine ⟨handlerOnly_map _ h.1, fun parseState cursor next rest htakes hreads => ?_⟩
  rw [outcome_of_runsS @hparse sim h parseState htakes hreads, ExceptT.run_map, map_eq_pure_bind,
    bind_map_left]
  refine bind_congr fun e => ?_
  rcases e with (kind' | error) | a
  · simp [afterProgram, convS, answer, Except.map, advance_takes htakes]
  · simp [afterProgram, convS, answer, Except.map]
  · simp [afterProgram, convS, answer, Except.map, advance_takes htakes]


/-- Steps that only move the parser, as a run without calls. -/
theorem RunsS.of_moves {step : σ → Parser.Internal.Input → PM H (Parser.Internal.Step σ R)} :
    {state last : σ} → {tokens : List Parser.Internal.Input} → Moves step state tokens last →
    RunsS noPoints step state tokens (pure ()) fun _ => pure (.more last)
  | _, _, [], .nil _ => RunsS.nil () rfl
  | _, _, _ :: _, .cons h hrest =>
    ((RunsS.token_more h).append fun _ => RunsS.of_moves hrest).congr
      (by simp) rfl

/-- From a state from which the steps only move the parser over the tokens and then fail at the
token with a syntax error, the parser rejects the tokens and the token on every cursor, making
no call. -/
theorem rejects_of_movesS [Parse P H m (Traits.Handler.Error H) R]
    (hparse : ∀ {Z : Type} [Produce Z] (parser : P) (parseState : ParseState H) (cursor : Z),
      Parse.parse parser parseState cursor = parseByToken parser parseState cursor)
    (sim : Simulates version mk step fresh) {kind : SyntaxErrorKind}
    {token : Parser.Internal.Input} {state last : σ} {tokens : List Parser.Internal.Input}
    (hmoves : Moves step state tokens last) (hfail : step last token = throw (.syntax kind)) :
    Rejects version (mk state) (tokens ++ [token]) (pure () : PM H Unit) kind := by
  have h₂ : RunsS noPoints step last [token] (do tick noPoints token; (pure () : PM H Unit))
      fun _ => throw (ParseErrorCause.syntax kind) :=
    RunsS.token (by simp only [pure_bind]; exact hfail) (handlerOnly_pure ())
  have h := (RunsS.of_moves hmoves).append fun _ => h₂
  have := rejects_of_runsS @hparse sim h
  simpa [tick_noPoints] using this

end

/-! ## Steps whose results are mapped

A parser that hands over its steps' results converted, as the parsers with owned results do,
runs as its steps do, with the results converted. -/

section

variable {H : Type} {m : Type → Type} [Monad m] [LawfulMonad m] [Traits.Handler H m]
variable {σ ρ τ α : Type} {points : BSmtLibSpec.Parser.Traversal.Points (StateT H m)}

/-- A step with its result converted by `f`. -/
def mapDone (f : ρ → τ) : Parser.Internal.Step σ ρ → Parser.Internal.Step σ τ
  | .more state => .more state
  | .done result => .done (f result)

/-- The steps with their results converted by `f`. -/
def mapSteps (f : ρ → τ) (step : σ → Parser.Internal.Input → PM H (Parser.Internal.Step σ ρ)) :
    σ → Parser.Internal.Input → PM H (Parser.Internal.Step σ τ) :=
  fun state token => mapDone f <$> step state token

/-- Where the steps stopped, with the result converted by `f`. -/
def Res.mapDone {E : Type} (f : ρ → τ) : Res σ ρ E → Res σ τ E
  | .waits state => .waits state
  | .done result rest => .done (f result) rest
  | .rejected kind rest => .rejected kind rest
  | .failed error => .failed error

theorem onStep_mapDone (f : ρ → τ)
    {k : σ → StateT H m (Res σ ρ (Traits.Handler.Error H))}
    {k' : σ → StateT H m (Res σ τ (Traits.Handler.Error H))}
    (hk : ∀ state, k' state = Res.mapDone f <$> k state) (rest : List Parser.Internal.Input)
    (e : Except (ParseErrorCause (Traits.Handler.Error H)) (Parser.Internal.Step σ ρ)) :
    onStep k' rest (mapDone f <$> e) = Res.mapDone f <$> onStep k rest e := by
  rcases e with (kind | error) | (state | result)
  · simp [onStep, Res.mapDone]; rfl
  · simp [onStep, Res.mapDone]; rfl
  · exact hk state
  · simp [onStep, Res.mapDone]; rfl

theorem driveS_mapSteps (f : ρ → τ)
    (step : σ → Parser.Internal.Input → PM H (Parser.Internal.Step σ ρ)) :
    (tokens : List Parser.Internal.Input) → (state : σ) →
    driveS points (mapSteps f step) state tokens =
      Res.mapDone f <$> driveS points step state tokens
  | [], state => by simp [driveS_nil, Res.mapDone]
  | token :: tokens, state => by
    rw [driveS_cons, driveS_cons, map_bind]
    simp only [mapSteps, ExceptT.run_bind, ExceptT.run_map, bind_assoc]
    refine bind_congr fun e => ?_
    rcases e with error | u
    · rcases error with kind | error <;> simp [onStep, Res.mapDone]
    · simp only [bind_map_left]
      refine bind_congr fun e' => ?_
      exact onStep_mapDone f (fun state => driveS_mapSteps f step tokens state) tokens e'

theorem resumeS_mapSteps (f : ρ → τ)
    (step : σ → Parser.Internal.Input → PM H (Parser.Internal.Step σ ρ))
    (next : PM H (Parser.Internal.Step σ ρ)) (rest : List Parser.Internal.Input) :
    resumeS points (mapSteps f step) (mapDone f <$> next) rest =
      Res.mapDone f <$> resumeS points step next rest := by
  simp only [resumeS, ExceptT.run_map, bind_map_left, map_bind]
  refine bind_congr fun e => ?_
  exact onStep_mapDone f (fun state => driveS_mapSteps f step rest state) rest e

/-- A run of the steps is a run of the steps with their results converted. -/
theorem RunsS.mapSteps (f : ρ → τ)
    {step : σ → Parser.Internal.Input → PM H (Parser.Internal.Step σ ρ)} {state : σ}
    {tokens : List Parser.Internal.Input} {program : PM H α}
    {next : α → PM H (Parser.Internal.Step σ ρ)}
    (h : RunsS points step state tokens program next) :
    RunsS points (CursorS.mapSteps f step) state tokens program
      (fun a => mapDone f <$> next a) := by
  refine ⟨h.1, fun rest => ?_⟩
  rw [driveS_mapSteps, h.2, map_bind]
  refine bind_congr fun e => ?_
  rcases e with (kind | error) | a
  · simp [afterProgram, Res.mapDone]
  · simp [afterProgram, Res.mapDone]
  · exact (resumeS_mapSteps f step (next a) rest).symm

/-- Steps that only move the parser move it alike with their results converted. -/
theorem Moves.mapSteps (f : ρ → τ)
    {step : σ → Parser.Internal.Input → PM H (Parser.Internal.Step σ ρ)} :
    {state last : σ} → {tokens : List Parser.Internal.Input} → Moves step state tokens last →
    Moves (CursorS.mapSteps f step) state tokens last
  | _, _, [], .nil _ => .nil _
  | _, _, _ :: _, .cons h hrest =>
    .cons (by simp [CursorS.mapSteps, h, mapDone]) (Moves.mapSteps f hrest)

end

section

variable {H P R ρ σ : Type} {m : Type → Type} [Monad m] [LawfulMonad m] [Traits.Handler H m]
variable [ParseByToken P H m (Traits.Handler.Error H) R] [Parse P H m (Traits.Handler.Error H) R]
variable {version : Token.Version} {mk : σ → P}
  {step : σ → Parser.Internal.Input → PM H (Parser.Internal.Step σ ρ)} {fresh : P} {f : ρ → R}
  {state : σ} {tokens : List Parser.Internal.Input}

/-- `parses_of_runsS` for a parser whose steps' results it converts by `f`. -/
theorem parses_of_runsS_map
    (hparse : ∀ {Z : Type} [Produce Z] (parser : P) (parseState : ParseState H) (cursor : Z),
      Parse.parse parser parseState cursor = parseByToken parser parseState cursor)
    (sim : Simulates version mk (mapSteps f step) fresh) {program : PM H ρ}
    (h : RunsS noPoints step state tokens program fun r => pure (.done r)) :
    Finishes version (mk state) tokens (f <$> program) fresh :=
  parses_of_runsS @hparse sim (RunsS.map_program (f := f) (next := fun r => pure (.done r))
    ((RunsS.mapSteps f h).congr rfl (by funext; simp [mapDone])))

/-- `waits_of_runsS` for a parser whose steps' results it converts by `f`. -/
theorem waits_of_runsS_map
    (hparse : ∀ {Z : Type} [Produce Z] (parser : P) (parseState : ParseState H) (cursor : Z),
      Parse.parse parser parseState cursor = parseByToken parser parseState cursor)
    (sim : Simulates version mk (mapSteps f step) fresh) {α : Type} {program : PM H α}
    {after : α → σ} (h : RunsS noPoints step state tokens program fun a => pure (.more (after a))) :
    Waits version (mk state) tokens program (fun a => mk (after a)) :=
  waits_of_runsS @hparse sim ((RunsS.mapSteps f h).congr rfl (by funext; simp [mapDone]))

/-- `rejects_of_runsS` for a parser whose steps' results it converts by `f`. -/
theorem rejects_of_runsS_map
    (hparse : ∀ {Z : Type} [Produce Z] (parser : P) (parseState : ParseState H) (cursor : Z),
      Parse.parse parser parseState cursor = parseByToken parser parseState cursor)
    (sim : Simulates version mk (mapSteps f step) fresh) {α : Type} {program : PM H α}
    {kind : SyntaxErrorKind}
    (h : RunsS noPoints step state tokens program fun _ => throw (.syntax kind)) :
    Rejects version (mk state) tokens ((fun _ => ()) <$> program) kind :=
  rejects_of_runsS @hparse sim ((RunsS.mapSteps f h).congr rfl (by funext; simp))

/-- `rejects_of_movesS` for a parser whose steps' results it converts by `f`. -/
theorem rejects_of_movesS_map
    (hparse : ∀ {Z : Type} [Produce Z] (parser : P) (parseState : ParseState H) (cursor : Z),
      Parse.parse parser parseState cursor = parseByToken parser parseState cursor)
    (sim : Simulates version mk (mapSteps f step) fresh) {kind : SyntaxErrorKind}
    {token : Parser.Internal.Input} {last : σ}
    (hmoves : Moves step state tokens last) (hfail : step last token = throw (.syntax kind)) :
    Rejects version (mk state) (tokens ++ [token]) (pure () : PM H Unit) kind :=
  rejects_of_movesS @hparse sim (Moves.mapSteps f hmoves) (by simp [mapSteps, hfail])

end

end BSmtLib.Facts.Proofs.Parser.Category.CursorS
