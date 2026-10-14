module

public import BSmtLib.Facts.Proofs.Reader.Param.Adapter
import all BSmtLib.Parser
import all BSmtLib.Parser.Adapter
import all BSmtLib.Parser.Script

@[expose] public section

/-!
# Two postures, one looser than the other

The script parser reads its posture only in `VersionPosture.check`, at a version declaration. A
posture `loose` is looser than `strict` (`Looser`) if it limits the declarations alike and allows
every version `strict` allows; then where `strict` lets a declaration pass, so does `loose`. So
the parse adapter with the recording handler, the same in all but the posture, takes each token
alike under the two postures, unless the token fails under `strict` (`takeOne_looser`), and so
does each call of the adapter (`consume_looser`).
-/

namespace BSmtLib.Facts.Proofs.Reader.Param.Posture

open BSmtLibSpec.Parser.Properties
open BSmtLib.Parser
open BSmtLib.Facts.Reader.Adapters (RecAdapter)
open BSmtLib.Facts.Proofs.Reader.Param.Adapter (paLoop startLog consume_eq id_bind_eq)
open BSmtLib.Facts.Proofs.Parser.Cut BSmtLib.Parser.Adapter BSmtLib.Parser.Command
open BSmtLib.Parser.Script BSmtLib.Parser.Script.VersionPosture BSmtLib.Traits

/-- `loose` limits the declarations as `strict` does and allows every version `strict` allows. -/
structure Looser (strict loose : Token.VersionPosture) : Prop where
  max : strict.maxDeclarations = loose.maxDeclarations
  allowed : ∀ version, strict.allowed.contains version = true →
    loose.allowed.contains version = true

theorem check_looser {strict loose : Token.VersionPosture} (hl : Looser strict loose)
    (declarations : Nat) (version : Token.Version)
    (h : (check strict) declarations version = none) :
    (check loose) declarations version = none := by
  unfold VersionPosture.check at h ⊢
  rw [← hl.max]
  cases hmax : strict.maxDeclarations with
  | none =>
    rw [hmax] at h
    simp only at h ⊢
    split at h
    · rename_i hc
      rw [hl.allowed version hc]
      rfl
    · cases h
  | some limit =>
    rw [hmax] at h
    simp only at h ⊢
    split at h
    · cases h
    · rename_i hlimit
      simp only [hlimit, ite_false]
      split at h
      · rename_i hc
        rw [hl.allowed version hc]
        rfl
      · cases h

/-! ## The parser under another posture -/

/-- The script parser with the posture replaced. -/
def withPosture (posture : Token.VersionPosture) (parser : ScriptParser (List Event)) :
    ScriptParser (List Event) :=
  { parser with posture }

/-- The adapter with the posture of its parser replaced. -/
def adapterWith (posture : Token.VersionPosture) (adapter : RecAdapter) : RecAdapter :=
  { adapter with parser := withPosture posture adapter.parser }

/-- What the script parser's step does after its command parser's step. -/
def scriptAfter (parser : ScriptParser (List Event)) :
    Step (CommandStateOf (List Event)) CommandOutcome →
      Parser.Quiet.RPM (Flow Parser.Quiet.RPM (ScriptParser (List Event)) Unit)
  | .more command => return .more { parser with command }
  | .done .command => return .more { parser with command := .awaiting }
  | .done (.setVersion declared) =>
    match (check parser.posture) parser.declarations declared with
    | some kind => syntaxError kind
    | none =>
      return .switchVersion declared (do
        ExceptT.lift (Handler.setVersion (H := List Event) declared)
        return .more
          { parser with command := .awaiting, declarations := parser.declarations + 1 })
  | .done .exit => return .discardRest (pure (.more { parser with command := .awaiting }))
  | .done .endOfInput => return .done ()

theorem step_eq (version : Token.Version) (parser : ScriptParser (List Event)) (token : Input) :
    Parse.step (H := List Event) version parser token =
      (commandStep version parser.command token >>= scriptAfter parser) := by
  show ScriptParser.step version parser token = _
  unfold ScriptParser.step
  congr
  funext outcome
  rcases outcome with command | (_ | declared | _ | _) <;> rfl

/-- A step of the parser under the posture, as the parser under `strict` makes it. -/
def StepWith (posture strict : Token.VersionPosture) :
    Step (ScriptParser (List Event)) Unit → Step (ScriptParser (List Event)) Unit → Prop
  | .more p, .more q => q = withPosture posture p ∧ p.posture = strict
  | .done r, .done r' => r = r'
  | _, _ => False

/-- A run of a resumption under the posture, as the one under `strict` runs, unless that one
fails. -/
def ResumeWith (posture strict : Token.VersionPosture)
    (x y : Except (ParseErrorCause Unit) (Step (ScriptParser (List Event)) Unit) × List Event) :
    Prop :=
  (∃ e, x.1 = .error e) ∨
    ∃ s₁ s₂, x.1 = .ok s₁ ∧ y = (.ok s₂, x.2) ∧ StepWith posture strict s₁ s₂

/-- What the step under the posture asks, as the one under `strict` asks. -/
def FlowWith (posture strict : Token.VersionPosture) :
    Flow Parser.Quiet.RPM (ScriptParser (List Event)) Unit → Flow Parser.Quiet.RPM
        (ScriptParser (List Event)) Unit → Prop
  | .more p, .more q => q = withPosture posture p ∧ p.posture = strict
  | .done r, .done r' => r = r'
  | .switchVersion v a, .switchVersion v' b =>
    v = v' ∧ ∀ events, ResumeWith posture strict (a.run.run events) (b.run.run events)
  | .discardRest a, .discardRest b =>
    ∀ events, ResumeWith posture strict (a.run.run events) (b.run.run events)
  | _, _ => False

theorem scriptAfter_looser {strict loose : Token.VersionPosture} (hl : Looser strict loose)
    (parser : ScriptParser (List Event)) (hp : parser.posture = strict)
    (outcome : Step (CommandStateOf (List Event)) CommandOutcome) (events : List Event) :
    (∃ e, ((scriptAfter parser outcome).run.run events).1 = .error e) ∨
      ∃ f₁ f₂, (scriptAfter parser outcome).run.run events = (.ok f₁, events) ∧
        (scriptAfter (withPosture loose parser) outcome).run.run events = (.ok f₂, events) ∧
        FlowWith loose strict f₁ f₂ := by
  rcases outcome with command | (_ | declared | _ | _)
  · exact .inr ⟨_, _, rfl, rfl, rfl, hp⟩
  · exact .inr ⟨_, _, rfl, rfl, rfl, hp⟩
  · unfold scriptAfter
    cases hc : (check parser.posture) parser.declarations declared with
    | some kind =>
      exact .inl ⟨.syntax kind, by simp only [hc]; rfl⟩
    | none =>
      have hc' : (check (withPosture loose parser).posture) (withPosture loose parser).declarations
          declared = none := check_looser hl _ _ (by rw [← hp]; exact hc)
      refine .inr ⟨.switchVersion declared (do
          ExceptT.lift (Handler.setVersion (H := List Event) declared)
          return .more
            { parser with command := .awaiting, declarations := parser.declarations + 1 }),
        .switchVersion declared (do
          ExceptT.lift (Handler.setVersion (H := List Event) declared)
          return .more
            { withPosture loose parser with
              command := .awaiting, declarations := parser.declarations + 1 }),
        by simp only [hc]; rfl, by simp only [hc']; rfl, rfl, fun ev => ?_⟩
      exact .inr ⟨_, _, rfl, rfl, rfl, hp⟩
  · exact .inr ⟨_, _, rfl, rfl, fun ev => .inr ⟨_, _, rfl, rfl, rfl, hp⟩⟩
  · exact .inr ⟨_, _, rfl, rfl, rfl⟩

/-! ## A token -/

/-- What the adapter does with a token under the posture, as under `strict`. -/
def AfterWith (posture strict : Token.VersionPosture) :
    ParseAdapter.After (ScriptParser (List Event)) Unit Unit →
      ParseAdapter.After (ScriptParser (List Event)) Unit Unit → Prop
  | .goOn p, .goOn q => q = withPosture posture p ∧ p.posture = strict
  | .stop a p, .stop a' q => a' = a ∧ q = withPosture posture p ∧ p.posture = strict
  | _, _ => False

/-- The adapter's handling of a token fails. -/
def IsFailure : ParseAdapter.After (ScriptParser (List Event)) Unit Unit → Prop
  | .stop (.error _) _ => True
  | _ => False

/-- The adapter takes a token under `loose` as under `strict`, unless it fails under `strict`. -/
theorem takeOne_looser {strict loose : Token.VersionPosture} (hl : Looser strict loose)
    (parser : ScriptParser (List Event)) (hp : parser.posture = strict) {b : Token.BatchTag}
    (cursor next : Token.BatchCursor b) (token : Token b) (consumed : next.Consumed cursor)
    (handler : List Event) :
    IsFailure ((ParseAdapter.takeOne (H := List Event) (m := Id) parser cursor token next
        consumed).run handler).1.1 ∨
      (AfterWith loose strict
          ((ParseAdapter.takeOne (H := List Event) (m := Id) parser cursor token next
            consumed).run handler).1.1
          ((ParseAdapter.takeOne (H := List Event) (m := Id) (withPosture loose parser) cursor
            token next consumed).run handler).1.1 ∧
        ((ParseAdapter.takeOne (H := List Event) (m := Id) (withPosture loose parser) cursor
            token next consumed).run handler).1.2 =
          ((ParseAdapter.takeOne (H := List Event) (m := Id) parser cursor token next
            consumed).run handler).1.2 ∧
        ((ParseAdapter.takeOne (H := List Event) (m := Id) (withPosture loose parser) cursor
            token next consumed).run handler).2 =
          ((ParseAdapter.takeOne (H := List Event) (m := Id) parser cursor token next
            consumed).run handler).2) := by
  simp only [ParseAdapter.takeOne, StateT.run_bind]
  rw [run_bind_ok (arrive_run _ _ _), run_bind_ok (arrive_run _ _ _), step_eq, step_eq,
    run_bind_split, run_bind_split]
  have hcmd : (withPosture loose parser).command = parser.command := rfl
  have harr : arrivalCalls (withPosture loose parser)
      (Input.ofSyntax (Token.Produce.«syntax» next token)) =
      arrivalCalls parser (Input.ofSyntax (Token.Produce.«syntax» next token)) := rfl
  rw [hcmd, harr]
  generalize (commandStep (Token.Produce.version next) parser.command
    (Input.ofSyntax (Token.Produce.«syntax» next token))).run.run
      (arrivalCalls parser (Input.ofSyntax (Token.Produce.«syntax» next token)) ++ handler) = c
  obtain ⟨res, handler'⟩ := c
  rcases res with e | outcome
  · exact .inl trivial
  · dsimp only
    rcases scriptAfter_looser hl parser hp outcome handler' with ⟨e, he⟩ | ⟨f₁, f₂, h₁, h₂, hf⟩
    · generalize (scriptAfter parser outcome).run.run handler' = s at he
      obtain ⟨r, h''⟩ := s
      dsimp only at he
      subst he
      exact .inl trivial
    · rw [h₁, h₂]
      simp only [id_bind_eq]
      cases f₁ with
      | more p₁ =>
        cases f₂ with
        | more p₂ =>
          obtain ⟨rfl, hp₁⟩ := hf
          exact .inr ⟨⟨rfl, hp₁⟩, rfl, rfl⟩
        | _ => cases hf
      | done r =>
        cases f₂ with
        | done r' =>
          cases hf
          exact .inr ⟨⟨rfl, rfl, hp⟩, rfl, rfl⟩
        | _ => cases hf
      | switchVersion v a =>
        cases f₂ with
        | switchVersion v' b' =>
          obtain ⟨rfl, hr⟩ := hf
          dsimp only
          split
          · exact .inl trivial
          · simp only [StateT.run_bind]
            rcases hr handler' with ⟨e, he⟩ | ⟨s₁, s₂, hs₁, hs₂, hs⟩
            · generalize a.run.run handler' = q at he
              obtain ⟨r, h''⟩ := q
              dsimp only at he
              subst he
              exact .inl trivial
            · generalize a.run.run handler' = q at hs₁ hs₂
              obtain ⟨r, h''⟩ := q
              dsimp only at hs₁ hs₂
              subst hs₁
              rw [hs₂]
              simp only [id_bind_eq]
              cases s₁ with
              | more p₁ =>
                cases s₂ with
                | more p₂ =>
                  obtain ⟨rfl, hp₁⟩ := hs
                  exact .inr ⟨⟨rfl, rfl, hp₁⟩, rfl, rfl⟩
                | done _ => cases hs
              | done r =>
                cases s₂ with
                | done r' =>
                  cases hs
                  exact .inr ⟨⟨rfl, rfl, hp⟩, rfl, rfl⟩
                | more _ => cases hs
        | _ => cases hf
      | discardRest a =>
        cases f₂ with
        | discardRest b' =>
          dsimp only
          simp only [StateT.run_bind]
          rcases hf handler' with ⟨e, he⟩ | ⟨s₁, s₂, hs₁, hs₂, hs⟩
          · generalize a.run.run handler' = q at he
            obtain ⟨r, h''⟩ := q
            dsimp only at he
            subst he
            exact .inl trivial
          · generalize a.run.run handler' = q at hs₁ hs₂
            obtain ⟨r, h''⟩ := q
            dsimp only at hs₁ hs₂
            subst hs₁
            rw [hs₂]
            simp only [id_bind_eq]
            cases s₁ with
            | more p₁ =>
              cases s₂ with
              | more p₂ =>
                obtain ⟨rfl, hp₁⟩ := hs
                exact .inr ⟨⟨rfl, rfl, hp₁⟩, rfl, rfl⟩
              | done _ => cases hs
            | done r =>
              cases s₂ with
              | done r' =>
                cases hs
                exact .inr ⟨⟨rfl, rfl, hp⟩, rfl, rfl⟩
              | more _ => cases hs
        | _ => cases hf

/-! ## A call -/

/-- The adapter's loop over a cursor goes alike under `loose` as under `strict`, unless it fails
under `strict`. -/
theorem paLoop_looser {strict loose : Token.VersionPosture} (hl : Looser strict loose)
    {b : Token.BatchTag} :
    ∀ (n : Nat) (parser : ScriptParser (List Event)) (cursor : Token.BatchCursor b)
      (handler : List Event), cursor.remaining < n → parser.posture = strict →
      (∃ e, ((paLoop parser cursor).run handler).1.1 = .error e) ∨
        ((paLoop (withPosture loose parser) cursor).run handler =
          ((((paLoop parser cursor).run handler).1.1,
            withPosture loose ((paLoop parser cursor).run handler).1.2.1,
            ((paLoop parser cursor).run handler).1.2.2), ((paLoop parser cursor).run handler).2) ∧
          ((paLoop parser cursor).run handler).1.2.1.posture = strict)
  | 0, _, _, _, hn, _ => absurd hn (Nat.not_lt_zero _)
  | n + 1, parser, cursor, handler, hn, hp => by
    rw [paLoop, paLoop]
    by_cases h : cursor.HasNext
    · rw [dite_eq_left_of_eq_true (eq_true h), dite_eq_left_of_eq_true (eq_true h)]
      rcases hnext : cursor.next h with ⟨token, ⟨next, consumed⟩⟩
      dsimp only
      simp only [StateT.run_bind]
      have ht := takeOne_looser hl parser hp cursor next token consumed handler
      generalize (ParseAdapter.takeOne (H := List Event) (m := Id) parser cursor token next
        consumed).run handler = t₁ at ht ⊢
      generalize (ParseAdapter.takeOne (H := List Event) (m := Id) (withPosture loose parser)
        cursor token next consumed).run handler = t₂ at ht ⊢
      obtain ⟨⟨after₁, ⟨later₁, taken₁⟩⟩, h₁⟩ := t₁
      obtain ⟨⟨after₂, ⟨later₂, taken₂⟩⟩, h₂⟩ := t₂
      simp only [id_bind_eq]
      rcases ht with hf | ⟨ha, hc, hh⟩
      · dsimp only at hf
        rcases after₁ with p₁ | ⟨e | flow, p₁⟩
        · simp only [IsFailure] at hf
        · exact .inl ⟨e, rfl⟩
        · simp only [IsFailure] at hf
      · simp only [Subtype.mk.injEq] at hc
        dsimp only at hh
        subst hc hh
        rcases after₁ with p₁ | ⟨answer, p₁⟩
        · rcases after₂ with p₂ | ⟨answer', p₂⟩
          · obtain ⟨rfl, hp₁⟩ := ha
            exact paLoop_looser hl n p₁ later₂ h₂
              (Nat.lt_of_lt_of_le (Token.BatchCursor.Consumed.remaining_lt taken₁)
                  (Nat.le_of_lt_succ hn))
              hp₁
          · cases ha
        · rcases after₂ with p₂ | ⟨answer', p₂⟩
          · cases ha
          · obtain ⟨rfl, rfl, hp₁⟩ := ha
            exact .inr ⟨rfl, hp₁⟩
    · rw [dite_eq_right_of_eq_false (eq_false h), dite_eq_right_of_eq_false (eq_false h)]
      exact .inr ⟨rfl, hp⟩

/-- A call of the adapter goes alike under `loose` as under `strict`, unless it fails under
`strict`; the parser keeps its posture. -/
theorem consume_looser {strict loose : Token.VersionPosture} (hl : Looser strict loose)
    {b : Token.BatchTag}
    (cursor : Token.BatchCursor b) (h : cursor.HasNext) (adapter : RecAdapter)
    (hp : adapter.parser.posture = strict) :
    (∃ e, ((Token.ConsumeFrom.consume (m := Id) cursor h : StateT RecAdapter Id _).run
        adapter).1.1 = .error e) ∨
      ((Token.ConsumeFrom.consume (m := Id) cursor h : StateT RecAdapter Id _).run
          (adapterWith loose adapter) =
        (((Token.ConsumeFrom.consume (m := Id) cursor h : StateT RecAdapter Id _).run adapter).1,
          adapterWith loose
            ((Token.ConsumeFrom.consume (m := Id) cursor h : StateT RecAdapter Id _).run
                adapter).2) ∧
        ((Token.ConsumeFrom.consume (m := Id) cursor h : StateT RecAdapter Id _).run
          adapter).2.parser.posture = strict) := by
  have e₁ := consume_eq cursor h adapter
  have e₂ := consume_eq cursor h (adapterWith loose adapter)
  have hs : startLog (adapterWith loose adapter) cursor.version = startLog adapter cursor.version :=
    rfl
  have hpa : (adapterWith loose adapter).parser = withPosture loose adapter.parser := rfl
  rw [hs, hpa] at e₂
  generalize (Token.ConsumeFrom.consume (m := Id) cursor h : StateT RecAdapter Id _).run adapter =
      q₁
    at e₁ ⊢
  generalize (Token.ConsumeFrom.consume (m := Id) cursor h : StateT RecAdapter Id _).run
    (adapterWith loose adapter) = q₂ at e₂ ⊢
  have hl' := paLoop_looser hl (cursor.remaining + 1) adapter.parser cursor
    (startLog adapter cursor.version) (Nat.lt_succ_self _) hp
  generalize (paLoop adapter.parser cursor).run (startLog adapter cursor.version) = r₁
    at e₁ hl'
  generalize (paLoop (withPosture loose adapter.parser) cursor).run
    (startLog adapter cursor.version) = r₂ at e₂ hl'
  obtain ⟨⟨a₁, ⟨c₁, t₁⟩⟩, s₁⟩ := q₁
  obtain ⟨⟨a₂, ⟨c₂, t₂⟩⟩, s₂⟩ := q₂
  simp only [Prod.mk.injEq] at e₁ e₂
  obtain ⟨rfl, rfl, rfl⟩ := e₁
  obtain ⟨rfl, rfl, rfl⟩ := e₂
  rcases hl' with ⟨e, he⟩ | ⟨hr, hp'⟩
  · exact .inl ⟨e, he⟩
  · subst hr
    exact .inr ⟨rfl, hp'⟩

end BSmtLib.Facts.Proofs.Reader.Param.Posture
