module

public import BSmtLib.Facts.Proofs.Reader.Param.Link
import all BSmtLib.Parser
import all BSmtLib.Parser.Script

@[expose] public section

/-!
# The script parser keeps its posture

Every parser state that the script parser's step goes on with has the posture of the parser it
started from (`step_posture`), so the recording run keeps the posture it starts with
(`recRun_posture`).
-/

namespace BSmtLib.Facts.Proofs.Reader.Param.KeepsPosture

open BSmtLib.Parser BSmtLib.Parser.Script
open BSmtLibSpec.Parser.Properties (Event)
open BSmtLib.Facts.Proofs.Parser.Quiet (RPM)
open BSmtLib.Facts.Proofs.Parser.Cut
open BSmtLib.Facts.Proofs.Reader.Param.Link (recRun recRun_snoc)
open BSmtLib.Facts.Parser.Adapters.Run (unrestrictedPosture)
open BSmtLib.Facts.Parser.Adapters.Run.Rejection (LibItem)
open BSmtLib.Facts.Proofs.Reader.Param.Adapter (id_bind_eq)

/-- Every result of the action, where it does not fail, satisfies `P`. -/
def MPost {α : Type} (P : α → Prop) (x : RPM α) : Prop :=
  ∀ log a log', x.run.run log = (.ok a, log') → P a

theorem MPost.pure {α : Type} {P : α → Prop} {a : α} (h : P a) :
    MPost P (Pure.pure a : RPM α) := by
  intro _ _ _ hr
  cases hr
  exact h

theorem MPost.throw {α : Type} {P : α → Prop} (e : ParseErrorCause Unit) :
    MPost P (MonadExcept.throw e : RPM α) := by
  intro _ _ _ hr
  cases hr

theorem MPost.bind {α β : Type} {P : β → Prop} {x : RPM α} {k : α → RPM β}
    (hk : ∀ a, MPost P (k a)) : MPost P (x >>= k) := by
  intro log b log' hr
  simp only [ExceptT.run_bind, StateT.run_bind] at hr
  rcases hx : x.run.run log with ⟨r, l⟩
  rw [hx] at hr
  rcases r with e | a
  · cases hr
  · exact hk a l b log' hr

/-- A step of the parser that goes on, with the posture. -/
def StepPost (q : Token.VersionPosture) : Internal.Step (ScriptParser (List Event)) Unit → Prop
  | .more parser => parser.posture = q
  | .done _ => True

/-- What a step asks of its loop: every parser it goes on with, then or after the action on the
cursor, has the posture. -/
def FlowPost (q : Token.VersionPosture) :
    Internal.Flow RPM (ScriptParser (List Event)) Unit → Prop
  | .more parser => parser.posture = q
  | .done _ => True
  | .switchVersion _ resume => MPost (StepPost q) resume
  | .discardRest resume => MPost (StepPost q) resume

/-- The script parser's step goes on with parsers of its posture. -/
theorem step_posture (version : Token.Version) (parser : ScriptParser (List Event))
    (token : Internal.Input) :
    MPost (FlowPost parser.posture) (ScriptParser.Internal.step version parser token) := by
  unfold ScriptParser.Internal.step
  refine MPost.bind fun r => ?_
  rcases r with command | (_ | declared | _ | _)
  · exact MPost.pure rfl
  · exact MPost.pure rfl
  · dsimp only
    split
    · exact MPost.throw _
    · refine MPost.pure ?_
      exact MPost.bind fun _ => MPost.pure rfl
  · exact MPost.pure (MPost.pure rfl)
  · exact MPost.pure trivial

theorem MPost.bind' {α β : Type} {Q : α → Prop} {P : β → Prop} {x : RPM α} {k : α → RPM β}
    (hx : MPost Q x) (hk : ∀ a, Q a → MPost P (k a)) : MPost P (x >>= k) := by
  intro log b log' hr
  simp only [ExceptT.run_bind, StateT.run_bind] at hr
  rcases hy : x.run.run log with ⟨r, l⟩
  rw [hy] at hr
  rcases r with e | a
  · cases hr
  · exact hk a (hx log a l hy) l b log' hr

theorem MPost.any {α : Type} (x : RPM α) : MPost (fun _ => True) x := fun _ _ _ _ => trivial

/-- What the driver does after an item's processing goes on with a parser of the posture. -/
theorem afterProcessing_posture (version : Token.Version) (parser : ScriptParser (List Event))
    (token : Internal.Input) :
    MPost (fun r => ∀ v p, r = .inl (v, p) → p.posture = parser.posture)
      (afterProcessing recordingProducer version parser token) := by
  unfold afterProcessing
  refine MPost.bind' (step_posture version parser token) fun f hf => ?_
  cases f with
  | more p => exact MPost.pure fun _ _ h => by cases h; exact hf
  | done => exact MPost.pure fun _ _ h => by cases h
  | switchVersion declared resume =>
    refine MPost.bind' (MPost.any _) fun r _ => ?_
    rcases r with _ | ⟨⟩
    · exact MPost.throw _
    · dsimp only
      refine MPost.bind' hf fun s hs => ?_
      cases s with
      | more p' => exact MPost.pure fun _ _ h => by cases h; exact hs
      | done => exact MPost.pure fun _ _ h => by cases h
  | discardRest resume =>
    refine MPost.bind' (MPost.any _) fun _ _ => ?_
    refine MPost.bind' hf fun s hs => ?_
    cases s with
    | more p' => exact MPost.pure fun _ _ h => by cases h; exact hs
    | done => exact MPost.pure fun _ _ h => by cases h

/-- The driver's run of one item goes on with a parser of the posture. -/
theorem recAfter_posture (version : Token.Version) (parser : ScriptParser (List Event))
    (token : Internal.Input) :
    MPost (fun r => ∀ v p, r = .inl (v, p) → p.posture = parser.posture)
      (recAfter version parser token) := by
  unfold recAfter afterToken
  exact MPost.bind' (MPost.any _) fun _ _ => MPost.bind' (MPost.any _) fun _ _ =>
    MPost.bind' (MPost.any _) fun _ _ => afterProcessing_posture version parser token

/-- A recording run that failed or finished does not go on after one more item. -/
theorem recRun_snoc_stop (version : BSmtLibSpec.Lexicon.Version) (items : List LibItem)
    (item : LibItem) {r : Except (ParseErrorCause Unit)
      ((Token.Version × ScriptParser (List Event)) ⊕ (Unit × List Internal.Input))}
    {log : List Event} (h : recRun version items = (r, log)) (hr : ∀ x, r ≠ .ok (.inl x)) :
    ∀ x log', recRun version (items ++ [item]) ≠ (.ok (.inl x), log') := by
  intro x log' h'
  unfold recRun at h h'
  rw [List.map_append, BSmtLib.Facts.Proofs.Parser.Rejection.Script.driveScript_append,
    run_bind_split, h] at h'
  rcases r with e | (y | ⟨u, rest⟩)
  · cases h'
  · exact hr y rfl
  · cases h'

/-- The recording run, where it goes on, goes on with a parser of the posture it starts with. -/
theorem recRun_posture (version : BSmtLibSpec.Lexicon.Version) (items : List LibItem)
    {v : Token.Version} {parser : ScriptParser (List Event)} {log : List Event}
    (h : recRun version items = (.ok (.inl (v, parser)), log)) :
    parser.posture = unrestrictedPosture := by
  obtain ⟨rev, rfl⟩ : ∃ rev, items = rev.reverse := ⟨items.reverse, by simp⟩
  induction rev generalizing v parser log with
  | nil =>
    cases h
    rfl
  | cons item rev ih =>
    rw [List.reverse_cons] at h
    rcases hR : recRun version rev.reverse with ⟨r, l⟩
    rcases r with e | (⟨v₀, p₀⟩ | u)
    · exact absurd h (recRun_snoc_stop version _ item hR (fun _ h => by cases h) _ _)
    · rw [recRun_snoc version rev.reverse item hR] at h
      have hp := recAfter_posture v₀ p₀ item.val l
      rcases hA : (recAfter v₀ p₀ item.val).run.run l with ⟨a, l'⟩
      rw [hA] at h
      rcases a with e | (⟨v₁, p₁⟩ | u)
      · cases h
      · cases h
        exact (hp _ _ hA _ _ rfl).trans (ih hR)
      · cases h
    · exact absurd h (recRun_snoc_stop version _ item hR (fun _ h => by cases h) _ _)

end BSmtLib.Facts.Proofs.Reader.Param.KeepsPosture
