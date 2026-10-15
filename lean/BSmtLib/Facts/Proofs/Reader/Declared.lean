module

public import BSmtLib.Facts.Proofs.Reader.Looser
public import BSmtLib.Facts.Proofs.Parser.QuietSteps
import all BSmtLib.Parser
import all BSmtLib.Parser.Adapter
import all BSmtLib.Parser.Script
import all BSmtLib.Token

@[expose] public section
open BSmtLib.Parser.Script.Internal
open BSmtLib.Token.BatchCursor.Internal (remaining)

/-!
# A handler under a posture is told only versions the posture allows

The handler of the parse adapter is told a version in two places: by the adapter, at the start
of an input, the version of the cursor it is handed; and by the script parser, the version of a
declaration its posture let pass. The command parser tells it none
(`QuietSteps.commandStep_silent` with `Quiet.isSwitch`). The cursor the adapter gives back is in
the version of the cursor it was handed, or in the version of a declaration the posture let pass.
So where nothing went wrong, the watched adapter under a posture, handed cursors in versions the
posture allows, tells its handler only such versions and gives back cursors in such versions
(`keeps_allowed`), and a reader under the posture from a version it allows that reads an input to
the end ends with a handler told only versions the posture allows (`readThrough_allowed`).
-/

namespace BSmtLib.Facts.Proofs.Reader.Declared

open BSmtLibSpec.Parser.Properties
open BSmtLib.Parser
open BSmtLib.Facts.Reader.Adapters (RecAdapter)
open BSmtLib.Facts.Proofs.Reader.Param.Adapter (paLoop startLog consume_eq id_bind_eq)
open BSmtLib.Facts.Proofs.Reader.Param.Posture
open BSmtLib.Facts.Proofs.Parser.Quiet (isSwitch)
open BSmtLib.Facts.Proofs.Parser.QuietSteps (commandStep_silent)
open BSmtLib.Facts.Proofs.Reader.Param (Watch)
open BSmtLib.Facts.Proofs.Reader.Param.Watch (WM consume_run)
open BSmtLib.Facts.Proofs.Reader.Looser (Good KeepsI readerWith readThrough_looser)
open BSmtLib.Facts.Parser.Adapters.Bridge BSmtLib.Facts.Proofs.Parser.Cut
open BSmtLib.Facts.Proofs.Parser.Script BSmtLib.Parser.Adapter BSmtLib.Parser.Command
open BSmtLib.Parser.Command.Internal
open BSmtLib.Parser.Script BSmtLib.Parser.Script.Internal.VersionPosture BSmtLib.Traits

/-- The handler was told only versions the posture allows. -/
def ToldAllowed (posture : Token.VersionPosture) (events : List Event) : Prop :=
  ∀ version, Event.handlerSwitch (Bridge.version version) ∈ events →
    posture.allowed.contains version = true

/-- The record's version is one the posture allows, and the handler was told only such. -/
def Allowed (posture : Token.VersionPosture) (w : Watch RecAdapter) : Prop :=
  posture.allowed.contains w.version = true ∧ ToldAllowed posture w.inner.handler

section

variable {posture : Token.VersionPosture}

theorem toldAllowed_append {added events : List Event} (h₁ : ∀ e ∈ added, isSwitch e = false)
    (h₂ : ToldAllowed posture events) : ToldAllowed posture (added ++ events) := by
  intro version hmem
  rcases List.mem_append.mp hmem with h | h
  · have := h₁ _ h
    simp [isSwitch] at this
  · exact h₂ version h

theorem toldAllowed_cons {version : Token.Version} {events : List Event}
    (h₁ : posture.allowed.contains version = true) (h₂ : ToldAllowed posture events) :
    ToldAllowed posture (.handlerSwitch (Bridge.version version) :: events) := by
  intro v hmem
  rcases List.mem_cons.mp hmem with h | h
  · injection h with h
    rw [Bridge.version_injective h]
    exact h₁
  · exact h₂ v h

theorem arrivalCalls_switchless (parser : ScriptParser (List Event))
    (item : Parser.Internal.Input) :
    ∀ e ∈ arrivalCalls parser item, isSwitch e = false := by
  intro e he
  unfold arrivalCalls at he
  split at he
  · cases he
  · split at he
    · split at he
      · split at he
        · simp only [List.mem_singleton] at he
          subst he
          rfl
        · cases he
      · cases he
    · cases he

theorem allowed_of_check {declarations : Nat} {version : Token.Version}
    (h : (check posture) declarations version = none) :
    posture.allowed.contains version = true := by
  unfold VersionPosture.check at h
  split at h
  · split at h
    · cases h
    · split at h
      · assumption
      · cases h
  · split at h
    · assumption
    · cases h

theorem setVersion_version {b : Token.BatchTag} {cursor next : Token.BatchCursor b}
    {version : Token.Version}
    (h : cursor.setVersion version = .ok next) : next.version = version := by
  unfold Token.BatchCursor.setVersion at h
  injection h with h
  subst h
  rfl

end

/-! ## A token -/

/-- The adapter, taking a token in a version the posture allows under the posture, tells its
handler only versions the posture allows and leaves the cursor in such a version, unless it
fails. -/
theorem takeOne_allowed {strict : Token.VersionPosture} (parser : ScriptParser (List Event))
    (hp : parser.posture = strict) {b : Token.BatchTag} (cursor next : Token.BatchCursor b)
    (token : Token b)
    (consumed : next.Consumed cursor) (hv : strict.allowed.contains next.version = true)
    (handler : List Event) (hh : ToldAllowed strict handler) :
    IsFailure ((Param.Stop.takeOne (H := List Event) (m := Id) parser cursor token next
        consumed).run handler).1.1 ∨
      (ToldAllowed strict ((Param.Stop.takeOne (H := List Event) (m := Id) parser cursor token
          next consumed).run handler).2 ∧
        strict.allowed.contains ((Param.Stop.takeOne (H := List Event) (m := Id) parser cursor
          token next consumed).run handler).1.2.val.version = true) := by
  simp only [Param.Stop.takeOne, StateT.run_bind]
  rw [run_bind_ok (arrive_run _ _ _), step_eq, run_bind_split]
  obtain ⟨added, hlog, hadded, -⟩ := (commandStep_silent (bad := isSwitch)
    (Token.Produce.version next) parser.command
    (Parser.Internal.Input.ofSyntax (Token.Produce.«syntax» next token))).holds
      (arrivalCalls parser (Parser.Internal.Input.ofSyntax
          (Token.Produce.«syntax» next token)) ++ handler)
  have hh' : ToldAllowed strict
      (added ++ (arrivalCalls parser (Parser.Internal.Input.ofSyntax
          (Token.Produce.«syntax» next token)) ++
          handler)) :=
    toldAllowed_append hadded (toldAllowed_append (arrivalCalls_switchless _ _) hh)
  generalize (commandStep (Token.Produce.version next) parser.command
    (Parser.Internal.Input.ofSyntax (Token.Produce.«syntax» next token))).run.run
      (arrivalCalls parser (Parser.Internal.Input.ofSyntax
          (Token.Produce.«syntax» next token)) ++ handler) =
          c at hlog
  obtain ⟨res, handler'⟩ := c
  dsimp only at hlog
  subst hlog
  rcases res with e | outcome
  · exact .inl trivial
  · dsimp only
    rcases outcome with command | (_ | declared | _ | _)
    · exact .inr ⟨hh', hv⟩
    · exact .inr ⟨hh', hv⟩
    · cases hc : (check parser.posture) parser.declarations declared with
      | some kind =>
        have hs : (scriptAfter parser (.done (.setVersion declared))).run.run
            (added ++ (arrivalCalls parser (Parser.Internal.Input.ofSyntax
                (Token.Produce.«syntax» next token)) ++
              handler)) =
            (.error (.syntax kind), added ++
              (arrivalCalls parser (Parser.Internal.Input.ofSyntax
                  (Token.Produce.«syntax» next token)) ++
                  handler)) := by
          simp only [Param.Posture.scriptAfter, hc]
          rfl
        rw [hs]
        exact .inl trivial
      | none =>
        have hs : (scriptAfter parser (.done (.setVersion declared))).run.run
            (added ++ (arrivalCalls parser (Parser.Internal.Input.ofSyntax
                (Token.Produce.«syntax» next token)) ++
              handler)) =
            (.ok (.switchVersion declared (do
              ExceptT.lift (Handler.setVersion (H := List Event) declared)
              return .more
                { parser with command := .awaiting, declarations := parser.declarations + 1 })),
              added ++ (arrivalCalls parser (Parser.Internal.Input.ofSyntax
                  (Token.Produce.«syntax» next token)) ++
                handler)) := by
          simp only [Param.Posture.scriptAfter, hc]
          rfl
        rw [hs]
        simp only [id_bind_eq]
        split
        · exact .inl trivial
        · rename_i switched hswitch
          refine .inr ⟨?_, ?_⟩
          · exact toldAllowed_cons (by rw [← hp]; exact allowed_of_check hc) hh'
          · show strict.allowed.contains switched.version = true
            rw [setVersion_version hswitch, ← hp]
            exact allowed_of_check hc
    · exact .inr ⟨hh', hv⟩
    · exact .inr ⟨hh', hv⟩

/-! ## A call -/

theorem looser_refl (posture : Token.VersionPosture) : Looser posture posture :=
  ⟨rfl, fun _ h => h⟩

theorem next_version {b : Token.BatchTag} (cursor : Token.BatchCursor b) (h : cursor.HasNext) :
    (cursor.next h).2.val.version = cursor.version := (rfl)

/-- The adapter's loop over a cursor in a version the posture allows, under the posture, tells its
handler only versions the posture allows and leaves the cursor in such a version, unless it
fails. -/
theorem paLoop_allowed {strict : Token.VersionPosture} {b : Token.BatchTag} :
    ∀ (n : Nat) (parser : ScriptParser (List Event)) (cursor : Token.BatchCursor b)
      (handler : List Event), remaining cursor < n → parser.posture = strict →
      strict.allowed.contains cursor.version = true → ToldAllowed strict handler →
      (∃ e, ((paLoop parser cursor).run handler).1.1 = .error e) ∨
        (ToldAllowed strict ((paLoop parser cursor).run handler).2 ∧
          strict.allowed.contains ((paLoop parser cursor).run handler).1.2.2.version = true)
  | 0, _, _, _, hn, _, _, _ => absurd hn (Nat.not_lt_zero _)
  | n + 1, parser, cursor, handler, hn, hp, hv, hh => by
    rw [paLoop]
    by_cases h : cursor.HasNext
    · rw [dite_eq_left_of_eq_true (eq_true h)]
      have hnv : (cursor.next h).2.val.version = cursor.version := next_version cursor h
      rcases hnext : cursor.next h with ⟨token, ⟨next, consumed⟩⟩
      rw [hnext] at hnv
      dsimp only at hnv ⊢
      simp only [StateT.run_bind]
      have ha := takeOne_allowed parser hp cursor next token consumed (hnv ▸ hv) handler hh
      have hl := takeOne_looser (looser_refl strict) parser hp cursor next token consumed handler
      generalize (Param.Stop.takeOne (H := List Event) (m := Id) (withPosture strict parser)
        cursor token next consumed).run handler = t₂ at hl
      generalize (Param.Stop.takeOne (H := List Event) (m := Id) parser cursor token next
        consumed).run handler = t₁ at ha hl ⊢
      obtain ⟨⟨after₁, ⟨later₁, taken₁⟩⟩, h₁⟩ := t₁
      simp only [id_bind_eq]
      rcases ha with hf | ⟨hh₁, hv₁⟩
      · dsimp only at hf
        rcases after₁ with p₁ | ⟨e | flow, p₁⟩
        · simp only [IsFailure] at hf
        · exact .inl ⟨e, rfl⟩
        · simp only [IsFailure] at hf
      · dsimp only at hh₁ hv₁
        rcases after₁ with p₁ | ⟨answer, p₁⟩
        · have hp₁ : p₁.posture = strict := by
            rcases hl with hf | ⟨ha, -, -⟩
            · simp only [IsFailure] at hf
            · obtain ⟨⟨_, _⟩ | _, _⟩ := t₂
              · exact ha.2
              · cases ha
          exact paLoop_allowed n p₁ later₁ h₁
            (Nat.lt_of_lt_of_le (Token.BatchCursor.Consumed.remaining_lt taken₁)
                (Nat.le_of_lt_succ hn))
            hp₁ hv₁ hh₁
        · exact .inr ⟨hh₁, hv₁⟩
    · rw [dite_eq_right_of_eq_false (eq_false h)]
      exact .inr ⟨hh, hv⟩

section Stop

attribute [local instance high] Param.Stop.consumeFrom

/-- A call of the adapter that stops, under the posture, on a cursor in a version the posture
allows, from a handler told only such versions, tells its handler only such versions and leaves
the cursor in such a version, unless it fails. -/
theorem consume_allowedS {strict : Token.VersionPosture} {b : Token.BatchTag}
    (cursor : Token.BatchCursor b) (h : cursor.HasNext) (A : RecAdapter)
    (hp : A.parser.posture = strict) (hv : strict.allowed.contains cursor.version = true)
    (hh : ToldAllowed strict (startLog A cursor.version)) :
    (∃ e, ((Token.ConsumeFrom.consume (m := Id) cursor h : StateT RecAdapter Id _).run A).1.1 =
        .error e) ∨
      (ToldAllowed strict ((Token.ConsumeFrom.consume (m := Id) cursor h :
          StateT RecAdapter Id _).run A).2.handler ∧
        strict.allowed.contains ((Token.ConsumeFrom.consume (m := Id) cursor h :
          StateT RecAdapter Id _).run A).1.2.val.version = true) := by
  have e₁ := consume_eq cursor h A
  have hloop := paLoop_allowed (remaining cursor + 1) A.parser cursor
    (startLog A cursor.version) (Nat.lt_succ_self _) hp hv hh
  generalize (Token.ConsumeFrom.consume (m := Id) cursor h : StateT RecAdapter Id _).run A = q
    at e₁ ⊢
  generalize (paLoop A.parser cursor).run (startLog A cursor.version) = r at e₁ hloop
  obtain ⟨⟨a, ⟨c, t⟩⟩, s⟩ := q
  simp only [Prod.mk.injEq] at e₁
  obtain ⟨rfl, rfl, rfl⟩ := e₁
  rcases hloop with ⟨e, he'⟩ | ⟨hh', hv'⟩
  · exact .inl ⟨e, he'⟩
  · exact .inr ⟨hh', hv'⟩

end Stop

section Continue

open BSmtLib.Facts.Proofs.Reader.Param.Split (outN outS resumeOut outN_split_eq script_parse_eq
  resumeOut_of_not)

/-- A call of the parse adapter under the posture, on a cursor in a version the posture allows,
from a handler told only such versions, tells its handler only such versions and leaves the
cursor in such a version, unless it fails: from the call of the adapter that stops, which does so
(`consume_allowedS`), and the call from where that stopped. -/
theorem outN_allowed {strict : Token.VersionPosture} {b : Token.BatchTag} :
    ∀ (n : Nat) (cursor : Token.BatchCursor b) (h : cursor.HasNext) (A : RecAdapter),
      (remaining cursor) < n → A.parser.posture = strict →
      strict.allowed.contains cursor.version = true →
      ToldAllowed strict (startLog A cursor.version) →
      (∃ e, (outN cursor h A).1.1 = .error e) ∨
        (ToldAllowed strict (outN cursor h A).2.handler ∧
          strict.allowed.contains (outN cursor h A).1.2.version = true)
  | 0, _, _, _, hn, _, _, _ => absurd hn (Nat.not_lt_zero _)
  | n + 1, cursor, h, A, hn, hp, hv, hh => by
    rw [outN_split_eq script_parse_eq]
    have hs := consume_allowedS cursor h A hp hv hh
    have hl := Param.Posture.consume_looser (looser_refl strict) cursor h A hp
    have eS : outS cursor h A =
        let x := (Param.Stop.consume (H := List Event) (P := ScriptParser (List Event)) cursor
          h).run A
        ((x.1.1, x.1.2.val), x.2) := rfl
    rw [eS]
    change (∃ e, ((Param.Stop.consume (H := List Event) (P := ScriptParser (List Event)) cursor
        h).run A).1.1 = .error e) ∨
      (ToldAllowed strict ((Param.Stop.consume (H := List Event) (P := ScriptParser (List Event))
          cursor h).run A).2.handler ∧
        strict.allowed.contains ((Param.Stop.consume (H := List Event)
          (P := ScriptParser (List Event)) cursor h).run A).1.2.val.version = true) at hs
    change (∃ e, ((Param.Stop.consume (H := List Event) (P := ScriptParser (List Event)) cursor
        h).run A).1.1 = .error e) ∨
      (_ ∧ ((Param.Stop.consume (H := List Event) (P := ScriptParser (List Event)) cursor h).run
          A).2.parser.posture = strict) at hl
    have hvs₀ := Param.Stop.versionSet_consume (H := List Event) (P := ScriptParser (List Event))
      cursor h A
    generalize (Param.Stop.consume (H := List Event) (P := ScriptParser (List Event)) cursor
      h).run A = x at hs hl hvs₀ ⊢
    obtain ⟨⟨a, ⟨d, hd⟩⟩, A'⟩ := x
    dsimp only at hs hl hvs₀ ⊢
    rcases hs with ⟨e, he⟩ | ⟨hh', hv'⟩
    · subst he
      left
      exact ⟨e, by rw [resumeOut_of_not (fun hc => by cases hc.1)]⟩
    · by_cases hc : a = .ok .continue ∧ d.HasNext
      · obtain ⟨rfl, hdn⟩ := hc
        have hp' : A'.parser.posture = strict := by
          rcases hl with ⟨e, he⟩ | ⟨-, hp'⟩
          · cases he
          · exact hp'
        have hvs : A'.versionSet = true := hvs₀
        simp only [resumeOut, hdn, ↓reduceDIte]
        refine outN_allowed n d hdn A'
          (Nat.lt_of_lt_of_le hd.remaining_lt (Nat.le_of_lt_succ hn)) hp' hv' ?_
        unfold startLog
        rw [hvs]
        exact hh'
      · rw [resumeOut_of_not hc]
        exact .inr ⟨hh', hv'⟩

end Continue

/-- Where nothing went wrong, a call of the watched adapter under the posture keeps `Allowed`. -/
theorem keeps_allowed (strict : Token.VersionPosture) : KeepsI strict (Allowed strict) := by
  intro b cursor h w he hg hfin
  rw [consume_run] at hfin ⊢
  simp only [Watch.after, he, Bool.false_or, Bool.or_eq_false_iff, bne_eq_false_iff_eq] at hfin
  obtain ⟨hcv, hok⟩ := hfin
  obtain ⟨hp, hv, hh⟩ := hg
  simp only [Watch.answer] at hok ⊢
  have hstart : ToldAllowed strict (startLog w.inner cursor.version) := by
    unfold startLog
    split
    · exact hh
    · exact toldAllowed_cons (by rw [hcv]; exact hv) hh
  have hloop := outN_allowed (remaining cursor + 1) cursor h w.inner (Nat.lt_succ_self _) hp
    (by rw [hcv]; exact hv) hstart
  have eN : Param.Split.outN cursor h w.inner =
      let x := (Token.ConsumeFrom.consume (m := Id) cursor h : StateT RecAdapter Id _).run w.inner
      ((x.1.1, x.1.2.val), x.2) := rfl
  rw [eN] at hloop
  generalize (Token.ConsumeFrom.consume (m := Id) cursor h : StateT RecAdapter Id _).run w.inner = q
    at hok hloop ⊢
  obtain ⟨⟨a, ⟨c, t⟩⟩, s⟩ := q
  dsimp only at hok hloop ⊢
  rcases hloop with ⟨e, he'⟩ | ⟨hh', hv'⟩
  · rw [he'] at hok
    cases hok
  · exact ⟨hv', hh'⟩

end BSmtLib.Facts.Proofs.Reader.Declared
