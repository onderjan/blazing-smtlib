module

public import BSmtLib.Facts.Proofs.Parser.Blank.Commands
public import BSmtLib.Facts.Proofs.Reader.Param.Stop
import all BSmtLib.Parser
import all BSmtLib.Parser.Script
import all BSmtLib.Facts.Proofs.Reader.Param.Stop
import all BSmtLib.Token
import all BSmtLib.Parser.Adapter

@[expose] public section

/-!
# The script parser's loop, blanked

The script parser's step asks its loop for actions on the cursor, whose resumptions run in the
parser's monad; with a handler whose calls never fail and with the blank handler, from blanked
parsers, the step asks for the same actions with resumptions related by `BSim` (`step_blank`).
So the loop of the reader proofs' adapter (`Param.Stop`) takes the same tokens with the two,
stops at the same token with the same answer, its errors blanked, and the same cursor, and leaves
blanked parsers (`takeOne_blank`, `rest_blank`).
-/

namespace BSmtLib.Facts.Proofs.Parser.Blank.Loop

open Basic States Simp Tactic Steps Commands
open BSmtLib.Parser.Internal (PM)

open BSmtLib.Parser BSmtLib.Nodes BSmtLib.Traits
open BSmtLib.Parser.Command BSmtLib.Parser.Script
open BSmtLib.Parser.Command.Internal
open BSmtLib.Facts.Proofs.Reader.Param (Stop.takeOne Stop.rest)
open BSmtLib.Token.BatchCursor.Internal (remaining)

/-- Results of the two runs, the first with a handler, the second with the blank handler: values
related by `Q`, or failures with the same cause, blanked. -/
def ERelB {ε α β : Type} (Q : α → β → Prop) :
    Except (ParseErrorCause ε) α → Except (ParseErrorCause Unit) β → Prop
  | .ok a, .ok b => Q a b
  | .error e, .error e' => e' = blankCause e
  | _, _ => False

theorem eRelB_blankResult {ε α β : Type} [Blanks α β] (r : Except (ParseErrorCause ε) α) :
    ERelB (fun a b => b = blank a) r (blankResult r) := by
  cases r <;> rfl

theorem id_bind {α β : Type} (x : α) (f : α → Id β) : (x >>= f : Id β) = f x := rfl

variable {H : Type} [CommandHandler H Id]

/-- What the script parser's step asks of its loop, on the two sides: the same, with blanked
parsers and resumptions related by `BSim`. -/
def FlowB : Internal.Flow (PM H) (ScriptParser H) Unit →
    Internal.Flow (PM Shell) (ScriptParser Shell) Unit → Prop
  | .more s, .more s' => s' = blank s
  | .done _, .done _ => True
  | .switchVersion v r, .switchVersion v' r' => v' = v ∧ BSim r r'
  | .discardRest r, .discardRest r' => BSim r r'
  | _, _ => False

theorem reset_blank (p : ScriptParser H) :
    blank (Internal.ParseByToken.reset p) = Internal.ParseByToken.reset (blank p) := (rfl)

theorem setVersion_resume_blank (declared : Token.Version) (p : ScriptParser H) :
    BSim (do
        ExceptT.lift (Handler.setVersion (H := H) declared)
        return Internal.Step.more
          (ScriptParser.Internal.mk (ScriptParser.Internal.posture p) .awaiting
            (ScriptParser.Internal.declarations p + 1)) :
        PM H (Internal.Step (ScriptParser H) Unit))
      (do
        ExceptT.lift (Handler.setVersion (H := Shell) declared)
        return Internal.Step.more
          (ScriptParser.Internal.mk (ScriptParser.Internal.posture (blank p)) .awaiting
            (ScriptParser.Internal.declarations (blank p) + 1)) :
        PM Shell (Internal.Step (ScriptParser Shell) Unit)) := by
  constructor
  intro h
  rfl

/-- The script parser's step, blanked. -/
theorem step_blank [NoFails H] (version : Token.Version) (p : ScriptParser H)
    (token : Internal.Input) (h : H) :
    ERelB FlowB ((ScriptParser.Internal.step version p token).run.run h).1
      ((ScriptParser.Internal.step version (blank p) token).run.run {}).1 := by
  have hc := (commandStep_blank (H := H) (version := version)
    (state := ScriptParser.Internal.command p) (token := token) rfl).run h
  have e₂ : ScriptParser.Internal.command (blank p) = blank (ScriptParser.Internal.command p) :=
    command_blankScriptParser p
  unfold ScriptParser.Internal.step
  simp only [ExceptT.run_bind, StateT.run_bind, e₂]
  generalize (commandStep version (ScriptParser.Internal.command p) token).run.run h = C₁
    at hc ⊢
  generalize (commandStep (H := Shell) version (blank (ScriptParser.Internal.command p))
    token).run.run {} = C₂ at hc ⊢
  obtain ⟨r₁, h₁⟩ := C₁
  obtain ⟨r₂, h₂⟩ := C₂
  dsimp only at hc ⊢
  subst hc
  simp only [id_bind]
  rcases r₁ with e | step
  · rfl
  · cases step with
    | more command =>
      exact (rfl : blank (ScriptParser.Internal.mk (H := H) (ScriptParser.Internal.posture p)
        command (ScriptParser.Internal.declarations p)) = _)
    | done outcome =>
      cases outcome with
      | command =>
        exact (rfl : blank (ScriptParser.Internal.mk (H := H) (ScriptParser.Internal.posture p)
          .awaiting (ScriptParser.Internal.declarations p)) = _)
      | setVersion declared =>
        simp only [blankResult, blankStep, Blanks.blank, id_eq, posture_blankScriptParser,
          declarations_blankScriptParser]
        rcases Internal.VersionPosture.check (ScriptParser.Internal.posture p)
          (ScriptParser.Internal.declarations p) declared with _ | kind
        · exact ⟨rfl, setVersion_resume_blank declared p⟩
        · rfl
      | exit => exact BSim.pure rfl
      | endOfFile => trivial

/-- A token's arrival at the script parser and its step, blanked. -/
theorem block_blank [NoFails H] (version : Token.Version) (p : ScriptParser H)
    (input : Internal.Input) (h : H) :
    ERelB FlowB
      ((do Internal.ParseByToken.arrive p input
           Internal.ParseByToken.step version p input : PM H _).run.run h).1
      ((do Internal.ParseByToken.arrive (blank p) input
           Internal.ParseByToken.step version (blank p) input : PM Shell _).run.run {}).1 := by
  have ha := (ScriptParser_arrive_blank (parser := p) (token := input)).run h
  show ERelB FlowB ((ScriptParser.Internal.arrive p input >>= fun _ =>
      ScriptParser.Internal.step version p input).run.run h).1
    ((ScriptParser.Internal.arrive (blank p) input >>= fun _ =>
      ScriptParser.Internal.step version (blank p) input).run.run {}).1
  simp only [ExceptT.run_bind, StateT.run_bind, id_bind]
  generalize (ScriptParser.Internal.arrive p input).run.run h = A₁ at ha ⊢
  generalize (ScriptParser.Internal.arrive (blank p) input).run.run {} = A₂ at ha ⊢
  obtain ⟨a₁, h₁⟩ := A₁
  obtain ⟨a₂, h₂⟩ := A₂
  dsimp only at ha ⊢
  subst ha
  rcases a₁ with e | u
  · rfl
  · exact step_blank version p input h₁

/-- What the parser did with a token, on the two sides: going on with blanked parsers, or
stopping with the answer blanked and blanked parsers. -/
def AfterB : Internal.After (ScriptParser H) Unit (Handler.Error H) →
    Internal.After (ScriptParser Shell) Unit Unit → Prop
  | .goOn p, .goOn p' => p' = blank p
  | .stop a p, .stop a' p' => a' = blankAnswer a ∧ p' = blank p
  | _, _ => False

section

variable {Z : Type} [Token.Produce Z]

theorem takeOne_blank [NoFails H] (p : ScriptParser H) (cursor : Z)
    (token : Token.Produce.Token Z) (next : Z) (consumed : Token.Produce.Consumed next cursor)
    (h : H) :
    AfterB ((Stop.takeOne (m := Id) p cursor token next consumed).run h).1.1
        ((Stop.takeOne (m := Id) (blank p) cursor token next consumed).run {}).1.1 ∧
      ((Stop.takeOne (m := Id) p cursor token next consumed).run h).1.2.val =
        ((Stop.takeOne (m := Id) (blank p) cursor token next consumed).run {}).1.2.val := by
  have hb := block_blank (H := H) (Token.Produce.version next) p
    (Internal.Input.ofSyntax (Token.Produce.«syntax» next token)) h
  unfold Stop.takeOne
  simp only [StateT.run_bind, id_bind]
  generalize hB₁ : ((Internal.ParseByToken.arrive p
      (Internal.Input.ofSyntax (Token.Produce.«syntax» next token)) >>= fun _ =>
    Internal.ParseByToken.step (Token.Produce.version next) p
      (Internal.Input.ofSyntax (Token.Produce.«syntax» next token)) : PM H _).run.run h) = B₁
    at hb
  generalize hB₂ : ((Internal.ParseByToken.arrive (blank p)
      (Internal.Input.ofSyntax (Token.Produce.«syntax» next token)) >>= fun _ =>
    Internal.ParseByToken.step (Token.Produce.version next) (blank p)
      (Internal.Input.ofSyntax (Token.Produce.«syntax» next token)) : PM Shell _).run.run {}) = B₂
    at hb
  obtain ⟨b₁, h₁⟩ := B₁
  obtain ⟨b₂, h₂⟩ := B₂
  dsimp only at hb ⊢
  rcases b₁ with e₁ | f₁ <;> rcases b₂ with e₂ | f₂ <;> simp only [ERelB] at hb
  · subst hb; exact ⟨⟨rfl, rfl⟩, rfl⟩
  · cases f₁ <;> cases f₂ <;> simp only [FlowB] at hb
    · exact ⟨hb, rfl⟩
    · exact ⟨⟨rfl, rfl⟩, rfl⟩
    · obtain ⟨rfl, hr⟩ := hb
      rename_i r₁ v r₂
      dsimp only
      split
      · exact ⟨⟨rfl, rfl⟩, rfl⟩
      · have hm := hr.run h₁
        simp only [StateT.run_bind, id_bind]
        generalize r₁.run.run h₁ = S₁ at hm ⊢
        generalize r₂.run.run {} = S₂ at hm ⊢
        obtain ⟨s₁, k₁⟩ := S₁
        obtain ⟨s₂, k₂⟩ := S₂
        dsimp only at hm ⊢
        subst hm
        rcases s₁ with e | st
        · exact ⟨⟨rfl, rfl⟩, rfl⟩
        · cases st <;> exact ⟨⟨rfl, rfl⟩, rfl⟩ <;> exact ⟨rfl, rfl⟩
    · rename_i r₁ r₂
      dsimp only
      have hm := hb.run h₁
      simp only [StateT.run_bind, id_bind]
      generalize r₁.run.run h₁ = S₁ at hm ⊢
      generalize r₂.run.run {} = S₂ at hm ⊢
      obtain ⟨s₁, k₁⟩ := S₁
      obtain ⟨s₂, k₂⟩ := S₂
      dsimp only at hm ⊢
      subst hm
      rcases s₁ with e | st
      · exact ⟨⟨rfl, rfl⟩, rfl⟩
      · cases st <;> exact ⟨⟨rfl, rfl⟩, rfl⟩ <;> exact ⟨rfl, rfl⟩

end

section

open BSmtLib.Parser.Adapter (ParseAdapter)

open BSmtLib.Facts.Proofs.Reader.Param (Stop.consume Stop.finish Stop.told)

variable {b : Token.BatchTag}

theorem next?_hasNext (cursor : Token.BatchCursor b) (h : cursor.HasNext) :
    Token.Produce.next? cursor = some (cursor.next h) := by
  show Token.BatchCursor.next? cursor = _
  unfold Token.BatchCursor.next?
  rw [dite_eq_left_of_eq_true (eq_true h)]

theorem next?_not (cursor : Token.BatchCursor b) (h : ¬ cursor.HasNext) :
    Token.Produce.next? cursor = none := by
  show Token.BatchCursor.next? cursor = _
  unfold Token.BatchCursor.next?
  rw [dite_eq_right_of_eq_false (eq_false h)]

/-- The loop over the rest of a cursor, blanked: the same answer, its errors blanked, the same
cursor, and blanked parsers. -/
theorem rest_blank [NoFails H] (origin : Token.BatchCursor b) :
    ∀ (n : Nat) (p : ScriptParser H) (cursor : Token.BatchCursor b)
      (consumed : Token.Produce.Consumed cursor origin) (h : H), remaining cursor < n →
      ((Stop.rest (m := Id) origin (blank p) cursor consumed).run {}).1.1 =
          blankAnswer ((Stop.rest (m := Id) origin p cursor consumed).run h).1.1 ∧
        ((Stop.rest (m := Id) origin (blank p) cursor consumed).run {}).1.2.1 =
          blank ((Stop.rest (m := Id) origin p cursor consumed).run h).1.2.1 ∧
        ((Stop.rest (m := Id) origin (blank p) cursor consumed).run {}).1.2.2.val =
          ((Stop.rest (m := Id) origin p cursor consumed).run h).1.2.2.val
  | 0, _, _, _, _, hn => absurd hn (Nat.not_lt_zero _)
  | n + 1, p, cursor, consumed, h, hn => by
    rw [Stop.rest, Stop.rest]
    by_cases hc : cursor.HasNext
    · rw [next?_hasNext cursor hc]
      dsimp only
      simp only [StateT.run_bind, id_bind]
      have ht := takeOne_blank p cursor (cursor.next hc).1 (cursor.next hc).2.val
        (cursor.next hc).2.property h
      generalize (Stop.takeOne (m := Id) p cursor (cursor.next hc).1 (cursor.next hc).2.val
        (cursor.next hc).2.property).run h = T₁ at ht ⊢
      generalize (Stop.takeOne (m := Id) (blank p) cursor (cursor.next hc).1
        (cursor.next hc).2.val (cursor.next hc).2.property).run {} = T₂ at ht ⊢
      obtain ⟨⟨a₁, later₁, taken₁⟩, h₁⟩ := T₁
      obtain ⟨⟨a₂, later₂, taken₂⟩, h₂⟩ := T₂
      obtain ⟨ha, hl⟩ := ht
      dsimp only at ha hl ⊢
      subst hl
      cases a₁ <;> cases a₂ <;> simp only [AfterB] at ha
      · subst ha
        exact rest_blank origin n _ later₁ _ h₁
          (Nat.lt_of_lt_of_le (Token.BatchCursor.Consumed.remaining_lt taken₁)
            (Nat.le_of_lt_succ hn))
      · obtain ⟨rfl, rfl⟩ := ha
        exact ⟨rfl, rfl, rfl⟩
    · rw [next?_not cursor hc]
      exact ⟨rfl, rfl, rfl⟩

/-- The parse adapter with the handler's values blanked, over the blank handler. -/
def blankAdapter (a : ParseAdapter H (ScriptParser H)) : ParseAdapter Shell (ScriptParser Shell) :=
  ParseAdapter.Internal.mk {} (blank a.parser) (ParseAdapter.Internal.versionSet a) .new

/-- A call of the reader proofs' adapter (`Param.Stop`), blanked: the same answer, its errors
blanked, the same cursor, and the adapter blanked. -/
theorem consume_blank [NoFails H] (cursor : Token.BatchCursor b) (hc : cursor.HasNext)
    (a : ParseAdapter H (ScriptParser H)) :
    ((Stop.consume cursor hc).run (blankAdapter a)).1.1 =
        blankAnswer ((Stop.consume cursor hc).run a).1.1 ∧
      ((Stop.consume cursor hc).run (blankAdapter a)).1.2.val =
        ((Stop.consume cursor hc).run a).1.2.val ∧
      ((Stop.consume cursor hc).run (blankAdapter a)).2 =
        blankAdapter ((Stop.consume cursor hc).run a).2 := by
  show (Stop.consume cursor hc (blankAdapter a)).1.1 = _ ∧ _
  unfold Stop.consume
  simp only [StateT.run]
  have ht := takeOne_blank a.parser cursor (cursor.next hc).1 (cursor.next hc).2.val
    (cursor.next hc).2.property (Stop.told a cursor)
  simp only [StateT.run] at ht
  have hp : (blankAdapter a).parser = blank a.parser := rfl
  have hs : ParseAdapter.Internal.parseState (blankAdapter a) = .new := rfl
  rw [hp, hs]
  generalize Stop.takeOne (m := Id) a.parser cursor (cursor.next hc).1 (cursor.next hc).2.val
    (cursor.next hc).2.property (Stop.told a cursor) = T₁ at ht ⊢
  generalize Stop.takeOne (m := Id) (blank a.parser) cursor (cursor.next hc).1
    (cursor.next hc).2.val (cursor.next hc).2.property (Stop.told (blankAdapter a) cursor)
      = T₂ at ht ⊢
  obtain ⟨⟨a₁, later₁, taken₁⟩, h₁⟩ := T₁
  obtain ⟨⟨a₂, later₂, taken₂⟩, h₂⟩ := T₂
  obtain ⟨ha, hl⟩ := ht
  dsimp only at ha hl ⊢
  subst hl
  obtain rfl : taken₁ = taken₂ := rfl
  cases h₂
  cases a₁ <;> cases a₂ <;> simp only [AfterB] at ha
  · subst ha
    simp only [Stop.finish]
    obtain ⟨r1, r2, r3⟩ := rest_blank cursor (remaining later₁ + 1) _ later₁ taken₁ h₁
      (Nat.lt_succ_self _)
    simp only [StateT.run] at r1 r2 r3
    refine ⟨r1, r3, ?_⟩
    show ParseAdapter.Internal.mk _ _ _ _ = ParseAdapter.Internal.mk _ _ _ _
    simp only [StateT.run]
    rw [r1, r2]
    congr 1
    rename_i q
    generalize (Stop.rest (m := Id) cursor q later₁ taken₁ h₁).1.1 = x
    cases x with
    | error => rfl
    | ok f => cases f <;> rfl
  · obtain ⟨rfl, rfl⟩ := ha
    refine ⟨rfl, rfl, ?_⟩
    simp only [Stop.finish]
    show ParseAdapter.Internal.mk _ _ _ _ = ParseAdapter.Internal.mk _ _ _ _
    congr 1
    rename_i ans _
    cases ans with
    | error => rfl
    | ok f => cases f <;> rfl

end

end BSmtLib.Facts.Proofs.Parser.Blank.Loop
