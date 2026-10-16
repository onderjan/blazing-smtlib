module

public import BSmtLib.Facts.Proofs.Parser.Cut
public import BSmtLib.Facts.Proofs.Reader.Param.Stop
import all BSmtLib.Parser
import all BSmtLib.Parser.Script
import all BSmtLib.Token
import all BSmtLib.Facts.Proofs.Reader.Param.Stop
import all BSmtLib.Facts.Parser.Adapters.Run

@[expose] public section

/-!
# The script parser over a list of tokens, with any handler

The parse adapter of the reader proofs (`Param.Stop`) has the script parser take a token of its
cursor as the parser's driver over a list of tokens does (`Cut.afterToken`), with token points
and a producer that do nothing: the same result and the same handler, the version the driver
goes on in being the cursor's after the token (`takeOne_drive`). `drive` is that driver over a
list, and the driver of the parser's proofs (`Run.driveParse`) is it with the result read
(`driveParse_eq`). Nothing here depends on the handler.
-/

namespace BSmtLib.Facts.Proofs.Reader.Handler.Drive

open BSmtLib.Parser BSmtLib.Traits BSmtLib.Parser.Script
open BSmtLib.Parser.Internal (PM)
open BSmtLibSpec.Parser.Traversal (Points Producer)
open BSmtLib.Facts.Parser.Adapters.Run (driveParse arriveAt processAt)
open BSmtLib.Facts.Proofs.Parser.Cut (afterToken afterProcessing driveParse_cons continueWith
  bind_ext)
open BSmtLib.Facts.Proofs.Reader.Param (Stop.takeOne)

variable {H : Type} [CommandHandler H Id]

/-- Token points that do nothing. -/
def nullPoints : Points (StateT H Id) := ⟨fun _ => pure (), fun _ => pure ()⟩

/-- A producer that never refuses and does nothing. -/
def nullProducer : Producer (StateT H Id) := ⟨fun _ => pure (), pure ()⟩

/-- What the driver does with one token, with token points and a producer that do nothing. -/
abbrev tokenStep (version : Token.Version) (parser : ScriptParser H)
    (token : Internal.Input) : PM H ((Token.Version × ScriptParser H) ⊕ Unit) :=
  afterToken nullPoints nullProducer version parser token

/-- The script parser over the tokens, from the version and the parser: where it goes on after
the last, in which version and state, or its end and the tokens after it. -/
def drive : Token.Version → ScriptParser H → List Internal.Input →
    PM H ((Token.Version × ScriptParser H) ⊕ (Unit × List Internal.Input))
  | version, parser, [] => pure (.inl (version, parser))
  | version, parser, token :: tokens => do
    match ← tokenStep version parser token with
    | .inl (version', parser') => drive version' parser' tokens
    | .inr () => pure (.inr ((), tokens))

theorem drive_append (version : Token.Version) (parser : ScriptParser H)
    (items items' : List Internal.Input) :
    drive version parser (items ++ items') =
      drive version parser items >>= fun r => match r with
        | .inl (version', parser') => drive version' parser' items'
        | .inr (u, rest) => pure (.inr (u, rest ++ items')) := by
  induction items generalizing version parser with
  | nil => simp [drive]
  | cons token tokens ih =>
    simp only [List.cons_append, drive, bind_assoc]
    refine bind_ext fun r => ?_
    rcases r with ⟨version', parser'⟩ | u
    · simp [ih]
    · simp

/-- The driver of the parser's proofs, with token points and a producer that do nothing, is
`drive` with its result read. -/
theorem driveParse_eq (version : Token.Version) (parser : ScriptParser H)
    (items : List Internal.Input) :
    driveParse nullPoints nullProducer version parser items =
      drive version parser items >>= fun r => match r with
        | .inl _ => pure none
        | .inr result => pure (some result) := by
  induction items generalizing version parser with
  | nil => simp [driveParse, drive]
  | cons token tokens ih =>
    rw [driveParse_cons]
    simp only [drive, bind_assoc]
    refine bind_ext fun r => ?_
    rcases r with ⟨version', parser'⟩ | u
    · simp [continueWith, ih]
    · simp [continueWith]

/-- What the reader proofs' adapter did with a token, as the driver's step: going on, also after
an action on the cursor, in the cursor's version, or the end, or the failure. -/
def afterOf {b : Token.BatchTag} :
    Internal.After (ScriptParser H) Unit (Handler.Error H) × Token.BatchCursor b →
      Except (ParseErrorCause (Handler.Error H)) ((Token.Version × ScriptParser H) ⊕ Unit)
  | (.goOn parser, cursor) => .ok (.inl (cursor.version, parser))
  | (.stop (.ok .continue) parser, cursor) => .ok (.inl (cursor.version, parser))
  | (.stop (.ok (.break ())) _, _) => .ok (.inr ())
  | (.stop (.error e) _, _) => .error e.cause

theorem id_bind {α β : Type} (x : α) (f : α → Id β) : (x >>= f : Id β) = f x := rfl

omit [CommandHandler H Id] in
theorem arriveAt_null (token : Internal.Input) :
    arriveAt nullPoints token = (pure () : StateT H Id Unit) := by
  unfold arriveAt
  split <;> rfl

omit [CommandHandler H Id] in
theorem processAt_null (token : Internal.Input) :
    processAt nullPoints token = (pure () : StateT H Id Unit) := by
  unfold processAt
  split <;> rfl

/-- The reader proofs' adapter takes a token of a batch cursor as the driver's step does. -/
theorem takeOne_drive {b : Token.BatchTag} (parser : ScriptParser H)
    (cursor next : Token.BatchCursor b) (token : BSmtLib.Token b)
    (consumed : Token.Cursor.Consumed next cursor) (s : H) :
    (tokenStep next.version parser (Internal.Input.ofSyntax (next.syntax token))).run.run s =
      (afterOf (((Stop.takeOne (m := Id) parser cursor token next consumed).run s).1.1,
          ((Stop.takeOne (m := Id) parser cursor token next consumed).run s).1.2.val),
        ((Stop.takeOne (m := Id) parser cursor token next consumed).run s).2) := by
  unfold tokenStep afterToken afterProcessing
  simp only [arriveAt_null, processAt_null, ExceptT.lift_pure, pure_bind]
  unfold Stop.takeOne
  simp only [ExceptT.run_bind, StateT.run_bind, id_bind]
  have hsy : Token.Cursor.syntax next token = next.syntax token := rfl
  have hve : Token.Cursor.version next = next.version := rfl
  simp only [hsy, hve]
  generalize Internal.Input.ofSyntax (next.syntax token) = input
  generalize (Internal.ParseByToken.arrive parser input).run.run s = A
  obtain ⟨a, s₁⟩ := A
  rcases a with e | u
  · rfl
  · dsimp only
    simp only [StateT.run_bind, id_bind]
    generalize (Internal.ParseByToken.step next.version parser input).run.run s₁ = B
    obtain ⟨r, s₂⟩ := B
    rcases r with e | flow
    · rfl
    · cases flow with
      | more p => rfl
      | done r => rfl
      | switchVersion declared resume =>
        dsimp only
        split
        · rename_i heq
          simp [Token.Cursor.setVersion, Token.BatchCursor.setVersion] at heq
        · rename_i switched hsw
          simp only [nullProducer, ExceptT.run_bind, StateT.run_bind, id_bind]
          have hv : switched.version = declared := by
            unfold Token.Cursor.setVersion at hsw
            change Token.BatchCursor.setVersion next declared = _ at hsw
            unfold Token.BatchCursor.setVersion at hsw
            injection hsw with hsw
            rw [← hsw]
          have hl : ((ExceptT.lift (m := StateT H Id) (ε := ParseErrorCause (Handler.Error H))
              ((pure () : ExceptT BSmtLibSpec.Parser.Traversal.VersionRefused (StateT H Id)
                Unit).run)).run.run
                s₂) = (.ok (.ok ()), s₂) := rfl
          rw [hl]
          dsimp only
          simp only [ExceptT.run_bind, StateT.run_bind, id_bind]
          generalize resume.run.run s₂ = C
          obtain ⟨c, s₃⟩ := C
          rcases c with e | st
          · rfl
          · cases st with
            | more p =>
              show _ = (Except.ok (Sum.inl (switched.version, p)), s₃)
              rw [hv]; rfl
            | done r => rfl
      | discardRest resume =>
        dsimp only
        simp only [nullProducer, ExceptT.run_bind, StateT.run_bind, id_bind]
        have hl : ((ExceptT.lift (m := StateT H Id) (ε := ParseErrorCause (Handler.Error H))
            (pure () : StateT H Id Unit)).run.run s₂) = (.ok (), s₂) := rfl
        rw [hl]
        dsimp only
        simp only [StateT.run_bind, id_bind]
        generalize resume.run.run s₂ = C
        obtain ⟨c, s₃⟩ := C
        rcases c with e | st
        · rfl
        · cases st with
          | more p => rfl
          | done r => rfl

end BSmtLib.Facts.Proofs.Reader.Handler.Drive
