module

public import BSmtLib.Facts.Proofs.Lexer.X1BatchInCoreLexer.Recovery
import all BSmtLib.Lexer
import all BSmtLib.Lexer.Internal.Helpers
import all BSmtLib.Lexer.Internal.WRustPort
import all BSmtLib.Lexer.Internal.WRustPort.Slice

@[expose] public section

/-!
# The end of the input, in the library's lexer and `X1BatchInCore`

`lexEofInner` sets the base to zero before it reads it, finishes the token in progress at the end
of the input, catches a relex and hands over the end-of-file token. It is simulated exactly, under
`coreMap 0`, by the rules of `Simulation` and the simulations of the finishing steps.
`X1BatchInCore` takes the batch it starts with from its operations (`Ops.eofBatch`), which is the
one in its state.
-/

open BSmtLib.Lexer.Cursor (LexerCursor)

namespace BSmtLib.Facts.Proofs.Lexer.X1BatchInCoreLexer.Eof

open BSmtLib.Facts.Proofs.Lexer.Simulation.Steps
open BSmtLib.Facts.Proofs.Lexer.X1BatchInCoreLexer.Core
open BSmtLib.Facts.Proofs.Lexer.X1BatchInCoreLexer.Finish
open BSmtLib.Facts.Proofs.Lexer.X1BatchInCoreLexer.HandOver
open BSmtLib.Facts.Proofs.Lexer.X1BatchInCoreLexer.Outer

section

variable {m : Type → Type} [Monad m] [LawfulMonad m] {H ε : Type} {S T α β : Type}
  {φ : S → T}


omit [LawfulMonad m] in
/-- A step simulated from the states of every base is simulated from every state. -/
theorem simP_true_of_base {start : Nat} {floor : Option Nat} {low : Nat} {ψ : α → β}
    {f : M m H ε (ZS floor low) α} {g : M m H ε (XS floor low) β}
    (hf : ∀ b, SimP (BaseIs b) (fun _ _ => True) (boundMap start) ψ f g) :
    SimP (fun _ => True) (fun _ _ => True) (boundMap start) ψ f g :=
  fun s _ h => hf s.val.base s rfl h

/-- A run of a step of the lexers' monads followed by a step of the consumer's monad that
gives the lexer state, for runs related by `φ` and continuations related by `coreMap 0`. -/
theorem bind_post {γ : Type} (A : StateT H m (α × S)) (A' : StateT H m (α × T))
    (K : α × S → StateT H m (γ × ZCore)) (K' : α × T → StateT H m (γ × XCore))
    (hA : ∀ h, (fun r => ((r.1.1, φ r.1.2), r.2)) <$> A.run h = A'.run h)
    (hK : ∀ a s h, (fun r => ((r.1.1, coreMap 0 r.1.2), r.2)) <$> (K (a, s)).run h =
      (K' (a, φ s)).run h) (h : H) :
    (fun r => ((r.1.1, coreMap 0 r.1.2), r.2)) <$> (A >>= K).run h = (A' >>= K').run h := by
  simp only [StateT.run_bind]
  rw [← hA, bind_map_left, map_bind]
  exact congrArg (_ >>= ·) (funext fun x => hK x.1.1 x.1.2 x.2)

/-- `bind_post` for a first run that is a step of the lexers simulated from its state. -/
theorem bind_post_sim {γ : Type} {P : S → Prop} {Q : α → S → Prop} (f : M m H ε S α)
    (g : M m H ε T α) (s : S) (hf : SimP P Q φ id f g) (hs : P s)
    (K : Except ε α × S → StateT H m (γ × ZCore)) (K' : Except ε α × T → StateT H m (γ × XCore))
    (hK : ∀ a s h, (fun r => ((r.1.1, coreMap 0 r.1.2), r.2)) <$> (K (a, s)).run h =
      (K' (a, φ s)).run h) (h : H) :
    (fun r => ((r.1.1, coreMap 0 r.1.2), r.2)) <$> (ExceptT.run f s >>= K).run h =
      (ExceptT.run g (φ s) >>= K').run h := by
  refine bind_post _ _ K K' (fun h => ?_) hK h
  refine Eq.trans ?_ (SimP.eq hf hs h)
  refine congrArg (· <$> _) (funext fun x => ?_)
  obtain ⟨⟨r, s⟩, h⟩ := x
  cases r <;> rfl

end

section

variable {H : Type} {m : Type → Type} [Monad m] [LawfulMonad m] {R E : Type} [Token.Consume H R E]
  [∀ batch, Token.ConsumeFrom H (LexerCursor batch) m]

theorem lexEofInner_exact (c : ZCore) (h : H) :
    (fun r => ((r.1.1, coreMap 0 r.1.2), r.2)) <$>
      runI (BSmtLib.Lexer.Internal.lexEofInner (H := H) (m := m) (R := R) (E := E)) c h =
    runI (Lexer.Internal.WRustPort.lexEofInner (H := H) (m := m) (R := R) (E := E))
        (coreMap 0 c) h := by
  unfold BSmtLib.Lexer.Internal.lexEofInner Lexer.Internal.WRustPort.lexEofInner
  simp only [eofBatch_eq]
  simp only [runI, StateT.run]
  refine bind_post_sim (φ := boundMap 0) (Q := fun _ _ => True) _ _ _ ?_ (rfl : BaseIs 0 _) _ _
    (fun a s h => ?_) h
  · refine SimP.bind (SimP.tryCatch (ψ := id) (Q := fun _ _ => True) ?_ fun e => ?_) fun _ => ?_
    · obtain ⟨v, iv, st, df, hd, rc, cd, ld, rs, ts, tc, off, bs, ln, ls, bt, tsd, be⟩ := c
      have ok : EndOk 0 0 0 Lexer.Internal.Helpers.TokenEnd.EOF :=
        ⟨by simp, by simp, by simp [Lexer.Internal.Helpers.TokenEnd.EOF],
          by simp [Lexer.Internal.Helpers.TokenEnd.EOF],
          by simp only [Lexer.Internal.Helpers.TokenEnd.EOF,
              USize.toNat_zero]; have := USize.le_size; omega⟩
      cases st <;> dsimp only
      case comment =>
        refine SimP.bind (Q := fun x s => BaseIs 0 s ∧
          x = Token.Consume.isConcrete (H := H)) (ψ := id) ?_ fun x => ?_
        · unfold BSmtLib.Lexer.Internal.consumesWhitespaceAndComments
            Lexer.Internal.WRustPort.consumesWhitespaceAndComments
          exact SimP.pure (fun _ h => ⟨h, rfl⟩) rfl
        refine SimP.ite Iff.rfl (fun _ => ?_) fun _ => SimP.pure (fun _ _ => trivial) rfl
        exact SimP.mono (P := BaseIs 0) (Q := fun _ => BaseIs 0) (fun _ h => h.1)
          (fun _ _ _ => trivial) (sinkStored_sim 0 0 _ _ _ 0 ok.hbase ok.hbp _ _)
      case normal => exact SimP.pure (fun _ _ => trivial) rfl
      case fraction =>
        exact SimP.mono (Q := fun _ => BaseIs 0) (fun _ h => h) (fun _ _ _ => trivial)
          (finishDecimal_sim 0 0 _ _ _ 0 ok _ _)
      case numeralOrDecimal =>
        exact SimP.mono (Q := fun _ => BaseIs 0) (fun _ h => h) (fun _ _ _ => trivial)
          (finishNumeral_sim 0 0 _ _ 0 ok _ _)
      case hexadecimal =>
        exact SimP.mono (Q := fun _ => BaseIs 0) (fun _ h => h) (fun _ _ _ => trivial)
          (finishDigitRun_sim 0 0 _ _ _ _ 0 ok _ _)
      case binary =>
        exact SimP.mono (Q := fun _ => BaseIs 0) (fun _ h => h) (fun _ _ _ => trivial)
          (finishDigitRun_sim 0 0 _ _ _ _ 0 ok _ _)
      case simpleSymbol =>
        exact SimP.mono (Q := fun _ => BaseIs 0) (fun _ h => h) (fun _ _ _ => trivial)
          (finishSimpleSymbol_sim 0 0 _ _ 0 ok _ _)
      case keyword =>
        exact SimP.mono (Q := fun _ => BaseIs 0) (fun _ h => h) (fun _ _ _ => trivial)
          (finishKeyword_sim 0 0 _ _ _ 0 ok _ _)
      case stringLiteralDoubleQuote =>
        exact SimP.mono (Q := fun _ => BaseIs 0) (fun _ h => h) (fun _ _ _ => trivial)
          (finishStringLiteral_sim 0 0 _ _ 0 ok _ _)
      case quotedSymbolClosed =>
        exact SimP.mono (Q := fun _ => BaseIs 0) (fun _ h => h) (fun _ _ _ => trivial)
          (sinkStored_sim 0 0 _ _ _ 0 ok.hbase ok.hbp _ _)
      case whitespace =>
        exact SimP.mono (Q := fun _ => BaseIs 0) (fun _ h => h) (fun _ _ _ => trivial)
          (sinkStored_sim 0 0 _ _ _ 0 ok.hbase ok.hbp _ _)
      all_goals exact fail_sim 0 id 0 _ _ ok.hb ok.hp ok.hno _
    · rcases e with ⟨_ | _ | _ | _ | _, _, _⟩ <;> dsimp only <;>
        try (first | exact SimP.pure (fun _ _ => trivial) rfl | exact SimP.throw _)
      all_goals
        refine modifyCore_sim (H := H) (m := m) (R := R) (E := E) 0 _ _ ?_ fun _ _ => trivial
      all_goals intro _ _; rfl
    · refine SimP.bind (simP_true_of_base fun b => SimP.mono (fun _ h => h)
        (fun _ _ _ => trivial) (startToken_sim 0 b _ 0 0 (by simp) (by simp) _ _)) fun x => ?_
      exact simP_true_of_base fun b => SimP.mono (fun _ h => h) (fun _ _ _ => trivial)
        (handOverEof_sim 0 b x.val)
  · cases a with
    | ok u => simp [boundMap]
    | error e => rcases e with ⟨_ | _ | _ | _ | _, _, _⟩ <;> simp [boundMap]

end

end BSmtLib.Facts.Proofs.Lexer.X1BatchInCoreLexer.Eof
