import BSmtLib.Proofs.X1BatchInCoreLexer.Outer

/-!
# The steps between calls of the library's lexer and of `X1BatchInCore`

The resetting and the skipping of bytes while recovering, the turning of a failure into the
error of a call, and the adding of the break location are coupled: they read the base only
through the current location, which is the offset in both lexers, and set it only to zero. The
two lexers have copies of their own of the function that skips bytes (`skipBytes`), which agree.
-/

namespace BSmtLib.Proofs.X1BatchInCoreLexer

/-- The skipping state of `X1BatchInCore` for that of the library's lexer. -/
def skMap (s : BSmtLib.Lexer.Internal.Skipping) : Lexer.WRustPort.Skipping :=
  { skip := s.skip, depth := s.depth, line := s.line, lineStart := s.lineStart }

-- Splits on a condition, reduces the branches that test it and closes the goals of a recursive
-- call.
set_option hygiene false in
local macro "bc " t:term:max : tactic =>
  `(tactic| (by_cases hc : $t = true <;>
    (try simp only [hc, ↓reduceIte, Bool.false_eq_true]) <;> try exact IH _))

theorem skipBytes_eq (bytes : ByteSlice) (legacy : Bool) (offset index : Nat)
    (s : BSmtLib.Lexer.Internal.Skipping) :
    (fun r => (r.1, skMap r.2)) (BSmtLib.Lexer.Internal.skipBytes bytes legacy offset index s) =
      Lexer.WRustPort.skipBytes bytes legacy offset index (skMap s) := by
  induction h : bytes.size - index using Nat.strongRecOn generalizing index s with
  | ind n ih =>
  rw [BSmtLib.Lexer.Internal.skipBytes, Lexer.WRustPort.skipBytes]
  by_cases hi : index < bytes.size
  · have IH : ∀ s', (fun r => (r.1, skMap r.2))
        (BSmtLib.Lexer.Internal.skipBytes bytes legacy offset (index + 1) s') =
        Lexer.WRustPort.skipBytes bytes legacy offset (index + 1) (skMap s') :=
      fun s' => ih _ (by omega) (index + 1) s' rfl
    simp only [hi, dite_true]
    generalize bytes[index] = c
    obtain ⟨sk, d, l, ls⟩ := s
    cases sk <;> dsimp only [skMap]
    iterate 3
      bc (c == 34) <;> bc (c == 124) <;> bc (Lexer.isDelimiter c && d == 0) <;> (try rfl) <;>
        bc (c == 59) <;> bc (c == 40) <;> bc (c == 41) <;> bc (d - 1 == 0) <;> (try rfl) <;>
        bc (c == 10)
    · bc (c == 34) <;> bc (c == 92 && legacy) <;> bc (c == 10)
    · bc (c == 10)
    · bc (c == 124) <;> bc (c == 10)
    · bc (c == 10 || c == 13) <;> bc (c == 10)
  · simp only [hi, dite_false]

section

variable {H : Type} {m : Type → Type} [Monad m] [LawfulMonad m] {R E : Type}

theorem reset_couple :
    Coupled (fun _ _ => True) (BSmtLib.Lexer.Internal.reset (H := H) (m := m))
      (Lexer.WRustPort.reset) := by
  unfold BSmtLib.Lexer.Internal.reset Lexer.WRustPort.reset
  refine Coupled.modify fun c x hx => ?_
  rw [eq_wb hx]
  rfl

theorem skipSlice_couple (slice : ByteSlice) (skip : Lexer.RecoveryState) :
    Coupled Eq (BSmtLib.Lexer.Internal.skipSlice (H := H) (m := m) slice skip)
      (Lexer.WRustPort.skipSlice slice skip) := by
  unfold BSmtLib.Lexer.Internal.skipSlice Lexer.WRustPort.skipSlice
  refine Coupled.bind Coupled.get fun c x hx => ?_
  rw [eq_wb hx]
  refine Coupled.ite Iff.rfl (fun _ => Coupled.pure rfl) fun _ => ?_
  dsimp only
  split <;> rename_i hz <;> split <;> rename_i hx' <;>
    have e1 := (congrArg (fun r => (r.1, skMap r.2)) hz).symm.trans
      ((skipBytes_eq slice _ _ 0 _).trans hx') <;>
    simp only [Prod.mk.injEq, reduceCtorEq, Option.some.injEq, false_and, true_and] at e1
  · obtain ⟨rfl, rfl⟩ := e1
    exact Coupled.bind
      (Coupled.set (rel_mk rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl))
      fun _ _ _ => Coupled.pure rfl
  · obtain rfl := e1
    exact Coupled.bind
      (Coupled.set (rel_mk rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl))
      fun _ _ _ => Coupled.pure rfl

/-- The current location of related states is the same: the offset. -/
theorem currentLocation_eq {c : ZCore} {x : XCore} (hx : Rel c x) :
    x.currentLocation = c.currentLocation := by
  rw [eq_wb hx]
  simp [Lexer.WRustPort.LexerCore.currentLocation, Lexer.WRustPort.LexerCore.locationAt,
    Lexer.WRustPort.LexerCore.offsetAt, BSmtLib.Lexer.LexerCore.currentLocation,
    BSmtLib.Lexer.LexerCore.locationAt, BSmtLib.Lexer.LexerCore.offsetAt, wb, coreMap]

theorem executeStep_couple {R : Type}
    {step : BSmtLib.Lexer.InnerM H m (Except (Lexer.Failure E) (ControlFlow R))}
    {step' : Lexer.WRustPort.InnerM H m (Except (Lexer.Failure E) (ControlFlow R))}
    (hs : Coupled Eq step step') :
    Coupled Eq (BSmtLib.Lexer.Internal.executeStep step) (Lexer.WRustPort.executeStep step') := by
  unfold BSmtLib.Lexer.Internal.executeStep Lexer.WRustPort.executeStep
  refine Coupled.bind hs fun a b e => ?_
  subst e
  rcases a with _ | _ | r
  · exact Coupled.pure rfl
  · exact Coupled.pure rfl
  · refine Coupled.bind Coupled.get fun c x hx => Coupled.pure ?_
    rw [currentLocation_eq hx]

theorem failCall_couple (abandon : Location → StateT H m Unit) (failure : Lexer.Failure E)
    (atEnd : Bool) :
    Coupled Eq (BSmtLib.Lexer.Internal.failCall abandon failure atEnd)
      (Lexer.WRustPort.fail abandon failure atEnd) := by
  unfold BSmtLib.Lexer.Internal.failCall Lexer.WRustPort.fail
  refine Coupled.bind Coupled.get fun c x hx => ?_
  rw [eq_wb hx]
  refine Coupled.ite Iff.rfl (fun _ => Coupled.pure rfl) fun _ => ?_
  refine Coupled.bind (Coupled.modify fun c x hx => ?_) fun _ _ _ => ?_
  · rw [eq_wb hx]
    rfl
  refine Coupled.bind (Coupled.modify fun c x hx => ?_) fun _ _ _ => ?_
  · rw [eq_wb hx]
    rfl
  refine Coupled.bind (Coupled.lift _) fun _ _ _ => ?_
  refine Coupled.bind (Coupled.modify fun c x hx => ?_) fun _ _ _ => Coupled.pure rfl
  rw [eq_wb hx]
  rfl

end

end BSmtLib.Proofs.X1BatchInCoreLexer
