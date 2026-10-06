import BSmtLib.Proofs.X2ContentsLexer.Outer

/-!
# The steps between calls of the library's lexer and of the lexer with the content buffer

The resetting, the discarding and the skipping of bytes while recovering, the turning of a
failure into the error of a call, and the adding of the break location are coupled: they read
the base only through the current location, which is the offset in both lexers, and set it only
to zero. The two lexers have copies of their own of the functions on bytes (`skipBytes`,
`countLineFeeds`), which agree.
-/

namespace BSmtLib.Proofs.X2ContentsLexer

/-- The skipping state of the lexer with the content buffer for that of the library's lexer. -/
def skMap (s : BSmtLib.Lexer.Internal.Skipping) : Lexer.X2Contents.Skipping :=
  { skip := s.skip, depth := s.depth, line := s.line, lineStart := s.lineStart }

theorem countLineFeeds_loop_eq (bytes : ByteSlice) (i count : Nat) (afterLast : Option Nat) :
    BSmtLib.Lexer.Internal.countLineFeeds.loop bytes i count afterLast =
      Lexer.X2Contents.countLineFeeds.loop bytes i count afterLast := by
  fun_induction BSmtLib.Lexer.Internal.countLineFeeds.loop bytes i count afterLast <;>
    rw [Lexer.X2Contents.countLineFeeds.loop] <;> simp_all <;> intro h <;> omega

theorem countLineFeeds_eq (bytes : ByteSlice) :
    BSmtLib.Lexer.Internal.countLineFeeds bytes = Lexer.X2Contents.countLineFeeds bytes :=
  countLineFeeds_loop_eq bytes 0 0 none

-- Splits on a condition, reduces the branches that test it and closes the goals of a recursive
-- call.
set_option hygiene false in
local macro "bc " t:term:max : tactic =>
  `(tactic| (by_cases hc : $t = true <;>
    (try simp only [hc, ↓reduceIte, Bool.false_eq_true]) <;> try exact IH _))

theorem skipBytes_eq (bytes : ByteSlice) (legacy : Bool) (offset index : Nat)
    (s : BSmtLib.Lexer.Internal.Skipping) :
    (fun r => (r.1, skMap r.2)) (BSmtLib.Lexer.Internal.skipBytes bytes legacy offset index s) =
      Lexer.X2Contents.skipBytes bytes legacy offset index (skMap s) := by
  induction h : bytes.size - index using Nat.strongRecOn generalizing index s with
  | ind n ih =>
  rw [BSmtLib.Lexer.Internal.skipBytes, Lexer.X2Contents.skipBytes]
  by_cases hi : index < bytes.size
  · have IH : ∀ s', (fun r => (r.1, skMap r.2))
        (BSmtLib.Lexer.Internal.skipBytes bytes legacy offset (index + 1) s') =
        Lexer.X2Contents.skipBytes bytes legacy offset (index + 1) (skMap s') :=
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

theorem discardBytes_couple (bytes : ByteSlice) :
    Couple (fun _ _ => True) (BSmtLib.Lexer.Internal.discardBytes (H := H) (m := m) bytes)
      (Lexer.X2Contents.discardBytes bytes) := by
  unfold BSmtLib.Lexer.Internal.discardBytes Lexer.X2Contents.discardBytes
  refine Couple.modify fun c x hx => ?_
  rw [eq_wb hx]
  apply rel_mk <;> dsimp only <;> rw [countLineFeeds_eq] <;>
    generalize Lexer.X2Contents.countLineFeeds bytes = r <;> obtain ⟨n, _ | a⟩ := r <;> rfl

theorem reset_couple :
    Couple (fun _ _ => True) (BSmtLib.Lexer.Internal.reset (H := H) (m := m))
      (Lexer.X2Contents.reset) := by
  unfold BSmtLib.Lexer.Internal.reset Lexer.X2Contents.reset
  refine Couple.modify fun c x hx => ?_
  rw [eq_wb hx]
  rfl

theorem skipSlice_couple (slice : ByteSlice) (skip : Lexer.RecoveryState) :
    Couple Eq (BSmtLib.Lexer.Internal.skipSlice (H := H) (m := m) slice skip)
      (Lexer.X2Contents.skipSlice slice skip) := by
  unfold BSmtLib.Lexer.Internal.skipSlice Lexer.X2Contents.skipSlice
  refine Couple.bind Couple.get fun c x hx => ?_
  rw [eq_wb hx]
  refine Couple.ite Iff.rfl (fun _ => Couple.pure rfl) fun _ => ?_
  dsimp only
  split <;> rename_i hz <;> split <;> rename_i hx' <;>
    have e1 := (congrArg (fun r => (r.1, skMap r.2)) hz).symm.trans
      ((skipBytes_eq slice _ _ 0 _).trans hx') <;>
    simp only [Prod.mk.injEq, reduceCtorEq, Option.some.injEq, false_and, true_and] at e1
  · obtain ⟨rfl, rfl⟩ := e1
    exact Couple.bind (Couple.set (rel_mk rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl))
      fun _ _ _ => Couple.pure rfl
  · obtain rfl := e1
    exact Couple.bind (Couple.set (rel_mk rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl))
      fun _ _ _ => Couple.pure rfl

/-- The current location of related states is the same: the offset. -/
theorem currentLocation_eq {c : ZCore} {x : XCore} (hx : Rel c x) :
    x.currentLocation = c.currentLocation := by
  rw [eq_wb hx]
  simp [Lexer.X2Contents.LexerCore.currentLocation, Lexer.X2Contents.LexerCore.locationAt,
    Lexer.X2Contents.LexerCore.offsetAt, BSmtLib.Lexer.LexerCore.currentLocation,
    BSmtLib.Lexer.LexerCore.locationAt, BSmtLib.Lexer.LexerCore.offsetAt, wb, coreMap]

theorem executeStep_couple {R : Type}
    {step : BSmtLib.Lexer.InnerM H m (Except (Lexer.Failure E) (ControlFlow R))}
    {step' : Lexer.X2Contents.InnerM H m (Except (Lexer.Failure E) (ControlFlow R))}
    (hs : Couple Eq step step') :
    Couple Eq (BSmtLib.Lexer.Internal.executeStep step) (Lexer.X2Contents.executeStep step') := by
  unfold BSmtLib.Lexer.Internal.executeStep Lexer.X2Contents.executeStep
  refine Couple.bind hs fun a b e => ?_
  subst e
  rcases a with _ | _ | r
  · exact Couple.pure rfl
  · exact Couple.pure rfl
  · refine Couple.bind Couple.get fun c x hx => Couple.pure ?_
    rw [currentLocation_eq hx]

theorem failCall_couple (abandon : Location → StateT H m Unit) (failure : Lexer.Failure E)
    (atEnd : Bool) :
    Couple Eq (BSmtLib.Lexer.Internal.failCall abandon failure atEnd)
      (Lexer.X2Contents.failCall abandon failure atEnd) := by
  unfold BSmtLib.Lexer.Internal.failCall Lexer.X2Contents.failCall
  refine Couple.bind Couple.get fun c x hx => ?_
  rw [eq_wb hx]
  refine Couple.ite Iff.rfl (fun _ => Couple.pure rfl) fun _ => ?_
  refine Couple.bind (Couple.modify fun c x hx => ?_) fun _ _ _ => ?_
  · rw [eq_wb hx]
    rfl
  refine Couple.bind (Couple.lift _) fun _ _ _ => ?_
  refine Couple.bind (Couple.modify fun c x hx => ?_) fun _ _ _ => Couple.pure rfl
  rw [eq_wb hx]
  rfl

end

end BSmtLib.Proofs.X2ContentsLexer
