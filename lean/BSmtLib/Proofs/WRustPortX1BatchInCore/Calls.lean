import BSmtLib.Proofs.WRustPortX1BatchInCore.Top

/-!
# The calls of the lexers

The lexers hold their consumer and their lexer state (`Lexer`); a call runs a step of `Top` on
them (`Lexer.run`). Lexers with the same consumer and lexer states related by `TopRel` correspond
(`LexRel`). The calls of two such lexers are the projections of one computation of pairs of
results that correspond (`MCouple`): the same results, with lexers that correspond again.
-/

namespace BSmtLib.Proofs.WRustPortX1BatchInCore

/-- The two lexers correspond: the same consumer, and lexer states related by `TopRel`. -/
def LexRel {H : Type} {recovery : Recovery} (a : Lexer.WRustPort.Lexer H recovery)
    (b : Lexer.X1BatchInCore.Lexer H recovery) : Prop :=
  a.handler = b.handler ∧ TopRel a.core b.core

/-- The computations `a` and `b` are the projections of one computation of pairs related by
`Rel`. -/
def MCouple {m : Type → Type} [Monad m] {α β : Type} (Rel : α → β → Prop) (a : m α) (b : m β) :
    Prop :=
  ∃ y : m {p : α × β // Rel p.1 p.2}, a = (fun p => p.val.1) <$> y ∧ b = (fun p => p.val.2) <$> y

section

variable {m : Type → Type} [Monad m] [LawfulMonad m] {α β γ δ : Type}

theorem MCouple.map {Rel : α → β → Prop} {Rel' : γ → δ → Prop} {a : m α} {b : m β}
    (f : α → γ) (g : β → δ) (h : MCouple Rel a b) (hfg : ∀ x y, Rel x y → Rel' (f x) (g y)) :
    MCouple Rel' (f <$> a) (g <$> b) := by
  obtain ⟨y, h1, h2⟩ := h
  refine ⟨(fun p => ⟨(f p.val.1, g p.val.2), hfg _ _ p.property⟩) <$> y, ?_, ?_⟩
  · rw [h1, Functor.map_map, Functor.map_map]
  · rw [h2, Functor.map_map, Functor.map_map]

theorem MCouple.bind {Rel : α → β → Prop} {Rel' : γ → δ → Prop} {a : m α} {b : m β}
    {k : α → m γ} {k' : β → m δ} (h : MCouple Rel a b)
    (hk : ∀ x y, Rel x y → MCouple Rel' (k x) (k' y)) : MCouple Rel' (a >>= k) (b >>= k') := by
  obtain ⟨y, h1, h2⟩ := h
  have hk' : ∀ p : {p : α × β // Rel p.1 p.2}, ∃ y' : m {q : γ × δ // Rel' q.1 q.2},
      k p.val.1 = (fun q => q.val.1) <$> y' ∧ k' p.val.2 = (fun q => q.val.2) <$> y' :=
    fun p => hk _ _ p.property
  obtain ⟨Y, hY⟩ := Classical.skolem.mp hk'
  refine ⟨y >>= Y, ?_, ?_⟩
  · rw [h1, bind_map_left, map_bind]
    exact congrArg (y >>= ·) (funext fun p => (hY p).1)
  · rw [h2, bind_map_left, map_bind]
    exact congrArg (y >>= ·) (funext fun p => (hY p).2)

theorem MCouple.pure {Rel : α → β → Prop} {x : α} {y : β} (h : Rel x y) :
    MCouple (m := m) Rel (Pure.pure x) (Pure.pure y) :=
  ⟨Pure.pure ⟨(x, y), h⟩, by simp, by simp⟩

end

section

variable {H : Type} {m : Type → Type} [Monad m] [LawfulMonad m] {recovery : Recovery}
  {α β : Type}

theorem run_couple {Q : α → β → WCore → XCore → Prop} {step : StateT WCore (StateT H m) α}
    {step' : StateT XCore (StateT H m) β} (hs : ISim TopRel Q step step')
    (self : Lexer.WRustPort.Lexer H recovery) (self' : Lexer.X1BatchInCore.Lexer H recovery)
    (h : LexRel self self') :
    MCouple (fun a b => Q a.1 b.1 a.2.core b.2.core ∧ a.2.handler = b.2.handler)
      (self.run step) (self'.run step') := by
  obtain ⟨handler, core⟩ := self
  obtain ⟨handler', core'⟩ := self'
  obtain ⟨hh, ht⟩ := h
  dsimp only at hh ht
  subst hh
  obtain ⟨y, h1, h2⟩ := hs core core' ht handler
  refine ⟨(fun z => ⟨((z.val.1.1, ⟨z.val.2.2, z.val.1.2⟩), (z.val.2.1.1, ⟨z.val.2.2, z.val.2.1.2⟩)),
    ⟨z.property, rfl⟩⟩) <$> y, ?_, ?_⟩
  · simp only [Lexer.WRustPort.Lexer.run, h1, map_eq_pure_bind, bind_assoc,
      pure_bind]
  · simp only [Lexer.X1BatchInCore.Lexer.run, h2, map_eq_pure_bind, bind_assoc,
      pure_bind]

end

/-- What the two lexers give back after a failed call on a slice corresponds. -/
def AfterRel {H : Type} : (recovery : Recovery) → Lexer.WRustPort.Lexer.AfterError H recovery →
    Lexer.X1BatchInCore.Lexer.AfterError H recovery → Prop
  | .failFast, _, _ => True
  | .recovering, a, b => LexRel (recovery := .recovering) a b

/-- What the two lexers give back after a failed call at the end of the input corresponds. -/
def AfterEofRel {H : Type} : (recovery : Recovery) →
    Lexer.WRustPort.Lexer.AfterEofError H recovery →
    Lexer.X1BatchInCore.Lexer.AfterEofError H recovery → Prop
  | .failFast, _, _ => True
  | .recovering, a, b =>
    match (a : Lexer.WRustPort.Lexer.AfterEof H), (b : Lexer.X1BatchInCore.Lexer.AfterEof H) with
    | .lexer a, .lexer b => LexRel a b
    | .pending a, .pending b => LexRel a.lexer b.lexer
    | _, _ => False

/-- The results of the calls of the two lexers correspond: the same result, with lexers that
correspond, or the same error, with what the lexers give back related by `AR`. -/
def ResRel {H R E A B : Type} {recovery : Recovery} (AR : A → B → Prop) :
    Except (LexError E × A) (ControlFlow (Located R) × Lexer.WRustPort.Lexer H recovery) →
      Except (LexError E × B) (ControlFlow (Located R) × Lexer.X1BatchInCore.Lexer H recovery) →
      Prop
  | .ok (f, a), .ok (g, b) => f = g ∧ LexRel a b
  | .error (e, a), .error (e', b) => e = e' ∧ AR a b
  | _, _ => False

theorem afterError_rel {H : Type} (recovery : Recovery) (a : Lexer.WRustPort.Lexer H recovery)
    (b : Lexer.X1BatchInCore.Lexer H recovery) (h : LexRel a b) :
    AfterRel recovery (Lexer.WRustPort.Lexer.afterError a)
      (Lexer.X1BatchInCore.Lexer.afterError b) := by
  cases recovery
  · trivial
  · exact h

theorem afterEofError_rel {H : Type} (recovery : Recovery) (a : Lexer.WRustPort.Lexer H recovery)
    (b : Lexer.X1BatchInCore.Lexer H recovery) (h : LexRel a b) (continues : Bool) :
    AfterEofRel recovery (Lexer.WRustPort.Lexer.afterEofError a continues)
      (Lexer.X1BatchInCore.Lexer.afterEofError b continues) := by
  cases recovery
  · trivial
  · cases continues
    · exact h
    · exact h

section

variable {H : Type} {m : Type → Type} {R E : Type} [Monad m] [LawfulMonad m] [Consume H m R E]
  {recovery : Recovery}

theorem lexSlice_couple (hcons : ConsumesAlike H m R E) [LexRecovery recovery H m]
    (self : Lexer.WRustPort.Lexer H recovery) (self' : Lexer.X1BatchInCore.Lexer H recovery)
    (h : LexRel self self') (slice : ByteSlice) :
    MCouple (ResRel (AfterRel recovery))
      (Lexer.WRustPort.Lexer.lexSlice (R := R) (E := E) self slice)
      (Lexer.X1BatchInCore.Lexer.lexSlice self' slice) := by
  unfold Lexer.WRustPort.Lexer.lexSlice Lexer.X1BatchInCore.Lexer.lexSlice
  refine MCouple.bind (run_couple (lexSliceStep_sim hcons _ _ slice) self self' h)
    fun a b hab => ?_
  obtain ⟨r, l⟩ := a
  obtain ⟨r', l'⟩ := b
  obtain ⟨⟨e, ht⟩, hh⟩ := hab
  dsimp only at e ht hh ⊢
  subst e
  cases r
  · exact MCouple.pure ⟨rfl, afterError_rel _ _ _ ⟨hh, ht⟩⟩
  · exact MCouple.pure ⟨rfl, hh, ht⟩

theorem lexEof_couple (hcons : ConsumesAlike H m R E) [LexRecovery recovery H m]
    (self : Lexer.WRustPort.Lexer H recovery) (self' : Lexer.X1BatchInCore.Lexer H recovery)
    (h : LexRel self self') :
    MCouple (ResRel (AfterEofRel recovery)) (Lexer.WRustPort.Lexer.lexEof (R := R) (E := E) self)
      (Lexer.X1BatchInCore.Lexer.lexEof self') := by
  unfold Lexer.WRustPort.Lexer.lexEof Lexer.X1BatchInCore.Lexer.lexEof
  refine MCouple.bind (run_couple (lexEofStep_sim hcons _ _) self self' h) fun a b hab => ?_
  obtain ⟨r, l⟩ := a
  obtain ⟨r', l'⟩ := b
  obtain ⟨⟨e, ht⟩, hh⟩ := hab
  dsimp only at e ht hh ⊢
  subst e
  cases r
  · exact MCouple.pure ⟨rfl, afterEofError_rel _ _ _ ⟨hh, ht⟩ _⟩
  · exact MCouple.pure ⟨rfl, hh, ht⟩

theorem pendingLexEof_couple (hcons : ConsumesAlike H m R E) [Recover H m]
    (self : Lexer.WRustPort.Lexer.PendingEof H) (self' : Lexer.X1BatchInCore.Lexer.PendingEof H)
    (h : LexRel self.lexer self'.lexer) :
    MCouple (ResRel (recovery := .recovering) LexRel)
      (Lexer.WRustPort.Lexer.PendingEof.lexEof (R := R) (E := E) self)
      (Lexer.X1BatchInCore.Lexer.PendingEof.lexEof self') := by
  unfold Lexer.WRustPort.Lexer.PendingEof.lexEof Lexer.X1BatchInCore.Lexer.PendingEof.lexEof
  refine MCouple.bind (run_couple (lexEofStep_sim hcons _ _) self.lexer self'.lexer h)
    fun a b hab => ?_
  obtain ⟨r, l⟩ := a
  obtain ⟨r', l'⟩ := b
  obtain ⟨⟨e, ht⟩, hh⟩ := hab
  dsimp only at e ht hh ⊢
  subst e
  cases r
  · exact MCouple.pure ⟨rfl, hh, ht⟩
  · exact MCouple.pure ⟨rfl, hh, ht⟩

end

end BSmtLib.Proofs.WRustPortX1BatchInCore
