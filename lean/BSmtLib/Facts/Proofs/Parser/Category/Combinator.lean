module

public import BSmtLib.Facts.Proofs.Parser.Category.Token
import all BSmtLib.Parser
import all BSmtLib.Parser.Category.Token
import all BSmtLib.Parser.Category.Combinator

@[expose] public section

/-!
# The combinators on a cursor

A combinator has its inner parsers parse the cursor it is handed. What it does on a cursor is
built from what its inner parsers do, as `Parses`, `Waits` and `Rejects` say, by `bind_outcome`:
a parse whose answer, read as `outcome` reads it, is known, followed by a continuation whose own
answer depends on no more than that.
-/

namespace BSmtLib.Facts.Proofs.Parser.Category.Combinator

open BSmtLib.Token (Cursor)
open BSmtLib.Parser (Parse ParseError ParseErrorCause ParseState SyntaxErrorKind VersionErrorKind)
open BSmtLib.Parser.Internal (PM)
open BSmtLib.Parser.Category.Token BSmtLib.Parser.Category.Combinator
open BSmtLib.Parser.Category.Token.Internal
open BSmtLib.Parser.Category.Combinator.Internal
open BSmtLib.Facts.Parser.Adapters
open BSmtLib.Facts.Parser.Adapters.Cursor (Takes Reads noPoints)
open BSmtLib.Facts.Parser.Adapters.Outcome (Outcome outcome answer HandlerOnly)
open BSmtLib.Facts.Proofs.Parser.Category.Cursor BSmtLib.Facts.Proofs.Parser.Category.Token
open BSmtLib.Facts.Proofs.Parser.Category.Steps

set_option hygiene false in
/-- Splits the answer `a` of a parse: a syntax error of the kind `kind`, the handler's error
`error`, continuing, or breaking with the result `result`. -/
macro "answer_cases" a:ident : tactic => `(tactic| (
  rcases $a:ident with e | (_ | result)
  all_goals (try (
    obtain ⟨c, rfl⟩ : ∃ c, e = BSmtLib.Parser.ParseError.Internal.new c :=
      ⟨e.cause, (BSmtLib.Parser.ParseError.Internal.new_eta e).symm⟩
    rcases c with kind | kind | error))))

/-! ## Answers known through `outcome` -/

section

variable {H : Type} {m : Type → Type} [Monad m] [LawfulMonad m]

theorem parseState_eq (a b : ParseState H) : a = b := by
  cases a
  cases b
  rfl

variable {P R E γ δ α : Type} {Z : Type} [Cursor Z] {cursor : Z}

/-- What a parse of the cursor gives. -/
abbrev Answer (H P R E : Type) {Z : Type} [Cursor Z] (cursor : Z) : Type :=
  Except (ParseError E) (ControlFlow R) × P × ParseState H ×
    { next : Z // Cursor.HasNext cursor → Cursor.Consumed next cursor }

/-- A continuation of a parse, on what `outcome` reads of the parse; `x₀` fills in what it does
not read. -/
noncomputable def onOutcome (k : Answer H P R E cursor → StateT H m γ)
    (x₀ : Answer H P R E cursor) : Outcome R P Z E → StateT H m γ
  | .finished result parser next =>
    @dite _ (Cursor.HasNext cursor → Cursor.Consumed next cursor) (Classical.propDecidable _)
      (fun h => k (.ok (.break result), parser, .new, ⟨next, h⟩)) fun _ => k x₀
  | .waits parser => k (.ok .continue, parser, .new, x₀.2.2.2)
  | .rejected kind next =>
    @dite _ (Cursor.HasNext cursor → Cursor.Consumed next cursor) (Classical.propDecidable _)
      (fun h => k (.error (ParseError.Internal.new (.syntax kind)), x₀.2.1, .new, ⟨next, h⟩))
      fun _ => k x₀
  | .rejectedVersion kind next =>
    @dite _ (Cursor.HasNext cursor → Cursor.Consumed next cursor) (Classical.propDecidable _)
      (fun h => k (.error (ParseError.Internal.new (.version kind)), x₀.2.1, .new, ⟨next, h⟩))
      fun _ => k x₀
  | .failed error => k (.error (ParseError.Internal.new (.handler error)), x₀.2.1, .new, x₀.2.2.2)

omit [Monad m] [LawfulMonad m] in
theorem onOutcome_finished (k : Answer H P R E cursor → StateT H m γ) (x₀ : Answer H P R E cursor)
    (result : R) (parser : P) {next : Z}
    (h : Cursor.HasNext cursor → Cursor.Consumed next cursor) :
    onOutcome k x₀ (.finished result parser next) =
      k (.ok (.break result), parser, .new, ⟨next, h⟩) := by
  simp only [onOutcome]
  rw [dite_eq_left_of_eq_true (eq_true h)]

omit [Monad m] [LawfulMonad m] in
theorem onOutcome_rejected (k : Answer H P R E cursor → StateT H m γ) (x₀ : Answer H P R E cursor)
    (kind : SyntaxErrorKind) {next : Z}
    (h : Cursor.HasNext cursor → Cursor.Consumed next cursor) :
    onOutcome k x₀ (.rejected kind next) =
      k (.error (ParseError.Internal.new (.syntax kind)), x₀.2.1, .new, ⟨next, h⟩) := by
  simp only [onOutcome]
  rw [dite_eq_left_of_eq_true (eq_true h)]

omit [Monad m] [LawfulMonad m] in
theorem onOutcome_rejectedVersion (k : Answer H P R E cursor → StateT H m γ)
    (x₀ : Answer H P R E cursor) (kind : VersionErrorKind) {next : Z}
    (h : Cursor.HasNext cursor → Cursor.Consumed next cursor) :
    onOutcome k x₀ (.rejectedVersion kind next) =
      k (.error (ParseError.Internal.new (.version kind)), x₀.2.1, .new, ⟨next, h⟩) := by
  simp only [onOutcome]
  rw [dite_eq_left_of_eq_true (eq_true h)]

/-- A parse followed by a continuation whose answer, read by `g`, depends on no more than what
`outcome` reads of the parse. -/
theorem bind_outcome (X : StateT H m (Answer H P R E cursor)) (g : γ → δ)
    (k : Answer H P R E cursor → StateT H m γ) (x₀ : Answer H P R E cursor)
    (hk : ∀ x, g <$> k x = g <$> onOutcome k x₀ (outcome x)) :
    g <$> (X >>= k) = (outcome <$> X) >>= fun o => g <$> onOutcome k x₀ o := by
  rw [map_bind, bind_map_left]
  exact bind_congr hk

/-- A parse followed by a continuation that depends on no more than what `outcome` reads of the
parse. -/
theorem bind_outcome_eq (X : StateT H m (Answer H P R E cursor))
    (k : Answer H P R E cursor → StateT H m γ) (x₀ : Answer H P R E cursor)
    (hk : ∀ x, k x = onOutcome k x₀ (outcome x)) :
    X >>= k = (outcome <$> X) >>= onOutcome k x₀ := by
  rw [bind_map_left]
  exact bind_congr hk

omit [LawfulMonad m] in
theorem handler_run {x : ExceptT (ParseErrorCause E) (StateT H m) α} (hx : HandlerOnly x) :
    ∃ calls : ExceptT E (StateT H m) α,
      x.run = (fun e => match e with
        | .ok a => .ok a
        | .error error => .error (.handler error)) <$> calls.run :=
  handlerOnly_run_eq hx

omit [Cursor Z] in
/-- The answer of a handler-only program, bound. -/
theorem answer_bind {Q : Type} {x : ExceptT (ParseErrorCause E) (StateT H m) α}
    {calls : ExceptT E (StateT H m) α}
    (hcalls : x.run = (fun e => match e with
        | .ok a => .ok a
        | .error error => .error (.handler error)) <$> calls.run)
    (onResult : α → Outcome R P Z E) (next : Z) (F : Outcome R P Z E → StateT H m Q) :
    (answer onResult next <$> x.run) >>= F =
      calls.run >>= fun e => match e with
        | .ok a => F (onResult a)
        | .error error => F (.failed error) := by
  rw [hcalls, Functor.map_map, bind_map_left]
  refine bind_congr fun e => ?_
  rcases e with error | a <;> rfl

omit [Cursor Z] in
/-- The answer of a handler-only program followed by more, as a map. -/
theorem answer_run_bind {β : Type} {x : ExceptT (ParseErrorCause E) (StateT H m) α}
    {calls : ExceptT E (StateT H m) α}
    (hcalls : x.run = (fun e => match e with
        | .ok a => .ok a
        | .error error => .error (.handler error)) <$> calls.run)
    (f : α → ExceptT (ParseErrorCause E) (StateT H m) β) (onResult : β → Outcome R P Z E)
    (next : Z) :
    answer onResult next <$> (x >>= f).run =
      calls.run >>= fun e => match e with
        | .ok a => answer onResult next <$> (f a).run
        | .error error => pure (.failed error) := by
  rw [ExceptT.run_bind, hcalls, bind_map_left, map_bind]
  refine bind_congr fun e => ?_
  rcases e with error | a
  · simp [answer]
  · rfl

omit [LawfulMonad m] in
/-- `outcome` reads alike two answers with the same answer, parser and cursor. -/
theorem outcome_rewrap {cursor' : Z} (a : Except (ParseError E) (ControlFlow R)) (p : P)
    (s s' : ParseState H) (z : Z) (h : Cursor.HasNext cursor → Cursor.Consumed z cursor)
    (h' : Cursor.HasNext cursor' → Cursor.Consumed z cursor') :
    outcome (cursor := cursor) (a, p, s, ⟨z, h⟩) =
      outcome (cursor := cursor') (a, p, s', ⟨z, h'⟩) := by
  rcases a with _ | (_ | _) <;> rfl

theorem outcome_bind_pure {cursor' : Z} (X : StateT H m (Answer H P R E cursor'))
    (w : Answer H P R E cursor' → Answer H P R E cursor)
    (hw : ∀ x, outcome (w x) = outcome x) :
    outcome <$> (X >>= fun x => pure (w x)) = outcome <$> X := by
  rw [map_bind]
  simp only [map_pure, hw]
  rw [bind_pure_comp]

/-- Waiting after a program whose result is changed: waiting after the program, the change made
by the parser given back. -/
theorem waits_of_map {Pa Ra : Type} [Parse Pa H m E Ra] {version : Version} {p : Pa}
    {tokens : List Parser.Internal.Input} {β : Type} {program : ExceptT (ParseErrorCause E)
      (StateT H m) α} {f : α → β} {after : β → Pa}
    (h : Outcome.Waits version p tokens (f <$> program) after) (hp : HandlerOnly program) :
    Outcome.Waits version p tokens program fun a => after (f a) := by
  refine ⟨hp, fun state cursor last htakes hnone => ?_⟩
  rw [h.2 state cursor last htakes hnone, ExceptT.run_map, Functor.map_map]
  congr 1
  funext e
  rcases e with (_ | _) | a <;> rfl

theorem Takes.consumed_of_ne {version : Version} {cursor next : Z}
    {tokens : List Parser.Internal.Input} (h : Takes version cursor tokens next)
    (hne : tokens ≠ []) : Cursor.HasNext cursor → Cursor.Consumed next cursor := by
  obtain ⟨first, rest, rfl⟩ := List.exists_cons_of_ne_nil hne
  exact fun _ => Takes.consumed h

theorem Takes.hasNext_of_ne {version : Version} {cursor next : Z}
    {tokens : List Parser.Internal.Input} (h : Takes version cursor tokens next)
    (hne : tokens ≠ []) : Cursor.HasNext cursor := by
  obtain ⟨first, rest, rfl⟩ := List.exists_cons_of_ne_nil hne
  exact Takes.hasNext h

end
section

variable {H : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
variable {P P' R R' E : Type} {Z : Type} [Cursor Z] {cursor : Z}

/-- A parse followed by a pure change of its answer that `outcome` reads through `F`. -/
theorem outcome_map {cursor' : Z} (X : StateT H m (Answer H P R E cursor'))
    (w : Answer H P R E cursor' → Answer H P' R' E cursor)
    (F : Outcome R P Z E → Outcome R' P' Z E) (hw : ∀ x, outcome (w x) = F (outcome x)) :
    outcome <$> (X >>= fun x => pure (w x)) = F <$> (outcome <$> X) := by
  rw [map_bind, Functor.map_map]
  simp only [map_pure, hw]
  rw [bind_pure_comp]

end

section

variable {H P₁ P₂ R₁ R₂ : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
  [Handler H m] [Parse P₁ H m (Handler.Error H) R₁]
  [Parse P₂ H m (Handler.Error H) R₂]

/-- What the pair answers after its second parser answered, the first having finished with
`first`. -/
private def afterSecond (p₁ : P₁) (first : R₁) {Z : Type} :
    Outcome R₂ P₂ Z (Handler.Error H) →
    Outcome (R₁ × R₂) (PairParser H P₁ P₂) Z (Handler.Error H)
  | .finished second p₂ next => .finished (first, second) (PairParser.new p₁ p₂) next
  | .waits p₂ => .waits ⟨p₁, p₂, some first⟩
  | .rejected kind next => .rejected kind next
  | .rejectedVersion kind next => .rejectedVersion kind next
  | .failed error => .failed error

private theorem parseSecond_outcome (p₁ : P₁) (p₂ : P₂) (first : R₁) {Z : Type} [Cursor Z]
    (state : ParseState H) (cursor : Z) :
    outcome <$> (PairParser.new (H := H) p₁ p₂).parseSecond first state cursor =
      afterSecond p₁ first <$> (outcome <$> Parse.parse p₂ state cursor) := by
  simp only [PairParser.parseSecond, PairParser.new]
  rw [map_bind, Functor.map_map, map_eq_pure_bind]
  refine bind_congr fun x => ?_
  obtain ⟨a, p, s, ⟨z, hz⟩⟩ := x
  rcases a with (_ | _) | (_ | _) <;> simp only [map_pure] <;> rfl

omit [LawfulMonad m] in
/-- The pair's parse, its first parser not finished yet: the first parser parses, then the pair
goes on as `pairAfterFirst` says. -/
private theorem pair_parse_eq (p₁ : P₁) (p₂ : P₂) {Z : Type} [Cursor Z] (state : ParseState H)
    (cursor : Z) :
    outcome <$> Parse.parse (PairParser.new (H := H) p₁ p₂) state cursor =
      outcome <$> (Parse.parse p₁ state cursor >>= fun x =>
        match x with
        | (answer, first, state, ⟨next, consumed⟩) =>
          match answer with
          | .error error => pure (.error error, (⟨first, p₂, none⟩ : PairParser H P₁ P₂), state,
              ⟨next, consumed⟩)
          | .ok .continue => pure (.ok .continue, ⟨first, p₂, none⟩, state, ⟨next, consumed⟩)
          | .ok (.break result) =>
            match Cursor.decideHasNext next with
            | .isFalse _ => pure (.ok .continue, ⟨first, p₂, some result⟩, state,
                ⟨next, consumed⟩)
            | .isTrue h => do
              let (answer, self, state, ⟨later, taken⟩) ←
                (PairParser.new (H := H) first p₂).parseSecond result state next
              return (answer, self, state,
                ⟨later, fun hn => Cursor.consumed_trans (taken h) (consumed hn)⟩)) := rfl

/-- What the pair's continuation after the first parser does, read by `outcome`, depends on no
more than what `outcome` reads of the first parser's answer. -/
private theorem pair_k_resp (p₂ : P₂) {Z : Type} [Cursor Z] {cursor : Z}
    (x₀ : Answer H P₁ R₁ (Handler.Error H) cursor)
    (x : Answer H P₁ R₁ (Handler.Error H) cursor) :
    let k := fun (x : Answer H P₁ R₁ (Handler.Error H) cursor) =>
      (match x with
        | (answer, first, state, ⟨next, consumed⟩) =>
          match answer with
          | .error error => pure (.error error, (⟨first, p₂, none⟩ : PairParser H P₁ P₂), state,
              ⟨next, consumed⟩)
          | .ok .continue => pure (.ok .continue, ⟨first, p₂, none⟩, state, ⟨next, consumed⟩)
          | .ok (.break result) =>
            match Cursor.decideHasNext next with
            | .isFalse _ => pure (.ok .continue, ⟨first, p₂, some result⟩, state,
                ⟨next, consumed⟩)
            | .isTrue h => do
              let (answer, self, state, ⟨later, taken⟩) ←
                (PairParser.new (H := H) first p₂).parseSecond result state next
              return (answer, self, state,
                ⟨later, fun hn => Cursor.consumed_trans (taken h) (consumed hn)⟩) :
        StateT H m (Answer H (PairParser H P₁ P₂) (R₁ × R₂) (Handler.Error H) cursor))
    outcome <$> k x = outcome <$> onOutcome k x₀ (outcome x) := by
  intro k
  obtain ⟨a, p, s, ⟨z, hz⟩⟩ := x
  answer_cases a
  · rw [show outcome (cursor := cursor)
        (.error (ParseError.Internal.new (.syntax kind)), p, s, ⟨z, hz⟩) =
      .rejected kind z from rfl, onOutcome_rejected _ _ _ hz]
    simp only [k, map_pure]
    rfl
  · rw [show outcome (cursor := cursor)
        (.error (ParseError.Internal.new (.version kind)), p, s, ⟨z, hz⟩) =
      .rejectedVersion kind z from rfl, onOutcome_rejectedVersion _ _ _ hz]
    simp only [k, map_pure]
    rfl
  · simp only [onOutcome, outcome, k, map_pure, ParseError.Internal.cause_new]
  · simp only [onOutcome, outcome, k, map_pure]
  · rw [show outcome (cursor := cursor) (.ok (.break result), p, s, ⟨z, hz⟩) =
      .finished result p z from rfl, onOutcome_finished _ _ _ _ hz, parseState_eq s .new]

/-- The pair on the values of its two parsers, one after the other. -/
theorem pair_parses {version : Version} {p₁ b₁ : P₁} {p₂ b₂ : P₂}
    {tokens₁ tokens₂ : List Parser.Internal.Input} {program₁ : PM H R₁} {program₂ : PM H R₂}
    (h₁ : Outcome.Finishes version p₁ tokens₁ program₁ b₁)
    (h₂ : Outcome.Finishes version p₂ tokens₂ program₂ b₂) (hne₁ : tokens₁ ≠ [])
    (hne₂ : tokens₂ ≠ []) :
    Outcome.Finishes version (PairParser.new (H := H) p₁ p₂) (tokens₁ ++ tokens₂)
      (do let first ← program₁; let second ← program₂; pure (first, second))
      (PairParser.new b₁ b₂) := by
  refine ⟨handlerOnly_bind h₁.1 fun _ => handlerOnly_bind h₂.1 fun _ => handlerOnly_pure _,
    fun state cursor next rest htakes hreads => ?_⟩
  obtain ⟨middle, ht₁, ht₂⟩ := Takes.split htakes
  obtain ⟨calls₁, hcalls₁⟩ := handler_run h₁.1
  obtain ⟨calls₂, hcalls₂⟩ := handler_run h₂.1
  have hc₁ := Takes.consumed_of_ne ht₁ hne₁
  rw [pair_parse_eq, bind_outcome _ outcome _ (.ok .continue, p₁, .new, ⟨middle, hc₁⟩) (by
      intro x
      obtain ⟨a, p, s, ⟨z, hz⟩⟩ := x
      answer_cases a
      · rw [show outcome (cursor := cursor)
            (.error (ParseError.Internal.new (.syntax kind)), p, s, ⟨z, hz⟩) =
          .rejected kind z from rfl, onOutcome_rejected _ _ _ hz]
        simp only [map_pure]
        rfl
      · rw [show outcome (cursor := cursor)
            (.error (ParseError.Internal.new (.version kind)), p, s, ⟨z, hz⟩) =
          .rejectedVersion kind z from rfl, onOutcome_rejectedVersion _ _ _ hz]
        simp only [map_pure]
        rfl
      · simp only [onOutcome, outcome, map_pure, ParseError.Internal.cause_new]
      · simp only [onOutcome, outcome, map_pure]
      · rw [show outcome (cursor := cursor) (.ok (.break result), p, s, ⟨z, hz⟩) =
          .finished result p z from rfl, onOutcome_finished _ _ _ _ hz, parseState_eq s .new]),
    h₁.2 state cursor middle (tokens₂ ++ rest) ht₁ (Reads.of_takes ht₂ hreads),
    answer_bind hcalls₁, answer_run_bind hcalls₁]
  refine bind_congr fun e => ?_
  rcases e with error | first
  · simp [onOutcome, outcome]
  · dsimp only
    rw [onOutcome_finished _ _ _ _ hc₁]
    dsimp only
    split
    · rename_i hn _
      exact absurd (Takes.hasNext_of_ne ht₂ hne₂) hn
    · rw [outcome_bind_pure _ _ (fun x => by
          obtain ⟨a, p, s, ⟨z, hz⟩⟩ := x
          rcases a with (_ | _) | (_ | _) <;> rfl),
        parseSecond_outcome, h₂.2 .new middle next rest ht₂ hreads, answer_run_bind hcalls₂,
        hcalls₂, Functor.map_map, Functor.map_map, map_eq_pure_bind]
      refine bind_congr fun e => ?_
      rcases e with error | second <;> simp [answer, afterSecond]

/-- The pair rejects where its first parser rejects. -/
theorem pair_rejects_first {version : Version} {p₁ : P₁} {p₂ : P₂}
    {tokens : List Parser.Internal.Input} {program : PM H Unit} {kind : SyntaxErrorKind}
    (h : Outcome.Rejects version p₁ tokens program kind) (hne : tokens ≠ []) :
    Outcome.Rejects version (PairParser.new (H := H) p₁ p₂) tokens program kind := by
  refine ⟨h.1, fun state cursor next rest htakes hreads => ?_⟩
  obtain ⟨calls, hcalls⟩ := handler_run h.1
  have hc := Takes.consumed_of_ne htakes hne
  rw [pair_parse_eq, bind_outcome _ outcome _ (.ok .continue, p₁, .new, ⟨next, hc⟩)
      (pair_k_resp p₂ _), h.2 state cursor next rest htakes hreads, answer_bind hcalls, hcalls,
    Functor.map_map]
  conv => rhs; rw [map_eq_pure_bind]
  refine bind_congr fun e => ?_
  rcases e with error | ⟨⟩
  · simp [onOutcome, outcome, answer]
  · dsimp only
    rw [onOutcome_rejected _ _ _ hc]
    simp [outcome, answer]

/-- The pair rejects where its second parser rejects, after the first finished. -/
theorem pair_rejects_second {version : Version} {p₁ b₁ : P₁} {p₂ : P₂}
    {tokens₁ tokens₂ : List Parser.Internal.Input} {program₁ : PM H R₁} {program₂ : PM H Unit}
    {kind : SyntaxErrorKind}
    (h₁ : Outcome.Finishes version p₁ tokens₁ program₁ b₁)
    (h₂ : Outcome.Rejects version p₂ tokens₂ program₂ kind) (hne₁ : tokens₁ ≠ [])
    (hne₂ : tokens₂ ≠ []) :
    Outcome.Rejects version (PairParser.new (H := H) p₁ p₂) (tokens₁ ++ tokens₂)
      (do let _ ← program₁; program₂) kind := by
  refine ⟨handlerOnly_bind h₁.1 fun _ => h₂.1, fun state cursor next rest htakes hreads => ?_⟩
  obtain ⟨middle, ht₁, ht₂⟩ := Takes.split htakes
  obtain ⟨calls₁, hcalls₁⟩ := handler_run h₁.1
  obtain ⟨calls₂, hcalls₂⟩ := handler_run h₂.1
  have hc₁ := Takes.consumed_of_ne ht₁ hne₁
  rw [pair_parse_eq, bind_outcome _ outcome _ (.ok .continue, p₁, .new, ⟨middle, hc₁⟩)
      (pair_k_resp p₂ _),
      h₁.2 state cursor middle (tokens₂ ++ rest) ht₁ (Reads.of_takes ht₂ hreads),
    answer_bind hcalls₁, answer_run_bind hcalls₁]
  refine bind_congr fun e => ?_
  rcases e with error | first
  · simp [onOutcome, outcome]
  · dsimp only
    rw [onOutcome_finished _ _ _ _ hc₁]
    dsimp only
    split
    · rename_i hn _
      exact absurd (Takes.hasNext_of_ne ht₂ hne₂) hn
    · rw [outcome_bind_pure _ _ (fun x => by
          obtain ⟨a, p, s, ⟨z, hz⟩⟩ := x
          rcases a with (_ | _) | (_ | _) <;> rfl),
        parseSecond_outcome, h₂.2 .new middle next rest ht₂ hreads, hcalls₂, Functor.map_map,
        Functor.map_map]
      simp only [Functor.map_map]
      refine congrArg (· <$> calls₂.run) (funext fun e => ?_)
      rcases e with error | ⟨⟩ <;> simp [answer, afterSecond]

/-- When its first parser continues on the tokens of the cursor, the pair continues, with the
waiting first parser as its first parser. -/
theorem pair_waits_first {version : Version} {p₁ : P₁} {p₂ : P₂}
    {tokens : List Parser.Internal.Input} {α : Type} {program : PM H α} {after : α → P₁}
    (h : Outcome.Waits version p₁ tokens program after) :
    Outcome.Waits version (PairParser.new (H := H) p₁ p₂) tokens program
      fun a => PairParser.new (after a) p₂ := by
  refine ⟨h.1, fun state cursor last htakes hnone => ?_⟩
  obtain ⟨calls, hcalls⟩ := handler_run h.1
  have hc : Cursor.HasNext cursor → Cursor.Consumed last cursor := by
    cases tokens with
    | nil =>
      rw [Takes.nil_inv htakes] at hnone ⊢
      exact fun hn => absurd hn (Parser.Internal.not_hasNext hnone)
    | cons token tokens => exact fun _ => Takes.consumed htakes
  rw [pair_parse_eq, bind_outcome _ outcome _ (.ok .continue, p₁, .new, ⟨last, hc⟩)
      (pair_k_resp p₂ _), h.2 state cursor last htakes hnone, answer_bind hcalls, hcalls,
    Functor.map_map]
  conv => rhs; rw [map_eq_pure_bind]
  refine bind_congr fun e => ?_
  rcases e with error | a
  · simp [onOutcome, outcome, answer]
  · simp [onOutcome, outcome, answer, PairParser.new]

private theorem parseSecond_outcome' (p₁ : P₁) (p₂ : P₂) (first : R₁) (fr : Option R₁) {Z : Type}
    [Cursor Z] (state : ParseState H) (cursor : Z) :
    outcome <$> (⟨p₁, p₂, fr⟩ : PairParser H P₁ P₂).parseSecond first state cursor =
      afterSecond p₁ first <$> (outcome <$> Parse.parse p₂ state cursor) := by
  simp only [PairParser.parseSecond]
  rw [map_bind, Functor.map_map, map_eq_pure_bind]
  refine bind_congr fun x => ?_
  obtain ⟨a, p, s, ⟨z, hz⟩⟩ := x
  rcases a with (_ | _) | (_ | _) <;> simp only [map_pure] <;> rfl

/-- A pair whose first parser finished with `first`: it finishes as its second parser does. -/
private theorem pairWith_finishes {version : Version} (b₁ : P₁) (first : R₁) {p₂ b₂ : P₂}
    {tokens : List Parser.Internal.Input} {program : PM H R₂}
    (h : Outcome.Finishes version p₂ tokens program b₂) :
    Outcome.Finishes version (⟨b₁, p₂, some first⟩ : PairParser H P₁ P₂) tokens
      ((fun second => (first, second)) <$> program) (PairParser.new b₁ b₂) := by
  refine ⟨handlerOnly_map _ h.1, fun state cursor next rest htakes hreads => ?_⟩
  obtain ⟨calls, hcalls⟩ := handler_run h.1
  rw [show Parse.parse (⟨b₁, p₂, some first⟩ : PairParser H P₁ P₂) state cursor =
      (⟨b₁, p₂, some first⟩ : PairParser H P₁ P₂).parseSecond first state cursor from rfl,
    parseSecond_outcome', h.2 state cursor next rest htakes hreads, hcalls, ExceptT.run_map,
    hcalls]
  simp only [Functor.map_map]
  refine congrArg (· <$> calls.run) (funext fun e => ?_)
  rcases e with error | second <;> simp [answer, afterSecond, Except.map]

/-- A pair whose first parser finished with `first`: it rejects where its second parser does. -/
private theorem pairWith_rejects {version : Version} (b₁ : P₁) (first : R₁) {p₂ : P₂}
    {tokens : List Parser.Internal.Input} {program : PM H Unit} {kind : SyntaxErrorKind}
    (h : Outcome.Rejects version p₂ tokens program kind) :
    Outcome.Rejects version (⟨b₁, p₂, some first⟩ : PairParser H P₁ P₂) tokens program kind := by
  refine ⟨h.1, fun state cursor next rest htakes hreads => ?_⟩
  obtain ⟨calls, hcalls⟩ := handler_run h.1
  rw [show Parse.parse (⟨b₁, p₂, some first⟩ : PairParser H P₁ P₂) state cursor =
      (⟨b₁, p₂, some first⟩ : PairParser H P₁ P₂).parseSecond first state cursor from rfl,
    parseSecond_outcome', h.2 state cursor next rest htakes hreads, hcalls]
  simp only [Functor.map_map]
  refine congrArg (· <$> calls.run) (funext fun e => ?_)
  rcases e with error | ⟨⟩ <;> simp [answer, afterSecond]

/--
When its first parser finishes on exactly the tokens of the cursor, the pair continues, as a pair
that, on the tokens after, finishes and rejects as its second parser does.
-/
theorem pair_waits_between {version : Version} {p₁ b₁ : P₁} {p₂ : P₂}
    {tokens : List Parser.Internal.Input} {program : PM H R₁}
    (h : Outcome.Finishes version p₁ tokens program b₁) (hne : tokens ≠ []) :
    ∃ after : R₁ → PairParser H P₁ P₂,
      Outcome.Waits version (PairParser.new (H := H) p₁ p₂) tokens program after ∧
      (∀ first {tokens₂ : List Parser.Internal.Input} {program₂ : PM H R₂} {b₂ : P₂},
        Outcome.Finishes version p₂ tokens₂ program₂ b₂ →
        Outcome.Finishes version (after first) tokens₂ ((fun second => (first, second)) <$>
          program₂) (PairParser.new b₁ b₂)) ∧
      (∀ first {tokens₂ : List Parser.Internal.Input} {program₂ : PM H Unit}
        {kind : SyntaxErrorKind}, Outcome.Rejects version p₂ tokens₂ program₂ kind →
        Outcome.Rejects version (after first) tokens₂ program₂ kind) := by
  refine ⟨fun first => ⟨b₁, p₂, some first⟩, ⟨h.1, fun state cursor last htakes hnone => ?_⟩,
    fun first _ _ _ h₂ => pairWith_finishes b₁ first h₂,
    fun first _ _ _ h₂ => pairWith_rejects b₁ first h₂⟩
  obtain ⟨calls, hcalls⟩ := handler_run h.1
  have hc := Takes.consumed_of_ne htakes hne
  have hreads : Reads version last [] := ⟨last, .nil last, hnone⟩
  rw [pair_parse_eq, bind_outcome _ outcome _ (.ok .continue, p₁, .new, ⟨last, hc⟩)
      (pair_k_resp p₂ _), h.2 state cursor last [] htakes hreads, answer_bind hcalls, hcalls,
    Functor.map_map]
  conv => rhs; rw [map_eq_pure_bind]
  refine bind_congr fun e => ?_
  rcases e with error | first
  · simp [onOutcome, outcome, answer]
  · dsimp only
    rw [onOutcome_finished _ _ _ _ hc]
    dsimp only
    split
    · simp [outcome, answer]
    · rename_i hn _
      exact absurd hn (Parser.Internal.not_hasNext hnone)

/--
When its first parser finishes on the first tokens of the cursor and its second parser continues on
the rest, the pair continues, as a pair that, on the tokens after, finishes and rejects as the
second parser does then.
-/
theorem pair_waits_second {version : Version} {p₁ b₁ : P₁} {p₂ : P₂}
    {tokens₁ tokens₂ : List Parser.Internal.Input} {program₁ : PM H R₁} {α : Type}
    {program₂ : PM H α} {after₂ : α → P₂}
    (h₁ : Outcome.Finishes version p₁ tokens₁ program₁ b₁)
    (h₂ : Outcome.Waits version p₂ tokens₂ program₂ after₂) (hne₁ : tokens₁ ≠ [])
    (hne₂ : tokens₂ ≠ []) :
    ∃ after : R₁ × α → PairParser H P₁ P₂,
      Outcome.Waits version (PairParser.new (H := H) p₁ p₂) (tokens₁ ++ tokens₂)
        (do let first ← program₁; let a ← program₂; pure (first, a)) after ∧
      (∀ first a {tokens₃ : List Parser.Internal.Input} {program₃ : PM H R₂} {b₂ : P₂},
        Outcome.Finishes version (after₂ a) tokens₃ program₃ b₂ →
        Outcome.Finishes version (after (first, a)) tokens₃ ((fun second => (first, second)) <$>
          program₃) (PairParser.new b₁ b₂)) ∧
      (∀ first a {tokens₃ : List Parser.Internal.Input} {program₃ : PM H Unit}
        {kind : SyntaxErrorKind}, Outcome.Rejects version (after₂ a) tokens₃ program₃ kind →
        Outcome.Rejects version (after (first, a)) tokens₃ program₃ kind) := by
  refine ⟨fun x => ⟨b₁, after₂ x.2, some x.1⟩,
    ⟨handlerOnly_bind h₁.1 fun _ => handlerOnly_bind h₂.1 fun _ => handlerOnly_pure _,
      fun state cursor last htakes hnone => ?_⟩,
    fun first a _ _ _ h₃ => pairWith_finishes b₁ first h₃,
    fun first a _ _ _ h₃ => pairWith_rejects b₁ first h₃⟩
  obtain ⟨middle, ht₁, ht₂⟩ := Takes.split htakes
  obtain ⟨calls₁, hcalls₁⟩ := handler_run h₁.1
  obtain ⟨calls₂, hcalls₂⟩ := handler_run h₂.1
  have hc₁ := Takes.consumed_of_ne ht₁ hne₁
  rw [pair_parse_eq, bind_outcome _ outcome _ (.ok .continue, p₁, .new, ⟨middle, hc₁⟩)
      (pair_k_resp p₂ _),
    h₁.2 state cursor middle tokens₂ ht₁
      (by simpa using Reads.of_takes ht₂ ⟨last, .nil last, hnone⟩),
    answer_bind hcalls₁, answer_run_bind hcalls₁]
  refine bind_congr fun e => ?_
  rcases e with error | first
  · simp [onOutcome, outcome]
  · dsimp only
    rw [onOutcome_finished _ _ _ _ hc₁]
    dsimp only
    split
    · rename_i hn _
      exact absurd (Takes.hasNext_of_ne ht₂ hne₂) hn
    · rw [outcome_bind_pure _ _ (fun x => by
          obtain ⟨a, p, s, ⟨z, hz⟩⟩ := x
          rcases a with (_ | _) | (_ | _) <;> rfl),
        parseSecond_outcome, h₂.2 .new middle last ht₂ hnone, answer_run_bind hcalls₂, hcalls₂,
        Functor.map_map, Functor.map_map]
      rw [map_eq_pure_bind]
      refine bind_congr fun e => ?_
      rcases e with error | a <;> simp [answer, afterSecond]

end

section

variable {H P R : Type} {m : Type → Type} [Monad m] [LawfulMonad m] [Handler H m]
  [Parse P H m (Handler.Error H) R]

/-- The closed parser's answer from its pair's. -/
private def closedF {Z : Type} :
    Outcome (R × Unit) (PairParser H P CloseParenParser) Z (Handler.Error H) →
    Outcome R (ClosedParser H P) Z (Handler.Error H)
  | .finished result pair next => .finished result.1 ⟨pair⟩ next
  | .waits pair => .waits ⟨pair⟩
  | .rejected kind next => .rejected kind next
  | .rejectedVersion kind next => .rejectedVersion kind next
  | .failed error => .failed error

/-- The opened parser's answer from its pair's. -/
private def openedF {Z : Type} :
    Outcome (Unit × R) (PairParser H OpenParenParser P) Z (Handler.Error H) →
    Outcome R (OpenedParser H P) Z (Handler.Error H)
  | .finished result pair next => .finished result.2 ⟨pair⟩ next
  | .waits pair => .waits ⟨pair⟩
  | .rejected kind next => .rejected kind next
  | .rejectedVersion kind next => .rejectedVersion kind next
  | .failed error => .failed error

private theorem closed_outcome (pair : PairParser H P CloseParenParser) {Z : Type} [Cursor Z]
    (state : ParseState H) (cursor : Z) :
    outcome <$> Parse.parse (⟨pair⟩ : ClosedParser H P) state cursor =
      closedF <$> (outcome <$> Parse.parse pair state cursor) := by
  rw [show Parse.parse (⟨pair⟩ : ClosedParser H P) state cursor =
      Parse.parse pair state cursor >>= fun x => pure (Internal.mapBreak (fun (r, ()) => r) x.1,
        (⟨x.2.1⟩ : ClosedParser H P), x.2.2.1, x.2.2.2) from rfl, map_bind, Functor.map_map,
    map_eq_pure_bind]
  refine bind_congr fun x => ?_
  obtain ⟨a, p, s, ⟨z, hz⟩⟩ := x
  rcases a with (_ | _) | (_ | ⟨r, ⟨⟩⟩) <;> simp only [map_pure] <;> rfl

private theorem opened_outcome (pair : PairParser H OpenParenParser P) {Z : Type} [Cursor Z]
    (state : ParseState H) (cursor : Z) :
    outcome <$> Parse.parse (⟨pair⟩ : OpenedParser H P) state cursor =
      openedF <$> (outcome <$> Parse.parse pair state cursor) := by
  rw [show Parse.parse (⟨pair⟩ : OpenedParser H P) state cursor =
      Parse.parse pair state cursor >>= fun x => pure (Internal.mapBreak (fun ((), r) => r) x.1,
        (⟨x.2.1⟩ : OpenedParser H P), x.2.2.1, x.2.2.2) from rfl, map_bind, Functor.map_map,
    map_eq_pure_bind]
  refine bind_congr fun x => ?_
  obtain ⟨a, p, s, ⟨z, hz⟩⟩ := x
  rcases a with (_ | _) | (_ | ⟨⟨⟩, r⟩) <;> simp only [map_pure] <;> rfl

/-- What the closed parser does, from what its pair does. -/
private theorem closed_finishes_of {version : Version}
    {pair back : PairParser H P CloseParenParser}
    {tokens : List Parser.Internal.Input} {program : PM H (R × Unit)}
    (h : Outcome.Finishes version pair tokens program back) :
    Outcome.Finishes version (⟨pair⟩ : ClosedParser H P) tokens ((·.1) <$> program) ⟨back⟩ := by
  refine ⟨handlerOnly_map _ h.1, fun state cursor next rest htakes hreads => ?_⟩
  obtain ⟨calls, hcalls⟩ := handler_run h.1
  rw [closed_outcome, h.2 state cursor next rest htakes hreads, hcalls, ExceptT.run_map, hcalls]
  simp only [Functor.map_map]
  refine congrArg (· <$> calls.run) (funext fun e => ?_)
  rcases e with error | result <;> simp [answer, closedF, Except.map]

private theorem closed_rejects_of {version : Version} {pair : PairParser H P CloseParenParser}
    {tokens : List Parser.Internal.Input} {program : PM H Unit} {kind : SyntaxErrorKind}
    (h : Outcome.Rejects version pair tokens program kind) :
    Outcome.Rejects version (⟨pair⟩ : ClosedParser H P) tokens program kind := by
  refine ⟨h.1, fun state cursor next rest htakes hreads => ?_⟩
  obtain ⟨calls, hcalls⟩ := handler_run h.1
  rw [closed_outcome, h.2 state cursor next rest htakes hreads, hcalls]
  simp only [Functor.map_map]
  refine congrArg (· <$> calls.run) (funext fun e => ?_)
  rcases e with error | ⟨⟩ <;> simp [answer, closedF]

private theorem closed_waits_of {version : Version} {pair : PairParser H P CloseParenParser}
    {tokens : List Parser.Internal.Input} {α : Type} {program : PM H α}
    {after : α → PairParser H P CloseParenParser}
    (h : Outcome.Waits version pair tokens program after) :
    Outcome.Waits version (⟨pair⟩ : ClosedParser H P) tokens program fun a => ⟨after a⟩ := by
  refine ⟨h.1, fun state cursor last htakes hnone => ?_⟩
  obtain ⟨calls, hcalls⟩ := handler_run h.1
  rw [closed_outcome, h.2 state cursor last htakes hnone, hcalls]
  simp only [Functor.map_map]
  refine congrArg (· <$> calls.run) (funext fun e => ?_)
  rcases e with error | a <;> simp [answer, closedF]

private theorem opened_finishes_of {version : Version}
    {pair back : PairParser H OpenParenParser P}
    {tokens : List Parser.Internal.Input} {program : PM H (Unit × R)}
    (h : Outcome.Finishes version pair tokens program back) :
    Outcome.Finishes version (⟨pair⟩ : OpenedParser H P) tokens ((·.2) <$> program) ⟨back⟩ := by
  refine ⟨handlerOnly_map _ h.1, fun state cursor next rest htakes hreads => ?_⟩
  obtain ⟨calls, hcalls⟩ := handler_run h.1
  rw [opened_outcome, h.2 state cursor next rest htakes hreads, hcalls, ExceptT.run_map, hcalls]
  simp only [Functor.map_map]
  refine congrArg (· <$> calls.run) (funext fun e => ?_)
  rcases e with error | result <;> simp [answer, openedF, Except.map]

private theorem opened_rejects_of {version : Version} {pair : PairParser H OpenParenParser P}
    {tokens : List Parser.Internal.Input} {program : PM H Unit} {kind : SyntaxErrorKind}
    (h : Outcome.Rejects version pair tokens program kind) :
    Outcome.Rejects version (⟨pair⟩ : OpenedParser H P) tokens program kind := by
  refine ⟨h.1, fun state cursor next rest htakes hreads => ?_⟩
  obtain ⟨calls, hcalls⟩ := handler_run h.1
  rw [opened_outcome, h.2 state cursor next rest htakes hreads, hcalls]
  simp only [Functor.map_map]
  refine congrArg (· <$> calls.run) (funext fun e => ?_)
  rcases e with error | ⟨⟩ <;> simp [answer, openedF]

private theorem opened_waits_of {version : Version} {pair : PairParser H OpenParenParser P}
    {tokens : List Parser.Internal.Input} {α : Type} {program : PM H α}
    {after : α → PairParser H OpenParenParser P}
    (h : Outcome.Waits version pair tokens program after) :
    Outcome.Waits version (⟨pair⟩ : OpenedParser H P) tokens program fun a => ⟨after a⟩ := by
  refine ⟨h.1, fun state cursor last htakes hnone => ?_⟩
  obtain ⟨calls, hcalls⟩ := handler_run h.1
  rw [opened_outcome, h.2 state cursor last htakes hnone, hcalls]
  simp only [Functor.map_map]
  refine congrArg (· <$> calls.run) (funext fun e => ?_)
  rcases e with error | a <;> simp [answer, openedF]

/-- The closed parser on the inner value and the `)` after it. -/
theorem closed_parses {version : Version} {p b : P} {tokens : List Parser.Internal.Input}
    {program : PM H R} (h : Outcome.Finishes version p tokens program b) (hne : tokens ≠ []) :
    Outcome.Finishes version (ClosedParser.new (H := H) p) (tokens ++ [.parenClose]) program
      (ClosedParser.new b) := by
  have := closed_finishes_of (pair_parses h (closeParen_parses (H := H) version) hne
    (List.cons_ne_nil _ _))
  simp only [bind_pure_comp, map_pure, Functor.map_map] at this
  simpa [ClosedParser.new] using this

/-- The closed parser rejects where its inner parser rejects. -/
theorem closed_rejects_inner {version : Version} {p : P} {tokens : List Parser.Internal.Input}
    {program : PM H Unit} {kind : SyntaxErrorKind}
    (h : Outcome.Rejects version p tokens program kind) (hne : tokens ≠ []) :
    Outcome.Rejects version (ClosedParser.new (H := H) p) tokens program kind :=
  closed_rejects_of (pair_rejects_first h hne)

/-- The closed parser on the inner value and a token after it that is not `)`. -/
theorem closed_rejects_close {version : Version} {p b : P}
    {tokens : List Parser.Internal.Input} {program : PM H R} {token : Parser.Internal.Input}
    (h : Outcome.Finishes version p tokens program b) (hne : tokens ≠ [])
    (htoken : token ≠ .parenClose) :
    Outcome.Rejects version (ClosedParser.new (H := H) p) (tokens ++ [token])
      (do let _ ← program; pure ()) (.expected #[.token .parenClose]) :=
  closed_rejects_of (pair_rejects_second h (closeParen_rejects (H := H) version htoken) hne
    (List.cons_ne_nil _ _))

/-- The closed parser, when its inner parser continues on the tokens of the cursor. -/
theorem closed_waits_inner {version : Version} {p : P} {tokens : List Parser.Internal.Input}
    {α : Type} {program : PM H α} {after : α → P}
    (h : Outcome.Waits version p tokens program after) :
    Outcome.Waits version (ClosedParser.new (H := H) p) tokens program
      fun a => ClosedParser.new (after a) :=
  closed_waits_of (pair_waits_first h)

/-- When the cursor holds exactly the tokens of its inner value, the closed parser continues, as
a parser that finishes at a `)` and rejects any other token. -/
theorem closed_waits_close {version : Version} {p b : P}
    {tokens : List Parser.Internal.Input} {program : PM H R}
    (h : Outcome.Finishes version p tokens program b) (hne : tokens ≠ []) :
    ∃ after : R → ClosedParser H P,
      Outcome.Waits version (ClosedParser.new (H := H) p) tokens program after ∧
      (∀ result, Outcome.Finishes version (after result) [.parenClose]
        (pure result : PM H R) (ClosedParser.new b)) ∧
      (∀ result {token : Parser.Internal.Input}, token ≠ .parenClose →
        Outcome.Rejects version (after result) [token] (pure () : PM H Unit)
          (.expected #[.token .parenClose])) := by
  obtain ⟨after, hwaits, hfin, hrej⟩ := pair_waits_between (p₂ := CloseParenParser.new) h hne
  refine ⟨fun r => ⟨after r⟩, closed_waits_of hwaits, fun r => ?_, fun r _ ht =>
    closed_rejects_of (hrej r (closeParen_rejects version ht))⟩
  have := closed_finishes_of (hfin r (closeParen_parses (H := H) version))
  simpa [ClosedParser.new] using this

/-- The opened parser on a `(` and the inner value. -/
theorem opened_parses {version : Version} {p b : P} {tokens : List Parser.Internal.Input}
    {program : PM H R} (h : Outcome.Finishes version p tokens program b) (hne : tokens ≠ []) :
    Outcome.Finishes version (OpenedParser.new (H := H) p) (.parenOpen :: tokens) program
      (OpenedParser.new b) := by
  have := opened_finishes_of (pair_parses (openParen_parses (H := H) version) h
    (List.cons_ne_nil _ _) hne)
  simp only [bind_pure_comp, Functor.map_map, pure_bind] at this
  simpa [OpenedParser.new] using this

/-- The opened parser on a first token that is not `(`. -/
theorem opened_rejects_open {version : Version} {p : P} {token : Parser.Internal.Input}
    (htoken : token ≠ .parenOpen) :
    Outcome.Rejects version (OpenedParser.new (H := H) p) [token] (pure () : PM H Unit)
      (.expected #[.token .parenOpen]) :=
  opened_rejects_of (pair_rejects_first (openParen_rejects version htoken) (List.cons_ne_nil _ _))

/-- The opened parser rejects where its inner parser rejects after the `(`. -/
theorem opened_rejects_inner {version : Version} {p : P}
    {tokens : List Parser.Internal.Input} {program : PM H Unit} {kind : SyntaxErrorKind}
    (h : Outcome.Rejects version p tokens program kind) (hne : tokens ≠ []) :
    Outcome.Rejects version (OpenedParser.new (H := H) p) (.parenOpen :: tokens) program kind := by
  have := opened_rejects_of (pair_rejects_second (openParen_parses (H := H) version) h
    (List.cons_ne_nil _ _) hne)
  simpa [OpenedParser.new] using this

/-- The opened parser on a cursor with no token: it continues, as it was. -/
theorem opened_waits_open {version : Version} {p : P} :
    Outcome.Waits version (OpenedParser.new (H := H) p) [] (pure () : PM H Unit)
      fun _ => OpenedParser.new p :=
  opened_waits_of (pair_waits_first (openParen_waits (H := H) version))

/-- When the cursor holds exactly its `(`, the opened parser continues, as a parser that finishes
and rejects on the inner tokens as the inner parser. -/
theorem opened_waits_after_open {version : Version} {p : P} :
    ∃ after : Unit → OpenedParser H P,
      Outcome.Waits version (OpenedParser.new (H := H) p) [.parenOpen] (pure () : PM H Unit)
        after ∧
      (∀ {tokens : List Parser.Internal.Input} {program : PM H R} {b : P},
        Outcome.Finishes version p tokens program b →
        Outcome.Finishes version (after ()) tokens program (OpenedParser.new b)) ∧
      (∀ {tokens : List Parser.Internal.Input} {program : PM H Unit} {kind : SyntaxErrorKind},
        Outcome.Rejects version p tokens program kind →
        Outcome.Rejects version (after ()) tokens program kind) := by
  obtain ⟨after, hwaits, hfin, hrej⟩ := pair_waits_between (p₂ := p)
    (openParen_parses (H := H) version) (List.cons_ne_nil _ _)
  refine ⟨fun u => ⟨after u⟩, opened_waits_of hwaits, fun h => ?_, fun h =>
    opened_rejects_of (hrej () h)⟩
  have := opened_finishes_of (hfin () h)
  simpa [OpenedParser.new] using this

/-- The opened parser, when the cursor holds a `(` and its inner parser continues on the tokens
after it. -/
theorem opened_waits_inner {version : Version} {p : P} {tokens : List Parser.Internal.Input}
    {α : Type} {program : PM H α} {after : α → P}
    (h : Outcome.Waits version p tokens program after) (hne : tokens ≠ []) :
    ∃ after' : α → OpenedParser H P,
      Outcome.Waits version (OpenedParser.new (H := H) p) (.parenOpen :: tokens) program after' ∧
      (∀ a {tokens' : List Parser.Internal.Input} {program' : PM H R} {b : P},
        Outcome.Finishes version (after a) tokens' program' b →
        Outcome.Finishes version (after' a) tokens' program' (OpenedParser.new b)) ∧
      (∀ a {tokens' : List Parser.Internal.Input} {program' : PM H Unit}
        {kind : SyntaxErrorKind}, Outcome.Rejects version (after a) tokens' program' kind →
        Outcome.Rejects version (after' a) tokens' program' kind) := by
  obtain ⟨after₂, hwaits, hfin, hrej⟩ := pair_waits_second
    (openParen_parses (H := H) version) h (List.cons_ne_nil _ _) hne
  refine ⟨fun a => ⟨after₂ ((), a)⟩, ?_, fun a _ _ _ h' => ?_, fun a _ _ _ h' =>
    opened_rejects_of (hrej () a h')⟩
  · have := opened_waits_of hwaits
    simp only [pure_bind, bind_pure_comp] at this
    exact waits_of_map (f := Prod.mk ()) (after := fun x => (⟨after₂ x⟩ : OpenedParser H P))
      (by simpa [OpenedParser.new] using this) h.1
  · have := opened_finishes_of (hfin () a h')
    simpa [OpenedParser.new] using this

end

/-! ## Parsers that wrap another one -/

section

variable {H Q W R : Type} {m : Type → Type} [Monad m] [LawfulMonad m] [Handler H m]
  [Parse Q H m (Handler.Error H) R] [Parse W H m (Handler.Error H) R]

/-- The answer of a parser that wraps another one, from the inner parser's answer: the inner
parser it gives back is wrapped. -/
def wrapF (wrap : Q → W) {Z : Type} :
    Outcome R Q Z (Handler.Error H) → Outcome R W Z (Handler.Error H)
  | .finished result inner next => .finished result (wrap inner) next
  | .waits inner => .waits (wrap inner)
  | .rejected kind next => .rejected kind next
  | .rejectedVersion kind next => .rejectedVersion kind next
  | .failed error => .failed error

/-- The parsers that `wrap` makes answer as the parser they wrap, with that parser wrapped. -/
def Wraps (wrap : Q → W) : Prop :=
  ∀ (inner : Q) {Z : Type} [Cursor Z] (state : ParseState H) (cursor : Z),
    outcome <$> Parse.parse (wrap inner) state cursor =
      wrapF (H := H) wrap <$> (outcome <$> Parse.parse inner state cursor)

/-- A wrapped parser finishes where the parser it wraps does. -/
theorem wraps_finishes {wrap : Q → W} (hw : Wraps (H := H) wrap) {version : Version}
    {inner back : Q} {tokens : List Parser.Internal.Input} {program : PM H R}
    (h : Outcome.Finishes version inner tokens program back) :
    Outcome.Finishes version (wrap inner) tokens program (wrap back) := by
  refine ⟨h.1, fun state cursor next rest htakes hreads => ?_⟩
  obtain ⟨calls, hcalls⟩ := handler_run h.1
  rw [hw, h.2 state cursor next rest htakes hreads, hcalls]
  simp only [Functor.map_map]
  refine congrArg (· <$> calls.run) (funext fun e => ?_)
  rcases e with error | result <;> simp [answer, wrapF]

/-- A wrapped parser rejects where the parser it wraps does. -/
theorem wraps_rejects {wrap : Q → W} (hw : Wraps (H := H) wrap) {version : Version} {inner : Q}
    {tokens : List Parser.Internal.Input} {program : PM H Unit} {kind : SyntaxErrorKind}
    (h : Outcome.Rejects version inner tokens program kind) :
    Outcome.Rejects version (wrap inner) tokens program kind := by
  refine ⟨h.1, fun state cursor next rest htakes hreads => ?_⟩
  obtain ⟨calls, hcalls⟩ := handler_run h.1
  rw [hw, h.2 state cursor next rest htakes hreads, hcalls]
  simp only [Functor.map_map]
  refine congrArg (· <$> calls.run) (funext fun e => ?_)
  rcases e with error | ⟨⟩ <;> simp [answer, wrapF]

/-- A wrapped parser waits where the parser it wraps does, as the wrap of what that parser
waits as. -/
theorem wraps_waits {wrap : Q → W} (hw : Wraps (H := H) wrap) {version : Version} {inner : Q}
    {tokens : List Parser.Internal.Input} {α : Type} {program : PM H α} {after : α → Q}
    (h : Outcome.Waits version inner tokens program after) :
    Outcome.Waits version (wrap inner) tokens program fun a => wrap (after a) := by
  refine ⟨h.1, fun state cursor last htakes hnone => ?_⟩
  obtain ⟨calls, hcalls⟩ := handler_run h.1
  rw [hw, h.2 state cursor last htakes hnone, hcalls]
  simp only [Functor.map_map]
  refine congrArg (· <$> calls.run) (funext fun e => ?_)
  rcases e with error | a <;> simp [answer, wrapF]

end

section

variable {H P R : Type} {m : Type → Type} [Monad m] [LawfulMonad m] [Handler H m]
  [Parse P H m (Handler.Error H) R]

/-- The parenthesised parser answers as the opened parser it wraps. -/
private theorem paren_wraps :
    Wraps (H := H) fun inner : OpenedParser H (ClosedParser H P) =>
      (⟨inner⟩ : ParenParser H P) := by
  intro inner Z _ state cursor
  rw [show Parse.parse (⟨inner⟩ : ParenParser H P) state cursor =
      Parse.parse inner state cursor >>= fun x =>
        pure (x.1, (⟨x.2.1⟩ : ParenParser H P), x.2.2.1, x.2.2.2) from rfl, map_bind,
    Functor.map_map, map_eq_pure_bind]
  refine bind_congr fun x => ?_
  obtain ⟨a, p, s, ⟨z, hz⟩⟩ := x
  rcases a with (_ | _) | (_ | _) <;> simp only [map_pure] <;> rfl

/-- The parenthesised parser on a `(`, the inner value and a `)`. -/
theorem paren_parses {version : Version} {p b : P} {tokens : List Parser.Internal.Input}
    {program : PM H R} (h : Outcome.Finishes version p tokens program b) (hne : tokens ≠ []) :
    Outcome.Finishes version (ParenParser.new (H := H) p)
      (.parenOpen :: (tokens ++ [.parenClose]))
      program (ParenParser.new b) :=
  wraps_finishes paren_wraps (opened_parses (closed_parses h hne) (by simp))

/-- The parenthesised parser on a first token that is not `(`. -/
theorem paren_rejects_open {version : Version} {p : P} {token : Parser.Internal.Input}
    (htoken : token ≠ .parenOpen) :
    Outcome.Rejects version (ParenParser.new (H := H) p)
      [token] (pure () : PM H Unit)
      (.expected #[.token .parenOpen]) :=
  wraps_rejects paren_wraps (opened_rejects_open htoken)

/-- The parenthesised parser rejects where its inner parser rejects after the `(`. -/
theorem paren_rejects_inner {version : Version} {p : P}
    {tokens : List Parser.Internal.Input} {program : PM H Unit} {kind : SyntaxErrorKind}
    (h : Outcome.Rejects version p tokens program kind) (hne : tokens ≠ []) :
    Outcome.Rejects version (ParenParser.new (H := H) p)
      (.parenOpen :: tokens) program kind :=
  wraps_rejects paren_wraps (opened_rejects_inner (closed_rejects_inner h hne) hne)

/-- The parenthesised parser on a `(`, the inner value and a token that is not `)`. -/
theorem paren_rejects_close {version : Version} {p b : P}
    {tokens : List Parser.Internal.Input} {program : PM H R} {token : Parser.Internal.Input}
    (h : Outcome.Finishes version p tokens program b) (hne : tokens ≠ [])
    (htoken : token ≠ .parenClose) :
    Outcome.Rejects version (ParenParser.new (H := H) p)
      (.parenOpen :: (tokens ++ [token]))
      (do let _ ← program; pure ()) (.expected #[.token .parenClose]) :=
  wraps_rejects paren_wraps (opened_rejects_inner (closed_rejects_close h hne htoken) (by simp))

end

end BSmtLib.Facts.Proofs.Parser.Category.Combinator
