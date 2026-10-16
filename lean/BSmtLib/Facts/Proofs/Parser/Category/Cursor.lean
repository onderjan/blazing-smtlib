module

public import BSmtLib.Facts.Proofs.Parser.Drive
import all BSmtLib.Parser

@[expose] public section

/-!
# A parser stepped by single tokens, on a cursor: the pieces

Cursors that give a list of tokens (`Takes`, `Reads`), the token points that mark nothing, and
the relation of a parser to its steps (`Simulates`): it is no more than a state of the steps, no
call is due at a token's arrival, it never acts on the cursor, and it goes back to its initial
state when it finishes. The loop over single tokens against those steps is in
`Category.CursorS`.
-/

namespace BSmtLib.Facts.Proofs.Parser.Category.Cursor

open BSmtLib.Token (Cursor)
open BSmtLib.Parser (Parse ParseErrorCause ParseState)
open BSmtLib.Parser.Internal (PM ParseByToken takeOne rest parseByToken After)
open BSmtLib.Facts.Parser.Adapters.Bridge BSmtLib.Facts.Parser.Adapters.Run
open BSmtLib.Facts.Parser.Adapters.Cursor
open BSmtLib.Facts.Proofs.Parser.Drive

/-! ## Cursors -/

section

variable {Z : Type} [Cursor Z] {version : Token.Version}

theorem Takes.cons_inv {cursor next : Z} {token : Parser.Internal.Input}
    {tokens : List Parser.Internal.Input} (h : Takes version cursor (token :: tokens) next) :
    ∃ (after : Z) (raw : Cursor.Token Z) (consumed : Cursor.Consumed after cursor),
      Cursor.HasNext cursor ∧ Cursor.next? cursor = some (raw, ⟨after, consumed⟩) ∧
      Cursor.version after = version ∧
      Parser.Internal.Input.ofSyntax (Cursor.syntax after raw) = token ∧
      Takes version after tokens next := by
  generalize hl : token :: tokens = l at h
  cases h with
  | nil => cases hl
  | cons hn hnext hver htail =>
    cases hl
    exact ⟨_, _, _, hn, hnext, hver, rfl, htail⟩

theorem Takes.nil_inv {cursor next : Z} (h : Takes version cursor [] next) : next = cursor := by
  generalize hl : ([] : List Parser.Internal.Input) = l at h
  cases h with
  | nil => rfl
  | cons => cases hl

theorem Takes.append {cursor middle next : Z} :
    {first second : List Parser.Internal.Input} → Takes version cursor first middle →
    Takes version middle second next → Takes version cursor (first ++ second) next
  | [], _, h₁, h₂ => by
    rw [Takes.nil_inv h₁] at h₂
    exact h₂
  | _ :: _, _, h₁, h₂ => by
    obtain ⟨_, _, _, hn, hnext, hver, rfl, htail⟩ := Takes.cons_inv h₁
    exact .cons hn hnext hver (Takes.append htail h₂)

theorem Takes.split {cursor next : Z} :
    {first second : List Parser.Internal.Input} → Takes version cursor (first ++ second) next →
    ∃ middle, Takes version cursor first middle ∧ Takes version middle second next
  | [], _, h => ⟨cursor, .nil cursor, h⟩
  | _ :: _, _, h => by
    obtain ⟨_, _, _, hn, hnext, hver, rfl, htail⟩ := Takes.cons_inv h
    obtain ⟨middle, h₁, h₂⟩ := Takes.split htail
    exact ⟨middle, .cons hn hnext hver h₁, h₂⟩

theorem Takes.consumed {cursor next : Z} :
    {token : Parser.Internal.Input} → {tokens : List Parser.Internal.Input} →
    Takes version cursor (token :: tokens) next → Cursor.Consumed next cursor
  | _, [], h => by
    obtain ⟨_, _, consumed, _, _, _, _, htail⟩ := Takes.cons_inv h
    rw [Takes.nil_inv htail]
    exact consumed
  | _, _ :: _, h => by
    obtain ⟨_, _, consumed, _, _, _, _, htail⟩ := Takes.cons_inv h
    exact Cursor.consumed_trans (Takes.consumed htail) consumed

theorem Takes.hasNext {cursor next : Z} {token : Parser.Internal.Input}
    {tokens : List Parser.Internal.Input} (h : Takes version cursor (token :: tokens) next) :
    Cursor.HasNext cursor := by
  obtain ⟨_, _, _, hn, _⟩ := Takes.cons_inv h
  exact hn

theorem Reads.of_takes {cursor next : Z} {first rest : List Parser.Internal.Input}
    (h₁ : Takes version cursor first next) (h₂ : Reads version next rest) :
    Reads version cursor (first ++ rest) := by
  obtain ⟨last, hlast, hnone⟩ := h₂
  exact ⟨last, Takes.append h₁ hlast, hnone⟩

/-- The cursor after taking `count` tokens, or fewer if it has fewer. -/
def advance : Nat → Z → Z
  | 0, cursor => cursor
  | count + 1, cursor =>
    match Cursor.next? cursor with
    | some (_, ⟨after, _⟩) => advance count after
    | none => cursor

theorem advance_succ {cursor after : Z} {raw : Cursor.Token Z}
    {consumed : Cursor.Consumed after cursor}
    (h : Cursor.next? cursor = some (raw, ⟨after, consumed⟩)) (count : Nat) :
    advance (count + 1) cursor = advance count after := by
  simp only [advance, h]

theorem advance_takes {cursor next : Z} :
    {tokens : List Parser.Internal.Input} → Takes version cursor tokens next →
    advance tokens.length cursor = next
  | [], h => (Takes.nil_inv h).symm
  | _ :: _, h => by
    obtain ⟨_, _, _, _, hnext, _, _, htail⟩ := Takes.cons_inv h
    rw [List.length_cons, advance_succ hnext]
    exact advance_takes htail

end

/-! ## The token points that mark nothing -/

section

variable {H : Type} {m : Type → Type} [Monad m] [LawfulMonad m] [Traits.Handler H m]

@[simp]
theorem tick_noPoints (token : Parser.Internal.Input) :
    tick (noPoints : BSmtLibSpec.Parser.Traversal.Points (StateT H m)) token = pure () := by
  cases h : Bridge.received token <;>
    simp [tick, arriveAt, processAt, h, noPoints, ExceptT.lift_pure]

end

/-! ## A parser and its steps -/

section

variable {H P R σ : Type} {m : Type → Type} [Monad m] [LawfulMonad m] [Traits.Handler H m]
variable [ParseByToken P H m (Traits.Handler.Error H) R]

/-- A step of the steps as the step of the parser. -/
def flowOf (mk : σ → P) : Parser.Internal.Step σ R → Parser.Internal.Flow (PM H) P R
  | .more state => .more (mk state)
  | .done result => .done result

/--
The parser in the version is the state `mk state` of the steps `step`: no call is due at a token's
arrival, a step of the parser is the step of its state, it goes back to `fresh` when it
finishes, and it hands no cursor over.
-/
structure Simulates (version : Token.Version) (mk : σ → P)
    (step : σ → Parser.Internal.Input → PM H (Parser.Internal.Step σ R)) (fresh : P) : Prop where
  arrive : ∀ (parser : P) (token : Parser.Internal.Input),
    ParseByToken.arrive parser token = (pure () : PM H Unit)
  step : ∀ (state : σ) (token : Parser.Internal.Input),
    ParseByToken.step version (mk state) token = flowOf mk <$> step state token
  reset : ∀ state : σ, ParseByToken.reset (mk state) = fresh
  handOver : ∀ {Z : Type} [Cursor Z] (state : σ) (cursor : Z),
    ParseByToken.handOver? (mk state) cursor = none

variable {version : Token.Version} {mk : σ → P}
  {step : σ → Parser.Internal.Input → PM H (Parser.Internal.Step σ R)} {fresh : P}

/-- What the loop does with what a step gave. -/
def afterOf (mk : σ → P) (fresh : P) :
    Except (ParseErrorCause (Traits.Handler.Error H)) (Parser.Internal.Step σ R) → After P R
      (Traits.Handler.Error H)
  | .error error => .stop (.error (Parser.ParseError.Internal.new error)) fresh
  | .ok (.more state) => .goOn (mk state)
  | .ok (.done result) => .stop (.ok (.break result)) fresh

variable {Z : Type} [Cursor Z]

theorem takeOne_sim (sim : Simulates version mk step fresh) (state : σ) (cursor : Z)
    (raw : Cursor.Token Z) (after : Z) (consumed : Cursor.Consumed after cursor)
    (hver : Cursor.version after = version) :
    takeOne (mk state) cursor raw after consumed =
      (fun e => (afterOf mk fresh e, (⟨after, consumed⟩ : { z : Z // Cursor.Consumed z cursor })))
        <$> (step state (Parser.Internal.Input.ofSyntax (Cursor.syntax after raw))).run := by
  unfold takeOne
  simp only [hver, sim.reset, sim.arrive, sim.step, pure_bind, map_eq_pure_bind,
    ExceptT.run_bind, bind_assoc]
  apply bind_congr
  intro e
  rcases e with error | st
  · simp only [pure_bind]
    rfl
  · cases st <;> simp [flowOf, afterOf]

/-! ## Steps that only move the parser -/

/-- The steps take the tokens, each only moving the parser to another state, from `state` to
`state'`. -/
inductive Moves (step : σ → Parser.Internal.Input → PM H (Parser.Internal.Step σ R)) :
    σ → List Parser.Internal.Input → σ → Prop where
  | nil (state : σ) : Moves step state [] state
  | cons {state middle last : σ} {token : Parser.Internal.Input}
      {tokens : List Parser.Internal.Input} :
      step state token = pure (.more middle) → Moves step middle tokens last →
      Moves step state (token :: tokens) last

end

end BSmtLib.Facts.Proofs.Parser.Category.Cursor
