import BSmtLib.Proofs.Simulation
import BSmtLib.Proofs.Adapter

/-!
# The library's lexer on a slice too large for its positions

The library's lexer lexes a slice whose end is not below `USize.size` chunk by chunk
(`Internal.lexChunks`): it copies each chunk into an array of its own and lexes it as a slice.
This module proves, of the library's lexer alone, that it hands over for such a slice what it
hands over for the chunks given one after another as slices of their own, as the adapter feeds
them (`feed_cut`), and so for every list of slices what it hands over for the list with each
too-large slice cut into its chunks (`handed_cutAll`); the chunks are not too large, and the cut
list has the same bytes (`flatten_cutAll`, `mem_cutAll`).

The two runs differ in the checks that `lexSliceStep` makes before each slice: whether the lexer
discards and whether it recovers. For the chunks given as slices these are made before every
chunk, for the large slice once. They agree as long as the lexer neither discards nor recovers
(`Inv`), which the lexing of a chunk keeps: no step below `lexSliceStep` reads or writes the two
fields. This is shown as a simulation of the lexer by itself under the map that sets the two
fields (`ρ`): every step commutes with it (`Nat'`, `INat`), step by step through the whole
lexer, with a tactic that takes the steps of code that is the same on both sides.
-/

namespace BSmtLib.Proofs.X2ContentsLexer.Chunks

open BSmtLib.Proofs.Simulation
open BSmtLib.Lexer (LexerCore Interrupted RecoveryState)
open BSmtLib.Lexer.Internal

/-- The lexer state with the two fields set. -/
def ρ (d : Bool) (r : Option RecoveryState) (c : LexerCore) : LexerCore :=
  { c with discard := d, recoveryState := r }

/-- The bounded lexer state with the two fields set. -/
def ρB (d : Bool) (r : Option RecoveryState) {floor : Option Nat} {low : Nat}
    (c : {c : LexerCore // c.Bound floor low}) : {c : LexerCore // c.Bound floor low} :=
  ⟨ρ d r c.val, c.property⟩

theorem Sim.dite {m : Type → Type} [Monad m] {H ε : Type} {S T α β : Type} {φ : S → T}
    {ψ : α → β} {c c' : Prop} [Decidable c]
    [Decidable c'] (e : c ↔ c') {f₁ : c → M m H ε S α} {f₂ : ¬c → M m H ε S α}
    {g₁ : c' → M m H ε T β} {g₂ : ¬c' → M m H ε T β}
    (h₁ : ∀ hc hc', Sim φ ψ (f₁ hc) (g₁ hc'))
    (h₂ : ∀ hc hc', Sim φ ψ (f₂ hc) (g₂ hc')) :
    Sim φ ψ (if hc : c then f₁ hc else f₂ hc) (if hc' : c' then g₁ hc' else g₂ hc') := by
  by_cases hc : c
  · simp only [hc, dite_true, e.mp hc]; exact h₁ hc (e.mp hc)
  · have : ¬c' := fun h => hc (e.mpr h)
    simp only [hc, dite_false, this]; exact h₂ hc this

/-- `Sim.bind` for a first step whose result is not mapped. -/
theorem Sim.bindId {m : Type → Type} [Monad m] [LawfulMonad m] {H ε : Type} {S T α γ δ : Type}
    {φ : S → T} {χ : γ → δ} {f : M m H ε S α} {g : M m H ε T α} {k : α → M m H ε S γ}
    {k' : α → M m H ε T δ} (hf : Sim φ id f g) (hk : ∀ a, Sim φ χ (k a) (k' a)) :
    Sim φ χ (f >>= k) (g >>= k') :=
  Simulation.Sim.bind hf hk

/-- Applies a lemma that a step commutes with setting the two fields; extended below. -/
syntax "nat_lemma" : tactic

set_option hygiene false in
/-- Takes the steps of code that is the same on both sides. -/
macro "nat_step" : tactic => `(tactic| (first
    | ((with_reducible refine Sim.pure ?_); rfl)
    | (with_reducible exact Sim.throw _)
    | (with_reducible refine Sim.bind (Sim.throw (ψ := id) _) fun _ => ?_)
    | ((with_reducible refine Sim.bind (getCore_nat _ _) fun _ => ?_)
       try dsimp -zeta only [ρ, BSmtLib.Lexer.LexerCore.locationAt,
         BSmtLib.Lexer.LexerCore.offsetAt])
    | (unfold modifyCore)
    | (unfold modifyBound)
    | ((with_reducible refine Sim.modify ?_); intro _; rfl)
    | ((with_reducible refine Sim.bindId (Sim.modify ?_) fun _ => ?_); intro _; rfl)
    | nat_lemma
    | ((with_reducible refine Sim.bindId ?_ fun _ => ?_); nat_lemma)
    | (with_reducible refine Sim.ite Iff.rfl (fun _ => ?_) fun _ => ?_)
    | (with_reducible refine Sim.dite Iff.rfl (fun _ _ => ?_) fun _ _ => ?_)
    | (with_reducible refine Sim.bindId ?_ fun _ => ?_)
    | split
    | (dsimp only)
    | (with_reducible assumption)))

/-- Takes the steps of code that is the same on both sides. -/
macro "nat_auto" : tactic => `(tactic| repeat' nat_step)

/-- Closes what the hypothesis of the functional induction leaves: a fact of the context, a
location that the hypothesis does not use, or arithmetic. -/
macro "nat_close" : tactic => `(tactic| first
    | assumption
    | exact BSmtLib.Location.initial
    | (simp +zetaDelta only at *; omega))

set_option hygiene false in
/-- Closes a recursive call by the hypothesis of the functional induction. -/
macro "nat_ih" : tactic => `(tactic| (expose_names; first
    | (apply ih1 <;> nat_close)
    | (apply ih2 <;> nat_close)
    | (apply ih1 ⟨_, ?_⟩ <;> nat_close)
    | (apply ih2 ⟨_, ?_⟩ <;> nat_close)))

section
variable {H : Type} {m : Type → Type} {R E : Type} [Monad m] [LawfulMonad m]
  [BSmtLib.Consume H m R E] {floor : Option Nat} {low : Nat} (d : Bool) (r : Option RecoveryState)

/-- A step that commutes with setting the two fields. -/
abbrev Nat' {α : Type} (f : BSmtLib.Lexer.LexM H m R E floor low α) : Prop :=
  Sim (ρB d r) id f f

omit [BSmtLib.Consume H m R E] in
theorem getCore_nat : Sim (ρB d r) (ρ d r)
    (getCore (H := H) (m := m) (R := R) (E := E) (floor := floor) (low := low)) getCore := by
  unfold getCore
  exact Sim.bind Sim.get fun a => Sim.pure rfl

omit [BSmtLib.Consume H m R E] in
theorem modifyCore_nat (f : LexerCore → LexerCore)
    (hf : ∀ c, c.Bound floor low → (f c).Bound floor low)
    (e : ∀ c, f (ρ d r c) = ρ d r (f c)) :
    Nat' (H := H) (m := m) (R := R) (E := E) d r (modifyCore f hf) := by
  unfold modifyCore
  exact Sim.modify fun s => Subtype.ext (e s.val)

omit [BSmtLib.Consume H m R E] in
theorem modifyBound_nat
    (f : (c : LexerCore) → c.Bound floor low → {c' : LexerCore // c'.Bound floor low})
    (e : ∀ c hc, (f (ρ d r c) hc).val = ρ d r (f c hc).val) :
    Nat' (H := H) (m := m) (R := R) (E := E) d r (modifyBound f) := by
  unfold modifyBound
  exact Sim.modify fun s => Subtype.ext (e s.val s.property)

theorem flushCursor_nat : ∀ n (cursor : BatchCursor), cursor.remaining = n → ∀ hfloor,
    Nat' (H := H) (m := m) (R := R) (E := E) (low := low) d r
      (flushCursor (floor := floor) cursor hfloor) := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
  intro cursor hn hfloor
  rw [flushCursor]
  split
  · refine Sim.bind (ψ := id) ?_ fun x => ?_
    · unfold callConsumer
      exact Sim.lift fun _ => by simp
    obtain ⟨result, next, consumed⟩ := x
    dsimp only [id]
    split
    · split
      · exact Sim.pure rfl
      · exact ih _ (by rw [← hn, BatchCursor.remaining_resetConsumed]; exact consumed.remaining_lt)
          _ rfl _
    · exact Sim.pure rfl
    · exact Sim.pure rfl
  · exact Sim.pure rfl

macro_rules | `(tactic| nat_lemma) => `(tactic| with_reducible exact flushCursor_nat _ _ _ _ rfl _)

omit [BSmtLib.Consume H m R E] in
theorem takeBatch_nat : Nat' (H := H) (m := m) (R := R) (E := E) (floor := floor) (low := low) d r
    takeBatch := by
  unfold takeBatch
  exact Sim.modifyGet fun _ => rfl

macro_rules | `(tactic| nat_lemma) => `(tactic| with_reducible exact takeBatch_nat _ _)

theorem handOver_nat (batch : TokenBatch) (bytesAfter : ByteArray) (hfloor) :
    Nat' (H := H) (m := m) (R := R) (E := E) (floor := floor) (low := low) d r
      (handOver batch bytesAfter hfloor) := by
  unfold handOver storeSpent
  nat_auto

macro_rules | `(tactic| nat_lemma) => `(tactic| with_reducible apply handOver_nat)

omit [BSmtLib.Consume H m R E] in
theorem setNormal_nat : Nat' (H := H) (m := m) (R := R) (E := E) (floor := floor) (low := low) d r
    setNormal := by
  unfold setNormal; nat_auto

macro_rules | `(tactic| nat_lemma) => `(tactic| with_reducible apply setNormal_nat)

omit [BSmtLib.Consume H m R E] in
theorem setTokenState_nat (state start h) :
    Nat' (H := H) (m := m) (R := R) (E := E) (floor := floor) (low := low) d r
      (setTokenState state start h) := by
  unfold setTokenState; nat_auto

macro_rules | `(tactic| nat_lemma) => `(tactic| with_reducible apply setTokenState_nat)

theorem consumes_nat :
    Nat' (H := H) (m := m) (R := R) (E := E) (floor := floor) (low := low) d r
      consumesWhitespaceAndComments := by
  unfold consumesWhitespaceAndComments; nat_auto

macro_rules | `(tactic| nat_lemma) => `(tactic| with_reducible apply consumes_nat)

omit [BSmtLib.Consume H m R E] in
theorem modifyContent_nat (f) :
    Nat' (H := H) (m := m) (R := R) (E := E) (floor := floor) (low := low) d r
      (modifyContent f) := by
  unfold modifyContent; nat_auto

macro_rules | `(tactic| nat_lemma) => `(tactic| with_reducible apply modifyContent_nat)

omit [BSmtLib.Consume H m R E] in
theorem extendContent_nat (input start stop) :
    Nat' (H := H) (m := m) (R := R) (E := E) (floor := floor) (low := low) d r
      (extendContent input start stop) := by
  unfold extendContent; nat_auto

macro_rules | `(tactic| nat_lemma) => `(tactic| with_reducible apply extendContent_nat)

omit [BSmtLib.Consume H m R E] in
theorem pushContent_nat (c) :
    Nat' (H := H) (m := m) (R := R) (E := E) (floor := floor) (low := low) d r
      (pushContent c) := by
  unfold pushContent; nat_auto

macro_rules | `(tactic| nat_lemma) => `(tactic| with_reducible apply pushContent_nat)

omit [BSmtLib.Consume H m R E] in
theorem startToken_nat (offset base position hframe) :
    Nat' (H := H) (m := m) (R := R) (E := E) (floor := floor) (low := low) d r
      (startToken offset base position hframe) := by
  unfold startToken; nat_auto

macro_rules | `(tactic| nat_lemma) => `(tactic| with_reducible apply startToken_nat)

omit [BSmtLib.Consume H m R E] in
theorem markLineFeedAt_nat (position) :
    Nat' (H := H) (m := m) (R := R) (E := E) (floor := floor) (low := low) d r
      (markLineFeedAt position) := by
  unfold markLineFeedAt; nat_auto

macro_rules | `(tactic| nat_lemma) => `(tactic| with_reducible apply markLineFeedAt_nat)

omit [BSmtLib.Consume H m R E] in
theorem failWith_nat {α : Type} (kind position failure) :
    Nat' (H := H) (m := m) (R := R) (E := E) (floor := floor) (low := low) (α := α) d r
      (failWith kind position failure) := by
  unfold failWith; nat_auto

macro_rules | `(tactic| nat_lemma) => `(tactic| with_reducible apply failWith_nat)

omit [BSmtLib.Consume H m R E] in
theorem failAt_nat {α : Type} (kind position) :
    Nat' (H := H) (m := m) (R := R) (E := E) (floor := floor) (low := low) (α := α) d r
      (failAt kind position) := by
  unfold failAt; nat_auto

macro_rules | `(tactic| nat_lemma) => `(tactic| with_reducible apply failAt_nat)

omit [BSmtLib.Consume H m R E] in
theorem fail_nat {α : Type} (kind te) :
    Nat' (H := H) (m := m) (R := R) (E := E) (floor := floor) (low := low) (α := α) d r
      (fail kind te) := by
  unfold fail; nat_auto

macro_rules | `(tactic| nat_lemma) => `(tactic| with_reducible apply fail_nat)

omit [BSmtLib.Consume H m R E] in
theorem expectDelimiter_nat (next position) :
    Nat' (H := H) (m := m) (R := R) (E := E) (floor := floor) (low := low) d r
      (expectDelimiter next position) := by
  unfold expectDelimiter; nat_auto

macro_rules | `(tactic| nat_lemma) => `(tactic| with_reducible apply expectDelimiter_nat)

omit [BSmtLib.Consume H m R E] in
theorem storeSpent_nat (spent) :
    Nat' (H := H) (m := m) (R := R) (E := E) (floor := floor) (low := low) d r
      (storeSpent spent) := by
  unfold storeSpent; nat_auto

macro_rules | `(tactic| nat_lemma) => `(tactic| with_reducible apply storeSpent_nat)

theorem flushBatch_nat :
    Nat' (H := H) (m := m) (R := R) (E := E) (floor := floor) (low := low) d r
      flushBatch := by
  unfold flushBatch; nat_auto

macro_rules | `(tactic| nat_lemma) => `(tactic| with_reducible apply flushBatch_nat)

theorem handOverStored_nat (ty hty s e hend hfloor) :
    Nat' (H := H) (m := m) (R := R) (E := E) (floor := floor) (low := low) d r
      (handOverStored ty hty s e hend hfloor) := by
  unfold handOverStored; nat_auto

macro_rules | `(tactic| nat_lemma) => `(tactic| with_reducible apply handOverStored_nat)

omit [BSmtLib.Consume H m R E] in
theorem locationFrom_nat (base position) :
    Nat' (H := H) (m := m) (R := R) (E := E) (floor := floor) (low := low) d r
      (locationFrom base position) := by
  unfold locationFrom; nat_auto

macro_rules | `(tactic| nat_lemma) => `(tactic| with_reducible apply locationFrom_nat)

theorem sinkStored_nat (ty hty te s base h) :
    Nat' (H := H) (m := m) (R := R) (E := E) (floor := floor) (low := low) d r
      (sinkStored ty hty te s base h) := by
  unfold sinkStored; nat_auto

macro_rules | `(tactic| nat_lemma) => `(tactic| with_reducible apply sinkStored_nat)

theorem finishDecimal_nat (te next s base h) :
    Nat' (H := H) (m := m) (R := R) (E := E) (floor := floor) (low := low) d r
      (finishDecimal te next s base h) := by
  unfold finishDecimal; nat_auto

theorem finishNumeral_nat (te s base h) :
    Nat' (H := H) (m := m) (R := R) (E := E) (floor := floor) (low := low) d r
      (finishNumeral te s base h) := by
  unfold finishNumeral; nat_auto

theorem finishDigitRun_nat (run hrun te next s base h) :
    Nat' (H := H) (m := m) (R := R) (E := E) (floor := floor) (low := low) d r
      (finishDigitRun run hrun te next s base h) := by
  unfold finishDigitRun; nat_auto

theorem finishSimpleSymbol_nat (te s base h) :
    Nat' (H := H) (m := m) (R := R) (E := E) (floor := floor) (low := low) d r
      (finishSimpleSymbol te s base h) := by
  unfold finishSimpleSymbol; nat_auto

theorem finishKeyword_nat (te next s base h) :
    Nat' (H := H) (m := m) (R := R) (E := E) (floor := floor) (low := low) d r
      (finishKeyword te next s base h) := by
  unfold finishKeyword; nat_auto

theorem finishStringLiteral_nat (te s base h) :
    Nat' (H := H) (m := m) (R := R) (E := E) (floor := floor) (low := low) d r
      (finishStringLiteral te s base h) := by
  unfold finishStringLiteral; nat_auto

theorem finishWhitespace_nat (te s base h) :
    Nat' (H := H) (m := m) (R := R) (E := E) (floor := floor) (low := low) d r
      (finishWhitespace te s base h) := by
  unfold finishWhitespace; nat_auto

macro_rules | `(tactic| nat_lemma) => `(tactic| with_reducible apply finishDecimal_nat)
macro_rules | `(tactic| nat_lemma) => `(tactic| with_reducible apply finishNumeral_nat)
macro_rules | `(tactic| nat_lemma) => `(tactic| with_reducible apply finishDigitRun_nat)
macro_rules | `(tactic| nat_lemma) => `(tactic| with_reducible apply finishSimpleSymbol_nat)
macro_rules | `(tactic| nat_lemma) => `(tactic| with_reducible apply finishKeyword_nat)
macro_rules | `(tactic| nat_lemma) => `(tactic| with_reducible apply finishStringLiteral_nat)
macro_rules | `(tactic| nat_lemma) => `(tactic| with_reducible apply finishWhitespace_nat)

omit [BSmtLib.Consume H m R E] in
theorem leave_nat (offset base position batch hframe hbatch) :
    Nat' (H := H) (m := m) (R := R) (E := E) (floor := floor) (low := low) d r
      (leave offset base position batch hframe hbatch) := by
  unfold leave; nat_auto

omit [BSmtLib.Consume H m R E] in
theorem leavePending_nat (state s offset base position batch hframe hbatch hstart hfloor) :
    Nat' (H := H) (m := m) (R := R) (E := E) (floor := floor) (low := low) d r
      (leavePending state s offset base position batch hframe hbatch hstart hfloor) := by
  unfold leavePending; nat_auto

macro_rules | `(tactic| nat_lemma) => `(tactic| with_reducible apply leave_nat)
macro_rules | `(tactic| nat_lemma) => `(tactic| with_reducible apply leavePending_nat)

theorem flushHeld_nat (batch origin hbatch) :
    Nat' (H := H) (m := m) (R := R) (E := E) (floor := floor) (low := low) d r
      (flushHeld batch origin hbatch) := by
  unfold flushHeld; nat_auto

macro_rules | `(tactic| nat_lemma) => `(tactic| with_reducible apply flushHeld_nat)

theorem pushFast_nat (batch offset base ty cs ce s e emit hty hstart hend hframe hbatch) :
    Nat' (H := H) (m := m) (R := R) (E := E) (floor := floor) (low := low) d r
      (pushFast batch offset base ty cs ce s e emit hty hstart hend hframe hbatch) := by
  unfold pushFast; nat_auto

theorem pushBorrowed_nat (batch offset base ty cs ce s te hty hafter hend hfloor) :
    Nat' (H := H) (m := m) (R := R) (E := E) (floor := floor) (low := low) d r
      (pushBorrowed batch offset base ty cs ce s te hty hafter hend hfloor) := by
  unfold pushBorrowed; nat_auto

macro_rules | `(tactic| nat_lemma) => `(tactic| with_reducible apply pushFast_nat)
macro_rules | `(tactic| nat_lemma) => `(tactic| with_reducible apply pushBorrowed_nat)

omit [BSmtLib.Consume H m R E] in
theorem storeUnfinishedSymbolRun_nat (input entry offset base index after runEndAt batch hframe
    hindex hrun hbatch) :
    Nat' (H := H) (m := m) (R := R) (E := E) (floor := floor) (low := low) d r
      (storeUnfinishedSymbolRun input entry offset base index after runEndAt batch hframe hindex
        hrun hbatch) := by
  unfold storeUnfinishedSymbolRun; nat_auto

macro_rules | `(tactic| nat_lemma) => `(tactic| with_reducible apply storeUnfinishedSymbolRun_nat)


theorem startWhitespaceFrom_nat (input offset base index «end» s batch hframe hstart hend hrun
    hbatch) :
    Nat' (H := H) (m := m) (R := R) (E := E) (floor := floor) (low := low) d r
      (startWhitespaceFrom input offset base index «end» s batch hframe hstart hend hrun
        hbatch) := by
  fun_induction startWhitespaceFrom (H := H) (m := m) (R := R) (E := E) input offset base index
    «end» s batch hframe hstart hend hrun
    hbatch <;> nat_auto

macro_rules | `(tactic| nat_lemma) => `(tactic| with_reducible apply startWhitespaceFrom_nat)

theorem startWhitespace_nat (input offset base index batch hrun hframe hindex hbatch) :
    Nat' (H := H) (m := m) (R := R) (E := E) (floor := floor) (low := low) d r
      (startWhitespace input offset base index batch hrun hframe hindex hbatch) := by
  unfold startWhitespace; nat_auto

macro_rules | `(tactic| nat_lemma) => `(tactic| with_reducible apply startWhitespace_nat)

set_option maxHeartbeats 4000000 in
theorem lexNormalFrom_nat (input offset base index batch hframe hindex hbatch origin horigin) :
    Nat' (H := H) (m := m) (R := R) (E := E) (floor := floor) (low := low) d r
      (lexNormalFrom input offset base index batch hframe hindex hbatch origin horigin) := by
  fun_induction lexNormalFrom (H := H) (m := m) (R := R) (E := E) input offset base index batch
    hframe hindex hbatch origin horigin <;> nat_auto
  all_goals first | nat_ih | (apply startWhitespace_nat)

macro_rules | `(tactic| nat_lemma) => `(tactic| with_reducible apply lexNormalFrom_nat)

theorem lexFractionFrom_nat (input start s base h) :
    Nat' (H := H) (m := m) (R := R) (E := E) (floor := floor) (low := low) d r
      (lexFractionFrom input start s base h) := by
  unfold lexFractionFrom; nat_auto

macro_rules | `(tactic| nat_lemma) => `(tactic| with_reducible apply lexFractionFrom_nat)

theorem lexNumeralOrDecimal_nat (input start s base h) :
    Nat' (H := H) (m := m) (R := R) (E := E) (floor := floor) (low := low) d r
      (lexNumeralOrDecimal input start s base h) := by
  unfold lexNumeralOrDecimal; nat_auto

omit [BSmtLib.Consume H m R E] in
theorem lexBaseSelection_nat (input start hstart s h) :
    Nat' (H := H) (m := m) (R := R) (E := E) (floor := floor) (low := low) d r
      (lexBaseSelection input start hstart s h) := by
  unfold lexBaseSelection; nat_auto

theorem lexDigitRun_nat (input start run hrun s base h) :
    Nat' (H := H) (m := m) (R := R) (E := E) (floor := floor) (low := low) d r
      (lexDigitRun input start run hrun s base h) := by
  unfold lexDigitRun; nat_auto

theorem lexStringLiteralLegacy_nat (input consumed origin horigin s base h) :
    Nat' (H := H) (m := m) (R := R) (E := E) (floor := floor) (low := low) d r
      (lexStringLiteralLegacy input consumed origin horigin s base h) := by
  fun_induction lexStringLiteralLegacy (H := H) (m := m) (R := R) (E := E) input consumed origin
    horigin s base h <;> nat_auto
  all_goals
    expose_names
    apply ih1 ⟨_, ?_⟩
    all_goals first | assumption | (simp +zetaDelta only at *; omega)

theorem lexStringLiteralFrom_nat (input consumed origin horigin s base h) :
    Nat' (H := H) (m := m) (R := R) (E := E) (floor := floor) (low := low) d r
      (lexStringLiteralFrom input consumed origin horigin s base h) := by
  fun_induction lexStringLiteralFrom (H := H) (m := m) (R := R) (E := E) input consumed origin
    horigin s base h
  all_goals nat_auto
  all_goals
    expose_names
    apply ih1 ⟨_, ?_⟩
    all_goals first | assumption | (simp +zetaDelta only at *; omega)

macro_rules | `(tactic| nat_lemma) => `(tactic| with_reducible apply lexStringLiteralLegacy_nat)
macro_rules | `(tactic| nat_lemma) => `(tactic| with_reducible apply lexStringLiteralFrom_nat)

theorem lexStringLiteral_nat (input start s base h) :
    Nat' (H := H) (m := m) (R := R) (E := E) (floor := floor) (low := low) d r
      (lexStringLiteral input start s base h) := by
  unfold lexStringLiteral; nat_auto

theorem lexSimpleSymbol_nat (input start s base h) :
    Nat' (H := H) (m := m) (R := R) (E := E) (floor := floor) (low := low) d r
      (lexSimpleSymbol input start s base h) := by
  unfold lexSimpleSymbol; nat_auto

theorem lexQuotedSymbol_nat (input consumed origin horigin hconsumed s base h) :
    Nat' (H := H) (m := m) (R := R) (E := E) (floor := floor) (low := low) d r
      (lexQuotedSymbol input consumed origin horigin hconsumed s base h) := by
  fun_induction lexQuotedSymbol (H := H) (m := m) (R := R) (E := E) input consumed origin
    horigin hconsumed s base h <;> nat_auto

theorem lexKeyword_nat (input start s base h) :
    Nat' (H := H) (m := m) (R := R) (E := E) (floor := floor) (low := low) d r
      (lexKeyword input start s base h) := by
  unfold lexKeyword; nat_auto

theorem lexQuotedSymbolClosed_nat (input start s base h) :
    Nat' (H := H) (m := m) (R := R) (E := E) (floor := floor) (low := low) d r
      (lexQuotedSymbolClosed input start s base h) := by
  unfold lexQuotedSymbolClosed; nat_auto

theorem lexWhitespace_nat (input start origin horigin hstart s base h) :
    Nat' (H := H) (m := m) (R := R) (E := E) (floor := floor) (low := low) d r
      (lexWhitespace input start origin horigin hstart s base h) := by
  fun_induction lexWhitespace (H := H) (m := m) (R := R) (E := E) input start origin
    horigin hstart s base h <;> nat_auto

theorem lexComment_nat (input start hstart s base h) :
    Nat' (H := H) (m := m) (R := R) (E := E) (floor := floor) (low := low) d r
      (lexComment input start hstart s base h) := by
  unfold lexComment; nat_auto

macro_rules | `(tactic| nat_lemma) => `(tactic| with_reducible apply lexNumeralOrDecimal_nat)
macro_rules | `(tactic| nat_lemma) => `(tactic| with_reducible apply lexBaseSelection_nat)
macro_rules | `(tactic| nat_lemma) => `(tactic| with_reducible apply lexDigitRun_nat)
macro_rules | `(tactic| nat_lemma) => `(tactic| with_reducible apply lexStringLiteral_nat)
macro_rules | `(tactic| nat_lemma) => `(tactic| with_reducible apply lexSimpleSymbol_nat)
macro_rules | `(tactic| nat_lemma) => `(tactic| with_reducible apply lexQuotedSymbol_nat)
macro_rules | `(tactic| nat_lemma) => `(tactic| with_reducible apply lexKeyword_nat)
macro_rules | `(tactic| nat_lemma) => `(tactic| with_reducible apply lexQuotedSymbolClosed_nat)
macro_rules | `(tactic| nat_lemma) => `(tactic| with_reducible apply lexWhitespace_nat)
macro_rules | `(tactic| nat_lemma) => `(tactic| with_reducible apply lexComment_nat)

theorem lexNormal_nat (input start hstart) :
    Nat' (H := H) (m := m) (R := R) (E := E) (floor := floor) (low := low) d r
      (lexNormal input start hstart) := by
  unfold lexNormal
  refine Sim.bindId (Sim.modifyGet fun _ => rfl) fun x => ?_
  nat_auto

macro_rules | `(tactic| nat_lemma) => `(tactic| with_reducible apply lexNormal_nat)

theorem afterStep_nat (input start hstart next) :
    Nat' (H := H) (m := m) (R := R) (E := E) (floor := floor) (low := low) d r
      (afterStep input start hstart next) := by
  unfold afterStep; nat_auto

macro_rules | `(tactic| nat_lemma) => `(tactic| with_reducible apply afterStep_nat)

theorem lexStep_nat (input start hstart state tokenStart base hpending) :
    Nat' (H := H) (m := m) (R := R) (E := E) (floor := floor) (low := low) d r
      (lexStep input start hstart state tokenStart base hpending) := by
  unfold lexStep; nat_auto

end

section
variable {H : Type} {m : Type → Type} {R E : Type} [Monad m] [LawfulMonad m]
  [BSmtLib.Consume H m R E] (d : Bool) (r : Option RecoveryState)

omit [BSmtLib.Consume H m R E] in
theorem bind_map_aux {α β γ : Type} {A A' : m α} {f : α → α} {K : α → m β} {K' : α → m γ}
    {F : γ → β} (e : A' = f <$> A) (hk : ∀ x, K (f x) = F <$> K' x) :
    A' >>= K = A >>= fun x => F <$> K' x := by
  subst e
  simp only [bind_map_left, hk]

@[simp] theorem ρB_val {floor : Option Nat} {low : Nat} (c : {c : LexerCore // c.Bound floor low}) :
    (ρB d r c).val = ρ d r c.val := rfl
@[simp] theorem ρ_state (c : LexerCore) : (ρ d r c).state = c.state := rfl
@[simp] theorem ρ_tokenStart (c : LexerCore) : (ρ d r c).tokenStart = c.tokenStart := rfl
@[simp] theorem ρ_base (c : LexerCore) : (ρ d r c).base = c.base := rfl
@[simp] theorem ρ_offset (c : LexerCore) : (ρ d r c).offset = c.offset := rfl
theorem mk_ρ {floor : Option Nat} {low : Nat} (c : LexerCore) (p : (ρ d r c).Bound floor low) :
    (⟨ρ d r c, p⟩ : {c : LexerCore // c.Bound floor low}) = ρB d r ⟨c, p⟩ := rfl

theorem lexSliceRun_nat {floor : Option Nat} (input : BSmtLib.Lexer.Input) (position : USize)
    (fnResult : Except (BSmtLib.Lexer.Failure E) (ControlFlow R))
    (core : {c : LexerCore // c.Bound floor 0}) (h : H) :
    (lexSliceRun (H := H) (m := m) input position fnResult (ρB d r core)).run h =
      (fun x => ((x.1.1, ρB d r x.1.2), x.2)) <$>
        (lexSliceRun input position fnResult core).run h := by
  fun_induction lexSliceRun (H := H) (m := m) input position fnResult core generalizing h
  case case1 position fnResult core failed hflush =>
    conv => lhs; rw [lexSliceRun.eq_def]
    rw [dite_eq_left_of_eq_true (eq_true hflush)]
    simp only [StateT.run_bind, map_bind]
    have e := flushBatch_nat (H := H) (m := m) (R := R) (E := E) (floor := floor) (low := 0) d r
      core h
    simp only [runM] at e
    rw [← e]
    simp only [bind_map_left]
    refine congrArg (_ >>= ·) (funext fun x => ?_)
    obtain ⟨⟨res, c'⟩, h'⟩ := x
    rcases res with ⟨⟨_ | _⟩, loc, sa⟩ | _ <;> simp [mapOut, Except.map]
  case case2 position fnResult core failed hflush hposition offset hpending step ih1 ih2 =>
    conv => lhs; rw [lexSliceRun.eq_def]
    rw [dite_eq_right_of_eq_false (eq_false hflush)]
    simp only [StateT.run_bind, map_bind]
    have e := lexStep_nat (H := H) (m := m) (R := R) (E := E) (floor := floor)
      (low := core.val.offset) d r input position hposition core.val.state core.val.tokenStart
      core.val.base hpending ⟨core.val, ⟨Nat.le_refl _, core.property.2⟩⟩ h
    simp only [runM] at e
    have e2 : (StateT.run (ExceptT.run (lexStep (H := H) (m := m) (R := R) (E := E)
        (floor := floor) (low := (ρB d r core).val.offset) input position hposition
        (ρB d r core).val.state (ρB d r core).val.tokenStart (ρB d r core).val.base hpending))
        ⟨(ρB d r core).val, ⟨Nat.le_refl _, (ρB d r core).property.2⟩⟩).run h =
        mapOut (ρB d r) id <$> (StateT.run (ExceptT.run (lexStep (H := H) (m := m) (R := R)
          (E := E) (floor := floor) (low := core.val.offset) input position hposition
          core.val.state core.val.tokenStart core.val.base hpending))
          ⟨core.val, ⟨Nat.le_refl _, core.property.2⟩⟩).run h := e.symm
    rw [e2]
    simp only [step]
    refine bind_map_aux (m := m) rfl fun x => ?_
    obtain ⟨⟨res, c'⟩, h'⟩ := x
    cases res with
    | error intr =>
      obtain ⟨res', loc, sa⟩ := intr
      cases res' with
      | error cause => exact ih2 c' cause loc h'
      | ok stop =>
        simp [mapOut, Except.map]
        rfl
    | ok nx =>
      obtain ⟨next, hnext⟩ := nx
      exact ih1 c' next hnext h'

theorem lexSliceFrom_nat (input : BSmtLib.Lexer.Input) (initialOffset floor : Nat) (hfloor)
    (position : USize) (fnResult : Except (BSmtLib.Lexer.Failure E) (ControlFlow R))
    (core : {c : LexerCore // c.Bound (some floor) 0}) (h : H) :
    (lexSliceFrom (H := H) (m := m) input initialOffset floor hfloor position fnResult
      (ρB d r core)).run h =
      (fun x => ((x.1.1, ρ d r x.1.2), x.2)) <$>
        (lexSliceFrom input initialOffset floor hfloor position fnResult core).run h := by
  fun_induction lexSliceFrom (H := H) (m := m) input initialOffset floor hfloor position fnResult
    core generalizing h
  expose_names
  conv => lhs; rw [lexSliceFrom.eq_def]
  simp only [StateT.run_bind, map_bind]
  rw [lexSliceRun_nat]
  refine bind_map_aux rfl fun x => ?_
  obtain ⟨⟨exit, c'⟩, h'⟩ := x
  cases exit with
  | done result => simp
  | stopped stop location after =>
    cases stop with
    | finished result =>
      simp
      rfl
    | relex =>
      by_cases hres : location.offset - initialOffset < input.stop.toNat - input.start.toNat
      · simp only [hres, dite_true]
        exact ih1 c' location after hres h'
      · simp [hres]
        rfl

/-- A step on the lexer state that commutes with setting the two fields. -/
def INat {α : Type} (f : BSmtLib.Lexer.InnerM H m α) : Prop :=
  ∀ c h, (f.run (ρ d r c)).run h = (fun x => ((x.1.1, ρ d r x.1.2), x.2)) <$> (f.run c).run h

omit [BSmtLib.Consume H m R E] in
theorem INat.pure {α : Type} (a : α) : INat (H := H) (m := m) d r (Pure.pure a) := by
  intro c h
  simp [ρ]

omit [BSmtLib.Consume H m R E] in
theorem INat.bind {α β : Type} {f : BSmtLib.Lexer.InnerM H m α}
    {k : α → BSmtLib.Lexer.InnerM H m β} (hf : INat d r f) (hk : ∀ a, INat d r (k a)) :
    INat d r (f >>= k) := by
  intro c h
  simp only [StateT.run_bind, hf c h, bind_map_left, map_bind]
  exact congrArg (_ >>= ·) (funext fun x => hk x.1.1 x.1.2 x.2)

theorem lexSliceInner_nat (input : BSmtLib.Lexer.Input) :
    INat d r (lexSliceInner (H := H) (m := m) (R := R) (E := E) input) := by
  intro c h
  unfold lexSliceInner
  refine Eq.trans ?_ (lexSliceFrom_nat d r input c.offset (c.offset - 1) _ input.start _ _ h)
  rfl

omit [LawfulMonad m] [BSmtLib.Consume H m R E] in
theorem getThe_run (c : LexerCore) :
    (getThe LexerCore : BSmtLib.Lexer.InnerM H m LexerCore).run c = pure (c, c) := rfl

omit [BSmtLib.Consume H m R E] in
theorem executeStep_nat (step : BSmtLib.Lexer.InnerM H m (Except (BSmtLib.Lexer.Failure E)
    (ControlFlow R))) (hs : INat d r step) : INat d r (executeStep step) := by
  intro c h
  unfold executeStep
  simp only [StateT.run_bind, hs c h, bind_map_left, map_bind]
  refine congrArg (_ >>= ·) (funext fun x => ?_)
  obtain ⟨⟨res, c'⟩, h'⟩ := x
  rcases res with _ | _ | _ <;> simp [getThe_run, ρ,
    BSmtLib.Lexer.LexerCore.currentLocation, BSmtLib.Lexer.LexerCore.locationAt,
    BSmtLib.Lexer.LexerCore.offsetAt]

theorem lexChunks_nat (slice : ByteSlice) (position : Nat) :
    INat d r (lexChunks (H := H) (m := m) (R := R) (E := E) slice position) := by
  fun_induction lexChunks (H := H) (m := m) (R := R) (E := E) slice position
  case case1 ih =>
    refine INat.bind d r (executeStep_nat d r _ (lexSliceInner_nat d r _)) fun x => ?_
    split
    · exact ih
    · exact INat.pure d r _
  case case2 => exact INat.pure d r _

end

/-! ## The adapter's lexer on the chunks -/

open BSmtLib.Proofs.Adapter (Collector feed)

/-- The step that `lexSliceStep` takes on a slice, past the discarding and the recovery. -/
def sliceStep (slice : ByteSlice) :
    BSmtLib.Lexer.InnerM Collector Id (Except (BSmtLib.Lexer.Failure Unit)
      (ControlFlow (Located Empty))) :=
  match BSmtLib.Lexer.Input.ofSlice? slice with
  | some input => executeStep (lexSliceInner input)
  | none => lexChunks slice 0

/-- What the chunk lemma needs of the lexer: it neither discards nor recovers. -/
def Inv (c : LexerCore) : Prop := c.discard = false ∧ c.recoveryState = none

/-- What feeding goes on with after a step of the lexer: the rest of the slices from the lexer
the step leaves, if the step goes on. -/
def afterStep' (rest : List Spec.Lexicon.Chars)
    (x : (Except (BSmtLib.Lexer.Failure Unit) (ControlFlow (Located Empty)) × LexerCore) ×
      Collector) : Option (List BSmtLib.Spec.Lexer.Handed) :=
  match x with
  | ((.ok .continue, c'), h') => feed Adapter.Lexer.ops (BSmtLib.Lexer.Internal.ofParts h' c') rest
  | ((.ok (.break x), _), _) => x.value.elim
  | ((.error _, _), _) => none

theorem feed_step (l : BSmtLib.Lexer Collector) (hl : Inv (BSmtLib.Lexer.Internal.core l))
    (s : Spec.Lexicon.Chars) (rest : List Spec.Lexicon.Chars) :
    feed Adapter.Lexer.ops l (s :: rest) =
      afterStep' rest (((sliceStep s.toByteArray.toByteSlice).run
        (BSmtLib.Lexer.Internal.core l)).run (BSmtLib.Lexer.Internal.handler l)) := by
  obtain ⟨hd, hr⟩ := hl
  simp only [feed, Adapter.Lexer.ops, BSmtLib.Lexer.lexSlice, BSmtLib.Lexer.Internal.run]
  generalize hX : ((sliceStep s.toByteArray.toByteSlice).run (BSmtLib.Lexer.Internal.core l)).run
    (BSmtLib.Lexer.Internal.handler l) = X
  unfold sliceStep at hX
  simp only [BSmtLib.Lexer.Internal.core, BSmtLib.Lexer.Internal.handler] at hd hr hX ⊢
  simp only [lexSliceStep, StateT.run_bind, getThe_run, hd, hr, pure_bind,
    Bool.false_eq_true, ite_false]
  cases hs : BSmtLib.Lexer.Input.ofSlice? (List.toByteArray s).toByteSlice <;>
    simp only [hs] at hX ⊢ <;>
    simp only [StateT.run_bind] <;>
    rw [hX] <;>
    rcases X with ⟨⟨res, c'⟩, h'⟩ <;>
    rcases res with f | (_ | ⟨⟨v, _⟩⟩)
  all_goals first | exact v.elim | rfl

theorem sliceStep_nat (slice : ByteSlice) (d : Bool) (r : Option RecoveryState) :
    INat d r (sliceStep slice) := by
  unfold sliceStep
  split
  · exact executeStep_nat d r _ (lexSliceInner_nat d r _)
  · exact lexChunks_nat d r _ _

/-- A step that commutes with setting the two fields keeps them. -/
theorem inv_of_nat {α : Type} (f : BSmtLib.Lexer.InnerM Collector Id α)
    (hf : ∀ d r, INat d r f) (c : LexerCore) (h : Collector) (hc : Inv c) :
    Inv ((f.run c).run h).1.2 := by
  have e := hf c.discard c.recoveryState c h
  have e1 : ρ c.discard c.recoveryState c = c := rfl
  rw [e1] at e
  have e2 := congrArg (fun x => x.1.2) e
  refine ⟨?_, ?_⟩
  · rw [show ((f.run c).run h).1.2.discard = c.discard from by rw [e2]; rfl]
    exact hc.1
  · rw [show ((f.run c).run h).1.2.recoveryState = c.recoveryState from by rw [e2]; rfl]
    exact hc.2

/-! ### The chunks -/


/-- The chunk of the input from `p` on, as `lexChunks` lexes it. -/
def chunkAt (s : Spec.Lexicon.Chars) (p : Nat) : Spec.Lexicon.Chars :=
  (s.drop p).take CHUNK_SIZE

/-- The chunks of the input from `p` on. -/
def chunksFrom (s : Spec.Lexicon.Chars) (p : Nat) : List Spec.Lexicon.Chars :=
  if p < s.length then chunkAt s p :: chunksFrom s (p + CHUNK_SIZE) else []
termination_by s.length - p
decreasing_by simp only [CHUNK_SIZE]; omega

/-- The input cut into slices that are not too large for the library's lexer: itself if it is
not, and its chunks if it is. -/
def cut (s : Spec.Lexicon.Chars) : List Spec.Lexicon.Chars :=
  if s.length < USize.size then [s] else chunksFrom s 0

theorem flatten_chunksFrom (s : Spec.Lexicon.Chars) (p : Nat) :
    (chunksFrom s p).flatten = s.drop p := by
  fun_induction chunksFrom s p with
  | case1 p hp ih =>
    rw [List.flatten_cons, ih, chunkAt, ← List.drop_drop, List.take_append_drop]
  | case2 p hp =>
    simp only [List.flatten_nil]
    exact (List.drop_eq_nil_of_le (by omega)).symm

theorem flatten_cut (s : Spec.Lexicon.Chars) : (cut s).flatten = s := by
  unfold cut
  split
  · simp
  · rw [flatten_chunksFrom, List.drop_zero]

theorem length_chunkAt (s : Spec.Lexicon.Chars) (p : Nat) : (chunkAt s p).length ≤ CHUNK_SIZE := by
  simp only [chunkAt, List.length_take]; omega

theorem mem_chunksFrom {s : Spec.Lexicon.Chars} {p : Nat} {c : Spec.Lexicon.Chars}
    (h : c ∈ chunksFrom s p) : c.length ≤ CHUNK_SIZE := by
  fun_induction chunksFrom s p with
  | case1 p hp ih =>
    rcases List.mem_cons.mp h with h | h
    · subst h; exact length_chunkAt s p
    · exact ih h
  | case2 p hp => simp at h

theorem chunk_lt_size : CHUNK_SIZE < USize.size := by
  have := USize.le_size
  simp only [CHUNK_SIZE]
  omega

theorem mem_cut {s c : Spec.Lexicon.Chars} (h : c ∈ cut s) : c.length < USize.size := by
  unfold cut at h
  split at h
  · simp at h; subst h; assumption
  · exact Nat.lt_of_le_of_lt (mem_chunksFrom h) chunk_lt_size

/-- The input of the chunk of the slice from `p` on, as `lexChunks` builds it. -/
def chunkInput (slice : ByteSlice) (p : Nat) : BSmtLib.Lexer.Input :=
  let chunk := slice.byteArray.extract (slice.start + p)
    (min (slice.start + p + CHUNK_SIZE) slice.stop)
  { bytes := chunk
    start := 0
    stop := USize.ofNatLT chunk.size (by
      have := chunk_lt_size
      simp only [chunk, ByteArray.size_extract, CHUNK_SIZE] at *
      omega)
    stop_le := by simp only [USize.toNat_ofNatLT]; exact Nat.le_refl _ }

/-- What `lexChunks` does after a chunk. -/
def chunksCont (slice : ByteSlice) (p : Nat)
    (result : Except (BSmtLib.Lexer.Failure Unit) (ControlFlow (Located Empty))) :
    BSmtLib.Lexer.InnerM Collector Id
      (Except (BSmtLib.Lexer.Failure Unit) (ControlFlow (Located Empty))) :=
  match result with
  | .ok .continue => lexChunks slice (p + CHUNK_SIZE)
  | result => pure result

theorem lexChunks_unfold (slice : ByteSlice) (p : Nat) (hp : p < slice.size) :
    lexChunks (H := Collector) (m := Id) (R := Empty) (E := Unit) slice p =
      (executeStep (lexSliceInner (chunkInput slice p)) >>= chunksCont slice p) := by
  rw [lexChunks]
  simp only [hp, dite_true]
  congr 1
  funext result
  rcases result with _ | _ | _ <;> rfl

theorem core_ofParts (h : Collector) (c : LexerCore) :
    BSmtLib.Lexer.Internal.core (BSmtLib.Lexer.Internal.ofParts h c : BSmtLib.Lexer Collector) =
      c := rfl

theorem handler_ofParts (h : Collector) (c : LexerCore) :
    BSmtLib.Lexer.Internal.handler
      (BSmtLib.Lexer.Internal.ofParts h c : BSmtLib.Lexer Collector) = h := rfl

theorem lexChunks_end (slice : ByteSlice) (p : Nat) (hp : ¬p < slice.size) :
    lexChunks (H := Collector) (m := Id) (R := Empty) (E := Unit) slice p =
      pure (.ok .continue) := by
  rw [lexChunks]
  simp only [hp, dite_false]

theorem toByteSlice_byteArray (a : ByteArray) : a.toByteSlice.byteArray = a := by
  simp [ByteArray.toByteSlice, ByteSlice.byteArray]

theorem toByteSlice_start (a : ByteArray) : a.toByteSlice.start = 0 := by
  simp [ByteArray.toByteSlice, ByteSlice.start]

theorem toByteSlice_stop (a : ByteArray) : a.toByteSlice.stop = a.size := by
  simp [ByteArray.toByteSlice, ByteSlice.stop]

theorem toByteSlice_size (a : ByteArray) : a.toByteSlice.size = a.size := by
  simp [ByteSlice.size, toByteSlice_start, toByteSlice_stop]

theorem toByteArray_chunkAt (s : Spec.Lexicon.Chars) (p : Nat) :
    (chunkAt s p).toByteArray =
      s.toByteArray.extract (0 + p) (min (0 + p + CHUNK_SIZE) s.toByteArray.size) := by
  apply ByteArray.ext
  rw [List.data_toByteArray, ByteArray.data_extract, List.data_toByteArray]
  apply Array.toList_inj.mp
  simp only [List.toList_toArray, Array.toList_extract, List.extract_eq_take_drop, chunkAt,
    List.size_toByteArray, Nat.zero_add]
  apply List.take_eq_take_iff.mpr
  simp only [List.length_drop]
  omega

theorem ofSlice_chunkAt (s : Spec.Lexicon.Chars) (p : Nat) :
    BSmtLib.Lexer.Input.ofSlice? (chunkAt s p).toByteArray.toByteSlice =
      some (chunkInput s.toByteArray.toByteSlice p) := by
  have hlen : (chunkAt s p).length < USize.size :=
    Nat.lt_of_le_of_lt (length_chunkAt s p) chunk_lt_size
  unfold BSmtLib.Lexer.Input.ofSlice?
  rw [dite_eq_left_of_eq_true
    (eq_true (by rw [toByteSlice_stop, List.size_toByteArray]; exact hlen))]
  simp only [chunkInput, toByteSlice_byteArray, toByteSlice_start, toByteSlice_stop,
    Option.some.injEq]
  have e := toByteArray_chunkAt s p
  congr 1 <;> first | exact e | simp only [e] | rfl

theorem sliceStep_chunkAt (s : Spec.Lexicon.Chars) (p : Nat) :
    sliceStep (chunkAt s p).toByteArray.toByteSlice =
      executeStep (lexSliceInner (chunkInput s.toByteArray.toByteSlice p)) := by
  unfold sliceStep
  rw [ofSlice_chunkAt]

theorem chunksCont_continue (slice : ByteSlice) (p : Nat) :
    chunksCont slice p (.ok .continue) = lexChunks slice (p + CHUNK_SIZE) := by
  simp only [chunksCont]

theorem chunksCont_error (slice : ByteSlice) (p : Nat) (f : BSmtLib.Lexer.Failure Unit) :
    chunksCont slice p (.error f) = pure (.error f) := by
  simp only [chunksCont]

/- The kernel must not be left to compare lists of chunks, which would make it unfold
`chunksFrom`; these state each case of `afterStep'` by its own. -/
theorem afterStep'_error (rest : List Spec.Lexicon.Chars) (f : BSmtLib.Lexer.Failure Unit)
    (c : LexerCore) (h : Collector) : afterStep' rest ((.error f, c), h) = none := rfl

theorem afterStep'_continue (rest : List Spec.Lexicon.Chars) (c : LexerCore) (h : Collector) :
    afterStep' rest ((.ok .continue, c), h) =
      feed Adapter.Lexer.ops (BSmtLib.Lexer.Internal.ofParts h c) rest := rfl

theorem run_pure_error (f : BSmtLib.Lexer.Failure Unit) (c : LexerCore) (h : Collector) :
    (((pure (.error f) : BSmtLib.Lexer.InnerM Collector Id
      (Except (BSmtLib.Lexer.Failure Unit) (ControlFlow (Located Empty)))).run c).run h) =
      ((.error f, c), h) := rfl

/-- After a chunk, feeding the further chunks goes on as `lexChunks` goes on. -/
theorem afterChunk (s : Spec.Lexicon.Chars) (rest : List Spec.Lexicon.Chars) (p : Nat)
    (ih : ∀ (c : LexerCore) (h : Collector), Inv c →
      feed Adapter.Lexer.ops (BSmtLib.Lexer.Internal.ofParts h c)
          (chunksFrom s (p + CHUNK_SIZE) ++ rest) =
        afterStep' rest (((lexChunks s.toByteArray.toByteSlice (p + CHUNK_SIZE)).run c).run h))
    (X : (Except (BSmtLib.Lexer.Failure Unit) (ControlFlow (Located Empty)) × LexerCore) ×
      Collector) (hX : Inv X.1.2) :
    afterStep' (chunksFrom s (p + CHUNK_SIZE) ++ rest) X =
      afterStep' rest (((chunksCont s.toByteArray.toByteSlice p X.1.1).run X.1.2).run X.2) := by
  obtain ⟨⟨res, c'⟩, h'⟩ := X
  cases res with
  | error f =>
    rw [chunksCont_error, afterStep'_error, run_pure_error]
    exact (afterStep'_error rest f c' h').symm
  | ok flow =>
    cases flow with
    | «continue» =>
      rw [chunksCont_continue, afterStep'_continue]
      exact ih c' h' hX
    | «break» v => exact v.value.elim

theorem feed_chunksFrom (s : Spec.Lexicon.Chars) (rest : List Spec.Lexicon.Chars) (p : Nat) :
    ∀ (c : LexerCore) (h : Collector), Inv c →
      feed Adapter.Lexer.ops (BSmtLib.Lexer.Internal.ofParts h c) (chunksFrom s p ++ rest) =
        afterStep' rest (((lexChunks s.toByteArray.toByteSlice p).run c).run h) := by
  fun_induction chunksFrom s p with
  | case1 p hp ih =>
    intro c h hc
    rw [List.cons_append, feed_step (BSmtLib.Lexer.Internal.ofParts h c) hc]
    have hp' : p < s.toByteArray.toByteSlice.size := by
      rw [toByteSlice_size, List.size_toByteArray]; exact hp
    rw [lexChunks_unfold _ _ hp']
    have hInv := inv_of_nat (executeStep (lexSliceInner (chunkInput s.toByteArray.toByteSlice p)))
      (fun d r => executeStep_nat d r _ (lexSliceInner_nat d r _)) c h hc
    rw [sliceStep_chunkAt, core_ofParts, handler_ofParts, StateT.run_bind, StateT.run_bind]
    exact afterChunk s rest p ih _ hInv
  | case2 p hp =>
    intro c h hc
    have hp' : ¬p < s.toByteArray.toByteSlice.size := by
      rw [toByteSlice_size, List.size_toByteArray]; exact hp
    rw [lexChunks_end _ _ hp']
    rfl

theorem ofSlice_large (s : Spec.Lexicon.Chars) (hs : ¬s.length < USize.size) :
    BSmtLib.Lexer.Input.ofSlice? s.toByteArray.toByteSlice = none := by
  unfold BSmtLib.Lexer.Input.ofSlice?
  rw [dite_eq_right_iff.mpr]
  intro h
  rw [toByteSlice_stop, List.size_toByteArray] at h
  exact absurd h hs

theorem ofParts_eta (l : BSmtLib.Lexer Collector) :
    BSmtLib.Lexer.Internal.ofParts (BSmtLib.Lexer.Internal.handler l)
      (BSmtLib.Lexer.Internal.core l) = l := rfl

/-- Feeding a slice is feeding its cut: the library's lexer lexes a slice too large for its
positions as it lexes the chunks of the slice given one after another. -/
theorem feed_cut (l : BSmtLib.Lexer Collector) (hl : Inv (BSmtLib.Lexer.Internal.core l))
    (s : Spec.Lexicon.Chars) (rest : List Spec.Lexicon.Chars) :
    feed Adapter.Lexer.ops l (s :: rest) = feed Adapter.Lexer.ops l (cut s ++ rest) := by
  unfold cut
  split
  · rfl
  · rename_i hs
    rw [feed_step l hl, sliceStep, ofSlice_large s hs]
    rw [← feed_chunksFrom s rest 0 _ _ hl, ofParts_eta]

/-- What feeding goes on with depends on the slices after the step only through feeding them. -/
theorem afterStep'_congr {L L' : List Spec.Lexicon.Chars}
    (hL : ∀ (c : LexerCore) (h : Collector), Inv c →
      feed Adapter.Lexer.ops (BSmtLib.Lexer.Internal.ofParts h c) L =
        feed Adapter.Lexer.ops (BSmtLib.Lexer.Internal.ofParts h c) L')
    (X : (Except (BSmtLib.Lexer.Failure Unit) (ControlFlow (Located Empty)) × LexerCore) ×
      Collector) (hX : Inv X.1.2) :
    afterStep' L X = afterStep' L' X := by
  obtain ⟨⟨res, c'⟩, h'⟩ := X
  cases res with
  | error f => rw [afterStep'_error, afterStep'_error]
  | ok flow =>
    cases flow with
    | «continue» =>
      rw [afterStep'_continue, afterStep'_continue]
      exact hL c' h' hX
    | «break» v => exact v.value.elim

theorem feed_append_congr {ys ys' : List Spec.Lexicon.Chars}
    (hy : ∀ l : BSmtLib.Lexer Collector, Inv (BSmtLib.Lexer.Internal.core l) →
      feed Adapter.Lexer.ops l ys = feed Adapter.Lexer.ops l ys') :
    ∀ (xs : List Spec.Lexicon.Chars) (l : BSmtLib.Lexer Collector),
      Inv (BSmtLib.Lexer.Internal.core l) →
      feed Adapter.Lexer.ops l (xs ++ ys) = feed Adapter.Lexer.ops l (xs ++ ys')
  | [], l, hl => by rw [List.nil_append, List.nil_append]; exact hy l hl
  | x :: xs, l, hl => by
    rw [List.cons_append, List.cons_append, feed_step l hl, feed_step l hl]
    exact afterStep'_congr (fun c h hc => feed_append_congr hy xs _ hc) _
      (inv_of_nat _ (fun d r => sliceStep_nat _ d r) _ _ hl)

/-- Every slice of the list cut, as `cut` cuts it. -/
def cutAll (slices : List Spec.Lexicon.Chars) : List Spec.Lexicon.Chars :=
  slices.flatMap cut

theorem flatten_cutAll (slices : List Spec.Lexicon.Chars) :
    (cutAll slices).flatten = slices.flatten := by
  induction slices with
  | nil => rfl
  | cons s rest ih =>
    rw [cutAll, List.flatMap_cons, List.flatten_append, ← cutAll, ih, flatten_cut,
      List.flatten_cons]

theorem mem_cutAll {slices : List Spec.Lexicon.Chars} {c : Spec.Lexicon.Chars}
    (h : c ∈ cutAll slices) : c.length < USize.size := by
  obtain ⟨s, _, hc⟩ := List.mem_flatMap.mp h
  exact mem_cut hc

theorem feed_cutAll : ∀ (slices : List Spec.Lexicon.Chars) (l : BSmtLib.Lexer Collector),
    Inv (BSmtLib.Lexer.Internal.core l) →
    feed Adapter.Lexer.ops l slices = feed Adapter.Lexer.ops l (cutAll slices)
  | [], _, _ => rfl
  | s :: rest, l, hl => by
    rw [feed_cut l hl, cutAll, List.flatMap_cons, ← cutAll]
    exact feed_append_congr (fun l' hl' => feed_cutAll rest l' hl') (cut s) l hl

/-- The library's lexer, run by the adapter, hands over for the slices what it hands over for
their cut: every slice too large for its positions cut into chunks that are not. -/
theorem handed_cutAll (v : Spec.Lexicon.Version) (slices : List Spec.Lexicon.Chars) :
    Adapter.handed Adapter.Lexer.ops v slices =
      Adapter.handed Adapter.Lexer.ops v (cutAll slices) :=
  feed_cutAll slices _ ⟨rfl, rfl⟩

end BSmtLib.Proofs.X2ContentsLexer.Chunks
