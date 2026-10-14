module

public import BSmtLib.Facts.Proofs.Lexer.WRustPortX1BatchInCore.Whitespace
import all BSmtLib.Lexer.Internal.WRustPort

@[expose] public section

/-!
# The loop of the normal state

The two loops of the normal state (`lexNormalFrom`) take the same steps on the same bytes: the
parentheses and the fast path append to the batches they hold, the slow path lexes the other
tokens, and both end where the slice or a token that the slice ends inside does. The locals of
the two loops are related at the line and the line start of the states (`OpsSim`): they are
stored back before the loop leaves or takes the slow path, and loaded again after the slow path.
The loops are shown alike by induction on the bytes left.
-/

namespace BSmtLib.Facts.Proofs.Lexer.WRustPortX1BatchInCore.Normal

open BSmtLib.Lexer (BATCH_CAPACITY Interrupted)
open BSmtLib.Lexer.Internal.WRustPort.Slice (get? runEnd)
open BSmtLib.Lexer.Internal.WRustPort (Ops)
open BSmtLib.Facts.Proofs.Lexer.Simulation.Batch BSmtLib.Facts.Proofs.Lexer.Simulation.Relation
open BSmtLib.Facts.Proofs.Lexer.Simulation.Steps
open BSmtLib.Facts.Proofs.Lexer.WRustPortX1BatchInCore.Held
open BSmtLib.Facts.Proofs.Lexer.WRustPortX1BatchInCore.Ops
open BSmtLib.Facts.Proofs.Lexer.WRustPortX1BatchInCore.Whitespace

set_option hygiene false in
/-- A token of the fast path, then the loop after it: the batches held after the token, and the
induction hypothesis `ih` for the loop. The names are those of `lexNormalFrom_sim`. -/
local macro "push_loop" : tactic => `(tactic| (
  refine SimR.bind (ho.pushFast l ls b b' hb a a' ha _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) fun x y => ?_
  refine SimR.of_fact' (Er := Core.ErS strict) fun hxy => ?_
  exact ih _ (by omega) _ x.val y.val l ls a a' rfl hxy ha _ _ _ _ _))

set_option hygiene false in
/-- The loop again after the slow path, from states with `SR0`: the locals are loaded again at
the line and the line start of the states, with the batches held `hnn`. -/
local macro "load_loop " hnn:term:max : tactic => `(tactic| (
  refine Core.SimR.of_sre fun l ls => SimR.bind (ho.loadLocals l ls Core.NoTokens)
    fun a a' => ?_
  refine SimR.of_fact' (Er := Core.ErS strict) fun ha => ?_
  exact ih _ (by omega) _ _ _ l ls a a' rfl $hnn ha _ _ _ _ _))

set_option hygiene false in
/-- What follows the whitespace run, from states with `SR0`: nothing if the run reaches the end
of the slice, and the loop after it otherwise. -/
local macro "ws_cont" : tactic => `(tactic| (
  refine SimR.bind (startWhitespace_sim ho input offset base index b b' hb _ _ _ _ _)
    fun x y => ?_
  rcases x with _ | ⟨⟨next, nb⟩, hnext, hnb⟩ <;>
    rcases y with _ | ⟨⟨next', nb'⟩, hnext', hnb'⟩
  · exact SimR.pure fun s t h => ⟨rfl, h⟩
  · exact SimR.of_false fun s t h => h
  · exact SimR.of_false fun s t h => h
  · refine SimR.intro fun s₀ t₀ h₀ => ?_
    simp only [WsQ] at h₀
    obtain ⟨e, hnn, h0⟩ := h₀
    subst e
    refine SimR.pre (fun s t h => by obtain ⟨-, rfl, rfl⟩ := h; exact h0) ?_
    load_loop hnn))

set_option hygiene false in
/-- The locals are stored back, from states with `SRE` whose line and line start the locals are
related at. -/
local macro "store" : tactic => `(tactic|
  refine SimR.seq (ho.storeLocals l ls Core.NoTokens a a' ha) ?_)

section

variable {H : Type} {m : Type → Type} {R E : Type} [Monad m] [LawfulMonad m] [Token.Consume H R E]
  [∀ batch, Token.ConsumeFrom H (Token.BatchCursor batch) m]
  {floor : Option Nat} {low : Nat} {strict : Bool} {o₁ o₂ : Ops H m R E}
  {LRel : Ops.Locals H m R E (self := o₁) → Ops.Locals H m R E (self := o₂) → Nat → Nat → Prop}

omit [∀ batch, Token.ConsumeFrom H (Token.BatchCursor batch) m] in
theorem lexNormalFrom_sim (ho : OpsSim o₁ o₂ LRel) (input : ByteSlice) (offset base : Nat)
    (origin : Nat) :
    ∀ k (index : Nat) (b b' : Token.TokenBatch) (l ls : Nat) (a : Ops.Locals H m R E (self := o₁))
      (a' : Ops.Locals H m R E (self := o₂)),
      input.size - index = k → Core.HR b b' → LRel a a' l ls →
      ∀ hframe hindex hbatch hbatch' horigin,
      Core.LSim strict (H := H) (m := m) (R := R) (E := E) (floor := floor) (low := low)
        (Core.SRE l ls) (fun x y s t => x.val = y.val ∧ Core.SRb strict s t)
        (Lexer.Internal.WRustPort.lexNormalFrom (ops := o₁) input offset base index b a hframe
            hindex
          hbatch origin horigin)
        (Lexer.Internal.WRustPort.lexNormalFrom (ops := o₂) input offset base index b' a' hframe
            hindex
          hbatch' origin horigin) := by
  intro k
  induction k using Nat.strongRecOn with
  | ind k ih =>
  intro index b b' l ls a a' hk hb ha hframe hindex hbatch hbatch' horigin
  rw [Lexer.Internal.WRustPort.lexNormalFrom.eq_def (ops := o₁),
    Lexer.Internal.WRustPort.lexNormalFrom.eq_def (ops := o₂)]
  split
  · store
    refine SimR.seq (SimR.pre (fun s t h => h.1) (Core.leave_sim _ _ _ _ _ _ _ hb _ _ _ _)) ?_
    exact SimR.pure fun s t h => ⟨rfl, h.1.1, h.2⟩
  rename_i c h1
  have hlt := Lexer.Internal.WRustPort.Slice.lt_size_of_get? h1
  dsimp only
  refine SimR.ite Iff.rfl (fun hc => ?_) fun hc => ?_
  · refine Core.getCore_bind_P fun s t h => ?_
    refine SimR.ite (by rw [h.1.1.recovers]) (fun _ => ?_) fun _ => ?_
    · refine SimR.seq (Core.modifyCore_sim _ (fun _ _ => Core.SRE l ls)
        fun s t h => ⟨⟨{ h.1.1 with lexedDepth := by simp [h.1.1.lexedDepth] }, h.1.2⟩, h.2⟩) ?_
      push_loop
    · push_loop
  refine SimR.ite Iff.rfl (fun hc' => ?_) fun hc' => ?_
  · refine Core.getCore_bind_P fun s t h => ?_
    refine SimR.ite (by rw [h.1.1.recovers]) (fun _ => ?_) fun _ => ?_
    · refine SimR.seq (Core.modifyCore_sim _ (fun _ _ => Core.SRE l ls)
        fun s t h => ⟨⟨{ h.1.1 with lexedDepth := by simp [h.1.1.lexedDepth] }, h.1.2⟩, h.2⟩) ?_
      push_loop
    · push_loop
  simp only [Lexer.Internal.WRustPort.consumesWhitespaceAndComments, pure_bind]
  generalize Token.Consume.isConcrete (H := H) = cw
  refine SimR.ite Iff.rfl (fun hf => ?_) fun hf => ?_
  · -- the fast path
    refine SimR.dite Iff.rfl (fun hws _ => ?_) fun hws _ => ?_
    · -- a whitespace run the consumer takes
      store
      refine SimR.pre (P := Core.SR0) (fun s t h => ⟨h.1.1, h.2⟩) ?_
      ws_cont
    refine SimR.dite Iff.rfl (fun hu _ => ?_) fun hu _ => ?_
    · -- a symbol run the slice ends inside
      store
      refine SimR.seq (Core.storeUnfinishedSymbolRun_sim _ _ _ _ _ _ _ _ _ _ _ hb _ _ _ _ _ _) ?_
      exact SimR.pure fun s t h => ⟨rfl, h.1.1, h.2⟩
    have hte : index < (if (Lexer.Helpers.fastFlags c &&& Lexer.Helpers.FAST_PIPE != 0) = true then
        runEnd input (index + 1) (Lexer.Helpers.fastFlags c &&& Lexer.Helpers.FAST_RUN_MASK) + 1
      else runEnd input (index + 1) (Lexer.Helpers.fastFlags c &&& Lexer.Helpers.FAST_RUN_MASK)) :=
          by
      have := Lexer.Internal.WRustPort.Slice.le_runEnd input (index + 1)
          (Lexer.Helpers.fastFlags c &&& Lexer.Helpers.FAST_RUN_MASK)
      split <;> omega
    refine SimR.ite Iff.rfl (fun he => ?_) fun he => ?_
    · split
      · rename_i next h2
        refine SimR.ite Iff.rfl (fun hd => ?_) fun hd => ?_
        · simp only [throw_bind]
          store
          refine SimR.seq (SimR.pre (fun s t h => h.1) (Core.leave_sim _ _ _ _ _ _ _ hb _ _ _ _)) ?_
          refine SimR.bind (Core.startToken_simx _ _ _ _ _ _ _ _) fun _ _ =>
            SimR.pre (fun s t h => h.2) ?_
          exact Core.errorAt_sim _ _ _ _ _
        · push_loop
      · -- a quoted symbol that ends at the end of the slice
        store
        refine SimR.bind (Core.startToken_simx _ _ _ _ _ _ _ _) fun a₁ a₂ => ?_
        obtain ⟨a₁, ha₁⟩ := a₁
        obtain ⟨a₂, ha₂⟩ := a₂
        refine SimR.of_fact' (Er := Core.ErS strict) fun (e : a₁ = a₂) => ?_
        subst e
        refine SimR.seq (Core.extendContent_sim _ _ _ _ _ _) ?_
        refine SimR.seq (SimR.pre (fun s t h => h.1) (Core.leavePending_sim _ _ _ _ _ _ _ _ _ hb
          _ _ _ _ _ _ _ _)) ?_
        exact SimR.pure fun s t h => ⟨rfl, h.1.1, h.2⟩
    · push_loop
  · -- the slow path
    store
    refine SimR.pre (P := Core.SR0) (fun s t h => ⟨h.1.1, h.2⟩) ?_
    split
    · -- a line feed
      refine SimR.ite Iff.rfl (fun hcw => ?_) fun hcw => ?_
      · ws_cont
      · refine SimR.seq (Core.markLineFeedAt_sim0 _) ?_
        load_loop hb
    · -- a comment
      refine Core.SimR.of_sre fun l ls => SimR.bind
          (Core.startToken_simx l ls _ _ _ _ _ _) fun a₁ a₂ => ?_
      obtain ⟨a₁, ha₁⟩ := a₁
      obtain ⟨a₂, ha₂⟩ := a₂
      refine SimR.of_fact' (Er := Core.ErS strict) fun (e : a₁ = a₂) => ?_
      subst e
      dsimp only
      have hle := Lexer.Internal.WRustPort.Slice.le_runEnd input
          (index + 1) Lexer.CharClass.RUN_COMMENT_PLAIN
      split
      · rename_i c₁ h3
        have := Lexer.Internal.WRustPort.Slice.lt_size_of_get? h3
        refine SimR.pre (P := Core.SR0) (fun s t h => ⟨h.1.1, h.2⟩) ?_
        refine SimR.ite Iff.rfl (fun _ => ?_) fun _ => ?_
        · refine SimR.seq (Core.markLineFeedAt_sim0 _) ?_
          refine SimR.ite Iff.rfl (fun _ => ?_) fun _ => ?_
          · refine Core.SimR.of_sre fun l ls => SimR.bind
              (pushBorrowed_sim ho l ls input b b' hb _ _
              _ _ _ _ _ _ _ _ _ _ _ _) fun x y => ?_
            refine SimR.of_fact' (Er := Core.ErS strict) fun hxy =>
              SimR.pre (P := Core.SR0) (fun s t h => ⟨h.1.1, h.2⟩) ?_
            load_loop hxy
          · load_loop hb
        · refine SimR.ite Iff.rfl (fun _ => ?_) fun _ => ?_
          · refine Core.SimR.of_sre fun l ls => SimR.bind
              (pushBorrowed_sim ho l ls input b b' hb _ _
              _ _ _ _ _ _ _ _ _ _ _ _) fun x y => ?_
            refine SimR.of_fact' (Er := Core.ErS strict) fun hxy =>
              SimR.pre (P := Core.SR0) (fun s t h => ⟨h.1.1, h.2⟩) ?_
            load_loop hxy
          · load_loop hb
      · refine SimR.ite Iff.rfl (fun _ => ?_) fun _ => ?_
        · refine SimR.seq (Core.extendContent_sim _ _ _ _ _ _) ?_
          refine SimR.seq (SimR.pre (fun s t h => h.1) (Core.leavePending_sim _ _ _ _ _ _ _ _ _ hb
            _ _ _ _ _ _ _ _)) ?_
          exact SimR.pure fun s t h => ⟨rfl, h.1.1, h.2⟩
        · refine SimR.seq (SimR.pre (fun s t h => h.1) (Core.leavePending_sim _ _ _ _ _ _ _ _ _ hb
            _ _ _ _ _ _ _ _)) ?_
          exact SimR.pure fun s t h => ⟨rfl, h.1.1, h.2⟩
    · -- a base selection
      refine Core.SimR.of_sre fun l ls => SimR.bind
          (Core.startToken_simx l ls _ _ _ _ _ _) fun a₁ a₂ => ?_
      obtain ⟨a₁, ha₁⟩ := a₁
      obtain ⟨a₂, ha₂⟩ := a₂
      refine SimR.of_fact' (Er := Core.ErS strict) fun (e : a₁ = a₂) => ?_
      subst e
      dsimp only
      split
      · rename_i run hrun h3
        have := Lexer.Internal.WRustPort.Slice.le_runEnd input (index + 1 + 1) run.flag
        refine SimR.dite Iff.rfl (fun _ _ => ?_) fun hne _ => ?_
        · refine SimR.seq (Core.extendContent_sim _ _ _ _ _ _) ?_
          refine SimR.seq (SimR.pre (fun s t h => h.1) (Core.leavePending_sim _ _ _ _ _ _ _ _ _ hb
            _ _ _ _ _ _ _ _)) ?_
          exact SimR.pure fun s t h => ⟨rfl, h.1.1, h.2⟩
        · refine Core.getCore_bind_P fun s t h => ?_
          simp only [throw_bind]
          refine SimR.ite (by rw [h.1.1.tokenContent]) (fun _ => ?_) fun _ => ?_
          · exact SimR.seq (SimR.pre (fun s t h => h.1) (Core.leave_sim _ _ _ _ _ _ _ hb _ _ _ _))
              (Core.error_sim _ _ _ _ _)
          · refine SimR.ite Iff.rfl (fun _ => ?_) fun _ => ?_
            · exact SimR.seq (SimR.pre (fun s t h => h.1) (Core.leave_sim _ _ _ _ _ _ _ hb _ _ _ _))
                (Core.errorAt_sim _ _ _ _ _)
            · refine SimR.bind (pushBorrowed_sim ho l ls input b b' hb _ _ _ _ _ _ _ _ _ _ _ _
                _ _) fun x y => ?_
              refine SimR.of_fact' (Er := Core.ErS strict) fun hxy =>
                SimR.pre (P := Core.SR0) (fun s t h => ⟨h.1.1, h.2⟩) ?_
              load_loop hxy
      · refine SimR.seq (SimR.pre (fun s t h => h.1) (Core.leavePending_sim _ _ _ _ _ _ _ _ _ hb
          _ _ _ _ _ _ _ _)) ?_
        exact SimR.pure fun s t h => ⟨rfl, h.1.1, h.2⟩
    · -- a string literal
      refine Core.SimR.of_sre fun l ls => SimR.bind
          (Core.startToken_simx l ls _ _ _ _ _ _) fun a₁ a₂ => ?_
      obtain ⟨a₁, ha₁⟩ := a₁
      obtain ⟨a₂, ha₂⟩ := a₂
      refine SimR.of_fact' (Er := Core.ErS strict) fun (e : a₁ = a₂) => ?_
      subst e
      refine Core.getCore_bind_P fun s t h => ?_
      refine SimR.ite (by rw [h.1.1.version]) (fun _ => ?_) fun _ => ?_
      · refine SimR.seq (SimR.pre (fun s t h => h.1) (Core.leavePending_sim _ _ _ _ _ _ _ _ _ hb
          _ _ _ _ _ _ _ _)) ?_
        exact SimR.pure fun s t h => ⟨rfl, h.1.1, h.2⟩
      have hle := Lexer.Internal.WRustPort.Slice.le_runEnd input
          (index + 1) Lexer.CharClass.RUN_STRING_PLAIN
      split
      · rename_i q n hn
        refine SimR.ite Iff.rfl (fun _ => ?_) fun _ => ?_
        · have := Lexer.Internal.WRustPort.Slice.lt_size_of_get? hn
          simp only [throw_bind]
          refine SimR.ite Iff.rfl (fun _ => ?_) fun _ => ?_
          · exact SimR.seq (SimR.pre (fun s t h => h.1) (Core.leave_sim _ _ _ _ _ _ _ hb _ _ _ _))
              (Core.errorAt_sim _ _ _ _ _)
          · refine SimR.bind (pushBorrowed_sim ho l ls input b b' hb _ _ _ _ _ _ _ _ _ _ _ _
              _ _) fun x y => ?_
            refine SimR.of_fact' (Er := Core.ErS strict) fun hxy =>
              SimR.pre (P := Core.SR0) (fun s t h => ⟨h.1.1, h.2⟩) ?_
            load_loop hxy
        · refine SimR.seq (Core.extendContent_sim _ _ _ _ _ _) ?_
          refine SimR.seq (SimR.pre (fun s t h => h.1) (Core.leavePending_sim _ _ _ _ _ _ _ _ _ hb
            _ _ _ _ _ _ _ _)) ?_
          exact SimR.pure fun s t h => ⟨rfl, h.1.1, h.2⟩
      · refine SimR.seq (Core.extendContent_sim _ _ _ _ _ _) ?_
        refine SimR.seq (SimR.pre (fun s t h => h.1) (Core.leavePending_sim _ _ _ _ _ _ _ _ _ hb
          _ _ _ _ _ _ _ _)) ?_
        exact SimR.pure fun s t h => ⟨rfl, h.1.1, h.2⟩
    · -- a keyword
      refine Core.SimR.of_sre fun l ls => SimR.bind
          (Core.startToken_simx l ls _ _ _ _ _ _) fun a₁ a₂ => ?_
      obtain ⟨a₁, ha₁⟩ := a₁
      obtain ⟨a₂, ha₂⟩ := a₂
      refine SimR.of_fact' (Er := Core.ErS strict) fun (e : a₁ = a₂) => ?_
      subst e
      dsimp only
      have := Lexer.Internal.WRustPort.Slice.le_runEnd input
          (index + 1) Lexer.CharClass.RUN_SIMPLE_SYMBOL
      refine SimR.dite Iff.rfl (fun _ _ => ?_) fun _ _ => ?_
      · refine SimR.seq (Core.extendContent_sim _ _ _ _ _ _) ?_
        refine SimR.seq (SimR.pre (fun s t h => h.1) (Core.leavePending_sim _ _ _ _ _ _ _ _ _ hb
          _ _ _ _ _ _ _ _)) ?_
        exact SimR.pure fun s t h => ⟨rfl, h.1.1, h.2⟩
      · refine Core.getCore_bind_P fun s t h => ?_
        simp only [throw_bind]
        refine SimR.ite (by rw [h.1.1.tokenContent]) (fun _ => ?_) fun _ => ?_
        · exact SimR.seq (SimR.pre (fun s t h => h.1) (Core.leave_sim _ _ _ _ _ _ _ hb _ _ _ _))
            (Core.error_sim _ _ _ _ _)
        · refine SimR.ite Iff.rfl (fun _ => ?_) fun _ => ?_
          · exact SimR.seq (SimR.pre (fun s t h => h.1) (Core.leave_sim _ _ _ _ _ _ _ hb _ _ _ _))
              (Core.errorAt_sim _ _ _ _ _)
          · refine SimR.bind (pushBorrowed_sim ho l ls input b b' hb _ _ _ _ _ _ _ _ _ _ _ _
              _ _) fun x y => ?_
            refine SimR.of_fact' (Er := Core.ErS strict) fun hxy =>
              SimR.pre (P := Core.SR0) (fun s t h => ⟨h.1.1, h.2⟩) ?_
            load_loop hxy
    · -- a numeral or a decimal
      refine Core.SimR.of_sre fun l ls => SimR.bind
          (Core.startToken_simx l ls _ _ _ _ _ _) fun a₁ a₂ => ?_
      obtain ⟨a₁, ha₁⟩ := a₁
      obtain ⟨a₂, ha₂⟩ := a₂
      refine SimR.of_fact' (Er := Core.ErS strict) fun (e : a₁ = a₂) => ?_
      subst e
      have := Lexer.Internal.WRustPort.Slice.le_runEnd input (index + 1) Lexer.CharClass.RUN_DIGIT
      simp only [throw_bind]
      refine SimR.ite Iff.rfl (fun _ => ?_) fun _ => ?_
      · exact SimR.seq (SimR.pre (fun s t h => h.1) (Core.leave_sim _ _ _ _ _ _ _ hb _ _ _ _))
          (Core.errorAt_sim _ _ _ _ _)
      split
      · rename_i next h3
        have := Lexer.Internal.WRustPort.Slice.lt_size_of_get? h3
        refine SimR.ite Iff.rfl (fun _ => ?_) fun _ => ?_
        · have := Lexer.Internal.WRustPort.Slice.le_runEnd input
            (runEnd input (index + 1) Lexer.CharClass.RUN_DIGIT + 1)
            Lexer.CharClass.RUN_DIGIT
          refine SimR.dite Iff.rfl (fun _ _ => ?_) fun _ _ => ?_
          · refine SimR.seq (Core.extendContent_sim _ _ _ _ _ _) ?_
            refine SimR.seq (SimR.pre (fun s t h => h.1) (Core.leavePending_sim _ _ _ _ _ _ _ _ _ hb
              _ _ _ _ _ _ _ _)) ?_
            exact SimR.pure fun s t h => ⟨rfl, h.1.1, h.2⟩
          · refine Core.getCore_bind_P fun s t h => ?_
            refine SimR.ite (by rw [h.1.1.tokenContent]) (fun _ => ?_) fun _ => ?_
            · exact SimR.seq (SimR.pre (fun s t h => h.1) (Core.leave_sim _ _ _ _ _ _ _ hb _ _ _ _))
                (Core.error_sim _ _ _ _ _)
            · refine SimR.ite Iff.rfl (fun _ => ?_) fun _ => ?_
              · exact SimR.seq (SimR.pre (fun s t h => h.1)
                  (Core.leave_sim _ _ _ _ _ _ _ hb _ _ _ _))
                  (Core.errorAt_sim _ _ _ _ _)
              · refine SimR.bind (pushBorrowed_sim ho l ls input b b' hb _ _ _ _ _ _ _ _ _ _ _
                  _ _ _) fun x y => ?_
                refine SimR.of_fact' (Er := Core.ErS strict) fun hxy =>
                  SimR.pre (P := Core.SR0) (fun s t h => ⟨h.1.1, h.2⟩) ?_
                load_loop hxy
        · refine SimR.ite Iff.rfl (fun _ => ?_) fun _ => ?_
          · exact SimR.seq (SimR.pre (fun s t h => h.1) (Core.leave_sim _ _ _ _ _ _ _ hb _ _ _ _))
              (Core.errorAt_sim _ _ _ _ _)
          · refine SimR.bind (pushBorrowed_sim ho l ls input b b' hb _ _ _ _ _ _ _ _ _ _ _
              _ _ _) fun x y => ?_
            refine SimR.of_fact' (Er := Core.ErS strict) fun hxy =>
              SimR.pre (P := Core.SR0) (fun s t h => ⟨h.1.1, h.2⟩) ?_
            load_loop hxy
      · refine SimR.seq (Core.extendContent_sim _ _ _ _ _ _) ?_
        refine SimR.seq (SimR.pre (fun s t h => h.1) (Core.leavePending_sim _ _ _ _ _ _ _ _ _ hb
          _ _ _ _ _ _ _ _)) ?_
        exact SimR.pure fun s t h => ⟨rfl, h.1.1, h.2⟩
    all_goals
      -- an unexpected character
      refine Core.SimR.of_sre fun l ls => ?_
      refine SimR.bind (Core.startToken_simx _ _ _ _ _ _ _ _) fun _ _ => ?_
      refine SimR.seq (SimR.pre (fun s t h => h.2.1) (Core.leave_sim _ _ _ _ _ _ _ hb _ _ _ _)) ?_
      exact Core.errorAt_sim _ _ _ _ _


omit [∀ batch, Token.ConsumeFrom H (Token.BatchCursor batch) m] in
/-- The normal state, from states whose batches have the same array of contents: the loops take
the batches out of the states and run from `start`. -/
theorem lexNormal_sim (ho : OpsSim o₁ o₂ LRel) (input : ByteSlice) (start : Nat)
    (hstart : start < input.size) :
    Core.LSim true (H := H) (m := m) (R := R) (E := E) (floor := floor) (low := low) (Core.SRb true)
      (fun a b s t => a.val = b.val ∧ Core.SRb true s t)
      (Lexer.Internal.WRustPort.lexNormal (ops := o₁) input start hstart)
      (Lexer.Internal.WRustPort.lexNormal (ops := o₂) input start hstart) := by
  unfold Lexer.Internal.WRustPort.lexNormal
  refine SimR.bind (SimR.modifyGet (Q := fun a b s t => a.val.1 = b.val.1 ∧
    a.val.2.1 = b.val.2.1 ∧ Core.HR a.val.2.2 b.val.2.2 ∧ Core.SR0 s t) fun s t h => ?_) fun a b =>
        ?_
  · obtain ⟨hst, hby⟩ := h
    exact ⟨hst.offset, hst.base, ⟨hst.batch, hby rfl, hst.capacity⟩,
      { hst with batch := agree_of_len_zero rfl rfl, capacity := Core.zero_lt_capacity }, rfl⟩
  obtain ⟨⟨offset, base, batch⟩, hframe, hbatch, hfloor⟩ := a
  obtain ⟨⟨offset', base', batch'⟩, hframe', hbatch', hfloor'⟩ := b
  refine SimR.intro fun s₀ t₀ h₀ => ?_
  obtain ⟨e1, e2, hb, -⟩ := h₀
  dsimp only at e1 e2 hb
  subst e1 e2
  refine SimR.pre (P := Core.SR0)
      (fun s t h => by obtain ⟨⟨-, -, -, h0⟩, rfl, rfl⟩ := h; exact h0) ?_
  refine Core.SimR.of_sre fun l ls => SimR.bind (ho.loadLocals l ls Core.NoTokens) fun a a' => ?_
  refine SimR.of_fact' (Er := Core.ErS true) fun ha => ?_
  refine SimR.bind (lexNormalFrom_sim ho input _ start start (input.size - start) start batch
    batch' l ls a a' rfl hb ha _ _ _ _ _) fun x y => ?_
  obtain ⟨x, hx⟩ := x
  obtain ⟨y, hy⟩ := y
  exact SimR.pure fun s t h => ⟨h.1, h.2⟩
end

end BSmtLib.Facts.Proofs.Lexer.WRustPortX1BatchInCore.Normal
