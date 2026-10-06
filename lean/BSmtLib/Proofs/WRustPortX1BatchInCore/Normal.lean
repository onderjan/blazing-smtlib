import BSmtLib.Proofs.WRustPortX1BatchInCore.Whitespace

/-!
# The loop of the normal state

The two loops of the normal state (`lexNormalFrom`) take the same steps on the same bytes:
the parentheses and the fast path append to the batches they hold, the slow path lexes the
other tokens, and both end where the slice or a token that the slice ends inside does. The
Rust port stores its locals back before it leaves the loop or takes the slow path, and loads
them again after the slow path, so that they are the line and the line start of its state
wherever it reads them; the other lexer reads its state. The loops are shown alike by
induction on the bytes left.
-/

namespace BSmtLib.Proofs.WRustPortX1BatchInCore

open BSmtLib.Proofs.Simulation (M runM)
open BSmtLib.Lexer (BATCH_CAPACITY Interrupted)
open BSmtLib.Proofs.Lexer.Slice (get? runEnd)

set_option hygiene false in
/-- A token of the fast path, then the loop after it: the batches held after the token, and
the induction hypothesis `ih` for the loop. The names are those of `lexNormalFrom_sim`. -/
local macro "push_loop " ety:term:max eemit:term:max : tactic => `(tactic| (
  refine SimR.bind (pushFast_sim' hcons _ _ b b' hb locals rfl rfl _ _ _ _ $ety _ _ _ _ _ $eemit
    _ _ _ _ _ _ _ _) fun x y => ?_
  refine SimR.of_fact' (Er := ErS strict) fun hxy => ?_
  exact ih _ (by omega) _ x.val y.val locals rfl hxy _ _ _ _ _ _))

set_option hygiene false in
/-- The loop again, after the Rust port loads its locals, from states with `SR0`, with the
batches held `hnn`. -/
local macro "load_loop " hnn:term:max : tactic => `(tactic| (
  refine load_bind_left fun s t h => ?_
  refine SimR.pre (fun s' t' h' => ?_) (ih _ (by omega) _ _ _ ⟨s.val.line, s.val.lineStart⟩ rfl
    $hnn _ _ _ _ _ _)
  obtain ⟨rfl, rfl⟩ := h'
  exact ⟨sr_srl h.1, h.2⟩))

set_option hygiene false in
/-- What follows the whitespace run, from states with `SR0`: nothing if the run reaches the end
of the slice, and the loop after it otherwise. -/
local macro "ws_cont" : tactic => `(tactic| (
  refine SimR.bind (startWhitespace_sim hcons input offset base index b b' hb _ _ _ _ _ _ _)
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

/-- The string literal is closed by a quote that is not doubled where the two bytes after its
content are a quote and another byte, as the Rust port tests them. -/
theorem closed_some {q n n' : UInt8} {p aq : Nat}
    (h : (if (q == 34) = true then (if (n != 34) = true then some (p, n) else none) else none) =
      some (aq, n')) : (q == 34 && n != 34) = true ∧ aq = p ∧ n' = n := by
  by_cases hq : (q == 34) = true <;> by_cases hn : (n != 34) = true <;> simp_all

theorem closed_none {q n : UInt8} {p : Nat}
    (h : (if (q == 34) = true then (if (n != 34) = true then some (p, n) else none) else none) =
      none) : ¬(q == 34 && n != 34) = true := by
  by_cases hq : (q == 34) = true <;> by_cases hn : (n != 34) = true <;> simp_all

section

variable {H : Type} {m : Type → Type} {R E : Type} [Monad m] [LawfulMonad m] [Consume H m R E]
  {floor : Option Nat} {low : Nat} {strict : Bool}

theorem lexNormalFrom_sim (hcons : ConsumesAlike H m R E) (input : ByteSlice) (offset base : Nat)
    (origin : Nat) :
    ∀ k (index : Nat) (b b' : TokenBatch) (locals : Lexer.WRustPort.FastState),
      input.size - index = k → HR b b' →
      ∀ hframe hframe' hindex hbatch hbatch' horigin,
      LSim strict (H := H) (m := m) (R := R) (E := E) (floor := floor) (low := low)
        (SRE locals.line locals.lineStart) (fun a b s t => a.val = b.val ∧ SRb strict s t)
        (Lexer.WRustPort.lexNormalFrom input offset base index b locals hframe hindex hbatch origin
          horigin)
        (Lexer.X1BatchInCore.lexNormalFrom input offset base index b' hframe' hindex hbatch' origin
          horigin) := by
  intro k
  induction k using Nat.strongRecOn with
  | ind k ih =>
  intro index b b' locals hk hb hframe hframe' hindex hbatch hbatch' horigin
  rw [Lexer.WRustPort.lexNormalFrom, Lexer.X1BatchInCore.lexNormalFrom]
  split_both
  · refine store_bind_left locals (fun s t h => ⟨h.1.2.1, h.1.2.2⟩) ?_
    refine SimR.seq (SimR.pre (fun s t h => h.1) (leave_sim _ _ _ _ _ _ _ hb _ _ _ _)) ?_
    exact SimR.pure fun s t h => ⟨rfl, h.1.1, h.2⟩
  · rename_i h1 c h2
    exact absurd (h1.symm.trans h2) (by simp)
  · rename_i c h1 h2
    exact absurd (h1.symm.trans h2) (by simp)
  · rename_i c h1 c' h2
    obtain rfl : c' = c := Option.some.inj (h2.symm.trans h1)
    have hlt := Lexer.Slice.lt_size_of_get? h1
    dsimp only
    refine SimR.ite Iff.rfl (fun hc => ?_) fun hc => ?_
    · refine getCore_bind_P fun s t h => ?_
      refine SimR.ite (by rw [h.1.1.recovers]) (fun _ => ?_) fun _ => ?_
      · refine SimR.seq (modifyCore_sim _ (fun _ _ => SRE locals.line locals.lineStart)
          fun s t h => ⟨⟨{ h.1.1 with lexedDepth := by simp [h.1.1.lexedDepth] }, h.1.2⟩, h.2⟩) ?_
        push_loop rfl rfl
      · refine SimR.bind (pushFast_sim' hcons _ _ b b' hb locals rfl rfl _ _ _ _ rfl _ _ _ _ _ rfl
          _ _ _ _ _ _ _ _) fun x y => ?_
        refine SimR.of_fact' (Er := ErS strict) fun hxy => ?_
        exact ih _ (by omega) _ x.val y.val locals rfl hxy _ _ _ _ _ _
    refine SimR.ite Iff.rfl (fun hc' => ?_) fun hc' => ?_
    · refine getCore_bind_P fun s t h => ?_
      refine SimR.ite (by rw [h.1.1.recovers]) (fun _ => ?_) fun _ => ?_
      · refine SimR.seq (modifyCore_sim _ (fun _ _ => SRE locals.line locals.lineStart)
          fun s t h => ⟨⟨{ h.1.1 with lexedDepth := by simp [h.1.1.lexedDepth] }, h.1.2⟩, h.2⟩) ?_
        push_loop rfl rfl
      · push_loop rfl rfl
    simp only [Lexer.WRustPort.consumesWhitespaceAndComments,
      Lexer.X1BatchInCore.consumesWhitespaceAndComments, pure_bind]
    generalize Consume.consumesWhitespaceAndComments (H := H) = cw
    refine SimR.ite Iff.rfl (fun hf => ?_) fun hf => ?_
    · -- the fast path
      refine SimR.dite Iff.rfl (fun hws _ => ?_) fun hws _ => ?_
      · -- a whitespace run the consumer takes
        refine store_bind_left locals (fun s t h => ⟨h.1.2.1, h.1.2.2⟩) ?_
        refine SimR.bind (SimR.pre (fun s t h => ⟨h.1.1, h.2⟩)
          (startWhitespace_sim hcons input offset base index b b' hb _ _ _ _ _ _ _)) fun x y => ?_
        rcases x with _ | ⟨⟨next, nb⟩, hnext, hnb⟩ <;>
          rcases y with _ | ⟨⟨next', nb'⟩, hnext', hnb'⟩
        · exact SimR.pure fun s t h => ⟨rfl, h⟩
        · exact SimR.of_false fun s t h => h
        · exact SimR.of_false fun s t h => h
        · refine SimR.intro fun s₀ t₀ h₀ => ?_
          simp only [WsQ] at h₀
          obtain ⟨e, hnn, h0⟩ := h₀
          subst e
          refine load_bind_left fun s t h => ?_
          obtain ⟨-, hs, ht⟩ := h
          subst s t
          refine SimR.pre (fun s t h => ?_) (ih _ (by omega) next nb nb' ⟨s₀.val.line,
            s₀.val.lineStart⟩ rfl hnn _ _ _ _ _ _)
          obtain ⟨rfl, rfl⟩ := h
          exact ⟨sr_srl h0.1, h0.2⟩
      · refine SimR.dite Iff.rfl (fun hu _ => ?_) fun hu _ => ?_
        · -- a symbol run the slice ends inside
          refine store_bind_left locals (fun s t h => ⟨h.1.2.1, h.1.2.2⟩) ?_
          refine SimR.seq (storeUnfinishedSymbolRun_sim _ _ _ _ _ _ _
            _ _ _ _ hb _ _ _ _ _ _) ?_
          exact SimR.pure fun s t h => ⟨rfl, h.1.1, h.2⟩
        · have eemit : ∀ (e w : Bool), (if cw = true then e || w else e) = (e || (cw && w)) := by
            intro e w
            cases cw <;> simp
          have hte : index < (if (Lexer.fastFlags c' &&& Lexer.FAST_PIPE != 0) = true then
              runEnd input (index + 1) (Lexer.fastFlags c' &&& Lexer.FAST_RUN_MASK) + 1
            else runEnd input (index + 1) (Lexer.fastFlags c' &&& Lexer.FAST_RUN_MASK)) := by
            have := Lexer.Slice.le_runEnd input (index + 1)
              (Lexer.fastFlags c' &&& Lexer.FAST_RUN_MASK)
            split <;> omega
          refine SimR.ite Iff.rfl (fun he => ?_) fun he => ?_
          · split_both
            · rename_i _ next h1 _ next' h2
              obtain rfl : next' = next := Option.some.inj (h2.symm.trans h1)
              refine SimR.ite Iff.rfl (fun hd => ?_) fun hd => ?_
              · simp only [throw_bind, failAt_bind]
                refine store_bind_left locals (fun s t h => ⟨h.1.2.1, h.1.2.2⟩) ?_
                refine SimR.seq (SimR.pre (fun s t h => h.1)
                  (leave_sim _ _ _ _ _ _ _ hb _ _ _ _)) ?_
                exact SimR.bind (startToken_sim _ _ _ _ _ _ _ _) fun _ _ =>
                  SimR.pre (fun s t h => h.2) (errorAt_sim _ _ _ _ _)
              · push_loop rfl (eemit _ _)
            · rename_i _ next h1 _ h2
              exact absurd (h1.symm.trans h2) (by simp)
            · rename_i _ h1 _ next h2
              exact absurd (h1.symm.trans h2) (by simp)
            · -- a quoted symbol that ends at the end of the slice
              refine store_bind_left locals (fun s t h => ⟨h.1.2.1, h.1.2.2⟩) ?_
              refine SimR.bind (startToken_sre _ _ _ _ _ _ _) fun a a' => ?_
              obtain ⟨a, ha⟩ := a
              obtain ⟨a', ha'⟩ := a'
              refine SimR.of_fact' (Er := ErS strict) fun (e : a = a') => ?_
              subst e
              refine SimR.seq (extendContentFrom_sre _ _ _) ?_
              refine SimR.seq (SimR.pre (fun s t h => h.1) (leavePending_sim _ _ _ _ _ _ _ _ _ hb
                _ _ _ _ _ _ _ _)) ?_
              exact SimR.pure fun s t h => ⟨rfl, h.1.1, h.2⟩
          · push_loop rfl (eemit _ _)
    · -- the slow path
      refine store_bind_left locals (fun s t h => ⟨h.1.2.1, h.1.2.2⟩) ?_
      split_both
      all_goals (try (rename_i h1 h2; have e := h1.symm.trans h2; cases e; done))
      all_goals refine SimR.pre (P := SR0) (fun s t h => ⟨h.1.1, h.2⟩) ?_
      · -- a line feed
        refine SimR.ite Iff.rfl (fun hcw => ?_) fun hcw => ?_
        · ws_cont
        · refine SimR.seq (markLineFeedAt_sim0 _) ?_
          load_loop hb
      · -- a comment
        refine LSim.of_sre fun l ls => SimR.bind (startToken_sre l ls _ _ _ _ _) fun a a' => ?_
        obtain ⟨a, ha⟩ := a
        obtain ⟨a', ha'⟩ := a'
        refine SimR.of_fact' (Er := ErS strict) fun (e : a = a') => ?_
        subst e
        dsimp only
        have hle := Lexer.Slice.le_runEnd input (index + 1) Lexer.RUN_COMMENT_PLAIN
        split_both
        · rename_i c h1 c' h2
          obtain rfl : c' = c := Option.some.inj (h2.symm.trans h1)
          have := Lexer.Slice.lt_size_of_get? h1
          refine SimR.pre (P := SR0) (fun s t h => ⟨h.1.1, h.2⟩) ?_
          refine SimR.ite Iff.rfl (fun _ => ?_) fun _ => ?_
          · refine SimR.seq (markLineFeedAt_sim0 _) ?_
            refine SimR.ite Iff.rfl (fun _ => ?_) fun _ => ?_
            · refine LSim.of_sre fun l ls => SimR.bind (pushBorrowed_sim hcons l ls b b' hb _ _ _
                _ _ _ _ _ _ _ _ _ _) fun x y => ?_
              refine SimR.of_fact' (Er := ErS strict) fun hxy =>
                SimR.pre (P := SR0) (fun s t h => ⟨h.1.1, h.2⟩) ?_
              load_loop hxy
            · load_loop hb
          · refine SimR.ite Iff.rfl (fun _ => ?_) fun _ => ?_
            · refine LSim.of_sre fun l ls => SimR.bind (pushBorrowed_sim hcons l ls b b' hb _ _ _
                _ _ _ _ _ _ _ _ _ _) fun x y => ?_
              refine SimR.of_fact' (Er := ErS strict) fun hxy =>
                SimR.pre (P := SR0) (fun s t h => ⟨h.1.1, h.2⟩) ?_
              load_loop hxy
            · load_loop hb
        · rename_i c h1 h2
          exact absurd (h1.symm.trans h2) (by simp)
        · rename_i h1 c h2
          exact absurd (h1.symm.trans h2) (by simp)
        · refine SimR.ite Iff.rfl (fun _ => ?_) fun _ => ?_
          · refine SimR.seq (extendContent_sre _ _ _ _ _) ?_
            refine SimR.seq (SimR.pre (fun s t h => h.1) (leavePending_sim _ _ _ _ _ _ _ _ _ hb
              _ _ _ _ _ _ _ _)) ?_
            exact SimR.pure fun s t h => ⟨rfl, h.1.1, h.2⟩
          · refine SimR.seq (SimR.pre (fun s t h => h.1) (leavePending_sim _ _ _ _ _ _ _ _ _ hb
              _ _ _ _ _ _ _ _)) ?_
            exact SimR.pure fun s t h => ⟨rfl, h.1.1, h.2⟩
      · -- a base selection
        refine LSim.of_sre fun l ls => SimR.bind (startToken_sre l ls _ _ _ _ _) fun a a' => ?_
        obtain ⟨a, ha⟩ := a
        obtain ⟨a', ha'⟩ := a'
        refine SimR.of_fact' (Er := ErS strict) fun (e : a = a') => ?_
        subst e
        dsimp only
        split_both
        · rename_i _ run hrun h1 _ run' hrun' h2
          obtain rfl : run = run' :=
            (congrArg Subtype.val (Option.some.inj (h2.symm.trans h1))).symm
          have := Lexer.Slice.le_runEnd input (index + 1 + 1) run.flag
          refine SimR.ite Iff.rfl (fun _ => ?_) fun hne => ?_
          · refine SimR.seq (extendContent_sre _ _ _ _ _) ?_
            refine SimR.seq (SimR.pre (fun s t h => h.1) (leavePending_sim _ _ _ _ _ _ _ _ _ hb
              _ _ _ _ _ _ _ _)) ?_
            exact SimR.pure fun s t h => ⟨rfl, h.1.1, h.2⟩
          · refine getCore_bind_P fun s t h => ?_
            simp only [throw_bind, fail_bind, failAt_bind]
            refine SimR.ite (by rw [h.1.1.tokenContent]; exact Iff.rfl) (fun _ => ?_) fun _ => ?_
            · exact SimR.seq (SimR.pre (fun s t h => h.1) (leave_sim _ _ _ _ _ _ _ hb _ _ _ _))
                (error_sim _ _ _ _ _)
            · refine SimR.ite Iff.rfl (fun _ => ?_) fun _ => ?_
              · exact SimR.seq (SimR.pre (fun s t h => h.1) (leave_sim _ _ _ _ _ _ _ hb _ _ _ _))
                  (errorAt_sim _ _ _ _ _)
              · refine SimR.bind (pushBorrowed_sim hcons l ls b b' hb _ _ _ _ _ _ _ _ _ _ _ _ _)
                  fun x y => ?_
                refine SimR.of_fact' (Er := ErS strict) fun hxy =>
                  SimR.pre (P := SR0) (fun s t h => ⟨h.1.1, h.2⟩) ?_
                load_loop hxy
        · rename_i _ run hrun h1 _ h2
          exact (h2 run hrun h1).elim
        · rename_i _ h1 _ run hrun h2
          exact (h1 run hrun h2).elim
        · refine SimR.seq (SimR.pre (fun s t h => h.1) (leavePending_sim _ _ _ _ _ _ _ _ _ hb
            _ _ _ _ _ _ _ _)) ?_
          exact SimR.pure fun s t h => ⟨rfl, h.1.1, h.2⟩
      · -- a string literal
        refine LSim.of_sre fun l ls => SimR.bind (startToken_sre l ls _ _ _ _ _) fun a a' => ?_
        obtain ⟨a, ha⟩ := a
        obtain ⟨a', ha'⟩ := a'
        refine SimR.of_fact' (Er := ErS strict) fun (e : a = a') => ?_
        subst e
        dsimp only
        refine getCore_bind_P fun s t h => ?_
        refine SimR.ite (by rw [h.1.1.version]) (fun _ => ?_) fun _ => ?_
        · refine SimR.seq (SimR.pre (fun s t h => h.1) (leavePending_sim _ _ _ _ _ _ _ _ _ hb
            _ _ _ _ _ _ _ _)) ?_
          exact SimR.pure fun s t h => ⟨rfl, h.1.1, h.2⟩
        have hle := Lexer.Slice.le_runEnd input (index + 1) Lexer.RUN_STRING_PLAIN
        have stayOpen : LSim strict (H := H) (m := m) (R := R) (E := E) (floor := floor)
            (low := low)
            (SRE l ls) (fun a b s t => a.val = b.val ∧ SRb strict s t)
            (Lexer.WRustPort.extendContent input (index + 1)
                (runEnd input (index + 1) Lexer.RUN_STRING_PLAIN) >>= fun _ =>
              Lexer.WRustPort.leavePending .stringLiteral a offset base
                (runEnd input (index + 1) Lexer.RUN_STRING_PLAIN) b hframe
                (hbatch.mono hindex (by omega)) (Lexer.WRustPort.started_lt ha hindex (by omega))
                (Lexer.WRustPort.started_floor ha hframe) >>= fun _ =>
              pure (Lexer.WRustPort.Past.from (input := input) horigin
                ⟨runEnd input (index + 1) Lexer.RUN_STRING_PLAIN, by omega, fun _ => by omega⟩))
            (Lexer.X1BatchInCore.extendContent input (index + 1)
                (runEnd input (index + 1) Lexer.RUN_STRING_PLAIN) >>= fun _ =>
              Lexer.X1BatchInCore.leavePending .stringLiteral a offset base
                (runEnd input (index + 1) Lexer.RUN_STRING_PLAIN) b' hframe'
                (hbatch'.mono hindex (by omega))
                (Lexer.X1BatchInCore.started_lt ha hindex (by omega))
                (Lexer.X1BatchInCore.started_floor ha hframe') >>= fun _ =>
              pure (Lexer.X1BatchInCore.Past.from (input := input) horigin
                ⟨runEnd input (index + 1) Lexer.RUN_STRING_PLAIN, by omega,
                  fun _ => by omega⟩)) := by
          refine SimR.seq (extendContent_sre _ _ _ _ _) ?_
          refine SimR.seq (SimR.pre (fun s t h => h.1) (leavePending_sim _ _ _ _ _ _ _ _ _ hb
            _ _ _ _ _ _ _ _)) ?_
          exact SimR.pure fun s t h => ⟨rfl, h.1.1, h.2⟩
        split_both
        · rename_i _ q n hq hn aq n' hc
          simp only [hq, hn] at hc
          obtain ⟨hcond, rfl, rfl⟩ := closed_some hc
          have := Lexer.Slice.lt_size_of_get? hn
          rw [ite_eq_left hcond]
          simp only [throw_bind, failAt_bind]
          refine SimR.ite Iff.rfl (fun _ => ?_) fun _ => ?_
          · exact SimR.seq (SimR.pre (fun s t h => h.1) (leave_sim _ _ _ _ _ _ _ hb _ _ _ _))
              (errorAt_sim _ _ _ _ _)
          · refine SimR.bind (pushBorrowed_sim hcons l ls b b' hb _ _ _ _ _ _ _ _ _ _ _ _ _)
              fun x y => ?_
            refine SimR.of_fact' (Er := ErS strict) fun hxy =>
              SimR.pre (P := SR0) (fun s t h => ⟨h.1.1, h.2⟩) ?_
            load_loop hxy
        · rename_i _ q n hq hn hc
          simp only [hq, hn] at hc
          rw [ite_eq_right (closed_none hc)]
          exact stayOpen
        · rename_i _ hno aq n' hc
          exfalso
          rcases hA : get? input (runEnd input (index + 1) Lexer.RUN_STRING_PLAIN) with _ | q
          · simp [hA] at hc
          · rcases hB : get? input (runEnd input (index + 1) Lexer.RUN_STRING_PLAIN + 1) with _ | n
            · simp [hA, hB] at hc
            · exact hno q n hA hB
        · exact stayOpen
      · -- a keyword
        refine LSim.of_sre fun l ls => SimR.bind (startToken_sre l ls _ _ _ _ _) fun a a' => ?_
        obtain ⟨a, ha⟩ := a
        obtain ⟨a', ha'⟩ := a'
        refine SimR.of_fact' (Er := ErS strict) fun (e : a = a') => ?_
        subst e
        dsimp only
        have := Lexer.Slice.le_runEnd input (index + 1) Lexer.RUN_SIMPLE_SYMBOL
        refine SimR.ite Iff.rfl (fun _ => ?_) fun _ => ?_
        · refine SimR.seq (extendContent_sre _ _ _ _ _) ?_
          refine SimR.seq (SimR.pre (fun s t h => h.1) (leavePending_sim _ _ _ _ _ _ _ _ _ hb
            _ _ _ _ _ _ _ _)) ?_
          exact SimR.pure fun s t h => ⟨rfl, h.1.1, h.2⟩
        · refine getCore_bind_P fun s t h => ?_
          simp only [throw_bind, fail_bind, failAt_bind]
          refine SimR.ite (by rw [h.1.1.tokenContent]; exact Iff.rfl) (fun _ => ?_) fun _ => ?_
          · exact SimR.seq (SimR.pre (fun s t h => h.1) (leave_sim _ _ _ _ _ _ _ hb _ _ _ _))
              (error_sim _ _ _ _ _)
          · refine SimR.ite Iff.rfl (fun _ => ?_) fun _ => ?_
            · exact SimR.seq (SimR.pre (fun s t h => h.1) (leave_sim _ _ _ _ _ _ _ hb _ _ _ _))
                (errorAt_sim _ _ _ _ _)
            · refine SimR.bind (pushBorrowed_sim hcons l ls b b' hb _ _ _ _ _ _ _ _ _ _ _ _ _)
                fun x y => ?_
              refine SimR.of_fact' (Er := ErS strict) fun hxy =>
                SimR.pre (P := SR0) (fun s t h => ⟨h.1.1, h.2⟩) ?_
              load_loop hxy
      · -- a numeral or a decimal
        refine LSim.of_sre fun l ls => SimR.bind (startToken_sre l ls _ _ _ _ _) fun a a' => ?_
        obtain ⟨a, ha⟩ := a
        obtain ⟨a', ha'⟩ := a'
        refine SimR.of_fact' (Er := ErS strict) fun (e : a = a') => ?_
        subst e
        dsimp only
        have := Lexer.Slice.le_runEnd input (index + 1) Lexer.RUN_DIGIT
        simp only [throw_bind, fail_bind, failAt_bind]
        refine SimR.ite Iff.rfl (fun _ => ?_) fun _ => ?_
        · exact SimR.seq (SimR.pre (fun s t h => h.1) (leave_sim _ _ _ _ _ _ _ hb _ _ _ _))
            (errorAt_sim _ _ _ _ _)
        split_both
        · rename_i next h1 next' h2
          obtain rfl : next = next' := Option.some.inj (h1.symm.trans h2)
          have := Lexer.Slice.lt_size_of_get? h1
          refine SimR.ite Iff.rfl (fun _ => ?_) fun _ => ?_
          · have := Lexer.Slice.le_runEnd input (runEnd input (index + 1) Lexer.RUN_DIGIT + 1)
              Lexer.RUN_DIGIT
            refine SimR.ite Iff.rfl (fun _ => ?_) fun _ => ?_
            · refine SimR.seq (extendContent_sre _ _ _ _ _) ?_
              refine SimR.seq (SimR.pre (fun s t h => h.1) (leavePending_sim _ _ _ _ _ _ _ _ _ hb
                _ _ _ _ _ _ _ _)) ?_
              exact SimR.pure fun s t h => ⟨rfl, h.1.1, h.2⟩
            · refine getCore_bind_P fun s t h => ?_
              refine SimR.ite (by rw [h.1.1.tokenContent]; exact Iff.rfl) (fun _ => ?_) fun _ => ?_
              · exact SimR.seq (SimR.pre (fun s t h => h.1) (leave_sim _ _ _ _ _ _ _ hb _ _ _ _))
                  (error_sim _ _ _ _ _)
              · refine SimR.ite Iff.rfl (fun _ => ?_) fun _ => ?_
                · exact SimR.seq (SimR.pre (fun s t h => h.1) (leave_sim _ _ _ _ _ _ _ hb _ _ _ _))
                    (errorAt_sim _ _ _ _ _)
                · refine SimR.bind (pushBorrowed_sim hcons l ls b b' hb _ _ _ _ _ _ _ _ _ _ _ _ _)
                    fun x y => ?_
                  refine SimR.of_fact' (Er := ErS strict) fun hxy =>
                    SimR.pre (P := SR0) (fun s t h => ⟨h.1.1, h.2⟩) ?_
                  load_loop hxy
          · refine SimR.ite Iff.rfl (fun _ => ?_) fun _ => ?_
            · exact SimR.seq (SimR.pre (fun s t h => h.1) (leave_sim _ _ _ _ _ _ _ hb _ _ _ _))
                (errorAt_sim _ _ _ _ _)
            · refine SimR.bind (pushBorrowed_sim hcons l ls b b' hb _ _ _ _ _ _ _ _ _ _ _ _ _)
                fun x y => ?_
              refine SimR.of_fact' (Er := ErS strict) fun hxy =>
                SimR.pre (P := SR0) (fun s t h => ⟨h.1.1, h.2⟩) ?_
              load_loop hxy
        · rename_i next h1 h2
          exact absurd (h1.symm.trans h2) (by simp)
        · rename_i h1 next h2
          exact absurd (h1.symm.trans h2) (by simp)
        · refine SimR.seq (extendContent_sre _ _ _ _ _) ?_
          refine SimR.seq (SimR.pre (fun s t h => h.1) (leavePending_sim _ _ _ _ _ _ _ _ _ hb
            _ _ _ _ _ _ _ _)) ?_
          exact SimR.pure fun s t h => ⟨rfl, h.1.1, h.2⟩
      all_goals
        -- an unexpected character
        refine LSim.of_sre fun l ls => ?_
        refine SimR.bind (startToken_sre _ _ _ _ _ _ _) fun _ _ => ?_
        refine SimR.seq (SimR.pre (fun s t h => h.2.1) (leave_sim _ _ _ _ _ _ _ hb _ _ _ _)) ?_
        exact errorAt_sim _ _ _ _ _

/-- The normal state, from states whose batches have the same array of contents: the loops take
the batches out of the states and run from `start`. -/
theorem lexNormal_sim (hcons : ConsumesAlike H m R E) (input : ByteSlice) (start : Nat)
    (hstart : start < input.size) :
    LSim true (H := H) (m := m) (R := R) (E := E) (floor := floor) (low := low) (SRb true)
      (fun a b s t => a.val = b.val ∧ SRb true s t)
      (Lexer.WRustPort.lexNormal input start hstart)
      (Lexer.X1BatchInCore.lexNormal input start hstart) := by
  unfold Lexer.WRustPort.lexNormal Lexer.X1BatchInCore.lexNormal
  refine SimR.bind (SimR.modifyGet (Q := fun a b s t => a.val.1 = b.val.1 ∧
    a.val.2.1 = b.val.2.1 ∧ HR a.val.2.2 b.val.2.2 ∧ SR0 s t) fun s t h => ?_) fun a b => ?_
  · obtain ⟨hst, hby⟩ := h
    exact ⟨hst.offset, hst.base, ⟨hst.batch, hby rfl, hst.capacity⟩,
      { hst with batch := agree_of_len_zero rfl rfl, capacity := zero_lt_capacity }, rfl⟩
  obtain ⟨⟨offset, base, batch⟩, hframe, hbatch, hfloor⟩ := a
  obtain ⟨⟨offset', base', batch'⟩, hframe', hbatch', hfloor'⟩ := b
  refine SimR.intro fun s₀ t₀ h₀ => ?_
  obtain ⟨e1, e2, hb, -⟩ := h₀
  dsimp only at e1 e2 hb
  subst e1 e2
  dsimp only
  refine load_bind_left fun s t h => ?_
  refine SimR.bind (SimR.pre (fun s' t' h' => ?_) (lexNormalFrom_sim hcons input _ start start
    (input.size - start) start batch batch' ⟨s.val.line, s.val.lineStart⟩ rfl hb _ _ _ _ _ _))
    fun x y => ?_
  · obtain ⟨rfl, rfl⟩ := h'
    obtain ⟨⟨-, -, -, h0⟩, -, -⟩ := h
    exact ⟨sr_srl h0.1, h0.2⟩
  · obtain ⟨x, hx⟩ := x
    obtain ⟨y, hy⟩ := y
    exact SimR.pure fun s t h => ⟨h.1, h.2⟩

end

end BSmtLib.Proofs.WRustPortX1BatchInCore
