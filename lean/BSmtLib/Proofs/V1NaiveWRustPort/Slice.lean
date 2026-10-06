import BSmtLib.Proofs.V1NaiveWRustPort.Eof

/-!
# The Rust port's loop over a slice

`sliceRun_ok`: the loop `lexSliceRun` over a slice, from a lexer state that is the naive
lexer's pure state at an index, with a batch that holds lexemes, hands over what the naive
lexer's run from there finishes: it ends with the batch handed over, in the pure state at the
end of the slice, or fails if the run fails or the consumer fails on a lexeme. It is proved by
induction on the bytes left, with `lexStep_wp` for each step; after an error the loop hands
over the batch as it was left, and the hand-over is done or fails (`flushBatch_noStop`), so the
loop fails (`sliceRun_error`).
-/

namespace BSmtLib.Proofs.Lexer.V1NaiveWRustPort

open BSmtLib.Proofs.Adapter V1Naive BSmtLib.Proofs.Simulation

section

variable {floor : Option Nat}

/-- Running a call of the consumer's monad. -/
theorem run_bindS {α β : Type} (x : StateT Collector Id α) (k : α → StateT Collector Id β)
    (coll : Collector) : (x >>= k).run coll = (k (x.run coll).1).run (x.run coll).2 := rfl

/-- The loop over a slice after an error fails. -/
theorem sliceRun_error (input : ByteSlice) (position : Nat) (f : Lexer.Failure Unit)
    (core : BS floor 0) (coll : Collector) :
    ∃ g, ((Lexer.WRustPort.lexSliceRun (H := Collector) (m := Id) (R := Empty) (E := Unit)
      input position (.error f) core).run coll).1.1 = .done (.error g) := by
  rw [Lexer.WRustPort.lexSliceRun]
  rw [dite_eq_left_of_eq_true (eq_true (by simp))]
  rw [run_step]
  have hw := flushBatch_noStop core coll
  unfold WP at hw
  generalize runM Lexer.WRustPort.Rust.flushBatch core coll = r at hw ⊢
  obtain ⟨⟨res, c'⟩, coll'⟩ := r
  cases res with
  | ok u => exact ⟨f, rfl⟩
  | error e =>
    obtain ⟨⟨cause, hc⟩, -⟩ := hw
    obtain ⟨result, location, stopAfter⟩ := e
    simp only at hc
    subst hc
    exact ⟨_, rfl⟩

/-- What the loop over a slice from the naive lexer's pure state `st` at `location` at the
index `position`, with the consumer `coll` and the lexemes `held` in the batch, ends with. -/
def SliceOut (v : Version) (input : ByteSlice) (st : St) (location : Location) (position : Nat)
    (coll : Collector) (held : List Lexeme)
    (r : (Lexer.WRustPort.SliceExit Empty Unit floor × BS floor 0) × Collector) : Prop :=
  match outcome v (pending v coll held) (feedFrom v input st location position) with
  | some (st', location', hs) =>
    r.1.1 = .done (.ok .continue) ∧ Fixed v r.1.2.val ∧ StAgrees v st' r.1.2.val ∧
      EofLoc r.1.2.val location' ∧ r.2.handed = hs
  | none => ∃ g, r.1.1 = .done (.error g)

theorem sliceRun_ok (v : Version) (input : ByteSlice) :
    ∀ (n position : Nat), input.size - position < n →
    ∀ (core : BS floor 0) (coll : Collector) (st : St) (location : Location)
      (held : List Lexeme), StepPre v input st location held position core.val →
      SliceOut v input st location position coll held
        ((Lexer.WRustPort.lexSliceRun (H := Collector) (m := Id) (R := Empty) (E := Unit)
          input position (.ok .continue) core).run coll) := by
  intro n
  induction n with
  | zero => intro position hn; omega
  | succ n ih =>
  intro position hn core coll st location held hpre
  rw [Lexer.WRustPort.lexSliceRun]
  by_cases hp : position < input.size
  · rw [dite_eq_right_of_eq_false (eq_false (by simp; omega))]
    extract_lets hposition offset hpending step
    rw [run_step]
    have hw := lexStep_wp v input position hposition core.val.state core.val.tokenStart
      core.val.base hpending ⟨core.val, ⟨Nat.le_refl _, core.property.2⟩⟩ coll st location held
      hpre rfl rfl rfl rfl
    unfold WP at hw
    generalize runM step ⟨core.val, ⟨Nat.le_refl _, core.property.2⟩⟩ coll = r at hw ⊢
    obtain ⟨⟨res, c'⟩, coll'⟩ := r
    cases res with
    | ok nx =>
      obtain ⟨next, hnext⟩ := nx
      obtain ⟨st', location', held', hfix, hb, hagree, hloc, hholds, hbytes, heq⟩ := hw
      unfold SliceOut
      rw [heq]
      refine ih next (by omega) _ coll' st' location' held'
        ⟨⟨hfix.1, hfix.2, hfix.3, hfix.4⟩, rfl, by cases st' <;> exact hagree, ?_, hholds,
          hbytes⟩
      obtain ⟨h1, h2, h3⟩ := hloc
      dsimp only at h1 hb
      refine ⟨?_, h2, h3⟩
      show location'.offset = c'.val.offset + (next - c'.val.base) + (next - next)
      omega
    | error e =>
      obtain ⟨⟨cause, hc⟩, hf⟩ := hw
      unfold SliceOut
      rw [show outcome v (pending v coll held) (feedFrom v input st location position) = none
        from hf]
      obtain ⟨result, location, stopAfter⟩ := e
      simp only at hc
      subst hc
      exact sliceRun_error input position _ _ coll'
  · rw [dite_eq_left_of_eq_true (eq_true (by simp; omega))]
    rw [run_step]
    have hw := flushBatch_wp v held core hpre.holds coll hpre.fixed.recovers hpre.fixed.version
      (Q := fun _ s' coll' => key s'.val = key core.val ∧ pending v coll' [] = pending v coll held)
      (QE := fun _ _ _ => pending v coll held = none)
      (fun s' coll' hk _ hc => ⟨hk, hc⟩) (fun hn _ _ _ => hn)
    unfold WP at hw
    generalize runM Lexer.WRustPort.Rust.flushBatch core coll = r at hw ⊢
    obtain ⟨⟨res, c'⟩, coll'⟩ := r
    unfold SliceOut
    rw [feedFrom_ge hp]
    cases res with
    | ok u =>
      obtain ⟨hk, hc⟩ := hw
      rw [pending_nil] at hc
      rw [← hc]
      simp only [outcome, Option.bind_some, handedAll, List.mapM_nil]
      obtain ⟨k1, k2, k3, k4, k5, k6, k7, k8, k9, k10, k11⟩ := key_fields hk
      refine ⟨rfl, fixed_of_key hpre.fixed hk, stAgrees_of_key hpre.agrees hk, ?_,
        (List.append_nil _).symm⟩
      obtain ⟨h1, h2, h3⟩ := hpre.loc
      show location.offset = c'.val.offset ∧ location.line = c'.val.line ∧
        c'.val.lineStart + location.column = location.offset
      refine ⟨?_, by rw [k10]; exact h2, by rw [k11]; exact h3⟩
      rw [k8, h1, hpre.base]
      omega
    | error e =>
      obtain ⟨⟨cause, hc⟩, hn⟩ := hw
      rw [show pending v coll held = none from hn]
      obtain ⟨result, location, stopAfter⟩ := e
      simp only at hc
      subst hc
      exact ⟨_, rfl⟩

end

end BSmtLib.Proofs.Lexer.V1NaiveWRustPort
