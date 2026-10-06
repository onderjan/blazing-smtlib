import BSmtLib.Proofs.V1NaiveWRustPort.Normal

/-!
# The Rust port's step in the normal state

`lexNormal_wp`: the step of the normal state, which takes the batch out of the lexer state and
runs the loop `lexNormalFrom` from the lexer's index, keeps the correspondence with the naive
lexer's pure run.
-/

namespace BSmtLib.Proofs.Lexer.V1NaiveWRustPort

open BSmtLib.Proofs.Adapter V1Naive BSmtLib.Proofs.Simulation
open Lexer.WRustPort (lexNormalFrom FastState Frame Held Past)

section

variable {floor : Option Nat} {low : Nat}

/-- The loop of the normal state keeps the correspondence. -/
theorem lexNormalFrom_wp (v : Version) (input : ByteSlice) (offset base : Nat)
    (hframe : Frame floor low offset) (index : Nat) :
    NormalSpec v input offset base hframe index :=
  normalSpec_lt v input offset base hframe _ index (Nat.lt_succ_self _)

/-- The step of the normal state keeps the correspondence. -/
theorem lexNormal_wp (v : Version) (input : ByteSlice) (start : Nat)
    (hstart : start < input.size) (s : BS floor low) (coll : Collector) (location : Location)
    (held : List Lexeme) (hpre : StepPre v input .idle location held start s.val) :
    WP (Lexer.WRustPort.lexNormal (H := Collector) (m := Id) (R := Empty) (E := Unit) input start
        hstart) s coll
      (fun r s' coll' => StepPost v input .idle location start coll held r.1 s'.val coll')
      (fun _ _ _ => StepFails v input .idle location start coll held) := by
  obtain ⟨hfix, hbase, hagree, hloc, hholds, hbytes⟩ := hpre
  unfold Lexer.WRustPort.lexNormal
  rw [rust_loadLocals]
  unfold FastState.load
  apply wp_bind; apply wp_modifyGetThe
  dsimp only
  split
  rename_i offset base batch hframe hb' hfl heq
  have he := congrArg Subtype.val heq
  simp only [Prod.mk.injEq] at he
  obtain ⟨rfl, rfl, rfl⟩ := he
  apply wp_bind; apply wp_bind; apply wp_getCore; apply wp_pure
  apply wp_bind
  refine wp_mono (lexNormalFrom_wp v input _ start _ start _ _ _ _ _ _ _ coll held location
    ⟨hfix.1, hfix.2, hfix.3, hfix.4⟩ ?_ (hbase.symm) rfl rfl hagree ?_ hholds hbytes) ?_ ?_
  · show s.val.offset + (start - s.val.base) = s.val.offset
    omega
  · obtain ⟨h1, h2, h3⟩ := hloc
    refine ⟨?_, h2, h3⟩
    show location.offset = s.val.offset + (start - s.val.base) + (start - start)
    omega
  · intro a s' coll' hp
    obtain ⟨next, hnext⟩ := a
    exact hp
  · intro e s' coll' hf
    exact hf

end

end BSmtLib.Proofs.Lexer.V1NaiveWRustPort
