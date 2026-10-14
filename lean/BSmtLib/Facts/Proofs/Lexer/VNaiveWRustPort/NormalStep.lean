module

public import BSmtLib.Facts.Proofs.Lexer.VNaiveWRustPort.Normal
import all BSmtLib.Lexer.Internal.WRustPort

@[expose] public section

/-!
# The Rust port's step in the normal state

`lexNormal_wp`: the step of the normal state, which takes the batch out of the lexer state and
runs the loop `lexNormalFrom` from the lexer's index, keeps the correspondence with the naive
lexer's pure run.
-/

namespace BSmtLib.Facts.Proofs.Lexer.VNaiveWRustPort.NormalStep

open BSmtLib.Facts.Lexer.Adapters
open BSmtLibSpec.Lexer (Handed)
open BSmtLib.Lexer.Internal.WRustPort (lexNormalFrom FastState Frame Held Past)
open BSmtLib.Facts.Proofs.Lexer.VNaiveWRustPort.Normal
open BSmtLib.Facts.Proofs.Lexer.VNaiveWRustPort.Normal.Basic
open BSmtLib.Facts.Proofs.Lexer.VNaiveWRustPort.Step BSmtLib.Lexer.Internal.VNaive

section

variable {floor : Option Nat} {low : Nat}
variable {C : BSmtLibSpec.Lexer.Consumer} {hd : Bool} {iv : Token.Version}

/-- The loop of the normal state keeps the correspondence. -/
theorem lexNormalFrom_wp (v : Token.Version) (input : ByteSlice) (offset base : Nat)
    (hframe : Frame floor low offset) (index : Nat) :
    NormalSpec C v hd iv input offset base hframe index :=
  normalSpec_lt (C := C) (hd := hd) (iv := iv) v input offset base hframe _ index
      (Nat.lt_succ_self _)

/-- The step of the normal state keeps the correspondence. -/
theorem lexNormal_wp (v : Token.Version) (input : ByteSlice) (start : Nat)
    (hstart : start < input.size) (s : WP.BS floor low) (coll : List Handed)
    (location : Span.Location)
    (held : List Lexeme) (hpre : StepPre C v hd iv input .idle location held start s.val) :
    WP (Lexer.Internal.WRustPort.lexNormal (H := Answering C) (m := AnswerM) (R := C.Result)
        (E := Option C.Error) input start
        hstart) s coll
      (fun r s' coll' => StepPost C v hd iv input .idle location start s.val.version coll held
          r.1 s'.val coll')
      (fun e s' coll' => StepFails C v hd iv input .idle location start s.val.version coll held e
          s'.val coll') := by
  obtain ⟨hfix, hbase, hagree, hloc, hholds, hbytes⟩ := hpre
  unfold Lexer.Internal.WRustPort.lexNormal
  rw [WP.rust_loadLocals]
  unfold FastState.load
  apply WP.wp_bind; apply WP.wp_modifyGetThe
  dsimp only
  split
  rename_i offset base batch hframe hb' hfl heq
  have he := congrArg Subtype.val heq
  simp only [Prod.mk.injEq] at he
  obtain ⟨rfl, rfl, rfl⟩ := he
  apply WP.wp_bind; apply WP.wp_bind; apply WP.wp_getCore; apply WP.wp_pure
  apply WP.wp_bind
  refine WP.wp_mono (lexNormalFrom_wp (C := C) (hd := hd)
      (iv := iv) v input _ start _ start _ _ _ _ _
      _ _ coll held location
    ⟨hfix.1, hfix.2, hfix.3, hfix.4, hfix.5, hfix.6⟩ ?_ (hbase.symm) rfl rfl hagree ?_
        hholds hbytes) ?_ ?_
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

end BSmtLib.Facts.Proofs.Lexer.VNaiveWRustPort.NormalStep
