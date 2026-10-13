import BSmtLib.Proofs.VNaiveWRustPort.ArmsWs
import BSmtLib.Proofs.VNaiveWRustPort.ArmsStrings

/-!
# A step of the Rust port's loop over a slice

`lexStep_wp`: the step `lexStep` keeps the correspondence with the naive lexer's pure run
(`StepPre` to `StepPost`, or `StepFails`), in every state of the lexer: the normal state by
`lexNormal_wp`, a token in progress by its arm followed by `afterStep_wp`. The state
`whitespace` is never reached, as the adapter's consumer does not take whitespace.
-/

namespace BSmtLib.Proofs.Lexer.VNaiveWRustPort

open BSmtLib.Proofs.Adapter VNaive BSmtLib.Proofs.Simulation
open Spec.Lexer (Handed)

section

variable {floor : Option Nat} {low : Nat}
variable {C : Spec.Lexer.Consumer} {hd : Bool} {iv : Version}

/-- The naive lexer's pure state that agrees with a lexer state other than the normal one is a
token in progress. -/
theorem token_of_agrees {v : Version} {st : St} {c : WCore} (h : StAgrees v C.concrete st c)
    (hn : c.state ≠ .normal) : ∃ p, st = .token p := by
  cases st with
  | idle => exact absurd h hn
  | token p => exact ⟨p, rfl⟩

set_option hygiene false in
/-- The step for a token in progress: its arm `arm`, then `afterStep`. -/
local macro "token_arm" arm:term : tactic => `(tactic| (
  obtain ⟨p, rfl⟩ := token_of_agrees hpre.agrees (by rw [hstate]; nofun)
  unfold Lexer.WRustPort.lexStep
  exact afterStep_wp v input start hstart s coll _ location held _ $arm))

/-- A step of the loop over a slice keeps the correspondence with the naive lexer. -/
theorem lexStep_wp (v : Version) (input : ByteSlice) (start : Nat)
    (hstart : start < input.size) (state : Lexer.LexerState) (tokenStart : Location)
    (base : Nat) (hpending : state = .normal ∨ Lexer.WRustPort.Started floor low tokenStart)
    (s : BS floor low) (coll : List Handed) (st : St) (location : Location) (held : List Lexeme)
    (hpre : StepPre C v hd iv input st location held start s.val) (hlow : low = s.val.offset)
    (hstate : s.val.state = state) (hts : s.val.tokenStart = tokenStart)
    (hb : base = s.val.base) :
    WP (Lexer.WRustPort.lexStep (H := Answering C) (m := AnswerM) (R := C.Result)
        (E := Option C.Error) input start
        hstart state tokenStart base hpending) s coll
      (fun r s' coll' => StepPost C v hd iv input st location start s.val.version coll held
          r.1 s'.val coll')
      (fun e s' coll' => StepFails C v hd iv input st location start s.val.version coll held e
          s'.val coll') := by
  have hts' := hts.symm
  cases state with
  | normal =>
    have hidle : st = .idle := by
      cases st with
      | idle => rfl
      | token p => exact (token_agrees hpre.agrees hstate).2.elim
    subst hidle
    exact lexNormal_wp v input start hstart s coll location held hpre
  | whitespace =>
    token_arm (arm_whitespace v input start hstart tokenStart base _ s coll p location held hpre
      hlow hts' hb hstate)
  | numeralOrDecimal =>
    token_arm (arm_numeralOrDecimal v input start hstart tokenStart base _ s coll p location held
      hpre hlow hts' hb hstate)
  | fraction =>
    token_arm (fractionFrom_wp (hd := hd) (iv := iv) v input start (Nat.le_of_lt hstart) start
        hstart (Nat.le_refl _)
      tokenStart base _ s coll (.token p) location held p location hpre.fixed hpre.base
      hpre.holds hpre.bytes hpre.loc hlow hb (token_agrees hpre.agrees hstate).2.1
      ((token_agrees hpre.agrees hstate).1.trans hts) (token_agrees hpre.agrees hstate).2.2
      (token_fits hpre.agrees) rfl)
  | baseSelection =>
    token_arm (arm_baseSelection v input start hstart tokenStart _ s coll p location held hpre
      hts' hstate)
  | hexadecimal =>
    token_arm (arm_digitRun v input start hstart tokenStart base _ s coll p location held hpre hlow
      hts' hb _ .hexadecimal (fun c => endsRun_hex c) rfl
      (fun st content q h => by rw [hstate] at h; exact ⟨h.1, h.2.1, h.2.2⟩) nofun
      (fun q st content hm hs hc => by rw [hstate]; exact ⟨hs, hm, hc⟩))
  | binary =>
    token_arm (arm_digitRun v input start hstart tokenStart base _ s coll p location held hpre hlow
      hts' hb _ .binary (fun c => endsRun_binary c) rfl
      (fun st content q h => by rw [hstate] at h; exact ⟨h.1, h.2.1, h.2.2⟩) nofun
      (fun q st content hm hs hc => by rw [hstate]; exact ⟨hs, hm, hc⟩))
  | stringLiteral =>
    token_arm (arm_stringLiteral v input start hstart tokenStart base _ s coll p location held hpre
      hlow hts' hb (.inl hstate))
  | stringLiteralDoubleQuote =>
    token_arm (arm_stringLiteral v input start hstart tokenStart base _ s coll p location held hpre
      hlow hts' hb (.inr (.inl hstate)))
  | stringLiteralBackslashEscape =>
    token_arm (arm_stringLiteral v input start hstart tokenStart base _ s coll p location held hpre
      hlow hts' hb (.inr (.inr hstate)))
  | simpleSymbol =>
    token_arm (arm_simpleSymbol v input start hstart tokenStart base _ s coll p location held hpre
      hlow hts' hb hstate)
  | quotedSymbol =>
    token_arm (arm_quotedSymbol v input start hstart tokenStart base _ s coll p location held hpre
      hlow hts' hb hstate)
  | keyword =>
    token_arm (arm_keyword v input start hstart tokenStart base _ s coll p location held hpre hlow
      hts' hb hstate)
  | comment =>
    token_arm (arm_comment v input start hstart tokenStart base _ s coll p location held hpre
      hlow hts' hb
      hstate)
  | quotedSymbolClosed =>
    token_arm (arm_quotedSymbolClosed v input start hstart tokenStart base _ s coll p location held
      hpre hlow hts' hb hstate)

end

end BSmtLib.Proofs.Lexer.VNaiveWRustPort
