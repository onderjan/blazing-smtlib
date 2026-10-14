module

public import BSmtLib.Facts.Proofs.Lexer.VNaiveWRustPort.StartWs
public import BSmtLib.Facts.Proofs.Lexer.VNaiveWRustPort.Tables
import all BSmtLib.Lexer.Internal.VNaive
import all BSmtLib.Lexer.Internal.WRustPort

@[expose] public section

/-!
# The normal state's invariant and the helpers of its proof

`NormalSpec`, what the loop of the Rust port's normal state keeps, and the lemmas that the steps
of its arms share.
-/

namespace BSmtLib.Facts.Proofs.Lexer.VNaiveWRustPort.Normal.Basic

open BSmtLib.Facts.Lexer.Adapters
open BSmtLibSpec.Lexer (Handed)
open BSmtLib.Lexer.Internal.WRustPort (lexNormalFrom FastState Frame Held Past)
open BSmtLib.Lexer.Internal.WRustPort.Slice (get? get)
open BSmtLib.Facts.Proofs.Lexer.Consumers.Pure BSmtLib.Facts.Proofs.Lexer.VNaive.Run
open BSmtLib.Facts.Proofs.Lexer.VNaiveWRustPort.Agree
open BSmtLib.Facts.Proofs.Lexer.VNaiveWRustPort.Batch
open BSmtLib.Facts.Proofs.Lexer.VNaiveWRustPort.Bytes
open BSmtLib.Facts.Proofs.Lexer.VNaiveWRustPort.Feed
open BSmtLib.Facts.Proofs.Lexer.VNaiveWRustPort.Model
open BSmtLib.Facts.Proofs.Lexer.VNaiveWRustPort.Step BSmtLib.Lexer.Internal.VNaive

/-- Takes the steps of the lexer that only read and change the lexer state, and throws. -/
-- Each step is tried first up to reducible unfolding, which fails at once on a program of
-- another shape, and only then up to the default unfolding, which can take long to fail.
macro "wp_walk" : tactic =>
  `(tactic| repeat (first
    | with_reducible apply WP.wp_throw
    | with_reducible apply WP.wp_modifyCore
    | with_reducible apply WP.wp_modifyBound
    | with_reducible apply WP.wp_getCore
    | with_reducible apply WP.wp_pure
    | with_reducible apply WP.wp_bind
    | apply WP.wp_throw
    | apply WP.wp_modifyCore
    | apply WP.wp_modifyBound
    | apply WP.wp_getCore
    | apply WP.wp_pure
    | apply WP.wp_bind))

section

variable {floor : Option Nat} {low : Nat}

variable {C : BSmtLibSpec.Lexer.Consumer} {hd : Bool} {iv : Token.Version}

theorem push_append' (a b : ByteArray) (c : UInt8) : (a ++ b).push c = a ++ b.push c := by
  apply ByteArray.ext
  simp only [ByteArray.data_push, ByteArray.data_append, Array.push_append]

/-- The content after a run and the byte that ends it. -/
theorem content_succ (input : ByteSlice) (content : ByteArray) {i j : Nat} (hij : i ≤ j)
    (hj : j < input.size) :
    content ++ (input.slice i (j + 1)).toByteArray =
      (content ++ bytesOf input i j).push input[j] := by
  rw [push_append']
  exact congrArg (content ++ ·) (bytesOf_push input hij hj)

/-- The line break that ends a comment the consumer takes is the last byte of its content. -/
theorem advance_comment_end_ws (start : Span.Location) (content : ByteArray)
    (location : Span.Location)
    {c : UInt8} (hc : isCommentRun c = false) :
    advance true ⟨.comment, start, content⟩ location c =
      .tokenWith ⟨.comment, content.push c, start, location.afterByte c⟩ := by
  simp only [isCommentRun, Bool.and_eq_false_iff, bne_eq_false_iff_eq] at hc
  rcases hc with h | h <;> subst h <;> rfl

theorem byteStep_token_with {v : Token.Version} {ws : Bool} {q : Pending} {location : Span.Location}
    {c : UInt8} {l : Lexeme} (h : advance ws q location c = .tokenWith l) :
    byteStepW v ws (.token q) location c = some (.idle, [l]) := by
  simp [byteStepW, h]

theorem answering_concrete : Token.Consume.isConcrete (H := Answering C) = C.concrete := rfl

theorem start_parenClose (v : Token.Version) (ws : Bool) (location : Span.Location) :
    start v ws location 41 =
      .token ⟨.parenClose, ByteArray.empty.push 41, location, location.afterByte 41⟩ := (rfl)

theorem start_parenOpen (v : Token.Version) (ws : Bool) (location : Span.Location) :
    start v ws location 40 =
      .token ⟨.parenOpen, ByteArray.empty.push 40, location, location.afterByte 40⟩ := (rfl)

/-- The rest of a step, from a later state whose outcome is that of the earlier one. -/
theorem wp_recurse {α : Type} {x : WP.M C floor low α} {f : α → Nat} {v : Token.Version}
    {input : ByteSlice} {st st1 : St} {location location1 : Span.Location} {start start1 : Nat}
    {ver ver1 : Token.Version} {coll coll1 : List Handed} {held held1 : List Lexeme}
    {s : WP.BS floor low}
    (h : WP x s coll1
      (fun r s' coll' =>
        StepPost C v hd iv input st1 location1 start1 ver1 coll1 held1 (f r) s'.val coll')
      (fun e s' coll' =>
        StepFails C v hd iv input st1 location1 start1 ver1 coll1 held1 e s'.val coll'))
    (heq : outcome C hd (pending C hd ver coll held)
        (feedFrom v C.concrete input st location start) =
      outcome C hd (pending C hd ver1 coll1 held1)
        (feedFrom v C.concrete input st1 location1 start1)) :
    WP x s coll1
      (fun r s' coll' => StepPost C v hd iv input st location start ver coll held
          (f r) s'.val coll')
      (fun e s' coll' => StepFails C v hd iv input st location start ver coll held e
          s'.val coll') :=
  WP.wp_mono h (fun _ _ _ hp => StepPost.trans heq hp) (fun _ _ _ hf => StepFails.trans heq hf)

/-- A step from a state with the same value. -/
theorem wp_state_congr {α : Type} {x : WP.M C floor low α} {s s' : WP.BS floor low}
    {coll : List Handed} {Q : α → WP.BS floor low → List Handed → Prop}
    {QE : WP.Intr C floor → WP.BS floor low → List Handed → Prop}
    (h : s'.val = s.val) (hw : WP x s coll Q QE) : WP x s' coll Q QE := by
  have : s' = s := Subtype.ext h
  subst this
  exact hw

/-- Writing the loop's copies of the line back, which are the lexer state's. -/
theorem wp_store {β : Type} {locals : FastState} {s : WP.BS floor low} {coll : List Handed}
    {f : Unit → WP.M C floor low β} {Q : β → WP.BS floor low → List Handed → Prop}
    {QE : WP.Intr C floor → WP.BS floor low → List Handed → Prop}
    (h1 : locals.line = s.val.line) (h2 : locals.lineStart = s.val.lineStart)
    (h : WP (f ()) s coll Q QE) :
    WP (Lexer.Internal.WRustPort.Ops.storeLocals (H := Answering C) (m := AnswerM) (R := C.Result)
      (E := Option C.Error) locals >>= f) s coll Q QE := by
  apply WP.wp_bind
  rw [WP.rust_storeLocals]; unfold FastState.store
  apply WP.wp_modifyCore
  refine wp_state_congr ?_ h
  show { s.val with line := locals.line, lineStart := locals.lineStart } = s.val
  rw [h1, h2]

/-- What the loop of the normal state keeps, from the index `index`: if the lexer state is in
the normal state at `location`, with the loop's copies of its offset, index of the offset and
line, and the loop holds a batch of lexemes, then the loop keeps the correspondence. -/
def NormalSpec (C : BSmtLibSpec.Lexer.Consumer) (v : Token.Version) (hd : Bool) (iv : Token.Version)
    (input : ByteSlice) (offset base : Nat)
    (hframe : Frame floor low offset) (index : Nat) : Prop :=
  ∀ (batch : Token.TokenBatch) (locals : FastState) (hindex : base ≤ index)
    (hbatch : Held floor offset base index batch) (origin : Nat) (horigin : origin ≤ index)
    (s : WP.BS floor low) (coll : List Handed) (held : List Lexeme) (location : Span.Location),
    Fixed v hd iv s.val → offset = s.val.offset → base = s.val.base → locals.line = s.val.line →
    locals.lineStart = s.val.lineStart → s.val.state = .normal →
    LocAt s.val offset base index location → Holds batch held → batch.bytes = input.byteArray →
    WP (lexNormalFrom (H := Answering C) (m := AnswerM) (R := C.Result) (E := Option C.Error)
        input offset base index batch locals hframe hindex hbatch origin horigin) s coll
      (fun r s' coll' =>
        StepPost C v hd iv input .idle location index s.val.version coll held r.1 s'.val coll')
      (fun e s' coll' =>
        StepFails C v hd iv input .idle location index s.val.version coll held e s'.val coll')

end

end BSmtLib.Facts.Proofs.Lexer.VNaiveWRustPort.Normal.Basic
