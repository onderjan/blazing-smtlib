module

public import BSmtLib.Facts.Proofs.Reader.Lexes.Told
import all BSmtLib.Lexer
import all BSmtLib.Lexer.Internal.VNaive
import all BSmtLib.Lexer.Internal.WRustPort
import all BSmtLib.Span

@[expose] public section

/-!
# The library's lexer hands no whitespace or comment to a consumer that does not take them

`noLayout`: from every state the library's lexer reaches with the adapter's consumer
(`Param.Reach`), it never fails with the adapter's error `none` for a consumer that does not take
whitespace and comments.

From every such state, there are states of the lexer with the batch kept in its state, of the
Rust port and of the naive lexer that correspond to it as the chain of lexers relates them
(`ZOK`):
- the library's lexer and the lexer with the batch kept in its state give the same results
  (`X1BatchInCoreLexer.step_fit`, `X1BatchInCoreLexer.run_lexEofStep`);
- so do that lexer and the Rust port (`WRustPortX1BatchInCore.slice_alike`,
  `WRustPortX1BatchInCore.eof_alike`);
- the Rust port, from a state that is the naive lexer's, never fails with the adapter's error
  `none` for such a consumer (`VNaiveWRustPort.slice_step_noNone`,
  `VNaiveWRustPort.eof_step_noNone`).
-/

namespace BSmtLib.Facts.Proofs.Reader.Lexes.NoLayout

open BSmtLib.Facts.Lexer.Adapters (Answering AnswerM LexOps)
open BSmtLibSpec.Lexer (Handed)
open BSmtLib.Facts.Proofs.Reader.Lexes.Told

/-- The states of the library's lexer that the chain of lexers relates to a state of the naive
lexer: a state of the lexer with the batch kept in its state that corresponds to it, one of the
Rust port that corresponds to that, and one of the naive lexer that corresponds to that. -/
def ZOK (C : BSmtLibSpec.Lexer.Consumer) (c : BSmtLib.Lexer.Internal.LexerCore) : Prop :=
  ∃ (x : Lexer.Adapters.X1BatchInCore.lexOps.Lexer C)
    (w : Lexer.Adapters.WRustPort.lexOps.Lexer C) (n : Lexer.Internal.VNaive.Core),
    Lexer.X1BatchInCoreLexer.Outer.Rel c x.core ∧ Lexer.WRustPortX1BatchInCore.Calls.LexRel w x ∧
      Lexer.VNaiveWRustPort.Calls.CR C w.core n

section

variable {C : BSmtLibSpec.Lexer.Consumer}

theorem answering_unique (a b : Answering C) : a = b := by
  cases a; cases b; rfl

/-- The lexer of the adapter's consumer with the Rust port's state, as the steps of
`VNaiveWRustPort` take it. -/
theorem wLexer_eq (w : Lexer.Adapters.WRustPort.lexOps.Lexer C) :
    w = ⟨{}, w.core, w.held⟩ := by
  obtain ⟨h, c, d⟩ := w
  rw [answering_unique h {}]

/-- A call on a slice that ends below `USize.size`, from a state that the chain relates: it does
not fail with the adapter's error `none` for a consumer that does not take whitespace and
comments, and where it does not fail, the chain relates the state after it. -/
theorem zok_fit (hc : C.concrete = false) {c : BSmtLib.Lexer.Internal.LexerCore} (hz : ZOK C c)
    (l : Lexer.Adapters.Lexer.lexOps.Lexer C) (hl : Lexer.Internal.core l = c)
    (bytes : BSmtLibSpec.Regex.Chars)
    (hs : bytes.toByteArray.toByteSlice.stop < USize.size) (taken : List Handed) :
    (∀ e, ((Lexer.Adapters.Lexer.lexOps.lexSliceStep l bytes.toByteArray.toByteSlice).run
        taken).1.1 = .error e → e.cause ≠ .consumer none) ∧
      (∀ r, ((Lexer.Adapters.Lexer.lexOps.lexSliceStep l bytes.toByteArray.toByteSlice).run
        taken).1.1 = .ok r →
        ZOK C (Lexer.Internal.core ((Lexer.Adapters.Lexer.lexOps.lexSliceStep l
          bytes.toByteArray.toByteSlice).run taken).1.2)) := by
  obtain ⟨x, w, n, hx, hw, hcr⟩ := hz
  have hL : Lexer.Consumers.ChainZ.LooseRel l x :=
    ⟨answering_unique _ _, by rw [hl]; exact hx⟩
  obtain ⟨e1, e2, -⟩ := Lexer.Consumers.ChainZ.step_fit l x hL _ hs taken
  obtain ⟨f1, f2, -⟩ := Lexer.Consumers.ChainX1.slice_alike C
    bytes.toByteArray.toByteSlice w x taken hw
  have hW := Lexer.VNaiveWRustPort.Calls.lexOps_lexSliceStepW (C := C) w.core w.held
    bytes.toByteArray.toByteSlice taken
  rw [← wLexer_eq w] at hW
  have hcall := Lexer.VNaiveWRustPort.Calls.slice_step w.core n bytes taken hcr
  have hnn := Lexer.VNaiveWRustPort.Calls.slice_step_noNone w.core n bytes taken hcr hc
  generalize (Lexer.Adapters.Lexer.lexOps.lexSliceStep l bytes.toByteArray.toByteSlice).run
    taken = Z at e1 e2 ⊢
  generalize (Lexer.Adapters.X1BatchInCore.lexOps.lexSliceStep x
    bytes.toByteArray.toByteSlice).run taken = X at e1 e2 f1 f2
  generalize (Lexer.Adapters.WRustPort.lexOps.lexSliceStep w
    bytes.toByteArray.toByteSlice).run taken = W at f1 f2 hW
  generalize Lexer.VNaiveWRustPort.Eof.runIA (Lexer.Internal.WRustPort.lexSliceStep
    (ops := Lexer.Internal.WRustPort.Rust.ops)
    (H := Answering C) (m := AnswerM) (R := C.Result) (E := Option C.Error) (fun _ => pure ())
    (fun _ => pure ()) bytes.toByteArray.toByteSlice) w.core taken = R at hW hcall hnn
  obtain ⟨⟨rz, lz⟩, tz⟩ := Z
  obtain ⟨⟨rx, lx⟩, tx⟩ := X
  obtain ⟨⟨rw, lw⟩, tw⟩ := W
  obtain ⟨⟨rr, cr⟩, tr⟩ := R
  simp only at e1 e2 f1 f2 hW hcall hnn
  obtain ⟨⟨rfl, rfl⟩, rfl⟩ := hW
  subst e1 f1
  obtain ⟨-, -, -, hok, -, -⟩ := hcall
  refine ⟨fun e he => hnn e he, fun r hr => ?_⟩
  subst hr
  exact ⟨lx, _, _, e2.2, f2, hok rfl⟩

/-- The chunks of a slice too large for the positions of the library's lexer, from a state that
the chain relates: no failure with the adapter's error `none`, and where the chunks do not fail,
the chain relates the state after them. -/
theorem zok_chunks (hc : C.concrete = false) (s : BSmtLibSpec.Regex.Chars) (p : Nat) :
    ∀ (acc : Option (Span.Located C.Result)) (l : Lexer.Adapters.Lexer.lexOps.Lexer C)
      (t : List Handed), ZOK C (Lexer.Internal.core l) →
      ∀ r (l' : Lexer.Adapters.Lexer.lexOps.Lexer C) t',
        (Lexer.Internal.run l (Lexer.Internal.lexChunks
            (Lexer.Recovery.LexerRecovery.abandon Lexer.Recovery.FailFast)
          (Lexer.Recovery.LexerRecovery.recover Lexer.Recovery.FailFast) s.toByteArray.toByteSlice p
              acc)).run t =
          ((r, l'), t') →
        (∀ e, r = .error e → e.cause ≠ .consumer none) ∧
          (∀ h, r = .ok h → ZOK C (Lexer.Internal.core l')) := by
  fun_induction Lexer.X1BatchInCoreLexer.Chunks.chunksFrom s p with
  | case1 p hp ih =>
    intro acc l t hz r l' t' hrun
    rw [Lexer.Consumers.ChainZ.run_lexChunks_lt l s p hp acc, StateT.run_bind] at hrun
    obtain ⟨n1, n2⟩ := zok_fit hc hz l rfl (Lexer.X1BatchInCoreLexer.Chunks.chunkAt s p)
      (Lexer.X1BatchInCoreLexer.Chunks.chunk_stop_lt s p) t
    generalize (Lexer.Adapters.Lexer.lexOps.lexSliceStep l
      (Lexer.X1BatchInCoreLexer.Chunks.chunkAt s p).toByteArray.toByteSlice).run t = A
      at n1 n2 hrun
    obtain ⟨⟨ra, la⟩, ta⟩ := A
    cases ra with
    | error err =>
      change ((Except.error err, la), ta) = ((r, l'), t') at hrun
      obtain ⟨h12, -⟩ := Prod.mk.inj hrun
      obtain ⟨h1, -⟩ := Prod.mk.inj h12
      subst h1
      refine ⟨fun e he => ?_, fun h he => by cases he⟩
      cases he
      exact n1 err rfl
    | ok ch => exact ih (ch.or acc) la ta (n2 ch rfl) r l' t' hrun
  | case2 p hp =>
    intro acc l t hz r l' t' hrun
    rw [Lexer.Consumers.ChainZ.run_lexChunks_ge l s p hp acc] at hrun
    change ((Except.ok acc, l), t) = ((r, l'), t') at hrun
    simp only [Prod.mk.injEq] at hrun
    obtain ⟨⟨rfl, rfl⟩, rfl⟩ := hrun
    exact ⟨fun e he => (nomatch he), fun _ _ => hz⟩

/-- A call on a slice, from a state that the chain relates: no failure with the adapter's error
`none`, and where the call does not fail, the chain relates the state after it. -/
theorem zok_slice (hc : C.concrete = false) {c : BSmtLib.Lexer.Internal.LexerCore} (hz : ZOK C c)
    (l : Lexer.Adapters.Lexer.lexOps.Lexer C) (hl : Lexer.Internal.core l = c)
    (bytes : BSmtLibSpec.Regex.Chars)
    (taken : List Handed) :
    (∀ e, ((Lexer.Adapters.Lexer.lexOps.lexSliceStep l bytes.toByteArray.toByteSlice).run
        taken).1.1 = .error e → e.cause ≠ .consumer none) ∧
      (∀ r, ((Lexer.Adapters.Lexer.lexOps.lexSliceStep l bytes.toByteArray.toByteSlice).run
        taken).1.1 = .ok r →
        ZOK C (Lexer.Internal.core ((Lexer.Adapters.Lexer.lexOps.lexSliceStep l
          bytes.toByteArray.toByteSlice).run taken).1.2)) := by
  by_cases hs : bytes.length < USize.size
  · exact zok_fit hc hz l hl bytes (Lexer.X1BatchInCoreLexer.Handed.stop_toByteSlice_lt hs) taken
  · have hs' : ¬ bytes.toByteArray.toByteSlice.stop < USize.size := by
      rw [Lexer.X1BatchInCoreLexer.Chunks.stop_toByteSlice, List.size_toByteArray]
      exact hs
    have hz' : (Lexer.Internal.run l (Lexer.Internal.lexChunks
        (Lexer.Recovery.LexerRecovery.abandon Lexer.Recovery.FailFast)
        (Lexer.Recovery.LexerRecovery.recover Lexer.Recovery.FailFast) bytes.toByteArray.toByteSlice
            0 none)).run
          taken =
        (Lexer.Adapters.Lexer.lexOps.lexSliceStep l bytes.toByteArray.toByteSlice).run taken := by
      show _ = (Lexer.Internal.run l (Lexer.Internal.lexSliceStep _ _ _)).run taken
      unfold Lexer.Internal.lexSliceStep
      rw [dite_eq_right_of_eq_false (eq_false hs')]
    generalize (Lexer.Adapters.Lexer.lexOps.lexSliceStep l bytes.toByteArray.toByteSlice).run
      taken = R at hz' ⊢
    obtain ⟨⟨r, l'⟩, t'⟩ := R
    obtain ⟨h1, h2⟩ := zok_chunks hc bytes 0 none l taken (by rw [hl]; exact hz) r l' t' hz'
    exact ⟨fun e he => h1 e he, fun h he => h2 h he⟩

/-- The end of the input, from a state that the chain relates: no failure with the adapter's
error `none`. -/
theorem zok_eof (hc : C.concrete = false) {c : BSmtLib.Lexer.Internal.LexerCore} (hz : ZOK C c)
    (l : Lexer.Adapters.Lexer.lexOps.Lexer C) (hl : Lexer.Internal.core l = c)
    (taken : List Handed) :
    ∀ e, ((Lexer.Adapters.Lexer.lexOps.lexEofStep l).run taken).1.1 = .error e →
      e.cause ≠ .consumer none := by
  obtain ⟨x, w, n, hx, hw, hcr⟩ := hz
  let x' : Lexer.Adapters.X1BatchInCore.lexOps.Lexer C := { x with held := Lexer.Internal.held l }
  let w' : Lexer.Adapters.WRustPort.lexOps.Lexer C := { w with held := Lexer.Internal.held l }
  have hLR : Lexer.X1BatchInCoreLexer.Top.LexerRel l x' :=
    ⟨answering_unique _ _, by rw [hl]; exact hx, rfl⟩
  have hWR : Lexer.WRustPortX1BatchInCore.Calls.LexRel w' x' := ⟨hw.1, hw.2.1, rfl⟩
  have hcoupled := Lexer.X1BatchInCoreLexer.Top.run_lexEofStep (m := AnswerM) (R := C.Result)
    (E := Option C.Error) (Lexer.Recovery.LexerRecovery.abandon Lexer.Recovery.FailFast)
    (Lexer.Recovery.LexerRecovery.recover Lexer.Recovery.FailFast) l x' hLR
  obtain ⟨⟨e1, -⟩, -⟩ := Lexer.Consumers.Alike.mcouple_answerM hcoupled taken
  change ((Lexer.Adapters.Lexer.lexOps.lexEofStep l).run taken).1.1 =
    ((Lexer.Adapters.X1BatchInCore.lexOps.lexEofStep x').run taken).1.1 at e1
  obtain ⟨f1, -, -⟩ := Lexer.Consumers.ChainX1.eof_alike C w' x' taken hWR
  have hW := Lexer.VNaiveWRustPort.Calls.lexOps_lexEofStepW (C := C) w'.core w'.held taken
  rw [← wLexer_eq w'] at hW
  have hnn := Lexer.VNaiveWRustPort.Calls.eof_step_noNone w.core n taken hcr hc
  intro e he
  rw [e1, ← f1, hW] at he
  revert he
  generalize Lexer.VNaiveWRustPort.Eof.runIA (Lexer.Internal.WRustPort.lexEofStep
    (ops := Lexer.Internal.WRustPort.Rust.ops) (H := Answering C) (m := AnswerM)
    (R := C.Result) (E := Option C.Error) (fun _ => pure ()) (fun _ => pure ())) w'.core
    taken = R at hnn
  obtain ⟨⟨rr, cr⟩, tr⟩ := R
  exact hnn e

/-- The state of the library's lexer constructed with the version is related by the chain. -/
theorem zok_new (version : Version) :
    ZOK C (Lexer.Internal.core (Lexer.Adapters.Lexer.lexOps.new C {} version)) :=
  ⟨Lexer.Adapters.X1BatchInCore.lexOps.new C {} version,
    Lexer.Adapters.WRustPort.lexOps.new C {} version,
    Lexer.Internal.VNaive.Core.initial version,
    (Lexer.X1BatchInCoreLexer.Handed.lexerRel_new ({} : Answering C) version).2.1,
    Lexer.WRustPortX1BatchInCore.Handed.new_rel ({} : Answering C) version,
    ⟨rfl, rfl, rfl, rfl, rfl, ⟨rfl, rfl, rfl⟩, .inl ⟨.idle, rfl, rfl, rfl⟩⟩⟩

/-- Every state the library's lexer reaches is related by the chain. -/
theorem zok_of_reach (hc : C.concrete = false) {version : Version}
    {c : BSmtLib.Lexer.Internal.LexerCore} (h : Reach C version c) : ZOK C c := by
  induction h with
  | new => exact zok_new version
  | step _ hok ih => exact (zok_slice hc ih _ rfl _ _).2 _ hok

end

/-- The library's lexer hands no whitespace or comment to the adapter's consumer for a consumer
of the formalism that does not take them. -/
theorem noLayout (C : BSmtLibSpec.Lexer.Consumer) (hc : C.concrete = false)
    (version : Version) :
    NoLayout C version :=
  fun _ hR =>
    ⟨fun held bytes taken e he =>
      (zok_slice hc (zok_of_reach hc hR) (zLexer C _ held) rfl bytes taken).1 e he,
     fun held taken e he => zok_eof hc (zok_of_reach hc hR) (zLexer C _ held) rfl taken e he⟩

end BSmtLib.Facts.Proofs.Reader.Lexes.NoLayout
