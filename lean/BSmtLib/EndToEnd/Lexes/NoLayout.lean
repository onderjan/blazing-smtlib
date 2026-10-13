import BSmtLib.EndToEnd.Lexes.Told

/-!
# The library's lexer hands no whitespace or comment to a consumer that does not take them

From every state the library's lexer reaches with the adapter's consumer (`Param.Reach`), there
are states of the lexer with the batch kept in its state, of the Rust port and of the naive lexer
that correspond to it as the chain of lexers relates them (`ZOK`): the library's lexer and the
lexer with the batch kept in its state give the same results (`X1BatchInCoreLexer.step_fit`,
`X1BatchInCoreLexer.run_lexEofStep`), and so do that lexer and the Rust port
(`WRustPortX1BatchInCore.slice_alike`, `WRustPortX1BatchInCore.eof_alike`). The Rust port, from a
state that is the naive lexer's, never fails with the adapter's error `none` for a consumer that
does not take whitespace and comments (`VNaiveWRustPort.slice_step_noNone`,
`VNaiveWRustPort.eof_step_noNone`), so neither does the library's lexer (`noLayout`).
-/

namespace BSmtLib.EndToEnd.Param

open BSmtLib.Lexer.Internal (core held handler run ofParts)
open BSmtLib.Proofs.Adapter (Answering AnswerM LexOps)
open BSmtLib.Spec.Lexer (Handed)

/-- The states of the library's lexer that the chain of lexers relates to a state of the naive
lexer: a state of the lexer with the batch kept in its state that corresponds to it, one of the
Rust port that corresponds to that, and one of the naive lexer that corresponds to that. -/
def ZOK (C : Spec.Lexer.Consumer) (c : BSmtLib.Lexer.LexerCore) : Prop :=
  ∃ (x : Proofs.Adapter.X1BatchInCore.lexOps.Lexer C)
    (w : Proofs.Adapter.WRustPort.lexOps.Lexer C) (n : Proofs.Lexer.VNaive.Core),
    Proofs.X1BatchInCoreLexer.Rel c x.core ∧ Proofs.WRustPortX1BatchInCore.LexRel w x ∧
      Proofs.Lexer.VNaiveWRustPort.CR C w.core n

section

variable {C : Spec.Lexer.Consumer}

theorem answering_unique (a b : Answering C) : a = b := by
  cases a; cases b; rfl

/-- The lexer of the adapter's consumer with the Rust port's state, as the steps of
`VNaiveWRustPort` take it. -/
theorem wLexer_eq (w : Proofs.Adapter.WRustPort.lexOps.Lexer C) :
    w = ⟨{}, w.core, w.held⟩ := by
  obtain ⟨h, c, d⟩ := w
  rw [answering_unique h {}]

/-- A call on a slice that ends below `USize.size`, from a state that the chain relates: it does
not fail with the adapter's error `none` for a consumer that does not take whitespace and
comments, and where it does not fail, the chain relates the state after it. -/
theorem zok_fit (hc : C.concrete = false) {c : BSmtLib.Lexer.LexerCore} (hz : ZOK C c)
    (l : Proofs.Adapter.Lexer.lexOps.Lexer C) (hl : core l = c) (bytes : Spec.Lexicon.Chars)
    (hs : bytes.toByteArray.toByteSlice.stop < USize.size) (taken : List Handed) :
    (∀ e, ((Proofs.Adapter.Lexer.lexOps.lexSliceStep l bytes.toByteArray.toByteSlice).run
        taken).1.1 = .error e → e.cause ≠ .consumer none) ∧
      (∀ r, ((Proofs.Adapter.Lexer.lexOps.lexSliceStep l bytes.toByteArray.toByteSlice).run
        taken).1.1 = .ok r →
        ZOK C (core ((Proofs.Adapter.Lexer.lexOps.lexSliceStep l
          bytes.toByteArray.toByteSlice).run taken).1.2)) := by
  obtain ⟨x, w, n, hx, hw, hcr⟩ := hz
  have hL : Proofs.X1BatchInCoreLexer.LooseRel l x :=
    ⟨answering_unique _ _, by rw [hl]; exact hx⟩
  obtain ⟨e1, e2, -⟩ := Proofs.X1BatchInCoreLexer.step_fit l x hL _ hs taken
  obtain ⟨f1, f2, -⟩ := Proofs.WRustPortX1BatchInCore.slice_alike C
    bytes.toByteArray.toByteSlice w x taken hw
  have hW := Proofs.Lexer.VNaiveWRustPort.lexOps_lexSliceStepW (C := C) w.core w.held
    bytes.toByteArray.toByteSlice taken
  rw [← wLexer_eq w] at hW
  have hcall := Proofs.Lexer.VNaiveWRustPort.slice_step w.core n bytes taken hcr
  have hnn := Proofs.Lexer.VNaiveWRustPort.slice_step_noNone w.core n bytes taken hcr hc
  generalize (Proofs.Adapter.Lexer.lexOps.lexSliceStep l bytes.toByteArray.toByteSlice).run
    taken = Z at e1 e2 ⊢
  generalize (Proofs.Adapter.X1BatchInCore.lexOps.lexSliceStep x
    bytes.toByteArray.toByteSlice).run taken = X at e1 e2 f1 f2
  generalize (Proofs.Adapter.WRustPort.lexOps.lexSliceStep w
    bytes.toByteArray.toByteSlice).run taken = W at f1 f2 hW
  generalize Proofs.Lexer.VNaiveWRustPort.runIA (Proofs.Lexer.WRustPort.lexSliceStep
    (ops := Proofs.Lexer.WRustPort.Rust.ops)
    (H := Answering C) (m := AnswerM) (R := C.Result) (E := Option C.Error) (fun _ => pure ())
    (fun _ => pure ()) bytes.toByteArray.toByteSlice) w.core taken = R at hW hcall hnn
  obtain ⟨⟨rz, lz⟩, tz⟩ := Z
  obtain ⟨⟨rx, lx⟩, tx⟩ := X
  obtain ⟨⟨rw, lw⟩, tw⟩ := W
  obtain ⟨⟨rr, cr⟩, tr⟩ := R
  simp only at e1 e2 f1 f2 hW hcall hnn
  obtain ⟨⟨rfl, rfl⟩, rfl⟩ := hW
  subst e1 f1
  obtain ⟨-, -, hok, -, -⟩ := hcall
  refine ⟨fun e he => hnn e he, fun r hr => ?_⟩
  subst hr
  exact ⟨lx, _, _, e2.2, f2, hok rfl⟩

open BSmtLib.Lexer.Internal (lexChunks lexSliceStep CHUNK_SIZE) in
/-- The chunks of a slice too large for the positions of the library's lexer, from a state that
the chain relates: no failure with the adapter's error `none`, and where the chunks do not fail,
the chain relates the state after them. -/
theorem zok_chunks (hc : C.concrete = false) (s : Spec.Lexicon.Chars) (p : Nat) :
    ∀ (acc : Option (Located C.Result)) (l : Proofs.Adapter.Lexer.lexOps.Lexer C)
      (t : List Handed), ZOK C (core l) →
      ∀ r (l' : Proofs.Adapter.Lexer.lexOps.Lexer C) t',
        (run l (lexChunks (LexRecovery.abandon Recovery.failFast)
          (LexRecovery.recover Recovery.failFast) s.toByteArray.toByteSlice p acc)).run t =
          ((r, l'), t') →
        (∀ e, r = .error e → e.cause ≠ .consumer none) ∧
          (∀ h, r = .ok h → ZOK C (core l')) := by
  fun_induction Proofs.X1BatchInCoreLexer.Chunks.chunksFrom s p with
  | case1 p hp ih =>
    intro acc l t hz r l' t' hrun
    rw [Proofs.X1BatchInCoreLexer.run_lexChunks_lt l s p hp acc, StateT.run_bind] at hrun
    obtain ⟨n1, n2⟩ := zok_fit hc hz l rfl (Proofs.X1BatchInCoreLexer.Chunks.chunkAt s p)
      (Proofs.X1BatchInCoreLexer.Chunks.chunk_stop_lt s p) t
    generalize (Proofs.Adapter.Lexer.lexOps.lexSliceStep l
      (Proofs.X1BatchInCoreLexer.Chunks.chunkAt s p).toByteArray.toByteSlice).run t = A
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
    rw [Proofs.X1BatchInCoreLexer.run_lexChunks_ge l s p hp acc] at hrun
    change ((Except.ok acc, l), t) = ((r, l'), t') at hrun
    simp only [Prod.mk.injEq] at hrun
    obtain ⟨⟨rfl, rfl⟩, rfl⟩ := hrun
    exact ⟨fun e he => (nomatch he), fun _ _ => hz⟩

open BSmtLib.Lexer.Internal (lexChunks lexSliceStep) in
/-- A call on a slice, from a state that the chain relates: no failure with the adapter's error
`none`, and where the call does not fail, the chain relates the state after it. -/
theorem zok_slice (hc : C.concrete = false) {c : BSmtLib.Lexer.LexerCore} (hz : ZOK C c)
    (l : Proofs.Adapter.Lexer.lexOps.Lexer C) (hl : core l = c) (bytes : Spec.Lexicon.Chars)
    (taken : List Handed) :
    (∀ e, ((Proofs.Adapter.Lexer.lexOps.lexSliceStep l bytes.toByteArray.toByteSlice).run
        taken).1.1 = .error e → e.cause ≠ .consumer none) ∧
      (∀ r, ((Proofs.Adapter.Lexer.lexOps.lexSliceStep l bytes.toByteArray.toByteSlice).run
        taken).1.1 = .ok r →
        ZOK C (core ((Proofs.Adapter.Lexer.lexOps.lexSliceStep l
          bytes.toByteArray.toByteSlice).run taken).1.2)) := by
  by_cases hs : bytes.length < USize.size
  · exact zok_fit hc hz l hl bytes (Proofs.X1BatchInCoreLexer.stop_toByteSlice_lt hs) taken
  · have hs' : ¬ bytes.toByteArray.toByteSlice.stop < USize.size := by
      rw [Proofs.X1BatchInCoreLexer.Chunks.stop_toByteSlice, List.size_toByteArray]
      exact hs
    have hz' : (run l (lexChunks (LexRecovery.abandon Recovery.failFast)
        (LexRecovery.recover Recovery.failFast) bytes.toByteArray.toByteSlice 0 none)).run
          taken =
        (Proofs.Adapter.Lexer.lexOps.lexSliceStep l bytes.toByteArray.toByteSlice).run taken := by
      show _ = (run l (lexSliceStep _ _ _)).run taken
      unfold lexSliceStep
      rw [dite_eq_right_of_eq_false (eq_false hs')]
    generalize (Proofs.Adapter.Lexer.lexOps.lexSliceStep l bytes.toByteArray.toByteSlice).run
      taken = R at hz' ⊢
    obtain ⟨⟨r, l'⟩, t'⟩ := R
    obtain ⟨h1, h2⟩ := zok_chunks hc bytes 0 none l taken (by rw [hl]; exact hz) r l' t' hz'
    exact ⟨fun e he => h1 e he, fun h he => h2 h he⟩

/-- The end of the input, from a state that the chain relates: no failure with the adapter's
error `none`. -/
theorem zok_eof (hc : C.concrete = false) {c : BSmtLib.Lexer.LexerCore} (hz : ZOK C c)
    (l : Proofs.Adapter.Lexer.lexOps.Lexer C) (hl : core l = c) (taken : List Handed) :
    ∀ e, ((Proofs.Adapter.Lexer.lexOps.lexEofStep l).run taken).1.1 = .error e →
      e.cause ≠ .consumer none := by
  obtain ⟨x, w, n, hx, hw, hcr⟩ := hz
  let x' : Proofs.Adapter.X1BatchInCore.lexOps.Lexer C := { x with held := held l }
  let w' : Proofs.Adapter.WRustPort.lexOps.Lexer C := { w with held := held l }
  have hLR : Proofs.X1BatchInCoreLexer.LexerRel l x' :=
    ⟨answering_unique _ _, by rw [hl]; exact hx, rfl⟩
  have hWR : Proofs.WRustPortX1BatchInCore.LexRel w' x' := ⟨hw.1, hw.2.1, rfl⟩
  have hcoupled := Proofs.X1BatchInCoreLexer.run_lexEofStep (m := AnswerM) (R := C.Result)
    (E := Option C.Error) (LexRecovery.abandon Recovery.failFast)
    (LexRecovery.recover Recovery.failFast) l x' hLR
  obtain ⟨⟨e1, -⟩, -⟩ := Proofs.Adapter.mcouple_answerM hcoupled taken
  change ((Proofs.Adapter.Lexer.lexOps.lexEofStep l).run taken).1.1 =
    ((Proofs.Adapter.X1BatchInCore.lexOps.lexEofStep x').run taken).1.1 at e1
  obtain ⟨f1, -, -⟩ := Proofs.WRustPortX1BatchInCore.eof_alike C w' x' taken hWR
  have hW := Proofs.Lexer.VNaiveWRustPort.lexOps_lexEofStepW (C := C) w'.core w'.held taken
  rw [← wLexer_eq w'] at hW
  have hnn := Proofs.Lexer.VNaiveWRustPort.eof_step_noNone w.core n taken hcr hc
  intro e he
  rw [e1, ← f1, hW] at he
  revert he
  generalize Proofs.Lexer.VNaiveWRustPort.runIA (Proofs.Lexer.WRustPort.lexEofStep
    (ops := Proofs.Lexer.WRustPort.Rust.ops) (H := Answering C) (m := AnswerM)
    (R := C.Result) (E := Option C.Error) (fun _ => pure ()) (fun _ => pure ())) w'.core
    taken = R at hnn
  obtain ⟨⟨rr, cr⟩, tr⟩ := R
  exact hnn e

/-- The state of the library's lexer constructed with the version is related by the chain. -/
theorem zok_new (version : Version) :
    ZOK C (core (Proofs.Adapter.Lexer.lexOps.new C {} version)) :=
  ⟨Proofs.Adapter.X1BatchInCore.lexOps.new C {} version,
    Proofs.Adapter.WRustPort.lexOps.new C {} version,
    Proofs.Lexer.VNaive.Core.initial version,
    (Proofs.X1BatchInCoreLexer.lexerRel_new ({} : Answering C) version).2.1,
    Proofs.WRustPortX1BatchInCore.new_rel ({} : Answering C) version,
    ⟨rfl, rfl, rfl, rfl, rfl, ⟨rfl, rfl, rfl⟩, .inl ⟨.idle, rfl, rfl, rfl⟩⟩⟩

/-- Every state the library's lexer reaches is related by the chain. -/
theorem zok_of_reach (hc : C.concrete = false) {version : Version}
    {c : BSmtLib.Lexer.LexerCore} (h : Reach C version c) : ZOK C c := by
  induction h with
  | new => exact zok_new version
  | step _ hok ih => exact (zok_slice hc ih _ rfl _ _).2 _ hok

end

/-- The library's lexer hands no whitespace or comment to the adapter's consumer for a consumer
of the spec that does not take them. -/
theorem noLayout (C : Spec.Lexer.Consumer) (hc : C.concrete = false) (version : Version) :
    NoLayout C version :=
  fun _ hR =>
    ⟨fun held bytes taken e he =>
      (zok_slice hc (zok_of_reach hc hR) (zLexer C _ held) rfl bytes taken).1 e he,
     fun held taken e he => zok_eof hc (zok_of_reach hc hR) (zLexer C _ held) rfl taken e he⟩

end BSmtLib.EndToEnd.Param
