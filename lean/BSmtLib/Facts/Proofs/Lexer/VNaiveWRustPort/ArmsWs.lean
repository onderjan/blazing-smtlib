import BSmtLib.Facts.Proofs.Lexer.VNaiveWRustPort.Arms

/-!
# The Rust port's arm for whitespace in progress, with a consumer that takes it

`arm_whitespace`: the arm of `lexStep` for the state `whitespace`, which only a consumer that
takes whitespace reaches (`lexWhitespace`), keeps the correspondence with the naive lexer. Its
loop (`wsSpec_lt`) goes over the run of whitespace other than line feeds, marks a line feed and
goes on after it, and ends the whitespace at the first byte that is not whitespace, handing it
over alone, or leaves it in progress at the end of the slice.
-/

namespace BSmtLib.Facts.Proofs.Lexer.VNaiveWRustPort.ArmsWs

open BSmtLib.Facts.Lexer.Adapters BSmtLib.Facts.Proofs.Lexer.Simulation.Bytes
open BSmtLibSpec.Lexer (Handed)
open BSmtLib.Facts.Proofs.Lexer.VNaive.Run BSmtLib.Facts.Proofs.Lexer.VNaiveWRustPort.Agree
open BSmtLib.Facts.Proofs.Lexer.VNaiveWRustPort.Arms
open BSmtLib.Facts.Proofs.Lexer.VNaiveWRustPort.Batch
open BSmtLib.Facts.Proofs.Lexer.VNaiveWRustPort.Bytes
open BSmtLib.Facts.Proofs.Lexer.VNaiveWRustPort.Feed
open BSmtLib.Facts.Proofs.Lexer.VNaiveWRustPort.HandOver
open BSmtLib.Facts.Proofs.Lexer.VNaiveWRustPort.Model
open BSmtLib.Facts.Proofs.Lexer.VNaiveWRustPort.Normal.Basic
open BSmtLib.Facts.Proofs.Lexer.VNaiveWRustPort.Pure BSmtLib.Facts.Proofs.Lexer.VNaiveWRustPort.Push
open BSmtLib.Facts.Proofs.Lexer.VNaiveWRustPort.Runs
open BSmtLib.Facts.Proofs.Lexer.VNaiveWRustPort.StartWs
open BSmtLib.Facts.Proofs.Lexer.VNaiveWRustPort.Step
open BSmtLib.Facts.Proofs.Lexer.VNaiveWRustPort.Tables.FastRuns BSmtLib.Lexer.Internal.VNaive

section

variable {C : BSmtLibSpec.Lexer.Consumer} {floor : Option Nat} {low : Nat} {hd : Bool}
    {iv : Token.Version}

/-- What the loop of `lexWhitespace` from the index `j` keeps: the step from `start0` in the
pure state `st0` at `loc0` is, at `j`, whitespace in progress with the content of the lexer
state. -/
def WsSpec (C : BSmtLibSpec.Lexer.Consumer) (v : Token.Version) (hd : Bool) (iv : Token.Version)
    (ver : Token.Version)
    (input : ByteSlice) (start0 : Nat) (st0 : St) (loc0 : Span.Location)
    (coll : List Handed) (held : List Lexeme) (tokenStart : Span.Location) (base : Nat)
    (h : Lexer.Internal.WRustPort.Started floor low tokenStart) (origin j : Nat) : Prop :=
  ∀ (horigin : origin ≤ j) (hj : j ≤ input.size) (s : WP.BS floor low) (locq : Span.Location),
    Fixed v hd iv s.val → s.val.base = start0 → Holds s.val.batch held →
    s.val.batch.bytes = input.byteArray → LocAt s.val s.val.offset s.val.base j locq →
    low = s.val.offset → base = s.val.base → tokenStart = s.val.tokenStart →
    s.val.state = .whitespace → Fits s.val.tokenContent → start0 ≤ j → start0 < input.size →
    feedFrom v C.concrete input st0 loc0 start0 =
      feedFrom v C.concrete input (.token ⟨.whitespace, tokenStart,
        contentBytes s.val.tokenContent⟩) locq j →
    s.val.version = ver → C.concrete = true →
    WP (Lexer.Internal.WRustPort.lexWhitespace (H := Answering C) (m := AnswerM) (R := C.Result)
        (E := Option C.Error) input j origin horigin hj tokenStart base h) s coll
      (fun r s' coll' => ArmPost C v hd iv input st0 loc0 start0 ver coll held r.1 s'.val coll')
      (fun e s' coll' => StepFails C v hd iv input st0 loc0 start0 ver coll held e s'.val coll')

set_option maxHeartbeats 1000000 in
theorem wsSpec_lt (v : Token.Version) (ver : Token.Version) (input : ByteSlice) (start0 : Nat)
    (st0 : St)
    (loc0 : Span.Location) (coll : List Handed) (held : List Lexeme) (tokenStart : Span.Location)
    (base : Nat) (h : Lexer.Internal.WRustPort.Started floor low tokenStart) (origin : Nat) :
    ∀ (n j : Nat), input.size - j < n →
      WsSpec C v hd iv ver input start0 st0 loc0 coll held tokenStart base h origin j := by
  intro n
  induction n with
  | zero => intro j hn; omega
  | succ n ih =>
  intro j hn horigin hj s locq hfix hbase0 hholds hbytes hloc hlow hb hts hstate hfits h0 hs0
    hanchor hver0 hcon
  have hI : Lexer.Internal.WRustPort.Slice.runEnd input j Lexer.CharClass.RUN_NON_LF_WHITESPACE =
      runEnd input isWhitespaceRun j := runEnd_eq endsRun_whitespace _ _
  have hle := le_runEnd input isWhitespaceRun j
  have hle' := runEnd_le input isWhitespaceRun j hj
  have hstop := fun h => runEnd_stop input isWhitespaceRun j h
  have hA := feedFrom_mode v C.concrete input isWhitespaceRun isWhitespaceRun_ne .whitespace
    (fun q l c hm hc => advance_whitespace_run C.concrete q l c hm hc) j
    ⟨.whitespace, tokenStart, contentBytes s.val.tokenContent⟩ locq rfl hj
  rw [← hI] at hA hle hle' hstop
  have hLI := hloc.afterColumns (by rw [hbase0]; exact h0) hle
  rw [Lexer.Internal.WRustPort.lexWhitespace]
  split
  · rename_i c hget
    obtain ⟨hIs, hIc⟩ := get?_eq hget
    have hIq := hstop hIs
    rw [hIc] at hIq
    apply WP.wp_ite
    · -- a line feed, which is marked and is in the content
      intro h10
      have h10' : c = 10 := by simpa using h10
      have hB : feedFrom v C.concrete input st0 loc0 start0 =
          feedFrom v C.concrete input (.token ⟨.whitespace, tokenStart,
            (contentBytes s.val.tokenContent ++ bytesOf input j
              (Lexer.Internal.WRustPort.Slice.runEnd input j
                  Lexer.CharClass.RUN_NON_LF_WHITESPACE)).push 10⟩)
            ((afterColumns locq (Lexer.Internal.WRustPort.Slice.runEnd input j
                Lexer.CharClass.RUN_NON_LF_WHITESPACE -
              j)).afterByte 10) (Lexer.Internal.WRustPort.Slice.runEnd input j
                  Lexer.CharClass.RUN_NON_LF_WHITESPACE + 1) := by
        rw [hanchor, hA, feedFrom_step hIs (byteStep_token_pending v C.concrete (by
          rw [hIc, h10']; exact advance_whitespace_lf C.concrete _ _ rfl)), prep_nil, hIc, h10']
      unfold Lexer.Internal.WRustPort.markLineFeedAt Lexer.Internal.WRustPort.extendContent
        Lexer.Internal.WRustPort.modifyContent
      apply WP.wp_bind; apply WP.wp_modifyCore
      apply WP.wp_bind; apply WP.wp_modifyCore
      refine ih (Lexer.Internal.WRustPort.Slice.runEnd input j
          Lexer.CharClass.RUN_NON_LF_WHITESPACE + 1) (by omega) _ _ _
        ((afterColumns locq (Lexer.Internal.WRustPort.Slice.runEnd input j
            Lexer.CharClass.RUN_NON_LF_WHITESPACE -
          j)).afterByte 10)
        ⟨hfix.1, hfix.2, hfix.3, hfix.4, hfix.5, hfix.6⟩ hbase0 hholds hbytes ?_ hlow hb hts hstate
        (fits_extendSlice input hfits (a := j)
          (b := Lexer.Internal.WRustPort.Slice.runEnd input j Lexer.CharClass.RUN_NON_LF_WHITESPACE
              + 1) (.inl (by omega)))
        (by omega) hs0 ?_ hver0 hcon
      · refine LocAt.lineFeed hLI (by rw [hbase0]; omega) rfl ?_
        show Lexer.Internal.WRustPort.LexerCore.offsetAt _ _ + 1 = _
        simp only [Lexer.Internal.WRustPort.LexerCore.offsetAt]
      · rw [hB]
        congr 3
        show _ = contentBytes (s.val.tokenContent.extendFrom input.byteArray (input.start + j)
          (input.start + (Lexer.Internal.WRustPort.Slice.runEnd input j
              Lexer.CharClass.RUN_NON_LF_WHITESPACE + 1)))
        rw [contentBytes_extendSlice input hfits (.inl (by omega)), content_succ input _ hle hIs,
          hIc, h10']
    · -- any other byte ends the whitespace, which is handed over alone
      intro h10
      have h10' : c ≠ 10 := by simpa using h10
      have hC : feedFrom v C.concrete input st0 loc0 start0 =
          Prep [⟨.whitespace, contentBytes s.val.tokenContent ++ bytesOf input j
              (Lexer.Internal.WRustPort.Slice.runEnd input j
                  Lexer.CharClass.RUN_NON_LF_WHITESPACE), tokenStart,
              afterColumns locq (Lexer.Internal.WRustPort.Slice.runEnd input j
                  Lexer.CharClass.RUN_NON_LF_WHITESPACE - j)⟩]
            (feedFrom v C.concrete input .idle
              (afterColumns locq (Lexer.Internal.WRustPort.Slice.runEnd input j
                  Lexer.CharClass.RUN_NON_LF_WHITESPACE - j))
              (Lexer.Internal.WRustPort.Slice.runEnd input j
                  Lexer.CharClass.RUN_NON_LF_WHITESPACE)) := by
        have hadv := advance_whitespace_end C.concrete ⟨.whitespace, tokenStart,
          contentBytes s.val.tokenContent ++ bytesOf input j
            (Lexer.Internal.WRustPort.Slice.runEnd input j Lexer.CharClass.RUN_NON_LF_WHITESPACE)⟩
          (afterColumns locq (Lexer.Internal.WRustPort.Slice.runEnd input j
              Lexer.CharClass.RUN_NON_LF_WHITESPACE - j))
          (c := input[Lexer.Internal.WRustPort.Slice.runEnd input j
              Lexer.CharClass.RUN_NON_LF_WHITESPACE]) rfl
          (by rw [hIc]; exact hIq) (by rw [hIc]; exact h10')
        rw [hanchor, hA, feedFrom_tokenBefore v C.concrete input hIs hadv]
      have hext : contentBytes (s.val.tokenContent.extendFrom input.byteArray (input.start + j)
          (input.start + Lexer.Internal.WRustPort.Slice.runEnd input j
              Lexer.CharClass.RUN_NON_LF_WHITESPACE)) =
          contentBytes s.val.tokenContent ++ bytesOf input j
            (Lexer.Internal.WRustPort.Slice.runEnd input j Lexer.CharClass.RUN_NON_LF_WHITESPACE) :=
        contentBytes_extendSlice input hfits (.inl (by omega))
      have hfits' := fits_extendSlice input hfits (a := j)
        (b := Lexer.Internal.WRustPort.Slice.runEnd input j Lexer.CharClass.RUN_NON_LF_WHITESPACE)
            (.inl (by omega))
      unfold Lexer.Internal.WRustPort.extendContent Lexer.Internal.WRustPort.modifyContent
        Lexer.Internal.WRustPort.finishWhitespace
      apply WP.wp_bind; apply WP.wp_modifyCore
      apply WP.wp_bind
      refine sinkStored_wp .whitespace (.mkAtByte _) tokenStart base h held _ (by exact hholds) coll
        (by exact hfix.recovers) hfits' ?_ ?_
      · intro s2 coll2 hk2 hb2 hc2
        obtain ⟨k1, k2, k3, k4, k5, k6, k7, k8, k9, k10, k11⟩ := key_fields hk2
        unfold Lexer.Internal.WRustPort.setNormal
        apply WP.wp_bind; apply WP.wp_modifyCore
        apply WP.wp_pure
        have hstep := stepLocation_eq' (pos := Lexer.Internal.WRustPort.Slice.runEnd input j
          Lexer.CharClass.RUN_NON_LF_WHITESPACE) hloc (by rw [hbase0]; exact h0) hb hlow hle
        refine armPost_finish (s0 := _) ⟨hfix.1, hfix.2, hfix.3, hfix.4, hfix.5, hfix.6⟩ hbase0
          (Nat.le_trans h0 hle) hbytes ⟨k1, k4, k3, k5, rfl, k8, k9, k10, k11, hb2⟩ hLI hc2 ?_ hver0
        rw [hC]
        show _ = Prep [⟨.whitespace, contentBytes (s.val.tokenContent.extendFrom input.byteArray
          (input.start + j) (input.start + Lexer.Internal.WRustPort.Slice.runEnd input j
            Lexer.CharClass.RUN_NON_LF_WHITESPACE)), tokenStart,
          stepLocation s.val low base (Lexer.Internal.WRustPort.Slice.runEnd input j
              Lexer.CharClass.RUN_NON_LF_WHITESPACE)⟩] _
        rw [hext, hstep]
      · intro e s2 p2 d hn hss
        have hstep := stepLocation_eq' (pos := Lexer.Internal.WRustPort.Slice.runEnd input j
          Lexer.CharClass.RUN_NON_LF_WHITESPACE) hloc (by rw [hbase0]; exact h0) hb hlow hle
        have hn' : Stops C s.val.holding s.val.version coll (held ++ [⟨.whitespace, contentBytes
            (s.val.tokenContent.extendFrom input.byteArray (input.start + j) (input.start +
              Lexer.Internal.WRustPort.Slice.runEnd input j
                  Lexer.CharClass.RUN_NON_LF_WHITESPACE)), tokenStart,
            stepLocation s.val low base
              (Lexer.Internal.WRustPort.Slice.runEnd input j
                  Lexer.CharClass.RUN_NON_LF_WHITESPACE)⟩]) e p2 d := hn
        rw [hext, hstep] at hn'
        exact stepFails_of_stops' hss ⟨hfix.1, hfix.2, hfix.3, hfix.4, hfix.5, hfix.6⟩
          ⟨_, by rw [hC, outcome_pending_prep, ← hver0]⟩ hn' hbytes
  · -- the run reaches the end of the slice: the whitespace is left in progress
    rename_i hnone
    have hge := Lexer.Internal.WRustPort.Slice.size_le_of_get?_none hnone
    have he : Lexer.Internal.WRustPort.Slice.runEnd input j Lexer.CharClass.RUN_NON_LF_WHITESPACE =
        input.size := by omega
    unfold Lexer.Internal.WRustPort.extendContent Lexer.Internal.WRustPort.modifyContent
    apply WP.wp_bind; apply WP.wp_modifyCore
    apply WP.wp_pure
    rw [he] at hA hLI
    refine armPost_pending (s0 := s.val) hfix hbase0 (by omega) hholds hbytes
      ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ ?_ hLI (hanchor.trans hA) rfl hver0
    refine ⟨?_, fits_extendSlice input hfits (a := j) (b := input.size) (.inl (by omega))⟩
    show TokenAgrees v C.concrete s.val.state s.val.tokenStart
      (contentBytes (s.val.tokenContent.extendFrom input.byteArray (input.start + j)
        (input.start + input.size))) _
    rw [contentBytes_extendSlice input hfits (a := j) (b := input.size) (.inl (by omega)),
      hstate]
    exact ⟨hts, hcon, rfl, rfl⟩

/-- The arm of `lexStep` for whitespace in progress, which the consumer takes. -/
theorem arm_whitespace (v : Token.Version) (input : ByteSlice) (start : Nat)
    (hstart : start < input.size) (tokenStart : Span.Location) (base : Nat)
    (h : Lexer.Internal.WRustPort.Started floor low tokenStart) (s : WP.BS floor low)
    (coll : List Handed)
    (p : Pending) (location : Span.Location) (held : List Lexeme)
    (hpre : StepPre C v hd iv input (.token p) location held start s.val)
    (hlow : low = s.val.offset) (hts : tokenStart = s.val.tokenStart) (hb : base = s.val.base)
    (hstate : s.val.state = .whitespace) :
    WP (Lexer.Internal.WRustPort.lexWhitespace (H := Answering C) (m := AnswerM) (R := C.Result)
        (E := Option C.Error) input start start (Nat.le_refl _) (Nat.le_of_lt hstart) tokenStart
        base h) s coll
      (fun r s' coll' =>
        ArmPost C v hd iv input (.token p) location start s.val.version coll held r.1 s'.val coll')
      (fun e s' coll' =>
        StepFails C v hd iv input (.token p) location start s.val.version coll held e s'.val
          coll') := by
  obtain ⟨hps, hcon, hm, hcont⟩ := token_agrees hpre.agrees hstate
  have hp : p = ⟨.whitespace, tokenStart, contentBytes s.val.tokenContent⟩ := by
    obtain ⟨mode, pstart, pcontent⟩ := p
    simp only at hps hm hcont
    rw [hm, hps, hcont, hts]
  exact wsSpec_lt v s.val.version input start (.token p) location coll held tokenStart base h start
    _ start (Nat.lt_succ_self _) (Nat.le_refl _) (Nat.le_of_lt hstart) s location hpre.fixed
    hpre.base hpre.holds hpre.bytes hpre.loc hlow hb hts hstate
    (token_fits hpre.agrees) (Nat.le_refl _) hstart (by rw [hp]) rfl hcon

end

end BSmtLib.Facts.Proofs.Lexer.VNaiveWRustPort.ArmsWs
