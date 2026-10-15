module

public import BSmtLib.Facts.Proofs.Lexer.VNaiveWRustPort.Arms
import all BSmtLib.Lexer.Internal.VNaive
import all BSmtLib.Lexer.Internal.WRustPort
import all BSmtLib.Lexer.Internal.WRustPort.Slice

@[expose] public section

/-!
# The arms of the Rust port's `lexStep` for numbers

The arms of `lexStep` for the base selection after a `#`, for a fraction after its dot and for
a numeral, which may go on to a fraction.
-/

namespace BSmtLib.Facts.Proofs.Lexer.VNaiveWRustPort.ArmsNumbers

open BSmtLib.Facts.Lexer.Adapters BSmtLib.Facts.Proofs.Lexer.Simulation.Bytes
open BSmtLib.Lexer.Internal (CharClass)
open BSmtLibSpec.Lexer (Handed)
open BSmtLib.Lexer.Internal.WRustPort.Slice (get? get)
open BSmtLib.Facts.Proofs.Lexer.VNaive.Run BSmtLib.Facts.Proofs.Lexer.VNaiveWRustPort.Agree
open BSmtLib.Facts.Proofs.Lexer.VNaiveWRustPort.Arms
open BSmtLib.Facts.Proofs.Lexer.VNaiveWRustPort.Batch
open BSmtLib.Facts.Proofs.Lexer.VNaiveWRustPort.Bytes
open BSmtLib.Facts.Proofs.Lexer.VNaiveWRustPort.Feed
open BSmtLib.Facts.Proofs.Lexer.VNaiveWRustPort.HandOver
open BSmtLib.Facts.Proofs.Lexer.VNaiveWRustPort.Model
open BSmtLib.Facts.Proofs.Lexer.VNaiveWRustPort.Pure BSmtLib.Facts.Proofs.Lexer.VNaiveWRustPort.Push
open BSmtLib.Facts.Proofs.Lexer.VNaiveWRustPort.Runs BSmtLib.Facts.Proofs.Lexer.VNaiveWRustPort.Step
open BSmtLib.Facts.Proofs.Lexer.VNaiveWRustPort.Tables.Delimiters
open BSmtLib.Facts.Proofs.Lexer.VNaiveWRustPort.Tables.NumeralRuns BSmtLib.Lexer.Internal.VNaive

section

variable {floor : Option Nat} {low : Nat}
variable {C : BSmtLibSpec.Lexer.Consumer} {hd : Bool} {iv : Token.Version}

/-- The arm of `lexStep` for the base selection after a `#`. -/
theorem arm_baseSelection (v : Token.Version) (input : ByteSlice) (start : Nat)
    (hstart : start < input.size) (tokenStart : Span.Location)
    (h : Lexer.Internal.WRustPort.Started floor low tokenStart) (s : WP.BS floor low)
    (coll : List Handed)
    (p : Pending) (location : Span.Location) (held : List Lexeme)
    (hpre : StepPre C v hd iv input (.token p) location held start s.val)
    (hts : tokenStart = s.val.tokenStart) (hstate : s.val.state = .baseSelection) :
    WP (Lexer.Internal.WRustPort.lexBaseSelection (H := Answering C) (m := AnswerM) (R := C.Result)
        (E := Option C.Error)
        input start hstart tokenStart h) s coll
      (fun r s' coll' => ArmPost C v hd iv input (.token p) location start s.val.version coll held
          r.1 s'.val coll')
      (fun e s' coll' => StepFails C v hd iv input (.token p) location start s.val.version coll held
          e s'.val coll') := by
  obtain ⟨hps, hm, hcont⟩ := token_agrees hpre.agrees hstate
  have hloc := hpre.loc
  obtain ⟨mode, pstart, pcontent⟩ := p
  simp only at hps hm hcont
  subst hm
  unfold Lexer.Internal.WRustPort.lexBaseSelection Lexer.Internal.WRustPort.setTokenState
  rw [get_eq hstart]
  dsimp only
  apply WP.wp_ite
  · intro hx
    have hx' : input[start] = 120 := by simpa using hx
    apply WP.wp_bind; apply WP.wp_modifyBound
    apply WP.wp_pure
    refine armPost_pending (s0 := s.val) hpre.fixed hpre.base (show start < start + 1 by omega)
      hpre.holds hpre.bytes ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
      (q := ⟨.digits .hexadecimal, pstart, pcontent⟩)
      ⟨⟨by show pstart = tokenStart; rw [hps, hts], rfl, hcont⟩, (show Fits s.val.tokenContent from
          token_fits hpre.agrees)⟩
      (hloc.afterByte (Nat.le_of_eq hpre.base) (b := input[start]) (by rw [hx']; decide)) ?_
    rw [feedFrom_step hstart (byteStep_token_pending v C.concrete (by rw [hx']; rfl)), prep_nil]
  · intro hx
    apply WP.wp_ite
    · intro hb'
      have hb'' : input[start] = 98 := by simpa using hb'
      apply WP.wp_bind; apply WP.wp_modifyBound
      apply WP.wp_pure
      refine armPost_pending (s0 := s.val) hpre.fixed hpre.base (show start < start + 1 by omega)
        hpre.holds hpre.bytes ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
        (q := ⟨.digits .binary, pstart, pcontent⟩)
        ⟨⟨by show pstart = tokenStart; rw [hps, hts], rfl, hcont⟩, (show Fits s.val.tokenContent
            from token_fits hpre.agrees)⟩
        (hloc.afterByte (Nat.le_of_eq hpre.base) (b := input[start]) (by rw [hb'']; decide)) ?_
      rw [feedFrom_step hstart (byteStep_token_pending v C.concrete (by rw [hb'']; rfl)), prep_nil]
    · intro hb'
      have hx' : input[start] ≠ 120 := by simpa using hx
      have hb'' : input[start] ≠ 98 := by simpa using hb'
      have hf : advance C.concrete ⟨.hash, pstart, pcontent⟩ location input[start] =
          .error (failAtByte .baseSelectionExpected pstart location) := by
        simp [advance, hx', hb'']
      unfold Lexer.Internal.WRustPort.errorAt Lexer.Internal.WRustPort.errorWith
      wp_walk
      refine stepFails_here ?_ hpre.holds
        ⟨hpre.fixed.1, hpre.fixed.2, hpre.fixed.3, hpre.fixed.4, hpre.fixed.5, hpre.fixed.6⟩ rfl
      rw [feedFrom_advance_error v C.concrete input hstart hf]
      rw [hps]
      have := hpre.base
      failure_eq hloc

theorem stored_last_append (a b : ByteArray) (hb : b.size ≠ 0) :
    lastOf (a ++ b) = lastOf b := by
  simp only [lastOf, ByteArray.size_append]
  have h1 : (a.size + b.size == 0) = false := by simp only [beq_eq_false_iff_ne]; omega
  have h2 : (b.size == 0) = false := by simp only [beq_eq_false_iff_ne]; omega
  simp only [h1, h2, Bool.false_eq_true, ↓reduceIte, Option.some.injEq]
  have e : ∀ (c : ByteArray) (i : Nat), c.get! i = c.data[i]! := by intro c i; cases c; rfl
  rw [e, e, ByteArray.data_append]
  have ha : a.size = a.data.size := rfl
  have hb' : b.size = b.data.size := rfl
  rw [getElem!_pos _ _ (by simp only [Array.size_append]; omega),
    getElem!_pos _ _ (by omega), Array.getElem_append_right (by omega)]
  congr 1
  omega

/-- What the arm for a fraction checks of its content: the last byte, which is a digit after the
dot or the dot. -/
abbrev fractionChecks (content : ByteArray) : Bool :=
  !((lastOf content).isNone ||
    lastOf content == some (byte! '.'))

/-- The run of the fraction's digits from `j`: a digit after the dot if there was one or the
run has one. -/
theorem fractionChecks_run (input : ByteSlice) (content : ByteArray) {j e : Nat} (hje : j ≤ e)
    (he : e ≤ input.size) (hdig : ∀ k (hk : k < input.size), j ≤ k → k < e →
      isDigit input[k] = true) :
    fractionChecks (content ++ bytesOf input j e) =
      (fractionChecks content || decide (j < e)) := by
  by_cases hlt : j < e
  · have hs := bytesOf_size input hje he
    unfold fractionChecks
    rw [stored_last_append _ _ (by omega), stored_last input hlt he]
    have hd := hdig (e - 1) (by omega) (by omega) (by omega)
    have h46 : input[e - 1] ≠ 46 := by intro h; rw [h] at hd; exact absurd hd (by decide)
    simp [hlt, h46]
  · have he' : e = j := by omega
    subst he'
    rw [bytesOf_self input _ he, ByteArray.append_empty]
    simp

/-- The fraction's digits from `j`, in a step that started at `start0`, where the naive lexer
was at the fraction `q` at `locq`. -/
theorem fractionFrom_wp (v : Token.Version) (input : ByteSlice) (j : Nat) (hj : j ≤ input.size)
    (start0 : Nat) (hstart0 : start0 < input.size) (hj0 : start0 ≤ j) (tokenStart : Span.Location)
    (base : Nat) (h : Lexer.Internal.WRustPort.Started floor low tokenStart) (s : WP.BS floor low)
    (coll : List Handed) (st0 : St) (loc0 : Span.Location) (held : List Lexeme) (q : Pending)
    (locq : Span.Location) (hfix : Fixed v hd iv s.val) (hbase0 : s.val.base = start0)
    (hholds : Holds s.val.batch held) (hbytes : s.val.batch.bytes = input.byteArray)
    (hloc : LocAt s.val s.val.offset s.val.base j locq) (hlow : low = s.val.offset)
    (hb : base = s.val.base)
    (hq : q.mode = .fraction (fractionChecks (contentBytes s.val.tokenContent))) (hqs : q.start =
        tokenStart)
    (hqc : q.content = contentBytes s.val.tokenContent) (hfits : Fits s.val.tokenContent)
    (hanchor : feedFrom v C.concrete input st0 loc0 start0 = feedFrom v C.concrete input
        (.token q) locq j) (hts : s.val.tokenStart = tokenStart) :
    WP (Lexer.Internal.WRustPort.lexFractionFrom (H := Answering C) (m := AnswerM) (R := C.Result)
        (E := Option C.Error)
        input j tokenStart base h) s coll
      (fun r s' coll' => ArmPost C v hd iv input st0 loc0 start0 s.val.version coll held
          r.1 s'.val coll')
      (fun e s' coll' => StepFails C v hd iv input st0 loc0 start0 s.val.version coll held e
          s'.val coll') := by
  have hJ : Lexer.Internal.WRustPort.Slice.runEnd input j CharClass.RUN_DIGIT = runEnd input
      isDigit j :=
    runEnd_eq endsRun_digit _ _
  have hle := le_runEnd input isDigit j
  have hle' := runEnd_le input isDigit j hj
  have hstop := fun h => runEnd_stop input isDigit j h
  have hmem := runEnd_mem input isDigit j
  have hA := feedFrom_fraction v C.concrete input j q locq _ hq hj
  rw [← hJ] at hA hle hle' hstop hmem
  have hext : contentBytes (s.val.tokenContent.extendFrom input.byteArray (input.start + j)
      (input.start + Lexer.Internal.WRustPort.Slice.runEnd input j CharClass.RUN_DIGIT)) =
      contentBytes s.val.tokenContent ++ bytesOf input j
          (Lexer.Internal.WRustPort.Slice.runEnd input j
          CharClass.RUN_DIGIT) :=
    contentBytes_extendSlice input hfits (.inl hle')
  have hfits' := fits_extendSlice input hfits (a := j) (.inl hle')
  have hfc := fractionChecks_run input (contentBytes s.val.tokenContent) hle hle' hmem
  have hA' : feedFrom v C.concrete input st0 loc0 start0 =
      feedFrom v C.concrete input (.token ⟨.fraction (fractionChecks
          (contentBytes s.val.tokenContent ++
          bytesOf input j (Lexer.Internal.WRustPort.Slice.runEnd input j
              CharClass.RUN_DIGIT))), tokenStart,
          contentBytes s.val.tokenContent ++ bytesOf input j
              (Lexer.Internal.WRustPort.Slice.runEnd input j
              CharClass.RUN_DIGIT)⟩)
        (afterColumns locq (Lexer.Internal.WRustPort.Slice.runEnd input j CharClass.RUN_DIGIT
            - j))
        (Lexer.Internal.WRustPort.Slice.runEnd input j CharClass.RUN_DIGIT) := by
    rw [hanchor, hA, hfc, hqs, hqc]
  have hLJ := hloc.afterColumns (by rw [hbase0]; exact hj0) hle
  unfold Lexer.Internal.WRustPort.lexFractionFrom Lexer.Internal.WRustPort.extendContent
      Lexer.Internal.WRustPort.modifyContent
  apply WP.wp_bind; apply WP.wp_modifyCore
  dsimp only
  apply WP.wp_dite
  · -- the digits end inside the slice: the decimal is finished
    intro hEs
    have hEs' := hstop hEs
    unfold Lexer.Internal.WRustPort.finishDecimal
    apply WP.wp_bind
    apply WP.wp_bind; apply WP.wp_getCore
    dsimp only
    apply WP.wp_ite
    · -- no digit after the dot
      intro hbad
      have hfc' : fractionChecks (contentBytes s.val.tokenContent ++
          bytesOf input j (Lexer.Internal.WRustPort.Slice.runEnd input j
              CharClass.RUN_DIGIT)) = false := by
        simp only [fractionChecks, Bool.not_eq_false']
        rw [← hext, ← last?_stored hfits']
        exact hbad
      have hf := advance_end_fraction_none (ws := C.concrete) (location := afterColumns locq
        (Lexer.Internal.WRustPort.Slice.runEnd input j CharClass.RUN_DIGIT - j))
        (q := ⟨.fraction (fractionChecks (contentBytes s.val.tokenContent ++
          bytesOf input j (Lexer.Internal.WRustPort.Slice.runEnd input j
              CharClass.RUN_DIGIT))), tokenStart,
          contentBytes s.val.tokenContent ++ bytesOf input j
              (Lexer.Internal.WRustPort.Slice.runEnd input j
              CharClass.RUN_DIGIT)⟩)
        (by rw [hfc']) hEs'
      unfold Lexer.Internal.WRustPort.error Lexer.Internal.WRustPort.errorWith
      wp_walk
      refine stepFails_here ?_ hholds
        ⟨hfix.1, hfix.2, hfix.3, hfix.4, hfix.5, hfix.6⟩ rfl
      rw [hA', feedFrom_advance_error v C.concrete input hEs hf]
      rw [← hts]
      failure_eq hloc
    · intro hgood
      have hfc' : fractionChecks (contentBytes s.val.tokenContent ++
          bytesOf input j (Lexer.Internal.WRustPort.Slice.runEnd input j
              CharClass.RUN_DIGIT)) = true := by
        simp only [fractionChecks, Bool.not_eq_true']
        rw [← hext, ← last?_stored hfits']
        exact Bool.eq_false_iff.mpr hgood
      have hC := feedFrom_end v C.concrete input hEs
        (q := ⟨.fraction (fractionChecks (contentBytes s.val.tokenContent ++
          bytesOf input j (Lexer.Internal.WRustPort.Slice.runEnd input j
              CharClass.RUN_DIGIT))), tokenStart,
          contentBytes s.val.tokenContent ++ bytesOf input j
              (Lexer.Internal.WRustPort.Slice.runEnd input j
              CharClass.RUN_DIGIT)⟩)
        (location := afterColumns locq (Lexer.Internal.WRustPort.Slice.runEnd input j
            CharClass.RUN_DIGIT - j))
        (advance_end_fraction (by rw [hfc']) hEs')
      rw [← hA'] at hC
      unfold Lexer.Internal.WRustPort.expectDelimiter
      rw [get_eq hEs]
      apply WP.wp_bind
      apply WP.wp_ite
      · intro hnd
        have hnd' : Lexer.Internal.VNaive.isDelimiter
            input[Lexer.Internal.WRustPort.Slice.runEnd input j CharClass.RUN_DIGIT] = false
                := by
          rw [← isDelimiter_eq]; simpa using hnd
        rw [hnd'] at hC
        unfold Lexer.Internal.WRustPort.errorAt Lexer.Internal.WRustPort.errorWith
        wp_walk
        refine stepFails_here ?_ hholds
          ⟨hfix.1, hfix.2, hfix.3, hfix.4, hfix.5, hfix.6⟩ rfl
        rw [hC]
        simp only [Bool.false_eq_true, ↓reduceIte]
        rw [← hts]
        failure_eq hloc
      · intro hd
        have hd' : Lexer.Internal.VNaive.isDelimiter
            input[Lexer.Internal.WRustPort.Slice.runEnd input j CharClass.RUN_DIGIT] = true
                := by
          rw [← isDelimiter_eq]; simpa using hd
        rw [hd'] at hC
        simp only [↓reduceIte] at hC
        apply WP.wp_pure
        refine sinkStored_wp .decimal (.mkAtByte _) tokenStart base h held _ ?_ coll ?_ ?_
          ?_ ?_
        · exact hholds
        · exact hfix.recovers
        · exact hfits'
        · intro s1 coll1 hk1 hb1 hc1
          obtain ⟨k1, k2, k3, k4, k5, k6, k7, k8, k9, k10, k11⟩ := key_fields hk1
          unfold Lexer.Internal.WRustPort.setNormal
          apply WP.wp_bind; apply WP.wp_modifyCore
          apply WP.wp_pure
          have hstep := stepLocation_eq' (pos := Lexer.Internal.WRustPort.Slice.runEnd input j
              CharClass.RUN_DIGIT)
            hloc (by rw [hbase0]; exact hj0) hb hlow hle
          refine armPost_finish (s0 := _) ⟨hfix.1, hfix.2, hfix.3, hfix.4, hfix.5, hfix.6⟩
            hbase0 (show start0 ≤ Lexer.Internal.WRustPort.Slice.runEnd input j
                CharClass.RUN_DIGIT by omega) hbytes
            ⟨k1, k4, k3, k5, rfl, k8, k9, k10, k11, hb1⟩
            hLJ hc1 ?_
          rw [hC]
          show _ = Prep [⟨.decimal, contentBytes (s.val.tokenContent.extendFrom input.byteArray
              (input.start + j)
            (input.start + (Lexer.Internal.WRustPort.Slice.runEnd input j
                CharClass.RUN_DIGIT))), tokenStart,
            stepLocation s.val low base (Lexer.Internal.WRustPort.Slice.runEnd input j
                CharClass.RUN_DIGIT)⟩]
            (feedFrom v C.concrete input .idle (afterColumns locq
                (Lexer.Internal.WRustPort.Slice.runEnd input j
              CharClass.RUN_DIGIT - j)) (Lexer.Internal.WRustPort.Slice.runEnd input j
                  CharClass.RUN_DIGIT))
          rw [hext, hstep]
        · intro e s' p d hn hss
          have hstep := stepLocation_eq' (pos := Lexer.Internal.WRustPort.Slice.runEnd input j
              CharClass.RUN_DIGIT)
            hloc (by rw [hbase0]; exact hj0) hb hlow hle
          have hn' : Stops C s.val.holding s.val.version coll
              (held ++ [⟨.decimal, contentBytes (s.val.tokenContent.extendFrom
              input.byteArray (input.start + j)
            (input.start + (Lexer.Internal.WRustPort.Slice.runEnd input j
                CharClass.RUN_DIGIT))), tokenStart,
              stepLocation s.val low base (Lexer.Internal.WRustPort.Slice.runEnd input j
                  CharClass.RUN_DIGIT)⟩]) e p d :=
            hn
          rw [hext, hstep] at hn'
          exact stepFails_of_stops' (hbytes := by first | assumption | exact hpre.bytes) hss (by
              first
              | exact ⟨hfix.1, hfix.2, hfix.3, hfix.4, hfix.5, hfix.6⟩
              | exact ⟨hpre.fixed.1, hpre.fixed.2, hpre.fixed.3, hpre.fixed.4, hpre.fixed.5,
                  hpre.fixed.6⟩)
            ⟨_, by rw [hC, outcome_pending_prep] <;> rfl⟩ hn'
  · -- the digits run to the end of the slice: the fraction is left in progress
    intro hEs
    unfold Lexer.Internal.WRustPort.setTokenState
    apply WP.wp_bind; apply WP.wp_modifyBound
    apply WP.wp_pure
    refine armPost_pending (s0 := s.val) hfix hbase0
      (show start0 < Lexer.Internal.WRustPort.Slice.runEnd input j
          CharClass.RUN_DIGIT by omega) hholds hbytes
      ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ ?_ hLJ hA'
    refine ⟨?_, hfits'⟩
    show TokenAgrees v C.concrete .fraction tokenStart (contentBytes (s.val.tokenContent.extendFrom
      input.byteArray (input.start + j) (input.start + Lexer.Internal.WRustPort.Slice.runEnd input
          j CharClass.RUN_DIGIT)))
      _
    rw [hext]
    exact ⟨rfl, rfl, rfl⟩

/-- The check of the numeral arm for a single `0` before its run. -/
abbrev isZero (content : ByteArray) : Bool :=
  content.size == 1 && content.get! 0 == byte! '0'

/-- The check of the numeral arm reads the content buffer as its content. -/
theorem isZero_contentBytes {buf : Lexer.Internal.Helpers.ContentBuffer} (h : Fits buf) :
    isZero (contentBytes buf) =
      (if h : buf.len = 1 then buf.bytes[0]'(by have := buf.fits; omega) == byte! '0'
       else false) := by
  unfold isZero
  rw [size_contentBytes h]
  by_cases h1 : buf.len = 1
  · have h0 : 0 < buf.bytes.size := by have := buf.fits; omega
    simp only [h1, beq_self_eq_true, Bool.true_and, get!_eq_getElem!,
      get!_contentBytes h (show 0 < buf.len by omega), ↓reduceDIte, getElem!_pos buf.bytes 0 h0]
  · have h1' : (buf.len == 1) = false := by simpa using h1
    simp [h1', h1]

theorem isZero_append (c b : ByteArray) (hc : c.size ≠ 0) (hz : isZero c = false) :
    isZero (c ++ b) = false := by
  have e : ∀ (a : ByteArray) (i : Nat), a.get! i = a.data[i]! := by intro a i; cases a; rfl
  unfold isZero at hz ⊢
  rw [ByteArray.size_append, e, ByteArray.data_append]
  rw [getElem!_pos _ _ (by simp only [Array.size_append]; show 0 < c.size + _; omega),
    Array.getElem_append_left (by show 0 < c.size; omega)]
  rw [e] at hz
  rw [getElem!_pos _ _ (by show 0 < c.size; omega)] at hz
  by_cases h1 : c.size = 1
  · simp only [h1, beq_self_eq_true, Bool.true_and] at hz
    simp only [hz, Bool.and_false]
  · have : (c.size + b.size == 1) = false := by
      simp only [beq_eq_false_iff_ne]; omega
    simp [this]

theorem fractionChecks_dot (c : ByteArray) : fractionChecks (c.push 46) = false := by
  have e : ∀ (a : ByteArray) (i : Nat), a.get! i = a.data[i]! := by intro a i; cases a; rfl
  unfold fractionChecks
  simp only [lastOf, ByteArray.size_push]
  have h1 : (c.size + 1 == 0) = false := by simp
  simp only [h1, Bool.false_eq_true, ↓reduceIte, Nat.add_sub_cancel, Option.isNone_some,
    Bool.false_or, e, ByteArray.data_push]
  rw [getElem!_pos _ _ (by simp only [Array.size_push]; show c.size < c.size + 1; omega)]
  show (!some ((c.data.push 46)[c.data.size]'(by simp)) == some 46) = false
  rw [Array.getElem_push_eq]
  rfl

set_option maxHeartbeats 400000 in
/-- The arm of `lexStep` for a numeral, which may go on to a fraction. -/
theorem arm_numeralOrDecimal (v : Token.Version) (input : ByteSlice) (start : Nat)
    (hstart : start < input.size) (tokenStart : Span.Location) (base : Nat)
    (h : Lexer.Internal.WRustPort.Started floor low tokenStart) (s : WP.BS floor low)
    (coll : List Handed)
    (p : Pending) (location : Span.Location) (held : List Lexeme)
    (hpre : StepPre C v hd iv input (.token p) location held start s.val)
        (hlow : low = s.val.offset)
    (hts : tokenStart = s.val.tokenStart) (hb : base = s.val.base)
    (hstate : s.val.state = .numeralOrDecimal) :
    WP (Lexer.Internal.WRustPort.lexNumeralOrDecimal (H := Answering C) (m := AnswerM)
        (R := C.Result)
        (E := Option C.Error)
        input start tokenStart base h) s coll
      (fun r s' coll' => ArmPost C v hd iv input (.token p) location start s.val.version coll held
          r.1 s'.val coll')
      (fun e s' coll' => StepFails C v hd iv input (.token p) location start s.val.version coll held
          e s'.val coll') := by
  obtain ⟨hps, hm, hcont, hsz⟩ := token_agrees hpre.agrees hstate
  have hJ : Lexer.Internal.WRustPort.Slice.runEnd input start CharClass.RUN_DIGIT = runEnd
      input isDigit start :=
    runEnd_eq endsRun_digit _ _
  have hle := le_runEnd input isDigit start
  have hle' := runEnd_le input isDigit start (Nat.le_of_lt hstart)
  have hstop := fun h => runEnd_stop input isDigit start h
  have hmem := runEnd_mem input isDigit start
  rw [← hJ] at hle hle' hstop hmem
  have hfits := token_fits hpre.agrees
  have hext : contentBytes (s.val.tokenContent.extendFrom input.byteArray (input.start + start)
      (input.start + Lexer.Internal.WRustPort.Slice.runEnd input start CharClass.RUN_DIGIT)) =
      contentBytes s.val.tokenContent ++
        bytesOf input start (Lexer.Internal.WRustPort.Slice.runEnd input start
            CharClass.RUN_DIGIT) :=
    contentBytes_extendSlice input hfits (.inl hle')
  have hfits' := fits_extendSlice input hfits (a := start) (.inl hle')
  have hloc := hpre.loc
  unfold Lexer.Internal.WRustPort.lexNumeralOrDecimal
  apply WP.wp_bind; apply WP.wp_getCore
  dsimp only
  apply WP.wp_ite
  · -- a single `0` followed by a digit
    intro hz
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hz
    obtain ⟨hlt, hzero⟩ := hz
    have hd := hmem start hstart (Nat.le_refl _) hlt
    have hf : advance C.concrete p location input[start] =
        .error (failAtByte .numeralLeadingZero p.start location) := by
      obtain ⟨mode, pstart, pcontent⟩ := p
      simp only at hm
      subst hm
      have : ((contentBytes s.val.tokenContent).size == 1 &&
          (contentBytes s.val.tokenContent).get! 0 == 48) = true := by
        have e := isZero_contentBytes hfits
        unfold isZero at e
        rw [e]
        exact hzero
      simp [advance, this, hd]
    unfold Lexer.Internal.WRustPort.errorAt Lexer.Internal.WRustPort.errorWith
    wp_walk
    refine stepFails_here ?_ hpre.holds
      ⟨hpre.fixed.1, hpre.fixed.2, hpre.fixed.3, hpre.fixed.4, hpre.fixed.5, hpre.fixed.6⟩ rfl
    rw [feedFrom_advance_error v C.concrete input hstart hf]
    rw [hps]
    have := hpre.base
    failure_eq hloc
  intro hz
  rw [← isZero_contentBytes hfits] at hz
  have hA : feedFrom v C.concrete input (.token p) location start =
      feedFrom v C.concrete input (.token ⟨.numeral (isZero (contentBytes
          s.val.tokenContent)), p.start,
          p.content ++ bytesOf input start (Lexer.Internal.WRustPort.Slice.runEnd input start
              CharClass.RUN_DIGIT)⟩)
        (afterColumns location (Lexer.Internal.WRustPort.Slice.runEnd input start
            CharClass.RUN_DIGIT - start))
        (Lexer.Internal.WRustPort.Slice.runEnd input start CharClass.RUN_DIGIT) := by
    obtain ⟨mode, pstart, pcontent⟩ := p
    simp only at hm
    subst hm
    by_cases hz0 : isZero (contentBytes s.val.tokenContent) = true
    · have he : Lexer.Internal.WRustPort.Slice.runEnd input start CharClass.RUN_DIGIT = start
        := by
        rcases Nat.lt_or_ge start (Lexer.Internal.WRustPort.Slice.runEnd input start
            CharClass.RUN_DIGIT) with hgt | hge
        · exact absurd (by simp only [Bool.and_eq_true, decide_eq_true_eq]
                           exact ⟨hgt, (Bool.and_eq_true _ _).mp hz0⟩) hz
        · omega
      rw [he, bytesOf_self input _ (Nat.le_of_lt hstart), ByteArray.append_empty, Nat.sub_self,
        afterColumns_zero]
    · have hz0' : ((contentBytes s.val.tokenContent).size == 1 &&
          (contentBytes s.val.tokenContent).get! 0 == 48) = false := by
        simpa using hz0
      have := feedFrom_mode v C.concrete input isDigit isDigit_ne (.numeral false)
        (fun q l c hm hc => advance_numeral_run C.concrete q l c hm hc) start
        ⟨Mode.numeral ((contentBytes s.val.tokenContent).size == 1 &&
          (contentBytes s.val.tokenContent).get! 0 == 48), pstart,
          pcontent⟩ location (by rw [hz0']) (Nat.le_of_lt hstart)
      rw [← hJ] at this
      rw [this]
  -- the zero flag after the run
  have hzero : isZero (contentBytes s.val.tokenContent ++ bytesOf input start
      (Lexer.Internal.WRustPort.Slice.runEnd input start CharClass.RUN_DIGIT)) = isZero
          (contentBytes s.val.tokenContent)
          := by
    by_cases hz0 : isZero (contentBytes s.val.tokenContent) = true
    · have he : Lexer.Internal.WRustPort.Slice.runEnd input start CharClass.RUN_DIGIT = start
        := by
        rcases Nat.lt_or_ge start (Lexer.Internal.WRustPort.Slice.runEnd input start
            CharClass.RUN_DIGIT) with hgt | hge
        · exact absurd (by simp only [Bool.and_eq_true, decide_eq_true_eq]
                           exact ⟨hgt, (Bool.and_eq_true _ _).mp hz0⟩) hz
        · omega
      rw [he, bytesOf_self input _ (Nat.le_of_lt hstart), ByteArray.append_empty]
    · have hz0' : isZero (contentBytes s.val.tokenContent) = false := by simpa using hz0
      rw [hz0', isZero_append _ _ hsz hz0']
  have hLE := hloc.afterColumns (Nat.le_of_eq hpre.base) hle
  unfold Lexer.Internal.WRustPort.extendContent Lexer.Internal.WRustPort.modifyContent
  apply WP.wp_bind; apply WP.wp_modifyCore
  split
  · -- a byte ends the digits inside the slice
    rename_i next hgetE
    obtain ⟨hEs, hEc⟩ := get?_eq hgetE
    have hEd := hstop hEs
    rw [hEc] at hEd
    apply WP.wp_ite
    · -- a dot: the fraction follows
      intro hdot
      have hdot' : next = 46 := by simpa using hdot
      have hB : feedFrom v C.concrete input (.token p) location start =
          feedFrom v C.concrete input (.token ⟨.fraction false, p.start,
              (p.content ++ bytesOf input start
            (Lexer.Internal.WRustPort.Slice.runEnd input start CharClass.RUN_DIGIT)).push 46⟩)
            (afterColumns location (Lexer.Internal.WRustPort.Slice.runEnd input start
                CharClass.RUN_DIGIT + 1 - start))
            (Lexer.Internal.WRustPort.Slice.runEnd input start CharClass.RUN_DIGIT + 1) := by
        rw [hA, feedFrom_step hEs (byteStep_token_pending v C.concrete
            (by rw [hEc, hdot']; rfl)), prep_nil,
          hEc, hdot', afterByte_eq_afterColumns' _ _ (by decide), afterColumns_add]
        congr 3
        omega
      unfold Lexer.Internal.WRustPort.pushContent Lexer.Internal.WRustPort.modifyContent
      apply WP.wp_bind; apply WP.wp_modifyCore
      apply WP.wp_bind
      refine WP.wp_mono (fractionFrom_wp (hd := hd) (iv := iv) v input
          (Lexer.Internal.WRustPort.Slice.runEnd input start CharClass.RUN_DIGIT + 1)
        (by omega) start hstart (by omega) tokenStart base h _ coll (.token p) location held
        ⟨.fraction false, p.start, (p.content ++ bytesOf input start
          (Lexer.Internal.WRustPort.Slice.runEnd input start CharClass.RUN_DIGIT)).push 46⟩
        (afterColumns location (Lexer.Internal.WRustPort.Slice.runEnd input start
            CharClass.RUN_DIGIT + 1 - start))
        ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ hB hts.symm) ?_ ?_
      · exact ⟨hpre.fixed.1, hpre.fixed.2, hpre.fixed.3, hpre.fixed.4,
            hpre.fixed.5, hpre.fixed.6⟩
      · exact hpre.base
      · exact hpre.holds
      · exact hpre.bytes
      · exact hloc.afterColumns (Nat.le_of_eq hpre.base)
          (show start ≤ Lexer.Internal.WRustPort.Slice.runEnd input start CharClass.RUN_DIGIT
              + 1 by omega)
      · exact hlow
      · exact hb
      · show _ = Mode.fraction (fractionChecks (contentBytes ((s.val.tokenContent.extendFrom
          input.byteArray (input.start + start)
          (input.start + Lexer.Internal.WRustPort.Slice.runEnd input start
              CharClass.RUN_DIGIT)).push 46)))
        rw [contentBytes_push hfits', fractionChecks_dot]
      · exact hps.trans hts.symm
      · show _ = contentBytes ((s.val.tokenContent.extendFrom input.byteArray (input.start + start)
          (input.start + Lexer.Internal.WRustPort.Slice.runEnd input start
              CharClass.RUN_DIGIT)).push 46)
        rw [contentBytes_push hfits', hext, hcont]
      · exact fits_push hfits' 46
      · intro r s' coll' hpost
        obtain ⟨e, he⟩ := r
        exact hpost
      · intro e s' coll' hf
        exact hf
    · -- the numeral ends before the byte
      intro hdot
      have hdot' : next ≠ 46 := by simpa using hdot
      have hC := feedFrom_end v C.concrete input hEs (q := ⟨.numeral (isZero (contentBytes
          s.val.tokenContent)), p.start,
          p.content ++ bytesOf input start (Lexer.Internal.WRustPort.Slice.runEnd input start
              CharClass.RUN_DIGIT)⟩)
        (location := afterColumns location (Lexer.Internal.WRustPort.Slice.runEnd input start
            CharClass.RUN_DIGIT - start))
        (advance_end_numeral rfl (by rw [hEc]; exact hEd) (by rw [hEc]; exact hdot'))
      rw [← hA, hEc] at hC
      unfold Lexer.Internal.WRustPort.expectDelimiter Lexer.Internal.WRustPort.finishNumeral
      apply WP.wp_bind
      apply WP.wp_ite
      · intro hnd
        have hnd' : Lexer.Internal.VNaive.isDelimiter next = false := by
          rw [← isDelimiter_eq]; simpa using hnd
        rw [hnd'] at hC
        unfold Lexer.Internal.WRustPort.errorAt Lexer.Internal.WRustPort.errorWith
        wp_walk
        refine stepFails_here ?_ hpre.holds
          ⟨hpre.fixed.1, hpre.fixed.2, hpre.fixed.3, hpre.fixed.4, hpre.fixed.5, hpre.fixed.6⟩ rfl
        rw [hC]
        simp only [Bool.false_eq_true, ↓reduceIte]
        rw [hps]
        have := hpre.base
        failure_eq hloc
      · intro hd
        have hd' : Lexer.Internal.VNaive.isDelimiter next = true := by
          rw [← isDelimiter_eq]; simpa using hd
        rw [hd'] at hC
        simp only [↓reduceIte] at hC
        apply WP.wp_pure
        apply WP.wp_bind
        refine sinkStored_wp .numeral (.mkAtByte _) tokenStart base h held _ ?_ coll ?_ ?_
          ?_ ?_
        · exact hpre.holds
        · exact hpre.fixed.recovers
        · exact hfits'
        · intro s1 coll1 hk1 hb1 hc1
          obtain ⟨k1, k2, k3, k4, k5, k6, k7, k8, k9, k10, k11⟩ := key_fields hk1
          unfold Lexer.Internal.WRustPort.setNormal
          apply WP.wp_bind; apply WP.wp_modifyCore
          apply WP.wp_pure
          have hstep := stepLocation_eq (pos := Lexer.Internal.WRustPort.Slice.runEnd input start
            CharClass.RUN_DIGIT) hloc hpre.base hb hlow hle
          refine armPost_finish (s0 := _) ⟨hpre.fixed.1, hpre.fixed.2, hpre.fixed.3, hpre.fixed.4,
            hpre.fixed.5, hpre.fixed.6⟩
            hpre.base hle hpre.bytes ⟨k1, k4, k3, k5, rfl, k8, k9, k10, k11, hb1⟩ hLE hc1 ?_
          rw [hC]
          show _ = Prep [⟨.numeral, contentBytes (s.val.tokenContent.extendFrom input.byteArray
              (input.start + start)
            (input.start + (Lexer.Internal.WRustPort.Slice.runEnd input start
                CharClass.RUN_DIGIT))), tokenStart,
            stepLocation s.val low base (Lexer.Internal.WRustPort.Slice.runEnd input start
                CharClass.RUN_DIGIT)⟩]
            (feedFrom v C.concrete input .idle (afterColumns location
                (Lexer.Internal.WRustPort.Slice.runEnd input start
              CharClass.RUN_DIGIT - start))
                  (Lexer.Internal.WRustPort.Slice.runEnd input start CharClass.RUN_DIGIT))
          rw [hext, hstep, hts, ← hps, ← hcont]
        · intro e s' p d hn hss
          have hstep := stepLocation_eq (pos := Lexer.Internal.WRustPort.Slice.runEnd input start
            CharClass.RUN_DIGIT) hloc hpre.base hb hlow hle
          have hn' : Stops C s.val.holding s.val.version coll
              (held ++ [⟨.numeral, contentBytes (s.val.tokenContent.extendFrom
              input.byteArray (input.start + start)
            (input.start + (Lexer.Internal.WRustPort.Slice.runEnd input start
                CharClass.RUN_DIGIT))), tokenStart,
              stepLocation s.val low base (Lexer.Internal.WRustPort.Slice.runEnd input start
                CharClass.RUN_DIGIT)⟩]) e p d := hn
          rw [hext, hstep, hts, ← hps, ← hcont] at hn'
          exact stepFails_of_stops' (hbytes := by first | assumption | exact hpre.bytes) hss (by
              first
              | exact ⟨hfix.1, hfix.2, hfix.3, hfix.4, hfix.5, hfix.6⟩
              | exact ⟨hpre.fixed.1, hpre.fixed.2, hpre.fixed.3, hpre.fixed.4, hpre.fixed.5,
                  hpre.fixed.6⟩)
            ⟨_, by rw [hC, outcome_pending_prep] <;> rfl⟩ hn'
  · -- the digits run to the end of the slice: the numeral is left in progress
    rename_i hgetE
    have hsz' := Lexer.Internal.WRustPort.Slice.size_le_of_get?_none hgetE
    apply WP.wp_pure
    refine armPost_pending (s0 := s.val) hpre.fixed hpre.base
      (show start < Lexer.Internal.WRustPort.Slice.runEnd input start
          CharClass.RUN_DIGIT by omega) hpre.holds hpre.bytes
      ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ ?_ hLE hA
    refine ⟨?_, hfits'⟩
    show TokenAgrees v C.concrete s.val.state s.val.tokenStart
      (contentBytes (s.val.tokenContent.extendFrom input.byteArray (input.start + start)
            (input.start + (Lexer.Internal.WRustPort.Slice.runEnd input start
                CharClass.RUN_DIGIT)))) _
    rw [hext, hstate]
    refine ⟨hps, ?_, ?_, ?_⟩
    · show _ = Mode.numeral (isZero (contentBytes s.val.tokenContent ++ bytesOf input start _))
      rw [hzero]
    · show p.content ++ _ = _
      rw [hcont]
    · show (contentBytes s.val.tokenContent ++ bytesOf input start _).size ≠ 0
      rw [ByteArray.size_append]
      omega

end

end BSmtLib.Facts.Proofs.Lexer.VNaiveWRustPort.ArmsNumbers
