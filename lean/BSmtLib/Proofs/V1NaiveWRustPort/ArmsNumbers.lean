import BSmtLib.Proofs.V1NaiveWRustPort.Arms

/-!
# The arms of the Rust port's `lexStep` for numbers

The arms of `lexStep` for the base selection after a `#`, for a fraction after its dot and for
a numeral, which may go on to a fraction.
-/

namespace BSmtLib.Proofs.Lexer.V1NaiveWRustPort

open BSmtLib.Proofs.Adapter V1Naive BSmtLib.Proofs.Simulation
open Lexer.Slice (get? get)

section

variable {floor : Option Nat} {low : Nat}

/-- The arm of `lexStep` for the base selection after a `#`. -/
theorem arm_baseSelection (v : Version) (input : ByteSlice) (start : Nat)
    (hstart : start < input.size) (tokenStart : Location)
    (h : Lexer.WRustPort.Started floor low tokenStart) (s : BS floor low) (coll : Collector)
    (p : Pending) (location : Location) (held : List Lexeme)
    (hpre : StepPre v input (.token p) location held start s.val)
    (hts : tokenStart = s.val.tokenStart) (hstate : s.val.state = .baseSelection) :
    WP (Lexer.WRustPort.lexBaseSelection (H := Collector) (m := Id) (R := Empty) (E := Unit)
        input start tokenStart h) s coll
      (fun r s' coll' => ArmPost v input (.token p) location start coll held r.1 s'.val coll')
      (fun _ _ _ => StepFails v input (.token p) location start coll held) := by
  obtain ⟨hps, hm, hcont⟩ := token_agrees hpre.agrees hstate
  have hloc := hpre.loc
  obtain ⟨mode, pstart, pcontent⟩ := p
  simp only at hps hm hcont
  subst hm
  unfold Lexer.WRustPort.lexBaseSelection Lexer.WRustPort.setTokenState
  rw [get_eq hstart]
  dsimp only
  apply wp_ite
  · intro hx
    have hx' : input[start] = 120 := by simpa using hx
    apply wp_bind; apply wp_modifyBound
    apply wp_pure
    refine armPost_pending (s0 := s.val) hpre.fixed hpre.base (show start < start + 1 by omega)
      hpre.holds hpre.bytes ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
      (q := ⟨.digits .hexadecimal, pstart, pcontent⟩)
      ⟨⟨by show pstart = tokenStart; rw [hps, hts], rfl, hcont⟩, (show Fits s.val.tokenContent from
          token_fits hpre.agrees)⟩
      (hloc.afterByte (Nat.le_of_eq hpre.base) (b := input[start]) (by rw [hx']; decide)) ?_
    rw [feedFrom_step hstart (byteStep_token_pending v (by rw [hx']; rfl)), prep_nil]
  · intro hx
    apply wp_ite
    · intro hb'
      have hb'' : input[start] = 98 := by simpa using hb'
      apply wp_bind; apply wp_modifyBound
      apply wp_pure
      refine armPost_pending (s0 := s.val) hpre.fixed hpre.base (show start < start + 1 by omega)
        hpre.holds hpre.bytes ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
        (q := ⟨.digits .binary, pstart, pcontent⟩)
        ⟨⟨by show pstart = tokenStart; rw [hps, hts], rfl, hcont⟩, (show Fits s.val.tokenContent
            from token_fits hpre.agrees)⟩
        (hloc.afterByte (Nat.le_of_eq hpre.base) (b := input[start]) (by rw [hb'']; decide)) ?_
      rw [feedFrom_step hstart (byteStep_token_pending v (by rw [hb'']; rfl)), prep_nil]
    · intro hb'
      have hx' : input[start] ≠ 120 := by simpa using hx
      have hb'' : input[start] ≠ 98 := by simpa using hb'
      have herr : ∃ f, advance false ⟨.hash, pstart, pcontent⟩ location input[start] = .error f :=
        by
        simp [advance, hx', hb'']
      obtain ⟨f, hf⟩ := herr
      unfold Lexer.WRustPort.errorAt Lexer.WRustPort.errorWith
      wp_walk
      show outcome v _ _ = none
      rw [feedFrom_advance_error v input hstart hf, outcome_none_right]

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
theorem fractionFrom_wp (v : Version) (input : ByteSlice) (j : Nat) (hj : j ≤ input.size)
    (start0 : Nat) (hstart0 : start0 < input.size) (hj0 : start0 ≤ j) (tokenStart : Location)
    (base : Nat) (h : Lexer.WRustPort.Started floor low tokenStart) (s : BS floor low)
    (coll : Collector) (st0 : St) (loc0 : Location) (held : List Lexeme) (q : Pending)
    (locq : Location) (hfix : Fixed v s.val) (hbase0 : s.val.base = start0)
    (hholds : Holds s.val.batch held) (hbytes : s.val.batch.bytes = input.byteArray)
    (hloc : LocAt s.val s.val.offset s.val.base j locq) (hlow : low = s.val.offset)
    (hb : base = s.val.base)
    (hq : q.mode = .fraction (fractionChecks (contentBytes s.val.tokenContent))) (hqs : q.start =
        tokenStart)
    (hqc : q.content = contentBytes s.val.tokenContent) (hfits : Fits s.val.tokenContent)
    (hanchor : feedFrom v input st0 loc0 start0 = feedFrom v input (.token q) locq j) :
    WP (Lexer.WRustPort.lexFractionFrom (H := Collector) (m := Id) (R := Empty) (E := Unit)
        input j tokenStart base h) s coll
      (fun r s' coll' => ArmPost v input st0 loc0 start0 coll held r.1 s'.val coll')
      (fun _ _ _ => StepFails v input st0 loc0 start0 coll held) := by
  have hJ : Lexer.Slice.runEnd input j Lexer.RUN_DIGIT = runEnd input isDigit j :=
    runEnd_eq endsRun_digit _ _
  have hle := le_runEnd input isDigit j
  have hle' := runEnd_le input isDigit j hj
  have hstop := fun h => runEnd_stop input isDigit j h
  have hmem := runEnd_mem input isDigit j
  have hA := feedFrom_fraction v input j q locq _ hq hj
  rw [← hJ] at hA hle hle' hstop hmem
  have hext : contentBytes (s.val.tokenContent.extendFrom input.byteArray (input.start + j)
      (input.start + Lexer.Slice.runEnd input j Lexer.RUN_DIGIT)) =
      contentBytes s.val.tokenContent ++ bytesOf input j (Lexer.Slice.runEnd input j
          Lexer.RUN_DIGIT) :=
    contentBytes_extendSlice input hfits (.inl hle')
  have hfits' := fits_extendSlice input hfits (a := j) (.inl hle')
  have hfc := fractionChecks_run input (contentBytes s.val.tokenContent) hle hle' hmem
  have hA' : feedFrom v input st0 loc0 start0 =
      feedFrom v input (.token ⟨.fraction (fractionChecks (contentBytes s.val.tokenContent ++
          bytesOf input j (Lexer.Slice.runEnd input j Lexer.RUN_DIGIT))), tokenStart,
          contentBytes s.val.tokenContent ++ bytesOf input j (Lexer.Slice.runEnd input j
              Lexer.RUN_DIGIT)⟩)
        (afterColumns locq (Lexer.Slice.runEnd input j Lexer.RUN_DIGIT - j))
        (Lexer.Slice.runEnd input j Lexer.RUN_DIGIT) := by
    rw [hanchor, hA, hfc, hqs, hqc]
  have hLJ := hloc.afterColumns (by rw [hbase0]; exact hj0) hle
  unfold Lexer.WRustPort.lexFractionFrom Lexer.WRustPort.extendContent Lexer.WRustPort.modifyContent
  apply wp_bind; apply wp_modifyCore
  dsimp only
  apply wp_ite
  · -- the digits end inside the slice: the decimal is finished
    intro hEs
    have hEs' := hstop hEs
    unfold Lexer.WRustPort.finishDecimal
    apply wp_bind
    apply wp_bind; apply wp_getCore
    dsimp only
    apply wp_ite
    · -- no digit after the dot
      intro hbad
      have hfc' : fractionChecks (contentBytes s.val.tokenContent ++
          bytesOf input j (Lexer.Slice.runEnd input j Lexer.RUN_DIGIT)) = false := by
        simp only [fractionChecks, Bool.not_eq_false']
        rw [← hext, ← last?_stored hfits']
        exact hbad
      obtain ⟨f, hf⟩ := advance_end_fraction_none (location := afterColumns locq
        (Lexer.Slice.runEnd input j Lexer.RUN_DIGIT - j))
        (q := ⟨.fraction (fractionChecks (contentBytes s.val.tokenContent ++
          bytesOf input j (Lexer.Slice.runEnd input j Lexer.RUN_DIGIT))), tokenStart,
          contentBytes s.val.tokenContent ++ bytesOf input j (Lexer.Slice.runEnd input j
              Lexer.RUN_DIGIT)⟩)
        (by rw [hfc']) hEs'
      unfold Lexer.WRustPort.error Lexer.WRustPort.errorWith
      wp_walk
      show outcome v _ _ = none
      rw [hA', feedFrom_advance_error v input hEs hf, outcome_none_right]
    · intro hgood
      have hfc' : fractionChecks (contentBytes s.val.tokenContent ++
          bytesOf input j (Lexer.Slice.runEnd input j Lexer.RUN_DIGIT)) = true := by
        simp only [fractionChecks, Bool.not_eq_true']
        rw [← hext, ← last?_stored hfits']
        exact Bool.eq_false_iff.mpr hgood
      have hC := feedFrom_end v input hEs
        (q := ⟨.fraction (fractionChecks (contentBytes s.val.tokenContent ++
          bytesOf input j (Lexer.Slice.runEnd input j Lexer.RUN_DIGIT))), tokenStart,
          contentBytes s.val.tokenContent ++ bytesOf input j (Lexer.Slice.runEnd input j
              Lexer.RUN_DIGIT)⟩)
        (location := afterColumns locq (Lexer.Slice.runEnd input j Lexer.RUN_DIGIT - j))
        (advance_end_fraction (by rw [hfc']) hEs')
      rw [← hA'] at hC
      unfold Lexer.WRustPort.expectDelimiter
      rw [get_eq hEs]
      apply wp_bind
      apply wp_ite
      · intro hnd
        have hnd' : V1Naive.isDelimiter
            input[Lexer.Slice.runEnd input j Lexer.RUN_DIGIT] = false := by
          rw [← isDelimiter_eq]; simpa using hnd
        rw [hnd'] at hC
        unfold Lexer.WRustPort.errorAt Lexer.WRustPort.errorWith
        wp_walk
        show outcome v _ _ = none
        rw [hC]
        simp only [Bool.false_eq_true, ↓reduceIte, outcome_none_right]
      · intro hd
        have hd' : V1Naive.isDelimiter
            input[Lexer.Slice.runEnd input j Lexer.RUN_DIGIT] = true := by
          rw [← isDelimiter_eq]; simpa using hd
        rw [hd'] at hC
        simp only [↓reduceIte] at hC
        apply wp_pure
        refine sinkStored_wp v .decimal (.mkAtByte _) tokenStart base h held _ ?_ coll ?_ ?_
          ?_ ?_ ?_
        · exact hholds
        · exact hfix.recovers
        · exact hfix.version
        · exact hfits'
        · intro s1 coll1 hk1 hb1 hc1
          obtain ⟨k1, k2, k3, k4, k5, k6, k7, k8, k9, k10, k11⟩ := key_fields hk1
          unfold Lexer.WRustPort.setNormal
          apply wp_bind; apply wp_modifyCore
          apply wp_pure
          have hstep := stepLocation_eq' (pos := Lexer.Slice.runEnd input j Lexer.RUN_DIGIT)
            hloc (by rw [hbase0]; exact hj0) hb hlow hle
          refine armPost_finish (s0 := _) ⟨hfix.1, hfix.2, hfix.3, hfix.4⟩
            hbase0 (show start0 ≤ Lexer.Slice.runEnd input j Lexer.RUN_DIGIT by omega) hbytes
            ⟨k1, k4, k3, k5, rfl, k8, k9, k10, k11, hb1⟩
            hLJ hc1 ?_
          rw [hC]
          show _ = Prep [⟨.decimal, contentBytes (s.val.tokenContent.extendFrom input.byteArray
              (input.start + j)
            (input.start + (Lexer.Slice.runEnd input j Lexer.RUN_DIGIT))), tokenStart,
            stepLocation s.val low base (Lexer.Slice.runEnd input j Lexer.RUN_DIGIT)⟩]
            (feedFrom v input .idle (afterColumns locq (Lexer.Slice.runEnd input j
              Lexer.RUN_DIGIT - j)) (Lexer.Slice.runEnd input j Lexer.RUN_DIGIT))
          rw [hext, hstep]
        · intro hn e s' coll'
          show outcome v _ _ = none
          rw [hC, outcome_prep]
          have hstep := stepLocation_eq' (pos := Lexer.Slice.runEnd input j Lexer.RUN_DIGIT)
            hloc (by rw [hbase0]; exact hj0) hb hlow hle
          have hn' : pending v coll (held ++ [⟨.decimal, contentBytes (s.val.tokenContent.extendFrom
              input.byteArray (input.start + j)
            (input.start + (Lexer.Slice.runEnd input j Lexer.RUN_DIGIT))), tokenStart,
              stepLocation s.val low base (Lexer.Slice.runEnd input j Lexer.RUN_DIGIT)⟩]) =
              none := hn
          rw [hext, hstep] at hn'
          exact (congrArg (fun x => outcome v x _) hn').trans (outcome_none_left v _)
  · -- the digits run to the end of the slice: the fraction is left in progress
    intro hEs
    unfold Lexer.WRustPort.setTokenState
    apply wp_bind; apply wp_modifyBound
    apply wp_pure
    refine armPost_pending (s0 := s.val) hfix hbase0
      (show start0 < Lexer.Slice.runEnd input j Lexer.RUN_DIGIT by omega) hholds hbytes
      ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ ?_ hLJ hA'
    refine ⟨?_, hfits'⟩
    show TokenAgrees v .fraction tokenStart (contentBytes (s.val.tokenContent.extendFrom
      input.byteArray (input.start + j) (input.start + Lexer.Slice.runEnd input j Lexer.RUN_DIGIT)))
      _
    rw [hext]
    exact ⟨rfl, rfl, rfl⟩

/-- The check of the numeral arm for a single `0` before its run. -/
abbrev isZero (content : ByteArray) : Bool :=
  content.size == 1 && content.get! 0 == byte! '0'

/-- The check of the numeral arm reads the content buffer as its content. -/
theorem isZero_contentBytes {buf : BSmtLib.Lexer.ContentBuffer} (h : Fits buf) :
    isZero (contentBytes buf) = (buf.len == 1 && buf.bytes.get! 0 == byte! '0') := by
  unfold isZero
  rw [size_contentBytes h]
  by_cases h1 : buf.len = 1
  · simp only [h1, beq_self_eq_true, Bool.true_and, get!_eq_getElem!,
      get!_contentBytes h (show 0 < buf.len by omega)]
  · have h1' : (buf.len == 1) = false := by simpa using h1
    simp [h1']

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

/-- The arm of `lexStep` for a numeral, which may go on to a fraction. -/
theorem arm_numeralOrDecimal (v : Version) (input : ByteSlice) (start : Nat)
    (hstart : start < input.size) (tokenStart : Location) (base : Nat)
    (h : Lexer.WRustPort.Started floor low tokenStart) (s : BS floor low) (coll : Collector)
    (p : Pending) (location : Location) (held : List Lexeme)
    (hpre : StepPre v input (.token p) location held start s.val) (hlow : low = s.val.offset)
    (hts : tokenStart = s.val.tokenStart) (hb : base = s.val.base)
    (hstate : s.val.state = .numeralOrDecimal) :
    WP (Lexer.WRustPort.lexNumeralOrDecimal (H := Collector) (m := Id) (R := Empty) (E := Unit)
        input start tokenStart base h) s coll
      (fun r s' coll' => ArmPost v input (.token p) location start coll held r.1 s'.val coll')
      (fun _ _ _ => StepFails v input (.token p) location start coll held) := by
  obtain ⟨hps, hm, hcont, hsz⟩ := token_agrees hpre.agrees hstate
  have hJ : Lexer.Slice.runEnd input start Lexer.RUN_DIGIT = runEnd input isDigit start :=
    runEnd_eq endsRun_digit _ _
  have hle := le_runEnd input isDigit start
  have hle' := runEnd_le input isDigit start (Nat.le_of_lt hstart)
  have hstop := fun h => runEnd_stop input isDigit start h
  have hmem := runEnd_mem input isDigit start
  rw [← hJ] at hle hle' hstop hmem
  have hfits := token_fits hpre.agrees
  have hext : contentBytes (s.val.tokenContent.extendFrom input.byteArray (input.start + start)
      (input.start + Lexer.Slice.runEnd input start Lexer.RUN_DIGIT)) =
      contentBytes s.val.tokenContent ++
        bytesOf input start (Lexer.Slice.runEnd input start Lexer.RUN_DIGIT) :=
    contentBytes_extendSlice input hfits (.inl hle')
  have hfits' := fits_extendSlice input hfits (a := start) (.inl hle')
  have hloc := hpre.loc
  unfold Lexer.WRustPort.lexNumeralOrDecimal
  apply wp_bind; apply wp_getCore
  dsimp only
  apply wp_ite
  · -- a single `0` followed by a digit
    intro hz
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hz
    obtain ⟨hlt, hzero⟩ := hz
    have hd := hmem start hstart (Nat.le_refl _) hlt
    have hf : ∃ f, advance false p location input[start] = .error f := by
      obtain ⟨mode, pstart, pcontent⟩ := p
      simp only at hm
      subst hm
      have : ((contentBytes s.val.tokenContent).size == 1 &&
          (contentBytes s.val.tokenContent).get! 0 == 48) = true := by
        have e := isZero_contentBytes hfits
        unfold isZero at e
        rw [e]
        exact Bool.and_eq_true _ _ ▸ hzero
      simp [advance, this, hd]
    obtain ⟨f, hf⟩ := hf
    unfold Lexer.WRustPort.errorAt Lexer.WRustPort.errorWith
    wp_walk
    show outcome v _ _ = none
    rw [feedFrom_advance_error v input hstart hf, outcome_none_right]
  intro hz
  rw [← isZero_contentBytes hfits] at hz
  have hA : feedFrom v input (.token p) location start =
      feedFrom v input (.token ⟨.numeral (isZero (contentBytes s.val.tokenContent)), p.start,
          p.content ++ bytesOf input start (Lexer.Slice.runEnd input start Lexer.RUN_DIGIT)⟩)
        (afterColumns location (Lexer.Slice.runEnd input start Lexer.RUN_DIGIT - start))
        (Lexer.Slice.runEnd input start Lexer.RUN_DIGIT) := by
    obtain ⟨mode, pstart, pcontent⟩ := p
    simp only at hm
    subst hm
    by_cases hz0 : isZero (contentBytes s.val.tokenContent) = true
    · have he : Lexer.Slice.runEnd input start Lexer.RUN_DIGIT = start := by
        rcases Nat.lt_or_ge start (Lexer.Slice.runEnd input start Lexer.RUN_DIGIT) with hgt | hge
        · exact absurd (by simp only [Bool.and_eq_true, decide_eq_true_eq]
                           exact ⟨hgt, (Bool.and_eq_true _ _).mp hz0⟩) hz
        · omega
      rw [he, bytesOf_self input _ (Nat.le_of_lt hstart), ByteArray.append_empty, Nat.sub_self,
        afterColumns_zero]
    · have hz0' : ((contentBytes s.val.tokenContent).size == 1 &&
          (contentBytes s.val.tokenContent).get! 0 == 48) = false := by
        simpa using hz0
      have := feedFrom_mode v input isDigit isDigit_ne (.numeral false)
        (fun q l c hm hc => advance_numeral_run false q l c hm hc) start
        ⟨Mode.numeral ((contentBytes s.val.tokenContent).size == 1 &&
          (contentBytes s.val.tokenContent).get! 0 == 48), pstart,
          pcontent⟩ location (by rw [hz0']) (Nat.le_of_lt hstart)
      rw [← hJ] at this
      rw [this]
  -- the zero flag after the run
  have hzero : isZero (contentBytes s.val.tokenContent ++ bytesOf input start
      (Lexer.Slice.runEnd input start Lexer.RUN_DIGIT)) = isZero (contentBytes s.val.tokenContent)
          := by
    by_cases hz0 : isZero (contentBytes s.val.tokenContent) = true
    · have he : Lexer.Slice.runEnd input start Lexer.RUN_DIGIT = start := by
        rcases Nat.lt_or_ge start (Lexer.Slice.runEnd input start Lexer.RUN_DIGIT) with hgt | hge
        · exact absurd (by simp only [Bool.and_eq_true, decide_eq_true_eq]
                           exact ⟨hgt, (Bool.and_eq_true _ _).mp hz0⟩) hz
        · omega
      rw [he, bytesOf_self input _ (Nat.le_of_lt hstart), ByteArray.append_empty]
    · have hz0' : isZero (contentBytes s.val.tokenContent) = false := by simpa using hz0
      rw [hz0', isZero_append _ _ hsz hz0']
  have hLE := hloc.afterColumns (Nat.le_of_eq hpre.base) hle
  unfold Lexer.WRustPort.extendContent Lexer.WRustPort.modifyContent
  apply wp_bind; apply wp_modifyCore
  split
  · -- a byte ends the digits inside the slice
    rename_i next hgetE
    obtain ⟨hEs, hEc⟩ := get?_eq hgetE
    have hEd := hstop hEs
    rw [hEc] at hEd
    apply wp_ite
    · -- a dot: the fraction follows
      intro hdot
      have hdot' : next = 46 := by simpa using hdot
      have hB : feedFrom v input (.token p) location start =
          feedFrom v input (.token ⟨.fraction false, p.start, (p.content ++ bytesOf input start
            (Lexer.Slice.runEnd input start Lexer.RUN_DIGIT)).push 46⟩)
            (afterColumns location (Lexer.Slice.runEnd input start Lexer.RUN_DIGIT + 1 - start))
            (Lexer.Slice.runEnd input start Lexer.RUN_DIGIT + 1) := by
        rw [hA, feedFrom_step hEs (byteStep_token_pending v (by rw [hEc, hdot']; rfl)), prep_nil,
          hEc, hdot', afterByte_eq_afterColumns' _ _ (by decide), afterColumns_add]
        congr 3
        omega
      unfold Lexer.WRustPort.pushContent Lexer.WRustPort.modifyContent
      apply wp_bind; apply wp_modifyCore
      apply wp_bind
      refine wp_mono (fractionFrom_wp v input (Lexer.Slice.runEnd input start Lexer.RUN_DIGIT + 1)
        (by omega) start hstart (by omega) tokenStart base h _ coll (.token p) location held
        ⟨.fraction false, p.start, (p.content ++ bytesOf input start
          (Lexer.Slice.runEnd input start Lexer.RUN_DIGIT)).push 46⟩
        (afterColumns location (Lexer.Slice.runEnd input start Lexer.RUN_DIGIT + 1 - start))
        ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ hB) ?_ ?_
      · exact ⟨hpre.fixed.1, hpre.fixed.2, hpre.fixed.3, hpre.fixed.4⟩
      · exact hpre.base
      · exact hpre.holds
      · exact hpre.bytes
      · exact hloc.afterColumns (Nat.le_of_eq hpre.base)
          (show start ≤ Lexer.Slice.runEnd input start Lexer.RUN_DIGIT + 1 by omega)
      · exact hlow
      · exact hb
      · show _ = Mode.fraction (fractionChecks (contentBytes ((s.val.tokenContent.extendFrom
          input.byteArray (input.start + start)
          (input.start + Lexer.Slice.runEnd input start Lexer.RUN_DIGIT)).push 46)))
        rw [contentBytes_push hfits', fractionChecks_dot]
      · exact hps.trans hts.symm
      · show _ = contentBytes ((s.val.tokenContent.extendFrom input.byteArray (input.start + start)
          (input.start + Lexer.Slice.runEnd input start Lexer.RUN_DIGIT)).push 46)
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
      have hC := feedFrom_end v input hEs (q := ⟨.numeral (isZero (contentBytes
          s.val.tokenContent)), p.start,
          p.content ++ bytesOf input start (Lexer.Slice.runEnd input start Lexer.RUN_DIGIT)⟩)
        (location := afterColumns location (Lexer.Slice.runEnd input start Lexer.RUN_DIGIT - start))
        (advance_end_numeral rfl (by rw [hEc]; exact hEd) (by rw [hEc]; exact hdot'))
      rw [← hA, hEc] at hC
      unfold Lexer.WRustPort.expectDelimiter Lexer.WRustPort.finishNumeral
      apply wp_bind
      apply wp_ite
      · intro hnd
        have hnd' : V1Naive.isDelimiter next = false := by
          rw [← isDelimiter_eq]; simpa using hnd
        rw [hnd'] at hC
        unfold Lexer.WRustPort.errorAt Lexer.WRustPort.errorWith
        wp_walk
        show outcome v _ _ = none
        rw [hC]
        simp only [Bool.false_eq_true, ↓reduceIte, outcome_none_right]
      · intro hd
        have hd' : V1Naive.isDelimiter next = true := by
          rw [← isDelimiter_eq]; simpa using hd
        rw [hd'] at hC
        simp only [↓reduceIte] at hC
        apply wp_pure
        apply wp_bind
        refine sinkStored_wp v .numeral (.mkAtByte _) tokenStart base h held _ ?_ coll ?_ ?_
          ?_ ?_ ?_
        · exact hpre.holds
        · exact hpre.fixed.recovers
        · exact hpre.fixed.version
        · exact hfits'
        · intro s1 coll1 hk1 hb1 hc1
          obtain ⟨k1, k2, k3, k4, k5, k6, k7, k8, k9, k10, k11⟩ := key_fields hk1
          unfold Lexer.WRustPort.setNormal
          apply wp_bind; apply wp_modifyCore
          apply wp_pure
          have hstep := stepLocation_eq (pos := Lexer.Slice.runEnd input start
            Lexer.RUN_DIGIT) hloc hpre.base hb hlow hle
          refine armPost_finish (s0 := _) ⟨hpre.fixed.1, hpre.fixed.2, hpre.fixed.3, hpre.fixed.4⟩
            hpre.base hle hpre.bytes ⟨k1, k4, k3, k5, rfl, k8, k9, k10, k11, hb1⟩ hLE hc1 ?_
          rw [hC]
          show _ = Prep [⟨.numeral, contentBytes (s.val.tokenContent.extendFrom input.byteArray
              (input.start + start)
            (input.start + (Lexer.Slice.runEnd input start Lexer.RUN_DIGIT))), tokenStart,
            stepLocation s.val low base (Lexer.Slice.runEnd input start Lexer.RUN_DIGIT)⟩]
            (feedFrom v input .idle (afterColumns location (Lexer.Slice.runEnd input start
              Lexer.RUN_DIGIT - start)) (Lexer.Slice.runEnd input start Lexer.RUN_DIGIT))
          rw [hext, hstep, hts, ← hps, ← hcont]
        · intro hn e s' coll'
          show outcome v _ _ = none
          rw [hC, outcome_prep]
          have hstep := stepLocation_eq (pos := Lexer.Slice.runEnd input start
            Lexer.RUN_DIGIT) hloc hpre.base hb hlow hle
          have hn' : pending v coll (held ++ [⟨.numeral, contentBytes (s.val.tokenContent.extendFrom
              input.byteArray (input.start + start)
            (input.start + (Lexer.Slice.runEnd input start Lexer.RUN_DIGIT))), tokenStart,
              stepLocation s.val low base (Lexer.Slice.runEnd input start
                Lexer.RUN_DIGIT)⟩]) = none := hn
          rw [hext, hstep, hts, ← hps, ← hcont] at hn'
          exact (congrArg (fun x => outcome v x _) hn').trans (outcome_none_left v _)
  · -- the digits run to the end of the slice: the numeral is left in progress
    rename_i hgetE
    have hsz' := Lexer.Slice.size_le_of_get?_none hgetE
    apply wp_pure
    refine armPost_pending (s0 := s.val) hpre.fixed hpre.base
      (show start < Lexer.Slice.runEnd input start Lexer.RUN_DIGIT by omega) hpre.holds hpre.bytes
      ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ ?_ hLE hA
    refine ⟨?_, hfits'⟩
    show TokenAgrees v s.val.state s.val.tokenStart
      (contentBytes (s.val.tokenContent.extendFrom input.byteArray (input.start + start)
            (input.start + (Lexer.Slice.runEnd input start Lexer.RUN_DIGIT)))) _
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

end BSmtLib.Proofs.Lexer.V1NaiveWRustPort
