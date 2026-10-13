import BSmtLib.Proofs.VNaiveWRustPort.ArmsQuoted

/-!
# The arms of the Rust port's `lexStep` over a run

The arms of `lexStep` for a simple symbol, a keyword, the digits of a hexadecimal or binary
literal and a comment: each takes the run of bytes that its token takes as they are, and ends
the token at the byte after the run, or leaves it in progress at the end of the slice.
-/

namespace BSmtLib.Proofs.Lexer.VNaiveWRustPort

open BSmtLib.Proofs.Adapter VNaive BSmtLib.Proofs.Simulation
open BSmtLibSpec.Lexer (Handed)
open Lexer.Slice (get? get)

section

variable {floor : Option Nat} {low : Nat}
variable {C : BSmtLibSpec.Lexer.Consumer} {hd : Bool} {iv : Version}

/-- The arm of `lexStep` for a simple symbol. -/
theorem arm_simpleSymbol (v : Version) (input : ByteSlice) (start : Nat)
    (hstart : start < input.size) (tokenStart : Location) (base : Nat)
    (h : Lexer.WRustPort.Started floor low tokenStart) (s : BS floor low) (coll : List Handed)
    (p : Pending) (location : Location) (held : List Lexeme)
    (hpre : StepPre C v hd iv input (.token p) location held start s.val)
        (hlow : low = s.val.offset)
    (hts : tokenStart = s.val.tokenStart) (hb : base = s.val.base)
    (hstate : s.val.state = .simpleSymbol) :
    WP (Lexer.WRustPort.lexSimpleSymbol (H := Answering C) (m := AnswerM) (R := C.Result)
        (E := Option C.Error)
        input start tokenStart base h) s coll
      (fun r s' coll' => ArmPost C v hd iv input (.token p) location start s.val.version coll held
          r.1 s'.val coll')
      (fun e s' coll' => StepFails C v hd iv input (.token p) location start s.val.version coll held
          e s'.val coll') := by
  obtain ⟨hps, hm, hcont⟩ := token_agrees hpre.agrees hstate
  have hJ : Lexer.Slice.runEnd input start Lexer.RUN_SIMPLE_SYMBOL =
      runEnd input isSymbolByte start := runEnd_eq endsRun_symbol _ _
  have hle := le_runEnd input isSymbolByte start
  have hle' := runEnd_le input isSymbolByte start (Nat.le_of_lt hstart)
  have hstop := fun h => runEnd_stop input isSymbolByte start h
  have hA := feedFrom_mode v C.concrete input isSymbolByte isSymbolByte_ne .simpleSymbol
    (fun q l c hm hc => advance_simpleSymbol_run C.concrete q l c hm hc) start p location hm
    (Nat.le_of_lt hstart)
  rw [← hJ] at hA hle hle' hstop
  have hfits := token_fits hpre.agrees
  have hext : contentBytes (s.val.tokenContent.extendFrom input.byteArray (input.start + start)
      (input.start + Lexer.Slice.runEnd input start Lexer.RUN_SIMPLE_SYMBOL)) =
      contentBytes s.val.tokenContent ++ bytesOf input start (Lexer.Slice.runEnd input start
          Lexer.RUN_SIMPLE_SYMBOL) :=
    contentBytes_extendSlice input hfits (.inl hle')
  have hfits' := fits_extendSlice input hfits (a := start) (.inl hle')
  have hloc := hpre.loc
  unfold Lexer.WRustPort.lexSimpleSymbol Lexer.WRustPort.extendContent Lexer.WRustPort.modifyContent
  apply wp_bind; apply wp_modifyCore
  dsimp only
  apply wp_dite
  · -- the symbol ends inside the slice
    intro hJs
    have hJs' := hstop hJs
    have hC := feedFrom_end v C.concrete input hJs
      (q := ⟨p.mode, p.start, p.content ++ bytesOf input start
        (Lexer.Slice.runEnd input start Lexer.RUN_SIMPLE_SYMBOL)⟩)
      (location := afterColumns location (Lexer.Slice.runEnd input start
        Lexer.RUN_SIMPLE_SYMBOL - start))
      (advance_end_simpleSymbol hm hJs')
    rw [← hA] at hC
    unfold Lexer.WRustPort.expectDelimiter Lexer.WRustPort.finishSimpleSymbol
    rw [get_eq hJs]
    apply wp_bind
    apply wp_ite
    · intro hnd
      have hnd' : VNaive.isDelimiter
          input[Lexer.Slice.runEnd input start Lexer.RUN_SIMPLE_SYMBOL] = false := by
        rw [← isDelimiter_eq]; simpa using hnd
      rw [hnd'] at hC
      unfold Lexer.WRustPort.errorAt Lexer.WRustPort.errorWith
      wp_walk
      refine stepFails_here ?_ hpre.holds
        ⟨hpre.fixed.1, hpre.fixed.2, hpre.fixed.3, hpre.fixed.4, hpre.fixed.5, hpre.fixed.6⟩ rfl
      rw [hC]
      simp only [Bool.false_eq_true, ↓reduceIte]
    · intro hd
      have hd' : VNaive.isDelimiter
          input[Lexer.Slice.runEnd input start Lexer.RUN_SIMPLE_SYMBOL] = true := by
        rw [← isDelimiter_eq]; simpa using hd
      rw [hd'] at hC
      simp only [↓reduceIte] at hC
      apply wp_pure
      apply wp_bind
      refine sinkStored_wp .unquotedSymbol (.mkAtByte _) tokenStart base h held _ ?_ coll ?_ ?_
        ?_ ?_
      · exact hpre.holds
      · exact hpre.fixed.recovers
      · exact hfits'
      · intro s1 coll1 hk1 hb1 hc1
        obtain ⟨k1, k2, k3, k4, k5, k6, k7, k8, k9, k10, k11⟩ := key_fields hk1
        unfold Lexer.WRustPort.setNormal
        apply wp_bind; apply wp_modifyCore
        apply wp_pure
        have hstep := stepLocation_eq (pos := Lexer.Slice.runEnd input start
          Lexer.RUN_SIMPLE_SYMBOL) hloc hpre.base hb hlow hle
        refine armPost_finish (s0 := _) ⟨hpre.fixed.1, hpre.fixed.2, hpre.fixed.3, hpre.fixed.4,
            hpre.fixed.5, hpre.fixed.6⟩
          hpre.base hle hpre.bytes ⟨k1, k4, k3, k5, rfl, k8, k9, k10, k11, hb1⟩
          (hloc.afterColumns (Nat.le_of_eq hpre.base) hle) hc1 ?_
        rw [hC]
        show _ = Prep [⟨.unquotedSymbol, contentBytes (s.val.tokenContent.extendFrom input.byteArray
            (input.start + start)
            (input.start + (Lexer.Slice.runEnd input start Lexer.RUN_SIMPLE_SYMBOL))), tokenStart,
          stepLocation s.val low base (Lexer.Slice.runEnd input start Lexer.RUN_SIMPLE_SYMBOL)⟩]
          (feedFrom v C.concrete input .idle (afterColumns location (Lexer.Slice.runEnd input start
            Lexer.RUN_SIMPLE_SYMBOL - start)) (Lexer.Slice.runEnd input start
              Lexer.RUN_SIMPLE_SYMBOL))
        rw [hext, hstep, hts, ← hps, ← hcont]
      · intro e s' p d hn hss
        have hstep := stepLocation_eq (pos := Lexer.Slice.runEnd input start
          Lexer.RUN_SIMPLE_SYMBOL) hloc hpre.base hb hlow hle
        have hn' : Stops C s.val.holding s.val.version coll (held ++ [⟨.unquotedSymbol, contentBytes
            (s.val.tokenContent.extendFrom input.byteArray (input.start + start)
            (input.start + (Lexer.Slice.runEnd input start
              Lexer.RUN_SIMPLE_SYMBOL))), tokenStart,
            stepLocation s.val low base (Lexer.Slice.runEnd input start
              Lexer.RUN_SIMPLE_SYMBOL)⟩]) e p d := hn
        rw [hext, hstep, hts, ← hps, ← hcont] at hn'
        exact stepFails_of_stops' (hbytes := by first | assumption | exact hpre.bytes) hss (by
            first
            | exact ⟨hfix.1, hfix.2, hfix.3, hfix.4, hfix.5, hfix.6⟩
            | exact ⟨hpre.fixed.1, hpre.fixed.2, hpre.fixed.3, hpre.fixed.4, hpre.fixed.5,
                hpre.fixed.6⟩)
          ⟨_, by rw [hC, outcome_pending_prep] <;> rfl⟩ hn'
  · -- the symbol runs to the end of the slice: it is left in progress
    intro hJs
    apply wp_pure
    have hJe : Lexer.Slice.runEnd input start Lexer.RUN_SIMPLE_SYMBOL = input.size := by omega
    refine armPost_pending (s0 := s.val) hpre.fixed hpre.base
      (show start < Lexer.Slice.runEnd input start Lexer.RUN_SIMPLE_SYMBOL by omega) hpre.holds
      hpre.bytes
      ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ ?_ ?_ hA
    · refine ⟨?_, hfits'⟩
      show TokenAgrees v C.concrete s.val.state s.val.tokenStart
        (contentBytes (s.val.tokenContent.extendFrom input.byteArray (input.start + start)
            (input.start + (Lexer.Slice.runEnd input start Lexer.RUN_SIMPLE_SYMBOL)))) _
      rw [hext, hstate]
      exact ⟨hps, hm, by rw [hcont]⟩
    · exact hloc.afterColumns (Nat.le_of_eq hpre.base) hle

/-- The arm of `lexStep` for a keyword. -/
theorem arm_keyword (v : Version) (input : ByteSlice) (start : Nat)
    (hstart : start < input.size) (tokenStart : Location) (base : Nat)
    (h : Lexer.WRustPort.Started floor low tokenStart) (s : BS floor low) (coll : List Handed)
    (p : Pending) (location : Location) (held : List Lexeme)
    (hpre : StepPre C v hd iv input (.token p) location held start s.val)
        (hlow : low = s.val.offset)
    (hts : tokenStart = s.val.tokenStart) (hb : base = s.val.base)
    (hstate : s.val.state = .keyword) :
    WP (Lexer.WRustPort.lexKeyword (H := Answering C) (m := AnswerM) (R := C.Result)
        (E := Option C.Error)
        input start tokenStart base h) s coll
      (fun r s' coll' => ArmPost C v hd iv input (.token p) location start s.val.version coll held
          r.1 s'.val coll')
      (fun e s' coll' => StepFails C v hd iv input (.token p) location start s.val.version coll held
          e s'.val coll') := by
  obtain ⟨hps, hm, hcont⟩ := token_agrees hpre.agrees hstate
  have hJ : Lexer.Slice.runEnd input start Lexer.RUN_SIMPLE_SYMBOL =
      runEnd input isSymbolByte start := runEnd_eq endsRun_symbol _ _
  have hle := le_runEnd input isSymbolByte start
  have hle' := runEnd_le input isSymbolByte start (Nat.le_of_lt hstart)
  have hstop := fun h => runEnd_stop input isSymbolByte start h
  have hA := feedFrom_mode v C.concrete input isSymbolByte isSymbolByte_ne .keyword
    (fun q l c hm hc => advance_keyword_run C.concrete q l c hm hc) start p location hm
    (Nat.le_of_lt hstart)
  rw [← hJ] at hA hle hle' hstop
  have hfits := token_fits hpre.agrees
  have hext : contentBytes (s.val.tokenContent.extendFrom input.byteArray (input.start + start)
      (input.start + Lexer.Slice.runEnd input start Lexer.RUN_SIMPLE_SYMBOL)) =
      contentBytes s.val.tokenContent ++ bytesOf input start (Lexer.Slice.runEnd input start
          Lexer.RUN_SIMPLE_SYMBOL) :=
    contentBytes_extendSlice input hfits (.inl hle')
  have hfits' := fits_extendSlice input hfits (a := start) (.inl hle')
  have hloc := hpre.loc
  unfold Lexer.WRustPort.lexKeyword Lexer.WRustPort.extendContent Lexer.WRustPort.modifyContent
  apply wp_bind; apply wp_modifyCore
  dsimp only
  apply wp_dite
  · -- the keyword ends inside the slice
    intro hJs
    have hJs' := hstop hJs
    unfold Lexer.WRustPort.finishKeyword
    apply wp_bind
    apply wp_bind; apply wp_getCore
    apply wp_ite
    · -- an empty keyword
      intro hempty
      have he : (p.content ++ bytesOf input start
          (Lexer.Slice.runEnd input start Lexer.RUN_SIMPLE_SYMBOL)).isEmpty = true := by
        rw [hcont, ← hext]; unfold ByteArray.isEmpty; rw [size_contentBytes hfits']; exact hempty
      obtain ⟨f, hf⟩ := advance_end_keyword_empty (location := afterColumns location
        (Lexer.Slice.runEnd input start Lexer.RUN_SIMPLE_SYMBOL - start))
        (q := ⟨p.mode, p.start, p.content ++ bytesOf input start
          (Lexer.Slice.runEnd input start Lexer.RUN_SIMPLE_SYMBOL)⟩) hm hJs' he
      unfold Lexer.WRustPort.error Lexer.WRustPort.errorWith
      wp_walk
      refine stepFails_here ?_ hpre.holds
        ⟨hpre.fixed.1, hpre.fixed.2, hpre.fixed.3, hpre.fixed.4, hpre.fixed.5, hpre.fixed.6⟩ rfl
      rw [hA, feedFrom_advance_error v C.concrete input hJs hf]
    intro hne
    have hne' : (p.content ++ bytesOf input start
        (Lexer.Slice.runEnd input start Lexer.RUN_SIMPLE_SYMBOL)).isEmpty = false := by
      rw [hcont, ← hext]
      simp only [ByteArray.isEmpty, beq_eq_false_iff_ne, size_contentBytes hfits']
      intro h0
      exact hne (by show (_ == 0) = true; rw [beq_iff_eq]; exact h0)
    have hC := feedFrom_end v C.concrete input hJs
      (q := ⟨p.mode, p.start, p.content ++ bytesOf input start
        (Lexer.Slice.runEnd input start Lexer.RUN_SIMPLE_SYMBOL)⟩)
      (location := afterColumns location (Lexer.Slice.runEnd input start
        Lexer.RUN_SIMPLE_SYMBOL - start))
      (advance_end_keyword hm hJs' hne')
    rw [← hA] at hC
    try apply wp_pure
    dsimp only
    unfold Lexer.WRustPort.expectDelimiter
    rw [get_eq hJs]
    apply wp_bind
    apply wp_ite
    · intro hnd
      have hnd' : VNaive.isDelimiter
          input[Lexer.Slice.runEnd input start Lexer.RUN_SIMPLE_SYMBOL] = false := by
        rw [← isDelimiter_eq]; simpa using hnd
      rw [hnd'] at hC
      unfold Lexer.WRustPort.errorAt Lexer.WRustPort.errorWith
      wp_walk
      refine stepFails_here ?_ hpre.holds
        ⟨hpre.fixed.1, hpre.fixed.2, hpre.fixed.3, hpre.fixed.4, hpre.fixed.5, hpre.fixed.6⟩ rfl
      rw [hC]
      simp only [Bool.false_eq_true, ↓reduceIte]
    · intro hd
      have hd' : VNaive.isDelimiter
          input[Lexer.Slice.runEnd input start Lexer.RUN_SIMPLE_SYMBOL] = true := by
        rw [← isDelimiter_eq]; simpa using hd
      rw [hd'] at hC
      simp only [↓reduceIte] at hC
      apply wp_pure
      refine sinkStored_wp .keyword (.mkAtByte _) tokenStart base h held _ ?_ coll ?_ ?_
        ?_ ?_
      · exact hpre.holds
      · exact hpre.fixed.recovers
      · exact hfits'
      · intro s1 coll1 hk1 hb1 hc1
        obtain ⟨k1, k2, k3, k4, k5, k6, k7, k8, k9, k10, k11⟩ := key_fields hk1
        unfold Lexer.WRustPort.setNormal
        apply wp_bind; apply wp_modifyCore
        apply wp_pure
        have hstep := stepLocation_eq (pos := Lexer.Slice.runEnd input start
          Lexer.RUN_SIMPLE_SYMBOL) hloc hpre.base hb hlow hle
        refine armPost_finish (s0 := _) ⟨hpre.fixed.1, hpre.fixed.2, hpre.fixed.3, hpre.fixed.4,
            hpre.fixed.5, hpre.fixed.6⟩
          hpre.base hle hpre.bytes ⟨k1, k4, k3, k5, rfl, k8, k9, k10, k11, hb1⟩
          (hloc.afterColumns (Nat.le_of_eq hpre.base) hle) hc1 ?_
        rw [hC]
        show _ = Prep [⟨.keyword, contentBytes (s.val.tokenContent.extendFrom input.byteArray
            (input.start + start)
            (input.start + (Lexer.Slice.runEnd input start Lexer.RUN_SIMPLE_SYMBOL))), tokenStart,
          stepLocation s.val low base (Lexer.Slice.runEnd input start Lexer.RUN_SIMPLE_SYMBOL)⟩]
          (feedFrom v C.concrete input .idle (afterColumns location (Lexer.Slice.runEnd input start
            Lexer.RUN_SIMPLE_SYMBOL - start)) (Lexer.Slice.runEnd input start
              Lexer.RUN_SIMPLE_SYMBOL))
        rw [hext, hstep, hts, ← hps, ← hcont]
      · intro e s' p d hn hss
        have hstep := stepLocation_eq (pos := Lexer.Slice.runEnd input start
          Lexer.RUN_SIMPLE_SYMBOL) hloc hpre.base hb hlow hle
        have hn' : Stops C s.val.holding s.val.version coll (held ++
            [⟨.keyword, contentBytes (s.val.tokenContent.extendFrom
            input.byteArray (input.start + start)
            (input.start + (Lexer.Slice.runEnd input start Lexer.RUN_SIMPLE_SYMBOL))), tokenStart,
            stepLocation s.val low base (Lexer.Slice.runEnd input start
              Lexer.RUN_SIMPLE_SYMBOL)⟩]) e p d := hn
        rw [hext, hstep, hts, ← hps, ← hcont] at hn'
        exact stepFails_of_stops' (hbytes := by first | assumption | exact hpre.bytes) hss (by
            first
            | exact ⟨hfix.1, hfix.2, hfix.3, hfix.4, hfix.5, hfix.6⟩
            | exact ⟨hpre.fixed.1, hpre.fixed.2, hpre.fixed.3, hpre.fixed.4, hpre.fixed.5,
                hpre.fixed.6⟩)
          ⟨_, by rw [hC, outcome_pending_prep] <;> rfl⟩ hn'
  · -- the keyword runs to the end of the slice: it is left in progress
    intro hJs
    apply wp_pure
    have hJe : Lexer.Slice.runEnd input start Lexer.RUN_SIMPLE_SYMBOL = input.size := by omega
    refine armPost_pending (s0 := s.val) hpre.fixed hpre.base
      (show start < Lexer.Slice.runEnd input start Lexer.RUN_SIMPLE_SYMBOL by omega) hpre.holds
      hpre.bytes ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ ?_ ?_ hA
    · refine ⟨?_, hfits'⟩
      show TokenAgrees v C.concrete s.val.state s.val.tokenStart
        (contentBytes (s.val.tokenContent.extendFrom input.byteArray (input.start + start)
            (input.start + (Lexer.Slice.runEnd input start Lexer.RUN_SIMPLE_SYMBOL)))) _
      rw [hext, hstate]
      exact ⟨hps, hm, by rw [hcont]⟩
    · exact hloc.afterColumns (Nat.le_of_eq hpre.base) hle


/-- The arm of `lexStep` for the digits of a hexadecimal or binary literal. -/
theorem arm_digitRun (v : Version) (input : ByteSlice) (start : Nat)
    (hstart : start < input.size) (tokenStart : Location) (base : Nat)
    (h : Lexer.WRustPort.Started floor low tokenStart) (s : BS floor low) (coll : List Handed)
    (p : Pending) (location : Location) (held : List Lexeme)
    (hpre : StepPre C v hd iv input (.token p) location held start s.val)
        (hlow : low = s.val.offset)
    (hts : tokenStart = s.val.tokenStart) (hb : base = s.val.base)
    (run : Lexer.DigitRun)
    (radix : Radix) (hflag : ∀ c, Lexer.endsRun c run.flag = !radix.allows c)
    (htyp : run.tokenType = radix.category)
    (hinv : ∀ st content q, TokenAgrees v C.concrete s.val.state st content q →
      q.start = st ∧ q.mode = .digits radix ∧ q.content = content)
    (hnotr : run.emptyError ≠ .unexpectedTrailingToken)
    (hagr : ∀ (q : Pending) st content, q.mode = .digits radix → q.start = st →
      q.content = content → TokenAgrees v C.concrete s.val.state st content q) :
    WP (Lexer.WRustPort.lexDigitRun (H := Answering C) (m := AnswerM) (R := C.Result)
        (E := Option C.Error)
        input start run tokenStart base h) s coll
      (fun r s' coll' => ArmPost C v hd iv input (.token p) location start s.val.version coll held
          r.1 s'.val coll')
      (fun e s' coll' => StepFails C v hd iv input (.token p) location start s.val.version coll held
          e s'.val coll') := by
  obtain ⟨hps, hm, hcont⟩ := hinv _ _ _ hpre.agrees.1
  have hJ : Lexer.Slice.runEnd input start run.flag =
      runEnd input radix.allows start := runEnd_eq hflag _ _
  have hle := le_runEnd input radix.allows start
  have hle' := runEnd_le input radix.allows start (Nat.le_of_lt hstart)
  have hstop := fun h => runEnd_stop input radix.allows start h
  have hA := feedFrom_mode v C.concrete input radix.allows (allows_ne radix) (.digits radix)
    (fun q l c hm hc => advance_digits_run radix C.concrete q l c hm hc) start p location hm
    (Nat.le_of_lt hstart)
  rw [← hJ] at hA hle hle' hstop
  have hfits := token_fits hpre.agrees
  have hext : contentBytes (s.val.tokenContent.extendFrom input.byteArray (input.start + start)
      (input.start + Lexer.Slice.runEnd input start run.flag)) =
      contentBytes s.val.tokenContent ++ bytesOf input start (Lexer.Slice.runEnd input start
          run.flag) :=
    contentBytes_extendSlice input hfits (.inl hle')
  have hfits' := fits_extendSlice input hfits (a := start) (.inl hle')
  have hloc := hpre.loc
  unfold Lexer.WRustPort.lexDigitRun Lexer.WRustPort.extendContent Lexer.WRustPort.modifyContent
  apply wp_bind; apply wp_modifyCore
  dsimp only
  apply wp_dite
  · -- the digits ends inside the slice
    intro hJs
    have hJs' := hstop hJs
    unfold Lexer.WRustPort.finishDigitRun
    apply wp_bind
    apply wp_bind; apply wp_getCore
    apply wp_ite
    · -- no digit
      intro hempty
      have he : (p.content ++ bytesOf input start
          (Lexer.Slice.runEnd input start run.flag)).isEmpty = true := by
        rw [hcont, ← hext]; unfold ByteArray.isEmpty; rw [size_contentBytes hfits']; exact hempty
      obtain ⟨f, hf⟩ := advance_end_digits_empty (location := afterColumns location
        (Lexer.Slice.runEnd input start run.flag - start))
        (q := ⟨p.mode, p.start, p.content ++ bytesOf input start
          (Lexer.Slice.runEnd input start run.flag)⟩) hm hJs' he
      unfold Lexer.WRustPort.error Lexer.WRustPort.errorWith
      wp_walk
      refine stepFails_here (he := ⟨_, rfl, hnotr⟩) ?_ hpre.holds
        ⟨hpre.fixed.1, hpre.fixed.2, hpre.fixed.3, hpre.fixed.4, hpre.fixed.5, hpre.fixed.6⟩ rfl
      rw [hA, feedFrom_advance_error v C.concrete input hJs hf]
    intro hne
    have hne' : (p.content ++ bytesOf input start
        (Lexer.Slice.runEnd input start run.flag)).isEmpty = false := by
      rw [hcont, ← hext]
      simp only [ByteArray.isEmpty, beq_eq_false_iff_ne, size_contentBytes hfits']
      intro h0
      exact hne (by show (_ == 0) = true; rw [beq_iff_eq]; exact h0)
    have hC := feedFrom_end v C.concrete input hJs
      (q := ⟨p.mode, p.start, p.content ++ bytesOf input start
        (Lexer.Slice.runEnd input start run.flag)⟩)
      (location := afterColumns location (Lexer.Slice.runEnd input start
        run.flag - start))
      (advance_end_digits hm hJs' hne')
    rw [← hA] at hC
    try apply wp_pure
    dsimp only
    unfold Lexer.WRustPort.expectDelimiter
    rw [get_eq hJs]
    apply wp_bind
    apply wp_ite
    · intro hnd
      have hnd' : VNaive.isDelimiter
          input[Lexer.Slice.runEnd input start run.flag] = false := by
        rw [← isDelimiter_eq]; simpa using hnd
      rw [hnd'] at hC
      unfold Lexer.WRustPort.errorAt Lexer.WRustPort.errorWith
      wp_walk
      refine stepFails_here ?_ hpre.holds
        ⟨hpre.fixed.1, hpre.fixed.2, hpre.fixed.3, hpre.fixed.4, hpre.fixed.5, hpre.fixed.6⟩ rfl
      rw [hC]
      simp only [Bool.false_eq_true, ↓reduceIte]
    · intro hd
      have hd' : VNaive.isDelimiter
          input[Lexer.Slice.runEnd input start run.flag] = true := by
        rw [← isDelimiter_eq]; simpa using hd
      rw [hd'] at hC
      simp only [↓reduceIte] at hC
      apply wp_pure
      refine sinkStored_wp run.tokenType (.mkAtByte _) tokenStart base h held _ ?_ coll ?_ ?_
        ?_ ?_
      · exact hpre.holds
      · exact hpre.fixed.recovers
      · exact hfits'
      · intro s1 coll1 hk1 hb1 hc1
        obtain ⟨k1, k2, k3, k4, k5, k6, k7, k8, k9, k10, k11⟩ := key_fields hk1
        unfold Lexer.WRustPort.setNormal
        apply wp_bind; apply wp_modifyCore
        apply wp_pure
        have hstep := stepLocation_eq (pos := Lexer.Slice.runEnd input start
          run.flag) hloc hpre.base hb hlow hle
        refine armPost_finish (s0 := _) ⟨hpre.fixed.1, hpre.fixed.2, hpre.fixed.3, hpre.fixed.4,
            hpre.fixed.5, hpre.fixed.6⟩
          hpre.base hle hpre.bytes ⟨k1, k4, k3, k5, rfl, k8, k9, k10, k11, hb1⟩
          (hloc.afterColumns (Nat.le_of_eq hpre.base) hle) hc1 ?_
        rw [hC]
        show _ = Prep [⟨run.tokenType, contentBytes (s.val.tokenContent.extendFrom input.byteArray
            (input.start + start)
            (input.start + (Lexer.Slice.runEnd input start run.flag))), tokenStart,
          stepLocation s.val low base (Lexer.Slice.runEnd input start run.flag)⟩]
          (feedFrom v C.concrete input .idle (afterColumns location (Lexer.Slice.runEnd input start
            run.flag - start)) (Lexer.Slice.runEnd input start
              run.flag))
        rw [hext, hstep, hts, ← hps, ← hcont, htyp]
      · intro e s' p d hn hss
        have hstep := stepLocation_eq (pos := Lexer.Slice.runEnd input start
          run.flag) hloc hpre.base hb hlow hle
        have hn' : Stops C s.val.holding s.val.version coll (held ++ [⟨run.tokenType, contentBytes
            (s.val.tokenContent.extendFrom input.byteArray (input.start + start)
            (input.start + (Lexer.Slice.runEnd input start run.flag))), tokenStart,
            stepLocation s.val low base (Lexer.Slice.runEnd input start
              run.flag)⟩]) e p d := hn
        rw [hext, hstep, hts, ← hps, ← hcont, htyp] at hn'
        exact stepFails_of_stops' (hbytes := by first | assumption | exact hpre.bytes) hss (by
            first
            | exact ⟨hfix.1, hfix.2, hfix.3, hfix.4, hfix.5, hfix.6⟩
            | exact ⟨hpre.fixed.1, hpre.fixed.2, hpre.fixed.3, hpre.fixed.4, hpre.fixed.5,
                hpre.fixed.6⟩)
          ⟨_, by rw [hC, outcome_pending_prep] <;> rfl⟩ hn'
  · -- the digits runs to the end of the slice: it is left in progress
    intro hJs
    apply wp_pure
    have hJe : Lexer.Slice.runEnd input start run.flag = input.size := by omega
    refine armPost_pending (s0 := s.val) hpre.fixed hpre.base
      (show start < Lexer.Slice.runEnd input start run.flag by omega) hpre.holds
      hpre.bytes ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ ?_ ?_ hA
    · refine ⟨?_, hfits'⟩
      show TokenAgrees v C.concrete s.val.state s.val.tokenStart
        (contentBytes (s.val.tokenContent.extendFrom input.byteArray (input.start + start)
            (input.start + (Lexer.Slice.runEnd input start run.flag)))) _
      rw [hext]
      exact hagr _ _ _ hm hps (by rw [hcont])
    · exact hloc.afterColumns (Nat.le_of_eq hpre.base) hle

/-- The arm of `lexStep` for a comment, which the consumer takes. -/
theorem arm_comment_ws (v : Version) (input : ByteSlice) (start : Nat)
    (hstart : start < input.size) (tokenStart : Location) (base : Nat)
    (h : Lexer.WRustPort.Started floor low tokenStart) (s : BS floor low) (coll : List Handed)
    (p : Pending) (location : Location) (held : List Lexeme)
    (hpre : StepPre C v hd iv input (.token p) location held start s.val)
    (hlow : low = s.val.offset) (hts : tokenStart = s.val.tokenStart) (hb : base = s.val.base)
    (hstate : s.val.state = .comment) (hcon : C.concrete = true) :
    WP (Lexer.WRustPort.lexComment (H := Answering C) (m := AnswerM) (R := C.Result)
        (E := Option C.Error) input start (Nat.le_of_lt hstart) tokenStart base h) s coll
      (fun r s' coll' =>
        ArmPost C v hd iv input (.token p) location start s.val.version coll held r.1 s'.val coll')
      (fun e s' coll' =>
        StepFails C v hd iv input (.token p) location start s.val.version coll held e s'.val
          coll') := by
  obtain ⟨hps, (hm : p.mode = .comment), hcont⟩ := token_agrees hpre.agrees hstate
  have hcont' : p.content = contentBytes s.val.tokenContent := hcont hcon
  have hfits := token_fits hpre.agrees
  have hJ : Lexer.Slice.runEnd input start Lexer.RUN_COMMENT_PLAIN =
      runEnd input isCommentRun start := runEnd_eq endsRun_comment _ _
  have hle := le_runEnd input isCommentRun start
  have hle' := runEnd_le input isCommentRun start (Nat.le_of_lt hstart)
  have hstop := fun h => runEnd_stop input isCommentRun start h
  have hA := feedFrom_mode v C.concrete input isCommentRun isCommentRun_ne .comment
    (fun q l c hm hc => advance_comment_run C.concrete q l c hm hc) start p location hm
    (Nat.le_of_lt hstart)
  rw [← hJ] at hA hle hle' hstop
  have hloc := hpre.loc
  have hLJ := hloc.afterColumns (Nat.le_of_eq hpre.base) hle
  unfold Lexer.WRustPort.lexComment Lexer.WRustPort.consumesWhitespaceAndComments
  dsimp only
  split
  rotate_left
  · -- the comment ends inside the slice, with its line break, and is handed over
    rename_i c hget
    obtain ⟨hJs, hJc⟩ := get?_eq hget
    have hJs' := hstop hJs
    rw [hJc] at hJs'
    have hext : contentBytes (s.val.tokenContent.extendFrom input.byteArray (input.start + start)
        (input.start + (Lexer.Slice.runEnd input start Lexer.RUN_COMMENT_PLAIN + 1))) =
        (p.content ++ bytesOf input start
          (Lexer.Slice.runEnd input start Lexer.RUN_COMMENT_PLAIN)).push c := by
      rw [contentBytes_extendSlice input hfits (.inl (by omega)), content_succ input _ hle hJs,
        hJc, hcont']
    have hfits' := fits_extendSlice input hfits (a := start)
      (b := Lexer.Slice.runEnd input start Lexer.RUN_COMMENT_PLAIN + 1) (.inl (by omega))
    have hB : feedFrom v C.concrete input (.token p) location start =
        Prep [⟨.comment, (p.content ++ bytesOf input start
            (Lexer.Slice.runEnd input start Lexer.RUN_COMMENT_PLAIN)).push c, p.start,
            (afterColumns location (Lexer.Slice.runEnd input start Lexer.RUN_COMMENT_PLAIN -
              start)).afterByte c⟩]
          (feedFrom v C.concrete input .idle
            ((afterColumns location (Lexer.Slice.runEnd input start Lexer.RUN_COMMENT_PLAIN -
              start)).afterByte c) (Lexer.Slice.runEnd input start
                  Lexer.RUN_COMMENT_PLAIN + 1)) := by
      have hadv : advance C.concrete ⟨p.mode, p.start, p.content ++ bytesOf input start
          (Lexer.Slice.runEnd input start Lexer.RUN_COMMENT_PLAIN)⟩ (afterColumns location
          (Lexer.Slice.runEnd input start Lexer.RUN_COMMENT_PLAIN - start))
          input[Lexer.Slice.runEnd input start Lexer.RUN_COMMENT_PLAIN] =
          .tokenWith ⟨.comment, (p.content ++ bytesOf input start
            (Lexer.Slice.runEnd input start Lexer.RUN_COMMENT_PLAIN)).push c, p.start,
            (afterColumns location (Lexer.Slice.runEnd input start Lexer.RUN_COMMENT_PLAIN -
              start)).afterByte c⟩ := by
        rw [hm, hJc, hcon]; exact advance_comment_end_ws _ _ _ hJs'
      rw [hA, feedFrom_step hJs (byteStep_token_with hadv), hJc]
    -- the hand-over of the comment from the lexer state `s1`, at the location `locp`
    have finish : ∀ (s1 : BS floor low) (locp : Location),
        s1.val = { s.val with
          tokenContent := s.val.tokenContent.extendFrom input.byteArray (input.start + start)
            (input.start + (Lexer.Slice.runEnd input start Lexer.RUN_COMMENT_PLAIN + 1)),
          line := s1.val.line, lineStart := s1.val.lineStart } →
        LocAt s1.val s1.val.offset s1.val.base
          (Lexer.Slice.runEnd input start Lexer.RUN_COMMENT_PLAIN + 1) locp →
        locp = (afterColumns location (Lexer.Slice.runEnd input start Lexer.RUN_COMMENT_PLAIN -
          start)).afterByte c →
        WP (do
            Lexer.WRustPort.sinkStored (H := Answering C) (m := AnswerM) (R := C.Result)
              (E := Option C.Error) .comment
              (.mkAtByte (Lexer.Slice.runEnd input start Lexer.RUN_COMMENT_PLAIN + 1))
              tokenStart base h
            Lexer.WRustPort.setNormal
            (pure ⟨Lexer.Slice.runEnd input start Lexer.RUN_COMMENT_PLAIN + 1, by omega⟩ :
              M C floor low {next : Nat // start ≤ next})) s1 coll
          (fun r s' coll' =>
            ArmPost C v hd iv input (.token p) location start s.val.version coll held r.1 s'.val
              coll')
          (fun e s' coll' =>
            StepFails C v hd iv input (.token p) location start s.val.version coll held e s'.val
              coll') := by
      intro s1 locp hs1 hlocp hlp
      have e1 : s1.val.version = s.val.version := by rw [hs1]
      have hfix1 : Fixed v hd iv s1.val := by
        rw [hs1]; exact ⟨hpre.fixed.1, hpre.fixed.2, hpre.fixed.3, hpre.fixed.4, hpre.fixed.5,
          hpre.fixed.6⟩
      have hbase1 : s1.val.base = start := by rw [hs1]; exact hpre.base
      have hholds1 : Holds s1.val.batch held := by rw [hs1]; exact hpre.holds
      have hbytes1 : s1.val.batch.bytes = input.byteArray := by rw [hs1]; exact hpre.bytes
      have hfits1 : Fits s1.val.tokenContent := by rw [hs1]; exact hfits'
      have hcont1 : contentBytes s1.val.tokenContent = (p.content ++ bytesOf input start
          (Lexer.Slice.runEnd input start Lexer.RUN_COMMENT_PLAIN)).push c := by
        rw [hs1]; exact hext
      have hlow1 : low = s1.val.offset := by rw [hs1]; exact hlow
      have hb1 : base = s1.val.base := by rw [hs1]; exact hb
      have hstep := stepLocation_eq' (pos := Lexer.Slice.runEnd input start
        Lexer.RUN_COMMENT_PLAIN + 1) hlocp (by rw [hbase1]; omega) hb1 hlow1 (Nat.le_refl _)
      rw [Nat.sub_self, afterColumns_zero] at hstep
      have hl : (⟨.comment, contentBytes s1.val.tokenContent, tokenStart,
          stepLocation s1.val low base
            (Lexer.Slice.TokenEnd.mkAtByte (Lexer.Slice.runEnd input start
              Lexer.RUN_COMMENT_PLAIN + 1)).position⟩ : Lexeme) =
          ⟨.comment, (p.content ++ bytesOf input start
            (Lexer.Slice.runEnd input start Lexer.RUN_COMMENT_PLAIN)).push c, p.start, locp⟩ := by
        rw [hcont1, show (Lexer.Slice.TokenEnd.mkAtByte (Lexer.Slice.runEnd input start
          Lexer.RUN_COMMENT_PLAIN + 1)).position = Lexer.Slice.runEnd input start
            Lexer.RUN_COMMENT_PLAIN + 1 from rfl, hstep, hts, ← hps]
      apply wp_bind
      refine sinkStored_wp .comment (.mkAtByte _) tokenStart base h held s1 hholds1 coll
        (hfix1.recovers) hfits1 ?_ ?_
      · intro s2 coll2 hk2 hb2 hc2
        obtain ⟨k1, k2, k3, k4, k5, k6, k7, k8, k9, k10, k11⟩ := key_fields hk2
        unfold Lexer.WRustPort.setNormal
        apply wp_bind; apply wp_modifyCore
        apply wp_pure
        rw [hl] at hc2
        refine armPost_finish (s0 := s1.val) hfix1 hbase1 (Nat.le_succ_of_le hle) hbytes1
          ⟨k1, k4, k3, k5, rfl, k8, k9, k10, k11, hb2⟩ hlocp hc2 ?_ e1
        rw [hB, hlp]
      · intro e s2 p2 d hn hss
        rw [hl] at hn
        exact stepFails_of_stops' hss hfix1 ⟨_, by rw [hB, hlp, outcome_pending_prep, e1]⟩ hn
          hbytes1
    apply wp_ite
    · -- a line feed, which is marked
      intro h10
      have h10' : c = 10 := by simpa using h10
      subst h10'
      unfold Lexer.WRustPort.markLineFeedAt
      apply wp_bind; apply wp_modifyCore
      apply wp_bind; apply wp_pure
      simp only [answering_concrete, hcon, ↓reduceIte]
      unfold Lexer.WRustPort.extendContent Lexer.WRustPort.modifyContent
      apply wp_bind; apply wp_modifyCore
      refine finish _ _ rfl ?_ rfl
      refine LocAt.lineFeed hLJ (by rw [hpre.base]; omega) rfl ?_
      show Lexer.WRustPort.LexerCore.offsetAt _ _ + 1 = _
      simp only [Lexer.WRustPort.LexerCore.offsetAt]
    · -- a carriage return
      intro h10
      have h10' : c ≠ 10 := by simpa using h10
      apply wp_bind; apply wp_pure
      simp only [answering_concrete, hcon, ↓reduceIte]
      unfold Lexer.WRustPort.extendContent Lexer.WRustPort.modifyContent
      apply wp_bind; apply wp_modifyCore
      exact finish _ _ rfl (hLJ.afterByte (by rw [hpre.base]; omega) h10') rfl
  · -- the comment runs to the end of the slice: it is left in progress, with its content
    rename_i hget
    have hJe := Lexer.Slice.size_le_of_get?_none hget
    have e : Lexer.Slice.runEnd input start Lexer.RUN_COMMENT_PLAIN = input.size := by omega
    apply wp_bind; apply wp_pure
    simp only [answering_concrete, hcon, ↓reduceIte]
    unfold Lexer.WRustPort.extendContent Lexer.WRustPort.modifyContent
    apply wp_bind; apply wp_modifyCore
    apply wp_pure
    rw [e] at hA hLJ
    refine armPost_pending (s0 := s.val) hpre.fixed hpre.base
      (show start < input.size by omega) hpre.holds
      hpre.bytes ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ ?_ hLJ hA
    refine ⟨?_, fits_extendSlice input hfits (a := start) (b := input.size) (.inl (by omega))⟩
    show TokenAgrees v C.concrete s.val.state s.val.tokenStart
      (contentBytes (s.val.tokenContent.extendFrom input.byteArray (input.start + start)
        (input.start + input.size))) _
    rw [contentBytes_extendSlice input hfits (a := start) (b := input.size) (.inl (by omega)),
      hstate, hcont']
    exact ⟨hps, hm, fun _ => rfl⟩

/-- The arm of `lexStep` for a comment. -/
theorem arm_comment (v : Version) (input : ByteSlice) (start : Nat)
    (hstart : start < input.size) (tokenStart : Location) (base : Nat)
    (h : Lexer.WRustPort.Started floor low tokenStart) (s : BS floor low) (coll : List Handed)
    (p : Pending) (location : Location) (held : List Lexeme)
    (hpre : StepPre C v hd iv input (.token p) location held start s.val)
    (hlow : low = s.val.offset) (hts : tokenStart = s.val.tokenStart) (hb : base = s.val.base)
    (hstate : s.val.state = .comment) :
    WP (Lexer.WRustPort.lexComment (H := Answering C) (m := AnswerM) (R := C.Result)
        (E := Option C.Error)
        input start (Nat.le_of_lt hstart) tokenStart base h) s coll
      (fun r s' coll' => ArmPost C v hd iv input (.token p) location start s.val.version coll held
          r.1 s'.val coll')
      (fun e s' coll' => StepFails C v hd iv input (.token p) location start s.val.version coll held
          e s'.val coll') := by
  by_cases hcon : C.concrete = true
  · exact arm_comment_ws v input start hstart tokenStart base h s coll p location held hpre hlow
      hts hb hstate hcon
  have hcon' : C.concrete = false := by simpa using hcon
  obtain ⟨hps, (hm : p.mode = .comment), -⟩ := token_agrees hpre.agrees hstate
  have hJ : Lexer.Slice.runEnd input start Lexer.RUN_COMMENT_PLAIN =
      runEnd input isCommentRun start := runEnd_eq endsRun_comment _ _
  have hle := le_runEnd input isCommentRun start
  have hle' := runEnd_le input isCommentRun start (Nat.le_of_lt hstart)
  have hstop := fun h => runEnd_stop input isCommentRun start h
  have hA := feedFrom_mode v C.concrete input isCommentRun isCommentRun_ne .comment
    (fun q l c hm hc => advance_comment_run C.concrete q l c hm hc) start p location hm
    (Nat.le_of_lt hstart)
  rw [← hJ] at hA hle hle' hstop
  have hloc := hpre.loc
  have hLJ := hloc.afterColumns (Nat.le_of_eq hpre.base) hle
  unfold Lexer.WRustPort.lexComment Lexer.WRustPort.consumesWhitespaceAndComments
  dsimp only
  split
  rotate_left
  · -- the comment ends inside the slice, with its line break
    rename_i c hget
    obtain ⟨hJs, hJc⟩ := get?_eq hget
    have hJs' := hstop hJs
    rw [hJc] at hJs'
    have hB : feedFrom v C.concrete input (.token p) location start =
        feedFrom v C.concrete input .idle
          ((afterColumns location (Lexer.Slice.runEnd input start Lexer.RUN_COMMENT_PLAIN -
            start)).afterByte c) (Lexer.Slice.runEnd input start Lexer.RUN_COMMENT_PLAIN + 1) := by
      have hadv : advance false ⟨p.mode, p.start, p.content ++ bytesOf input start
          (Lexer.Slice.runEnd input start Lexer.RUN_COMMENT_PLAIN)⟩ (afterColumns location
          (Lexer.Slice.runEnd input start Lexer.RUN_COMMENT_PLAIN - start))
          input[Lexer.Slice.runEnd input start Lexer.RUN_COMMENT_PLAIN] = .idle := by
        rw [hm, hJc]; exact advance_comment_end _ _ _ hJs'
      rw [hA, feedFrom_step hJs (byteStep_token_idle v C.concrete
          (by rw [hcon']; exact hadv)), prep_nil, hJc]
    apply wp_ite
    · -- a line feed, which is marked
      intro h10
      have h10' : c = 10 := by simpa using h10
      subst h10'
      unfold Lexer.WRustPort.markLineFeedAt
      apply wp_bind; apply wp_modifyCore
      apply wp_bind; apply wp_pure
      simp only [answering_concrete, hcon', Bool.false_eq_true, ↓reduceIte]
      unfold Lexer.WRustPort.setNormal
      apply wp_bind; apply wp_modifyCore
      apply wp_pure
      refine armPost_idle (s0 := s.val) hpre.fixed hpre.base
        (show start < Lexer.Slice.runEnd input start Lexer.RUN_COMMENT_PLAIN + 1 by omega)
        hpre.holds hpre.bytes
        ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ ?_ hB
      refine LocAt.lineFeed hLJ (by rw [hpre.base]; omega) rfl ?_
      show Lexer.WRustPort.LexerCore.offsetAt _ _ + 1 = _
      simp only [Lexer.WRustPort.LexerCore.offsetAt]
    · -- a carriage return
      intro h10
      have h10' : c ≠ 10 := by simpa using h10
      apply wp_bind; apply wp_pure
      simp only [answering_concrete, hcon', Bool.false_eq_true, ↓reduceIte]
      unfold Lexer.WRustPort.setNormal
      apply wp_bind; apply wp_modifyCore
      apply wp_pure
      refine armPost_idle (s0 := s.val) hpre.fixed hpre.base
        (show start < Lexer.Slice.runEnd input start Lexer.RUN_COMMENT_PLAIN + 1 by omega)
        hpre.holds hpre.bytes
        ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ ?_ hB
      exact hLJ.afterByte (by rw [hpre.base]; omega) h10'
  · -- the comment runs to the end of the slice: it is left in progress
    rename_i hget
    have hJe := Lexer.Slice.size_le_of_get?_none hget
    apply wp_bind; apply wp_pure
    simp only [answering_concrete, hcon', Bool.false_eq_true, ↓reduceIte]
    apply wp_pure
    refine armPost_pending (s0 := s.val) hpre.fixed hpre.base
      (show start < input.size by omega) hpre.holds
      hpre.bytes ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ ?_ ?_ (hA.trans (by rw [show
        Lexer.Slice.runEnd input start Lexer.RUN_COMMENT_PLAIN = input.size by omega]))
    · refine ⟨?_, token_fits hpre.agrees⟩
      show TokenAgrees v C.concrete s.val.state s.val.tokenStart (contentBytes s.val.tokenContent) _
      rw [hstate]
      exact ⟨hps, hm, fun h => nomatch h.symm.trans hcon'⟩
    · have e : Lexer.Slice.runEnd input start Lexer.RUN_COMMENT_PLAIN = input.size := by omega
      rw [e] at hLJ; exact hLJ

end

end BSmtLib.Proofs.Lexer.VNaiveWRustPort
