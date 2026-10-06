import BSmtLib.Proofs.V4FastPathsWRustPort.ArmsQuoted

/-!
# The arms of the Rust port's `lexStep` for a string literal

The loops `lexStringLiteralLegacy` (version 2.0) and `lexStringLiteralFrom` (the later versions)
take the run of bytes that a string takes as they are, and act on the byte after it. Each is
proved by induction on the bytes left in the slice (`LegacySpec`, `StringSpec`), with the naive
lexer's pure run from where the step started anchored to the loop's index; the part of a loop
after its first byte, which the code reaches from several places, is proved once in each case.
-/

namespace BSmtLib.Proofs.Lexer.V4FastPathsWRustPort

open BSmtLib.Proofs.Adapter V1Naive V1NaiveV2Batched V3Runs V2BatchedV3Runs
open Lexer.Slice (get? get)

/-! ## The naive lexer in a string under version 2.0 -/

theorem isLegacyRun_ne (c : UInt8) (h : isLegacyRun c = true) : c ≠ 10 :=
  isLegacyStringRun_ne c (by simp only [isLegacyRun, Bool.and_eq_true] at h; exact h.1)

theorem advance_legacyRun (q : Pending) (location : Location) (c : UInt8)
    (hm : q.mode = .legacyString) (hc : isLegacyRun c = true) :
    advance false q location c = .pending { q with content := q.content.push c } :=
  advance_legacyString_run false q location c hm
    (by simp only [isLegacyRun, Bool.and_eq_true] at hc; exact hc.1)

theorem feedFrom_advance_congr {v : Version} {s : ByteSlice} {i : Nat} (hi : i < s.size)
    {p p' : Pending} {location : Location}
    (h : advance false p location s[i] = advance false p' location s[i]) :
    feedFrom v s (.token p) location i = feedFrom v s (.token p') location i := by
  rw [feedFrom_lt hi, feedFrom_lt hi]
  simp only [byteStep, h]

theorem attach_none {s : ByteSlice} {i : Nat}
    (h : ∀ (c : UInt8) (hc : get? s i = some c), (get? s i).attach = some ⟨c, hc⟩ → False) :
    s.size ≤ i := by
  cases hg : get? s i with
  | none => exact Lexer.Slice.size_le_of_get?_none hg
  | some c =>
    exfalso
    refine h c hg ?_
    simp [hg]

/-- The derived equality test of the lexer states is equality. -/
theorem state_beq_iff {a b : Lexer.LexerState} : (a == b) = true ↔ a = b := by
  constructor
  · intro h
    cases a <;> cases b <;> first | rfl | exact absurd h (by decide)
  · intro h
    subst h
    cases a <;> decide

/-- The derived equality test of the versions is equality. -/
theorem version_beq_iff {a b : Version} : (a == b) = true ↔ a = b := by
  constructor
  · intro h
    cases a <;> cases b <;> first | rfl | exact absurd h (by decide)
  · intro h
    subst h
    cases a <;> decide

section

variable {floor : Option Nat} {low : Nat}

/-- What the loop of a string under version 2.0 keeps, from the index `consumed`: if the lexer
state is in the string from `tokenStart`, and the naive lexer's run from the step's index
`start0` is its run from the string `q` at `consumed`, then the loop ends the step as the naive
lexer does. -/
def LegacySpec (v : Version) (input : ByteSlice) (start0 : Nat) (st0 : St) (loc0 : Location)
    (coll : Collector) (held : List Lexeme) (tokenStart : Location) (base : Nat)
    (h : Lexer.WRustPort.Started floor low tokenStart) (origin consumed : Nat) : Prop :=
  ∀ (horigin : origin ≤ consumed) (s : BS floor low) (locq : Location) (q : Pending),
    Fixed v s.val → s.val.base = start0 → Holds s.val.batch held →
    s.val.batch.bytes = input.byteArray → LocAt s.val s.val.offset s.val.base consumed locq →
    low = s.val.offset → base = s.val.base → tokenStart = s.val.tokenStart → v = .v2_0 →
    StAgrees v (.token q) s.val →
    (s.val.state = .stringLiteral ∨ s.val.state = .stringLiteralDoubleQuote ∨
      s.val.state = .stringLiteralBackslashEscape) →
    start0 ≤ consumed → start0 < input.size → consumed ≤ input.size →
    feedFrom v input st0 loc0 start0 = feedFrom v input (.token q) locq consumed →
    WP (Lexer.WRustPort.lexStringLiteralLegacy (H := Collector) (m := Id) (R := Empty)
        (E := Unit) input consumed origin horigin tokenStart base h) s coll
      (fun r s' coll' => ArmPost v input st0 loc0 start0 coll held r.1 s'.val coll')
      (fun _ _ _ => StepFails v input st0 loc0 start0 coll held)

set_option maxHeartbeats 4000000 in
theorem legacySpec_lt (v : Version) (input : ByteSlice) (start0 : Nat) (st0 : St)
    (loc0 : Location) (coll : Collector) (held : List Lexeme) (tokenStart : Location)
    (base : Nat) (h : Lexer.WRustPort.Started floor low tokenStart) (origin : Nat) :
    ∀ (n consumed : Nat), input.size - consumed < n →
      LegacySpec v input start0 st0 loc0 coll held tokenStart base h origin consumed := by
  intro n
  induction n with
  | zero => intro consumed hn; omega
  | succ n ih =>
  intro consumed hn horigin s locq q hfix hbase0 hholds hbytes hloc hlow hb hts hv hagree
    hstates h0 hs0 hcs hanchor
  rw [Lexer.WRustPort.lexStringLiteralLegacy]
  split
  rotate_left
  · -- no byte left: the string is left in progress
    rename_i hnone
    have hge := attach_none hnone
    apply wp_pure
    exact armPost_pending (s0 := s.val) hfix hbase0 (show start0 < consumed by omega) hholds hbytes
      ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ hagree hloc hanchor
  rename_i first hfirst _
  extract_lets hlt c0 jpRun jpSet c1
  -- the run of the string from the index `X`, in the state `stringLiteral`
  have hrun : ∀ (X : {position // consumed ≤ position}) (s' : BS floor low) (locX : Location),
      Fixed v s'.val → s'.val.base = start0 → Holds s'.val.batch held →
      s'.val.batch.bytes = input.byteArray → LocAt s'.val s'.val.offset s'.val.base X.1 locX →
      low = s'.val.offset → base = s'.val.base → tokenStart = s'.val.tokenStart →
      s'.val.state = .stringLiteral → start0 ≤ X.1 → X.1 ≤ input.size →
      feedFrom v input st0 loc0 start0 =
        feedFrom v input (.token ⟨.legacyString, tokenStart, s'.val.tokenContent⟩) locX X.1 →
      WP (jpRun () X) s' coll
        (fun r s' coll' => ArmPost v input st0 loc0 start0 coll held r.1 s'.val coll')
        (fun _ _ _ => StepFails v input st0 loc0 start0 coll held) := by
    intro X s' locX hfix' hbase' hholds' hbytes' hloc' hlow' hb' hts' hstate' hX0 hXs hanchor'
    unfold jpRun
    dsimp -zeta only
    extract_lets index hidx1 hidx2
    have hI : index = V3Runs.runEnd input isLegacyRun X.1 := runEndAll_legacy input X.1
    have hle : X.1 ≤ index := hidx1
    have hle' : index ≤ input.size := hI ▸ runEnd_le input isLegacyRun X.1 hXs
    have hstop : ∀ (h : index < input.size), isLegacyRun input[index] = false := by
      intro h'; have := runEnd_stop input isLegacyRun X.1 (hI ▸ h'); simp only [← hI] at this
      exact this
    have hA := feedFrom_mode v input isLegacyRun isLegacyRun_ne .legacyString
      (fun q l c hm hc => advance_legacyRun q l c hm hc) X.1
      ⟨.legacyString, tokenStart, s'.val.tokenContent⟩ locX rfl hXs
    rw [← hI] at hA
    have hA' := hanchor'.trans hA
    have hLI := hloc'.afterColumns (by rw [hbase']; omega) hle
    split
    rotate_left
    · -- the run reaches the end of the slice: the string is left in progress
      rename_i hnone
      have hge := attach_none hnone
      have he : index = input.size := by omega
      unfold Lexer.WRustPort.extendContent Lexer.WRustPort.extendContentFrom
        Lexer.WRustPort.modifyContent
      apply wp_bind; apply wp_modifyCore
      apply wp_pure
      rw [he] at hA' hLI
      refine armPost_pending (s0 := s'.val) hfix' hbase' (by omega) hholds' hbytes'
        ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ ?_ hLI hA'
      show TokenAgrees v s'.val.state s'.val.tokenStart
        (s'.val.tokenContent ++ (input.slice X.1 input.size).toByteArray) _
      rw [hstate']
      exact ⟨hts', by subst hv; rfl, rfl⟩
    rename_i c hc _
    have hIs := Lexer.Slice.lt_size_of_get? hc
    have hIc : input[index] = c := (get?_eq hc).2
    have hIq := hstop hIs
    rw [hIc] at hIq
    extract_lets jpEnd
    -- the loop goes on after the byte
    have hrec : ∀ (s2 : BS floor low) (locN : Location) (qN : Pending),
        Fixed v s2.val → s2.val.base = start0 → Holds s2.val.batch held →
        s2.val.batch.bytes = input.byteArray →
        LocAt s2.val s2.val.offset s2.val.base (index + 1) locN → low = s2.val.offset →
        base = s2.val.base → tokenStart = s2.val.tokenStart → StAgrees v (.token qN) s2.val →
        (s2.val.state = .stringLiteral ∨ s2.val.state = .stringLiteralDoubleQuote ∨
          s2.val.state = .stringLiteralBackslashEscape) →
        feedFrom v input st0 loc0 start0 = feedFrom v input (.token qN) locN (index + 1) →
        WP (hidx2 ()) s2 coll
          (fun r s' coll' => ArmPost v input st0 loc0 start0 coll held r.1 s'.val coll')
          (fun _ _ _ => StepFails v input st0 loc0 start0 coll held) := by
      intro s2 locN qN hf2 hb2 hh2 hy2 hl2 hlow2 hbb2 hts2 hag2 hst2 han2
      unfold hidx2
      exact ih (index + 1) (by omega) _ s2 locN qN hf2 hb2 hh2 hy2 hl2 hlow2 hbb2 hts2 hv hag2
        hst2 (by omega) hs0 (by omega) han2
    have hLJ := hloc'.afterColumns (by rw [hbase']; omega)
      (show X.1 ≤ index + 1 by omega)
    apply wp_ite
    · -- a line feed, which is marked and is in the content
      intro h10
      have h10' : c = 10 := by simpa using h10
      have hB : feedFrom v input st0 loc0 start0 =
          feedFrom v input (.token ⟨.legacyString, tokenStart,
            (s'.val.tokenContent ++ bytesOf input X.1 index).push 10⟩)
            ((afterColumns locX (index - X.1)).afterByte 10) (index + 1) := by
        rw [hA', feedFrom_step hIs (byteStep_token_pending v (by rw [hIc, h10']; rfl)),
          prep_nil, hIc, h10']
      unfold Lexer.WRustPort.markLineFeedAt
      apply wp_bind; apply wp_modifyCore
      apply wp_bind; apply wp_pure
      unfold jpEnd
      simp only [↓reduceIte]
      unfold Lexer.WRustPort.extendContent Lexer.WRustPort.extendContentFrom
        Lexer.WRustPort.pushContent Lexer.WRustPort.modifyContent
      apply wp_bind; apply wp_modifyCore
      apply wp_bind; apply wp_modifyCore
      refine hrec _ ((afterColumns locX (index - X.1)).afterByte 10) ⟨.legacyString, tokenStart,
          (s'.val.tokenContent ++ bytesOf input X.1 index).push 10⟩
        ⟨hfix'.1, hfix'.2, hfix'.3, hfix'.4⟩ hbase' hholds' hbytes' ?_ hlow' hb' hts' ?_
        (.inl hstate') ?_
      · refine LocAt.lineFeed hLI (by rw [hbase']; omega) rfl ?_
        show Lexer.WRustPort.LexerCore.offsetAt _ _ + 1 = _
        simp only [Lexer.WRustPort.LexerCore.offsetAt]
      · show TokenAgrees v s'.val.state s'.val.tokenStart
          ((s'.val.tokenContent ++ (input.slice X.1 index).toByteArray).push c) _
        rw [hstate', h10']
        exact ⟨hts', by subst hv; rfl, rfl⟩
      · exact hB
    intro h10
    have h10' : c ≠ 10 := by simpa using h10
    apply wp_ite
    · -- a quote, which may end the string
      intro h34
      have h34' : c = 34 := by simpa using h34
      have hB : feedFrom v input st0 loc0 start0 =
          feedFrom v input (.token ⟨.legacyQuote, tokenStart,
            s'.val.tokenContent ++ bytesOf input X.1 index⟩)
            (afterColumns locX (index + 1 - X.1)) (index + 1) := by
        rw [hA', feedFrom_step hIs (byteStep_token_pending v (by rw [hIc, h34']; rfl)),
          prep_nil, hIc, h34', afterByte_eq_afterColumns' _ _ (by decide), afterColumns_add]
        congr 2
        omega
      unfold Lexer.WRustPort.setTokenState
      apply wp_bind; apply wp_modifyBound
      apply wp_bind; apply wp_pure
      unfold jpEnd
      simp only [Bool.false_eq_true, ↓reduceIte]
      unfold Lexer.WRustPort.extendContent Lexer.WRustPort.extendContentFrom
        Lexer.WRustPort.modifyContent
      apply wp_bind; apply wp_modifyCore
      refine hrec _ (afterColumns locX (index + 1 - X.1)) _
        ⟨hfix'.1, hfix'.2, hfix'.3, hfix'.4⟩ hbase' hholds' hbytes' hLJ hlow' hb' rfl ?_
        (.inr (.inl rfl)) hB
      exact ⟨rfl, by subst hv; rfl, rfl⟩
    intro h34
    have h34' : c ≠ 34 := by simpa using h34
    apply wp_ite
    · -- a backslash, which may start an escape
      intro h92
      have h92' : c = 92 := by simpa using h92
      have hB : feedFrom v input st0 loc0 start0 =
          feedFrom v input (.token ⟨.legacyEscape, tokenStart,
            s'.val.tokenContent ++ bytesOf input X.1 index⟩)
            (afterColumns locX (index + 1 - X.1)) (index + 1) := by
        rw [hA', feedFrom_step hIs (byteStep_token_pending v (by rw [hIc, h92']; rfl)),
          prep_nil, hIc, h92', afterByte_eq_afterColumns' _ _ (by decide), afterColumns_add]
        congr 2
        omega
      unfold Lexer.WRustPort.setTokenState
      apply wp_bind; apply wp_modifyBound
      apply wp_bind; apply wp_pure
      unfold jpEnd
      simp only [Bool.false_eq_true, ↓reduceIte]
      unfold Lexer.WRustPort.extendContent Lexer.WRustPort.extendContentFrom
        Lexer.WRustPort.modifyContent
      apply wp_bind; apply wp_modifyCore
      refine hrec _ (afterColumns locX (index + 1 - X.1)) _
        ⟨hfix'.1, hfix'.2, hfix'.3, hfix'.4⟩ hbase' hholds' hbytes' hLJ hlow' hb' rfl ?_
        (.inr (.inr rfl)) hB
      exact ⟨rfl, hv, rfl, rfl⟩
    intro h92
    have h92' : c ≠ 92 := by simpa using h92
    apply wp_ite
    · -- a pipe, which is in the content
      intro h124
      have h124' : c = 124 := by simpa using h124
      have hB : feedFrom v input st0 loc0 start0 =
          feedFrom v input (.token ⟨.legacyString, tokenStart,
            (s'.val.tokenContent ++ bytesOf input X.1 index).push 124⟩)
            (afterColumns locX (index + 1 - X.1)) (index + 1) := by
        rw [hA', feedFrom_step hIs (byteStep_token_pending v (by rw [hIc, h124']; rfl)),
          prep_nil, hIc, h124', afterByte_eq_afterColumns' _ _ (by decide), afterColumns_add]
        congr 2
        omega
      apply wp_bind; apply wp_pure
      unfold jpEnd
      simp only [↓reduceIte]
      unfold Lexer.WRustPort.extendContent Lexer.WRustPort.extendContentFrom
        Lexer.WRustPort.pushContent Lexer.WRustPort.modifyContent
      apply wp_bind; apply wp_modifyCore
      apply wp_bind; apply wp_modifyCore
      refine hrec _ (afterColumns locX (index + 1 - X.1)) ⟨.legacyString, tokenStart,
          (s'.val.tokenContent ++ bytesOf input X.1 index).push 124⟩
        ⟨hfix'.1, hfix'.2, hfix'.3, hfix'.4⟩ hbase' hholds' hbytes' hLJ hlow' hb' hts' ?_
        (.inl hstate') hB
      show TokenAgrees v s'.val.state s'.val.tokenStart
        ((s'.val.tokenContent ++ (input.slice X.1 index).toByteArray).push c) _
      rw [hstate', h124']
      exact ⟨hts', by subst hv; rfl, rfl⟩
    · -- any other byte is not in a string
      intro h124
      have h124' : c ≠ 124 := by simpa using h124
      have htext : isTextByte c = false := by
        simp only [isLegacyRun, isLegacyStringRun, Bool.and_eq_false_iff,
          bne_eq_false_iff_eq] at hIq
        rcases hIq with (((h1 | h1) | h1) | h1) | h1
        · exact h1
        · exact absurd h1 h34'
        · exact absurd h1 h92'
        · exact absurd h1 h10'
        · exact absurd h1 h124'
      have hf : ∃ f, advance false ⟨.legacyString, tokenStart,
          s'.val.tokenContent ++ bytesOf input X.1 index⟩ (afterColumns locX (index - X.1))
          input[index] = .error f := by
        rw [hIc]
        simp [advance, legacyStringByte, h34', h92', htext]
      obtain ⟨f, hf⟩ := hf
      unfold Lexer.WRustPort.errorAt Lexer.WRustPort.errorWith
      wp_walk
      show outcome v _ _ = none
      rw [hA', feedFrom_advance_error v input hIs hf, outcome_none_right]
  -- the first byte, in the state the string is in
  apply wp_bind; apply wp_getCore
  split
  · -- the quote before the byte ends the string
    rename_i hstate
    obtain ⟨hps, hm, hcont⟩ := token_agrees hagree hstate
    have hm' : q.mode = .legacyQuote := by rw [hm, hv]; rfl
    have hC := feedFrom_end v input hlt (q := q) (location := locq)
      (advance_end_legacyQuote hm')
    rw [← hanchor, (get?_eq hfirst).2] at hC
    unfold Lexer.WRustPort.expectDelimiter Lexer.WRustPort.finishStringLiteral
    apply wp_bind
    apply wp_ite
    · intro hnd
      have hnd' : V1Naive.isDelimiter first = false := by
        rw [← isDelimiter_eq]; simpa using hnd
      rw [hnd'] at hC
      unfold Lexer.WRustPort.errorAt Lexer.WRustPort.errorWith
      wp_walk
      show outcome v _ _ = none
      rw [hC]
      simp only [Bool.false_eq_true, ↓reduceIte, outcome_none_right]
    · intro hd
      have hd' : V1Naive.isDelimiter first = true := by
        rw [← isDelimiter_eq]; simpa using hd
      rw [hd'] at hC
      simp only [↓reduceIte] at hC
      apply wp_pure
      apply wp_bind
      refine sinkStored_wp v .string _ (.mkAtByte _) tokenStart base h held _ hholds coll
        hfix.recovers hfix.version ?_ ?_
      · intro s1 coll1 hk1 hb1 hc1
        obtain ⟨k1, k2, k3, k4, k5, k6, k7, k8, k9, k10, k11⟩ := key_fields hk1
        unfold Lexer.WRustPort.setNormal
        apply wp_bind; apply wp_modifyCore
        apply wp_pure
        have hstep := stepLocation_eq' (pos := consumed) hloc (by rw [hbase0]; exact h0) hb
          hlow (Nat.le_refl _)
        refine armPost_finish (s0 := _) hfix hbase0 h0 hbytes
          ⟨k1, k4, k3, k5, rfl, k8, k9, k10, k11, hb1⟩ hloc hc1 ?_
        rw [hC]
        show _ = Prep [⟨.string, s.val.tokenContent, tokenStart,
          stepLocation s.val low base consumed⟩] _
        rw [hstep, Nat.sub_self, afterColumns_zero, hts, ← hps, ← hcont]
      · intro hn e s' coll'
        show outcome v _ _ = none
        rw [hC, outcome_prep]
        have hstep := stepLocation_eq' (pos := consumed) hloc (by rw [hbase0]; exact h0) hb
          hlow (Nat.le_refl _)
        have hn' : pending v coll (held ++ [⟨.string, s.val.tokenContent, tokenStart,
            stepLocation s.val low base consumed⟩]) = none := hn
        rw [hstep, Nat.sub_self, afterColumns_zero, hts, ← hps, ← hcont] at hn'
        exact (congrArg (fun x => outcome v x _) hn').trans (outcome_none_left v _)
  · -- the backslash before the byte
    rename_i hstate
    obtain ⟨hps, -, hm, hcont⟩ := token_agrees hagree hstate
    apply wp_ite
    · -- an escape: only the escaped byte is in the content
      intro hesc
      have hfc := (get?_eq hfirst).2
      have hesc' : first = 34 ∨ first = 92 := by simpa using hesc
      have hB : feedFrom v input st0 loc0 start0 =
          feedFrom v input (.token ⟨.legacyString, tokenStart, s.val.tokenContent.push first⟩)
            (afterColumns locq 1) (consumed + 1) := by
        rw [hanchor, feedFrom_step hlt (byteStep_token_pending v
          (q' := ⟨.legacyString, tokenStart, s.val.tokenContent.push first⟩) ?_), prep_nil,
          afterByte_eq_afterColumns' _ _ (by rw [hfc]; rcases hesc' with h | h <;> rw [h] <;>
            decide)]
        obtain ⟨mode, pstart, pcontent⟩ := q
        simp only at hm hps hcont
        rw [hm, hps, hcont, hfc, ← hts]
        rcases hesc' with h | h <;> rw [h] <;> rfl
      unfold Lexer.WRustPort.pushContent Lexer.WRustPort.modifyContent
      apply wp_bind; apply wp_modifyCore
      unfold jpSet Lexer.WRustPort.setTokenState
      dsimp -zeta only
      apply wp_bind; apply wp_modifyBound
      refine hrun c1 _ (afterColumns locq 1) ⟨hfix.1, hfix.2, hfix.3, hfix.4⟩ hbase0 hholds hbytes
        ?_ hlow hb rfl rfl (by show start0 ≤ consumed + 1; omega)
        (by show consumed + 1 ≤ input.size; omega) hB
      have := hloc.afterColumns (by rw [hbase0]; exact h0) (show consumed ≤ consumed + 1 by omega)
      rw [Nat.add_sub_cancel_left] at this
      exact this
    · -- not an escape: the backslash is in the content
      intro hesc
      have hfc := (get?_eq hfirst).2
      have hesc' : first ≠ 34 ∧ first ≠ 92 := by simpa using hesc
      have hB : feedFrom v input st0 loc0 start0 =
          feedFrom v input (.token ⟨.legacyString, tokenStart, s.val.tokenContent.push 92⟩)
            locq consumed := by
        rw [hanchor]
        refine feedFrom_advance_congr hlt ?_
        obtain ⟨mode, pstart, pcontent⟩ := q
        simp only at hm hps hcont
        rw [hm, hps, hcont, hfc, ← hts]
        simp [advance, hesc'.1, hesc'.2]
      unfold Lexer.WRustPort.pushContent Lexer.WRustPort.modifyContent
      apply wp_bind; apply wp_modifyCore
      unfold jpSet Lexer.WRustPort.setTokenState
      dsimp -zeta only
      apply wp_bind; apply wp_modifyBound
      exact hrun c0 _ locq ⟨hfix.1, hfix.2, hfix.3, hfix.4⟩ hbase0 hholds hbytes hloc hlow hb rfl
        rfl h0 hcs hB
  · -- the string itself
    rename_i hdq hbe
    have hstate : s.val.state = .stringLiteral := by
      rcases hstates with h1 | h1 | h1
      · exact h1
      · exact absurd h1 hdq
      · exact absurd h1 hbe
    obtain ⟨hps, hm, hcont⟩ := token_agrees hagree hstate
    refine hrun c0 s locq hfix hbase0 hholds hbytes hloc hlow hb hts hstate h0 hcs ?_
    rw [hanchor]
    obtain ⟨mode, pstart, pcontent⟩ := q
    simp only at hm hps hcont
    rw [hm, hps, hcont, ← hts, hv]
    rfl

/-- What the loop of a string under the versions after 2.0 keeps, from the index `consumed`:
if the lexer state is in the string from `tokenStart`, and the naive lexer's run from the
step's index `start0` is its run from the string `q` at `consumed`, then the loop ends the step
as the naive lexer does. -/
def StringSpec (v : Version) (input : ByteSlice) (start0 : Nat) (st0 : St) (loc0 : Location)
    (coll : Collector) (held : List Lexeme) (tokenStart : Location) (base : Nat)
    (h : Lexer.WRustPort.Started floor low tokenStart) (origin consumed : Nat) : Prop :=
  ∀ (horigin : origin ≤ consumed) (s : BS floor low) (locq : Location) (q : Pending),
    Fixed v s.val → s.val.base = start0 → Holds s.val.batch held →
    s.val.batch.bytes = input.byteArray → LocAt s.val s.val.offset s.val.base consumed locq →
    low = s.val.offset → base = s.val.base → tokenStart = s.val.tokenStart →
    (v == .v2_0) = false → StAgrees v (.token q) s.val →
    (s.val.state = .stringLiteral ∨ s.val.state = .stringLiteralDoubleQuote) →
    start0 ≤ consumed → start0 < input.size → consumed ≤ input.size →
    feedFrom v input st0 loc0 start0 = feedFrom v input (.token q) locq consumed →
    WP (Lexer.WRustPort.lexStringLiteralFrom (H := Collector) (m := Id) (R := Empty)
        (E := Unit) input consumed origin horigin tokenStart base h) s coll
      (fun r s' coll' => ArmPost v input st0 loc0 start0 coll held r.1 s'.val coll')
      (fun _ _ _ => StepFails v input st0 loc0 start0 coll held)

set_option maxHeartbeats 4000000 in
theorem stringSpec_lt (v : Version) (input : ByteSlice) (start0 : Nat) (st0 : St)
    (loc0 : Location) (coll : Collector) (held : List Lexeme) (tokenStart : Location)
    (base : Nat) (h : Lexer.WRustPort.Started floor low tokenStart) (origin : Nat) :
    ∀ (n consumed : Nat), input.size - consumed < n →
      StringSpec v input start0 st0 loc0 coll held tokenStart base h origin consumed := by
  intro n
  induction n with
  | zero => intro consumed hn; omega
  | succ n ih =>
  intro consumed hn horigin s locq q hfix hbase0 hholds hbytes hloc hlow hb hts hv hagree
    hstates h0 hs0 hcs hanchor
  rw [Lexer.WRustPort.lexStringLiteralFrom]
  split
  rotate_left
  · -- no byte left: the string is left in progress
    rename_i hnone
    have hge := attach_none hnone
    apply wp_pure
    exact armPost_pending (s0 := s.val) hfix hbase0 (show start0 < consumed by omega) hholds
      hbytes ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ hagree hloc hanchor
  rename_i first hfirst _
  extract_lets hlt c0 jpRun c1
  -- the run of the string from the index `X`, in the state `stringLiteral`
  have hrun : ∀ (X : {position // consumed ≤ position}) (s' : BS floor low) (locX : Location),
      Fixed v s'.val → s'.val.base = start0 → Holds s'.val.batch held →
      s'.val.batch.bytes = input.byteArray → LocAt s'.val s'.val.offset s'.val.base X.1 locX →
      low = s'.val.offset → base = s'.val.base → tokenStart = s'.val.tokenStart →
      s'.val.state = .stringLiteral → start0 ≤ X.1 → X.1 ≤ input.size →
      feedFrom v input st0 loc0 start0 =
        feedFrom v input (.token ⟨.string, tokenStart, s'.val.tokenContent⟩) locX X.1 →
      WP (jpRun () X) s' coll
        (fun r s' coll' => ArmPost v input st0 loc0 start0 coll held r.1 s'.val coll')
        (fun _ _ _ => StepFails v input st0 loc0 start0 coll held) := by
    intro X s' locX hfix' hbase' hholds' hbytes' hloc' hlow' hb' hts' hstate' hX0 hXs hanchor'
    unfold jpRun
    dsimp -zeta only
    extract_lets index hidx1
    have hI : index = V3Runs.runEnd input isStringRun X.1 := runEnd_eq endsRun_string _ _
    have hle : X.1 ≤ index := hidx1
    have hle' : index ≤ input.size := hI ▸ runEnd_le input isStringRun X.1 hXs
    have hstop : ∀ (h : index < input.size), isStringRun input[index] = false := by
      intro h'; have := runEnd_stop input isStringRun X.1 (hI ▸ h'); simp only [← hI] at this
      exact this
    have hA := feedFrom_mode v input isStringRun isStringRun_ne .string
      (fun q l c hm hc => advance_string_run false q l c hm hc) X.1
      ⟨.string, tokenStart, s'.val.tokenContent⟩ locX rfl hXs
    rw [← hI] at hA
    have hA' := hanchor'.trans hA
    have hLI := hloc'.afterColumns (by rw [hbase']; omega) hle
    have hLJ := hloc'.afterColumns (by rw [hbase']; omega)
      (show X.1 ≤ index + 1 by omega)
    split
    · rename_i c hc
      have hIs := Lexer.Slice.lt_size_of_get? hc
      have hIc : input[index] = c := (get?_eq hc).2
      have hIq := hstop hIs
      rw [hIc] at hIq
      apply wp_ite
      · -- a line feed, which is marked and is in the content
        intro h10
        have h10' : c = 10 := by simpa using h10
        have hB : feedFrom v input st0 loc0 start0 =
            feedFrom v input (.token ⟨.string, tokenStart,
              (s'.val.tokenContent ++ bytesOf input X.1 index).push 10⟩)
              ((afterColumns locX (index - X.1)).afterByte 10) (index + 1) := by
          rw [hA', feedFrom_step hIs (byteStep_token_pending v (by rw [hIc, h10']; rfl)),
            prep_nil, hIc, h10']
        unfold Lexer.WRustPort.markLineFeedAt Lexer.WRustPort.extendContent
          Lexer.WRustPort.extendContentFrom Lexer.WRustPort.modifyContent
        apply wp_bind; apply wp_modifyCore
        apply wp_bind; apply wp_modifyCore
        refine ih (index + 1) (by omega) _ _ ((afterColumns locX (index - X.1)).afterByte 10)
          ⟨.string, tokenStart, (s'.val.tokenContent ++ bytesOf input X.1 index).push 10⟩
          ⟨hfix'.1, hfix'.2, hfix'.3, hfix'.4⟩ hbase' hholds' hbytes' ?_ hlow' hb' hts' hv ?_
          (.inl hstate') (by omega) hs0 (by omega) hB
        · refine LocAt.lineFeed hLI (by rw [hbase']; omega) rfl ?_
          show Lexer.WRustPort.LexerCore.offsetAt _ _ + 1 = _
          simp only [Lexer.WRustPort.LexerCore.offsetAt]
        · show TokenAgrees v s'.val.state s'.val.tokenStart
            (s'.val.tokenContent ++ (input.slice X.1 (index + 1)).toByteArray) _
          rw [hstate', content_succ input _ hle hIs, hIc, h10']
          exact ⟨hts', by simp [hv], rfl⟩
      intro h10
      have h10' : c ≠ 10 := by simpa using h10
      apply wp_ite
      · -- a quote, which may end the string
        intro h34
        have h34' : c = 34 := by simpa using h34
        have hB : feedFrom v input st0 loc0 start0 =
            feedFrom v input (.token ⟨.stringQuote, tokenStart,
              s'.val.tokenContent ++ bytesOf input X.1 index⟩)
              (afterColumns locX (index + 1 - X.1)) (index + 1) := by
          rw [hA', feedFrom_step hIs (byteStep_token_pending v (by rw [hIc, h34']; rfl)),
            prep_nil, hIc, h34', afterByte_eq_afterColumns' _ _ (by decide), afterColumns_add]
          congr 2
          omega
        unfold Lexer.WRustPort.setTokenState Lexer.WRustPort.extendContent
          Lexer.WRustPort.extendContentFrom Lexer.WRustPort.modifyContent
        apply wp_bind; apply wp_modifyCore
        apply wp_bind; apply wp_modifyBound
        refine ih (index + 1) (by omega) _ _ (afterColumns locX (index + 1 - X.1))
          ⟨.stringQuote, tokenStart, s'.val.tokenContent ++ bytesOf input X.1 index⟩
          ⟨hfix'.1, hfix'.2, hfix'.3, hfix'.4⟩ hbase' hholds' hbytes' hLJ hlow' hb' rfl hv ?_
          (.inr rfl) (by omega) hs0 (by omega) hB
        exact ⟨rfl, by simp [hv], rfl⟩
      · -- any other byte is not in a string
        intro h34
        have h34' : c ≠ 34 := by simpa using h34
        have htext : isTextByte c = false := by
          simp only [isStringRun, Bool.and_eq_false_iff, bne_eq_false_iff_eq] at hIq
          rcases hIq with ((h1 | h1) | h1)
          · exact h1
          · exact absurd h1 h34'
          · exact absurd h1 h10'
        have hf : ∃ f, advance false ⟨.string, tokenStart,
            s'.val.tokenContent ++ bytesOf input X.1 index⟩ (afterColumns locX (index - X.1))
            input[index] = .error f := by
          rw [hIc]
          simp [advance, h34', htext]
        obtain ⟨f, hf⟩ := hf
        unfold Lexer.WRustPort.errorAt Lexer.WRustPort.errorWith
        wp_walk
        show outcome v _ _ = none
        rw [hA', feedFrom_advance_error v input hIs hf, outcome_none_right]
    · -- the run reaches the end of the slice: the string is left in progress
      rename_i hnone
      have hge := Lexer.Slice.size_le_of_get?_none hnone
      have he : index = input.size := by omega
      unfold Lexer.WRustPort.extendContent Lexer.WRustPort.extendContentFrom
        Lexer.WRustPort.modifyContent
      apply wp_bind; apply wp_modifyCore
      apply wp_pure
      rw [he] at hA' hLI
      refine armPost_pending (s0 := s'.val) hfix' hbase' (by omega) hholds' hbytes'
        ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ ?_ hLI hA'
      show TokenAgrees v s'.val.state s'.val.tokenStart
        (s'.val.tokenContent ++ (input.slice X.1 input.size).toByteArray) _
      rw [hstate']
      exact ⟨hts', by simp [hv], rfl⟩
  -- the first byte, in the state the string is in
  apply wp_bind; apply wp_getCore
  have hfc := (get?_eq hfirst).2
  apply wp_ite
  · -- after a quote
    intro hdq
    have hstate : s.val.state = .stringLiteralDoubleQuote := state_beq_iff.mp hdq
    obtain ⟨hps, hm, hcont⟩ := token_agrees hagree hstate
    have hm' : q.mode = .stringQuote := by rw [hm, hv]; rfl
    apply wp_ite
    · -- the quote ends the string
      intro hne
      have hne' : first ≠ 34 := by simpa using hne
      have hC := feedFrom_end v input hlt (q := q) (location := locq)
        (advance_end_stringQuote hm' (by rw [hfc]; exact hne'))
      rw [← hanchor, hfc] at hC
      unfold Lexer.WRustPort.expectDelimiter Lexer.WRustPort.finishStringLiteral
      apply wp_bind
      apply wp_ite
      · intro hnd
        have hnd' : V1Naive.isDelimiter first = false := by
          rw [← isDelimiter_eq]; simpa using hnd
        rw [hnd'] at hC
        unfold Lexer.WRustPort.errorAt Lexer.WRustPort.errorWith
        wp_walk
        show outcome v _ _ = none
        rw [hC]
        simp only [Bool.false_eq_true, ↓reduceIte, outcome_none_right]
      · intro hd
        have hd' : V1Naive.isDelimiter first = true := by
          rw [← isDelimiter_eq]; simpa using hd
        rw [hd'] at hC
        simp only [↓reduceIte] at hC
        apply wp_pure
        apply wp_bind
        refine sinkStored_wp v .string _ (.mkAtByte _) tokenStart base h held _ hholds coll
          hfix.recovers hfix.version ?_ ?_
        · intro s1 coll1 hk1 hb1 hc1
          obtain ⟨k1, k2, k3, k4, k5, k6, k7, k8, k9, k10, k11⟩ := key_fields hk1
          unfold Lexer.WRustPort.setNormal
          apply wp_bind; apply wp_modifyCore
          apply wp_pure
          have hstep := stepLocation_eq' (pos := consumed) hloc (by rw [hbase0]; exact h0) hb
            hlow (Nat.le_refl _)
          refine armPost_finish (s0 := _) hfix hbase0 h0 hbytes
            ⟨k1, k4, k3, k5, rfl, k8, k9, k10, k11, hb1⟩ hloc hc1 ?_
          rw [hC]
          show _ = Prep [⟨.string, s.val.tokenContent, tokenStart,
            stepLocation s.val low base consumed⟩] _
          rw [hstep, Nat.sub_self, afterColumns_zero, hts, ← hps, ← hcont]
        · intro hn e s' coll'
          show outcome v _ _ = none
          rw [hC, outcome_prep]
          have hstep := stepLocation_eq' (pos := consumed) hloc (by rw [hbase0]; exact h0) hb
            hlow (Nat.le_refl _)
          have hn' : pending v coll (held ++ [⟨.string, s.val.tokenContent, tokenStart,
              stepLocation s.val low base consumed⟩]) = none := hn
          rw [hstep, Nat.sub_self, afterColumns_zero, hts, ← hps, ← hcont] at hn'
          exact (congrArg (fun x => outcome v x _) hn').trans (outcome_none_left v _)
    · -- a second quote: a quote in the content
      intro hq
      have hq' : first = 34 := by simpa using hq
      have hB : feedFrom v input st0 loc0 start0 =
          feedFrom v input (.token ⟨.string, tokenStart, s.val.tokenContent.push 34⟩)
            (afterColumns locq 1) (consumed + 1) := by
        rw [hanchor, feedFrom_step hlt (byteStep_token_pending v
          (q' := ⟨.string, tokenStart, s.val.tokenContent.push 34⟩) ?_), prep_nil,
          afterByte_eq_afterColumns' _ _ (by rw [hfc, hq']; decide)]
        obtain ⟨mode, pstart, pcontent⟩ := q
        simp only at hm' hps hcont
        rw [hm', hps, hcont, hfc, hq', ← hts]
        rfl
      unfold Lexer.WRustPort.pushContent Lexer.WRustPort.modifyContent
        Lexer.WRustPort.setTokenState
      apply wp_bind; apply wp_modifyCore
      apply wp_bind; apply wp_modifyBound
      refine hrun c1 _ (afterColumns locq 1) ⟨hfix.1, hfix.2, hfix.3, hfix.4⟩ hbase0 hholds hbytes
        ?_ hlow hb rfl rfl (by show start0 ≤ consumed + 1; omega)
        (by show consumed + 1 ≤ input.size; omega) hB
      have := hloc.afterColumns (by rw [hbase0]; exact h0) (show consumed ≤ consumed + 1 by omega)
      rw [Nat.add_sub_cancel_left] at this
      exact this
  · -- in the string
    intro hdq
    have hdq' : s.val.state ≠ .stringLiteralDoubleQuote := fun e => hdq (state_beq_iff.mpr e)
    have hstate : s.val.state = .stringLiteral := by
      rcases hstates with h1 | h1
      · exact h1
      · exact absurd h1 hdq'
    obtain ⟨hps, hm, hcont⟩ := token_agrees hagree hstate
    refine hrun c0 s locq hfix hbase0 hholds hbytes hloc hlow hb hts hstate h0 hcs ?_
    rw [hanchor]
    obtain ⟨mode, pstart, pcontent⟩ := q
    simp only at hm hps hcont
    rw [hm, hps, hcont, ← hts, hv]
    rfl

/-- The arm of `lexStep` for a string literal. -/
theorem arm_stringLiteral (v : Version) (input : ByteSlice) (start : Nat)
    (hstart : start < input.size) (tokenStart : Location) (base : Nat)
    (h : Lexer.WRustPort.Started floor low tokenStart) (s : BS floor low) (coll : Collector)
    (p : Pending) (location : Location) (held : List Lexeme)
    (hpre : StepPre v input (.token p) location held start s.val) (hlow : low = s.val.offset)
    (hts : tokenStart = s.val.tokenStart) (hb : base = s.val.base)
    (hstate : s.val.state = .stringLiteral ∨ s.val.state = .stringLiteralDoubleQuote ∨
      s.val.state = .stringLiteralBackslashEscape) :
    WP (Lexer.WRustPort.lexStringLiteral (H := Collector) (m := Id) (R := Empty) (E := Unit)
        input start tokenStart base h) s coll
      (fun r s' coll' => ArmPost v input (.token p) location start coll held r.1 s'.val coll')
      (fun _ _ _ => StepFails v input (.token p) location start coll held) := by
  unfold Lexer.WRustPort.lexStringLiteral
  apply wp_bind; apply wp_getCore
  apply wp_ite
  · intro hv
    have hv' : v = .v2_0 := by rw [← hpre.fixed.version]; exact version_beq_iff.mp hv
    exact legacySpec_lt v input start (.token p) location coll held tokenStart base h start _
      start (Nat.lt_succ_self _) (Nat.le_refl _) s location p hpre.fixed hpre.base hpre.holds
      hpre.bytes hpre.loc hlow hb hts hv' hpre.agrees hstate (Nat.le_refl _) hstart
      (Nat.le_of_lt hstart) rfl
  · intro hv
    have hv' : (v == .v2_0) = false := by
      rw [← hpre.fixed.version]; exact Bool.eq_false_iff.mpr hv
    have hstate' : s.val.state = .stringLiteral ∨ s.val.state = .stringLiteralDoubleQuote := by
      rcases hstate with h1 | h1 | h1
      · exact .inl h1
      · exact .inr h1
      · have := token_agrees hpre.agrees h1
        obtain ⟨-, hv2, -⟩ := this
        rw [hv2] at hv'
        exact absurd hv' (by decide)
    exact stringSpec_lt v input start (.token p) location coll held tokenStart base h start _
      start (Nat.lt_succ_self _) (Nat.le_refl _) s location p hpre.fixed hpre.base hpre.holds
      hpre.bytes hpre.loc hlow hb hts hv' hpre.agrees hstate' (Nat.le_refl _) hstart
      (Nat.le_of_lt hstart) rfl

end

end BSmtLib.Proofs.Lexer.V4FastPathsWRustPort
