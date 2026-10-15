module

public import BSmtLib.Facts.Proofs.Lexer.VNaiveWRustPort.Arms
import all BSmtLib.Lexer.Internal.Helpers
import all BSmtLib.Lexer.Internal.VNaive
import all BSmtLib.Lexer.Internal.WRustPort
import all BSmtLib.Lexer.Internal.WRustPort.Slice
import all BSmtLib.Token

@[expose] public section

/-!
# The arms of the Rust port's `lexStep` for a string literal

The loops `lexStringLiteralLegacy` (version 2.0) and `lexStringLiteralFrom` (the later versions)
take the run of bytes that a string takes as they are, and act on the byte after it. Each is
proved by induction on the bytes left in the slice (`LegacySpec`, `StringSpec`), with the naive
lexer's pure run from where the step started anchored to the loop's index; the part of a loop
after its first byte, which the code reaches from several places, is proved once in each case.
-/

namespace BSmtLib.Facts.Proofs.Lexer.VNaiveWRustPort.ArmsStrings

open BSmtLib.Facts.Lexer.Adapters BSmtLib.Facts.Proofs.Lexer.Simulation.Bytes
open BSmtLibSpec.Lexer (Handed)
open BSmtLib.Lexer.Internal.WRustPort.Slice (get? get)
open BSmtLib.Facts.Proofs.Lexer.Consumers.Pure BSmtLib.Facts.Proofs.Lexer.VNaive.Run
open BSmtLib.Facts.Proofs.Lexer.VNaiveWRustPort.Agree
open BSmtLib.Facts.Proofs.Lexer.VNaiveWRustPort.Arms
open BSmtLib.Facts.Proofs.Lexer.VNaiveWRustPort.Batch
open BSmtLib.Facts.Proofs.Lexer.VNaiveWRustPort.Bytes
open BSmtLib.Facts.Proofs.Lexer.VNaiveWRustPort.Feed
open BSmtLib.Facts.Proofs.Lexer.VNaiveWRustPort.HandOver
open BSmtLib.Facts.Proofs.Lexer.VNaiveWRustPort.Model
open BSmtLib.Facts.Proofs.Lexer.VNaiveWRustPort.Normal.Basic
open BSmtLib.Facts.Proofs.Lexer.VNaiveWRustPort.Pure BSmtLib.Facts.Proofs.Lexer.VNaiveWRustPort.Push
open BSmtLib.Facts.Proofs.Lexer.VNaiveWRustPort.Runs BSmtLib.Facts.Proofs.Lexer.VNaiveWRustPort.Step
open BSmtLib.Facts.Proofs.Lexer.VNaiveWRustPort.Tables.Delimiters
open BSmtLib.Facts.Proofs.Lexer.VNaiveWRustPort.Tables.Legacy
open BSmtLib.Facts.Proofs.Lexer.VNaiveWRustPort.Tables.TextRuns BSmtLib.Lexer.Internal.VNaive

/-! ## The naive lexer in a string under version 2.0 -/

theorem isLegacyRun_ne (c : UInt8) (h : isLegacyRun c = true) : c ≠ 10 :=
  isLegacyStringRun_ne c (by simp only [isLegacyRun, Bool.and_eq_true] at h; exact h.1)

theorem advance_legacyRun {ws : Bool} (q : Pending) (location : Span.Location) (c : UInt8)
    (hm : q.mode = .legacyString) (hc : isLegacyRun c = true) :
    advance ws q location c = .pending { q with content := q.content.push c } :=
  advance_legacyString_run ws q location c hm
    (by simp only [isLegacyRun, Bool.and_eq_true] at hc; exact hc.1)

theorem feedFrom_advance_congr {v : Token.Version} {ws : Bool} {s : ByteSlice} {i : Nat}
    (hi : i < s.size)
    {p p' : Pending} {location : Span.Location}
    (h : advance ws p location s[i] = advance ws p' location s[i]) :
    feedFrom v ws s (.token p) location i = feedFrom v ws s (.token p') location i := by
  rw [feedFrom_lt hi, feedFrom_lt hi]
  simp only [byteStepW, failedBeforeW, h]

theorem attach_none {s : ByteSlice} {i : Nat}
    (h : ∀ (c : UInt8) (hc : get? s i = some c), (get? s i).attach = some ⟨c, hc⟩ → False) :
    s.size ≤ i := by
  cases hg : get? s i with
  | none => exact Lexer.Internal.WRustPort.Slice.size_le_of_get?_none hg
  | some c =>
    exfalso
    refine h c hg ?_
    simp [hg]

/-- The derived equality test of the lexer states is equality. -/
theorem state_beq_iff {a b : Lexer.Internal.Helpers.LexerState} : (a == b) = true ↔ a = b := by
  constructor
  · intro h
    cases a <;> cases b <;> first | rfl | exact absurd h (by decide)
  · intro h
    subst h
    cases a <;> decide

/-- The derived equality test of the versions is equality. -/
theorem version_beq_iff {a b : Token.Version} : (a == b) = true ↔ a = b := by
  constructor
  · intro h
    cases a <;> cases b <;> first | rfl | exact absurd h (by decide)
  · intro h
    subst h
    cases a <;> decide

section

variable {floor : Option Nat} {low : Nat}
variable {C : BSmtLibSpec.Lexer.Consumer} {hd : Bool} {iv : Token.Version}

/-- What the loop of a string under version 2.0 keeps, from the index `consumed`: if the lexer
state is in the string from `tokenStart`, and the naive lexer's run from the step's index
`start0` is its run from the string `q` at `consumed`, then the loop ends the step as the naive
lexer does. -/
def LegacySpec (C : BSmtLibSpec.Lexer.Consumer) (v : Token.Version) (hd : Bool)
    (iv : Token.Version) (ver : Token.Version)
    (input : ByteSlice) (start0 : Nat) (st0 : St) (loc0 : Span.Location)
    (coll : List Handed) (held : List Lexeme) (tokenStart : Span.Location) (base : Nat)
    (h : Lexer.Internal.WRustPort.Started floor low tokenStart) (origin consumed : Nat) : Prop :=
  ∀ (horigin : origin ≤ consumed) (s : WP.BS floor low) (locq : Span.Location) (q : Pending),
    Fixed v hd iv s.val → s.val.base = start0 → Holds s.val.batch held →
    s.val.batch.bytes = input.byteArray → LocAt s.val s.val.offset s.val.base consumed locq →
    low = s.val.offset → base = s.val.base → tokenStart = s.val.tokenStart → v = .v2_0 →
    StAgrees v C.concrete (.token q) s.val →
    (s.val.state = .stringLiteral ∨ s.val.state = .stringLiteralDoubleQuote ∨
      s.val.state = .stringLiteralBackslashEscape) →
    start0 ≤ consumed → start0 < input.size → consumed ≤ input.size →
    feedFrom v C.concrete input st0 loc0 start0 = feedFrom v C.concrete input
        (.token q) locq consumed →
    s.val.version = ver →
    WP (Lexer.Internal.WRustPort.lexStringLiteralLegacy (H := Answering C) (m := AnswerM)
        (R := C.Result)
        (E := Option C.Error) input consumed origin horigin tokenStart base h) s coll
      (fun r s' coll' => ArmPost C v hd iv input st0 loc0 start0 ver coll held r.1 s'.val coll')
      (fun e s' coll' => StepFails C v hd iv input st0 loc0 start0 ver coll held e s'.val coll')

set_option maxHeartbeats 4000000 in
theorem legacySpec_lt (v : Token.Version) (ver : Token.Version) (input : ByteSlice) (start0 : Nat)
    (st0 : St)
    (loc0 : Span.Location) (coll : List Handed) (held : List Lexeme) (tokenStart : Span.Location)
    (base : Nat) (h : Lexer.Internal.WRustPort.Started floor low tokenStart) (origin : Nat) :
    ∀ (n consumed : Nat), input.size - consumed < n →
      LegacySpec C v hd iv ver input start0 st0 loc0 coll held tokenStart base h
          origin consumed := by
  intro n
  induction n with
  | zero => intro consumed hn; omega
  | succ n ih =>
  intro consumed hn horigin s locq q hfix hbase0 hholds hbytes hloc hlow hb hts hv hagree
    hstates h0 hs0 hcs hanchor hver0
  rw [Lexer.Internal.WRustPort.lexStringLiteralLegacy]
  split
  rotate_left
  · -- no byte left: the string is left in progress
    rename_i hnone
    have hge := attach_none hnone
    apply WP.wp_pure
    exact armPost_pending (s0 := s.val) hfix hbase0 (show start0 < consumed by omega) hholds hbytes
      ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ hagree hloc hanchor
  rename_i first hfirst _
  extract_lets hlt c0 jpRun jpSet c1
  -- the run of the string from the index `X`, in the state `stringLiteral`
  have hrun : ∀ (X : {position // consumed ≤ position}) (s' : WP.BS floor low)
      (locX : Span.Location),
      Fixed v hd iv s'.val → s'.val.base = start0 → Holds s'.val.batch held →
      s'.val.batch.bytes = input.byteArray → LocAt s'.val s'.val.offset s'.val.base X.1 locX →
      low = s'.val.offset → base = s'.val.base → tokenStart = s'.val.tokenStart →
      s'.val.state = .stringLiteral → Fits s'.val.tokenContent → start0 ≤ X.1 → X.1 ≤ input.size →
      feedFrom v C.concrete input st0 loc0 start0 =
        feedFrom v C.concrete input (.token ⟨.legacyString, tokenStart, contentBytes
            s'.val.tokenContent⟩) locX
            X.1 →
      s'.val.version = ver →
      WP (jpRun () X) s' coll
        (fun r s' coll' => ArmPost C v hd iv input st0 loc0 start0 ver coll held r.1 s'.val coll')
        (fun e s' coll' => StepFails C v hd iv input st0 loc0 start0 ver coll held e
            s'.val coll') := by
    intro X s' locX hfix' hbase' hholds' hbytes' hloc' hlow' hb' hts' hstate' hfitsX hX0 hXs
        hanchor' hverX
    unfold jpRun
    dsimp -zeta only
    extract_lets index hidx1 hidx2
    have hI : index = runEnd input isLegacyRun X.1 := runEndAll_legacy input X.1
    have hle : X.1 ≤ index := hidx1
    have hle' : index ≤ input.size := hI ▸ runEnd_le input isLegacyRun X.1 hXs
    have hstop : ∀ (h : index < input.size), isLegacyRun input[index] = false := by
      intro h'; have := runEnd_stop input isLegacyRun X.1 (hI ▸ h'); simp only [← hI] at this
      exact this
    have hA := feedFrom_mode v C.concrete input isLegacyRun isLegacyRun_ne .legacyString
      (fun q l c hm hc => advance_legacyRun q l c hm hc) X.1
      ⟨.legacyString, tokenStart, contentBytes s'.val.tokenContent⟩ locX rfl hXs
    rw [← hI] at hA
    have hA' := hanchor'.trans hA
    have hextX : contentBytes (s'.val.tokenContent.extendFrom input.byteArray (input.start + X.1)
        (input.start + index)) = contentBytes s'.val.tokenContent ++ bytesOf input X.1 index :=
      contentBytes_extendSlice input hfitsX (.inl hle')
    have hfitsX' := fits_extendSlice input hfitsX (a := X.1) (.inl hle')
    have hLI := hloc'.afterColumns (by rw [hbase']; omega) hle
    split
    rotate_left
    · -- the run reaches the end of the slice: the string is left in progress
      rename_i hnone
      have hge := attach_none hnone
      have he : index = input.size := by omega
      unfold Lexer.Internal.WRustPort.extendContent Lexer.Internal.WRustPort.modifyContent
      apply WP.wp_bind; apply WP.wp_modifyCore
      apply WP.wp_pure
      rw [he] at hA' hLI hextX hfitsX'
      refine armPost_pending (s0 := s'.val) hfix' hbase' (by omega) hholds' hbytes'
        ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ ?_ hLI hA'
      refine ⟨?_, hfitsX'⟩
      show TokenAgrees v C.concrete s'.val.state s'.val.tokenStart
        (contentBytes (s'.val.tokenContent.extendFrom input.byteArray (input.start + X.1)
            (input.start + input.size))) _
      rw [hextX, hstate']
      exact ⟨hts', by subst hv; rfl, rfl⟩
    rename_i c hc _
    have hIs := Lexer.Internal.WRustPort.Slice.lt_size_of_get? hc
    have hIc : input[index] = c := (get?_eq hc).2
    have hIq := hstop hIs
    rw [hIc] at hIq
    extract_lets jpEnd
    -- the loop goes on after the byte
    have hrec : ∀ (s2 : WP.BS floor low) (locN : Span.Location) (qN : Pending),
        Fixed v hd iv s2.val → s2.val.base = start0 → Holds s2.val.batch held →
        s2.val.batch.bytes = input.byteArray →
        LocAt s2.val s2.val.offset s2.val.base (index + 1) locN → low = s2.val.offset →
        base = s2.val.base → tokenStart = s2.val.tokenStart → StAgrees v C.concrete
            (.token qN) s2.val →
        (s2.val.state = .stringLiteral ∨ s2.val.state = .stringLiteralDoubleQuote ∨
          s2.val.state = .stringLiteralBackslashEscape) →
        feedFrom v C.concrete input st0 loc0 start0 = feedFrom v C.concrete input (.token qN)
            locN (index + 1) →
        s2.val.version = ver →
        WP (hidx2 ()) s2 coll
          (fun r s' coll' => ArmPost C v hd iv input st0 loc0 start0 ver coll held r.1 s'.val coll')
          (fun e s' coll' => StepFails C v hd iv input st0 loc0 start0 ver coll held e
              s'.val coll') := by
      intro s2 locN qN hf2 hb2 hh2 hy2 hl2 hlow2 hbb2 hts2 hag2 hst2 han2 hver2
      unfold hidx2
      exact ih (index + 1) (by omega) _ s2 locN qN hf2 hb2 hh2 hy2 hl2 hlow2 hbb2 hts2 hv hag2
        hst2 (by omega) hs0 (by omega) han2 hver2
    have hLJ := hloc'.afterColumns (by rw [hbase']; omega)
      (show X.1 ≤ index + 1 by omega)
    apply WP.wp_ite
    · -- a line feed, which is marked and is in the content
      intro h10
      have h10' : c = 10 := by simpa using h10
      have hB : feedFrom v C.concrete input st0 loc0 start0 =
          feedFrom v C.concrete input (.token ⟨.legacyString, tokenStart,
            (contentBytes s'.val.tokenContent ++ bytesOf input X.1 index).push 10⟩)
            ((afterColumns locX (index - X.1)).afterByte 10) (index + 1) := by
        rw [hA', feedFrom_step hIs (byteStep_token_pending v C.concrete (by rw [hIc, h10']; rfl)),
          prep_nil, hIc, h10']
      unfold Lexer.Internal.WRustPort.markLineFeedAt
      apply WP.wp_bind; apply WP.wp_modifyCore
      apply WP.wp_bind; apply WP.wp_pure
      unfold jpEnd
      simp only [↓reduceIte]
      unfold Lexer.Internal.WRustPort.extendContent Lexer.Internal.WRustPort.pushContent
          Lexer.Internal.WRustPort.modifyContent
      apply WP.wp_bind; apply WP.wp_modifyCore
      apply WP.wp_bind; apply WP.wp_modifyCore
      refine hrec _ ((afterColumns locX (index - X.1)).afterByte 10) ⟨.legacyString, tokenStart,
          (contentBytes s'.val.tokenContent ++ bytesOf input X.1 index).push 10⟩
        ⟨hfix'.1, hfix'.2, hfix'.3, hfix'.4, hfix'.5, hfix'.6⟩ hbase' hholds' hbytes' ?_
            hlow' hb' hts' ?_
        (.inl hstate') ?_ (by first | rfl | assumption)
      · refine LocAt.lineFeed hLI (by rw [hbase']; omega) rfl ?_
        show Lexer.Internal.WRustPort.LexerCore.offsetAt _ _ + 1 = _
        simp only [Lexer.Internal.WRustPort.LexerCore.offsetAt]
      · refine ⟨?_, fits_push hfitsX' _⟩
        show TokenAgrees v C.concrete s'.val.state s'.val.tokenStart
          (contentBytes ((s'.val.tokenContent.extendFrom input.byteArray (input.start + X.1)
            (input.start + index)).push c)) _
        rw [contentBytes_push hfitsX', hextX, hstate', h10']
        exact ⟨hts', by subst hv; rfl, rfl⟩
      · exact hB
    intro h10
    have h10' : c ≠ 10 := by simpa using h10
    apply WP.wp_ite
    · -- a quote, which may end the string
      intro h34
      have h34' : c = 34 := by simpa using h34
      have hB : feedFrom v C.concrete input st0 loc0 start0 =
          feedFrom v C.concrete input (.token ⟨.legacyQuote, tokenStart,
            contentBytes s'.val.tokenContent ++ bytesOf input X.1 index⟩)
            (afterColumns locX (index + 1 - X.1)) (index + 1) := by
        rw [hA', feedFrom_step hIs (byteStep_token_pending v C.concrete (by rw [hIc, h34']; rfl)),
          prep_nil, hIc, h34', afterByte_eq_afterColumns' _ _ (by decide), afterColumns_add]
        congr 2
        omega
      unfold Lexer.Internal.WRustPort.setTokenState
      apply WP.wp_bind; apply WP.wp_modifyBound
      apply WP.wp_bind; apply WP.wp_pure
      unfold jpEnd
      simp only [Bool.false_eq_true, ↓reduceIte]
      unfold Lexer.Internal.WRustPort.extendContent Lexer.Internal.WRustPort.modifyContent
      apply WP.wp_bind; apply WP.wp_modifyCore
      refine hrec _ (afterColumns locX (index + 1 - X.1)) _
        ⟨hfix'.1, hfix'.2, hfix'.3, hfix'.4, hfix'.5, hfix'.6⟩ hbase' hholds' hbytes' hLJ
            hlow' hb' rfl ?_
        (.inr (.inl rfl)) hB (by first | rfl | assumption)
      exact ⟨⟨rfl, by subst hv; rfl, hextX.symm⟩, hfitsX'⟩
    intro h34
    have h34' : c ≠ 34 := by simpa using h34
    apply WP.wp_ite
    · -- a backslash, which may start an escape
      intro h92
      have h92' : c = 92 := by simpa using h92
      have hB : feedFrom v C.concrete input st0 loc0 start0 =
          feedFrom v C.concrete input (.token ⟨.legacyEscape, tokenStart,
            contentBytes s'.val.tokenContent ++ bytesOf input X.1 index⟩)
            (afterColumns locX (index + 1 - X.1)) (index + 1) := by
        rw [hA', feedFrom_step hIs (byteStep_token_pending v C.concrete (by rw [hIc, h92']; rfl)),
          prep_nil, hIc, h92', afterByte_eq_afterColumns' _ _ (by decide), afterColumns_add]
        congr 2
        omega
      unfold Lexer.Internal.WRustPort.setTokenState
      apply WP.wp_bind; apply WP.wp_modifyBound
      apply WP.wp_bind; apply WP.wp_pure
      unfold jpEnd
      simp only [Bool.false_eq_true, ↓reduceIte]
      unfold Lexer.Internal.WRustPort.extendContent Lexer.Internal.WRustPort.modifyContent
      apply WP.wp_bind; apply WP.wp_modifyCore
      refine hrec _ (afterColumns locX (index + 1 - X.1)) _
        ⟨hfix'.1, hfix'.2, hfix'.3, hfix'.4, hfix'.5, hfix'.6⟩ hbase' hholds' hbytes' hLJ
            hlow' hb' rfl ?_
        (.inr (.inr rfl)) hB (by first | rfl | assumption)
      exact ⟨⟨rfl, hv, rfl, hextX.symm⟩, hfitsX'⟩
    intro h92
    have h92' : c ≠ 92 := by simpa using h92
    apply WP.wp_ite
    · -- a pipe, which is in the content
      intro h124
      have h124' : c = 124 := by simpa using h124
      have hB : feedFrom v C.concrete input st0 loc0 start0 =
          feedFrom v C.concrete input (.token ⟨.legacyString, tokenStart,
            (contentBytes s'.val.tokenContent ++ bytesOf input X.1 index).push 124⟩)
            (afterColumns locX (index + 1 - X.1)) (index + 1) := by
        rw [hA', feedFrom_step hIs (byteStep_token_pending v C.concrete (by rw [hIc, h124']; rfl)),
          prep_nil, hIc, h124', afterByte_eq_afterColumns' _ _ (by decide), afterColumns_add]
        congr 2
        omega
      apply WP.wp_bind; apply WP.wp_pure
      unfold jpEnd
      simp only [↓reduceIte]
      unfold Lexer.Internal.WRustPort.extendContent Lexer.Internal.WRustPort.pushContent
          Lexer.Internal.WRustPort.modifyContent
      apply WP.wp_bind; apply WP.wp_modifyCore
      apply WP.wp_bind; apply WP.wp_modifyCore
      refine hrec _ (afterColumns locX (index + 1 - X.1)) ⟨.legacyString, tokenStart,
          (contentBytes s'.val.tokenContent ++ bytesOf input X.1 index).push 124⟩
        ⟨hfix'.1, hfix'.2, hfix'.3, hfix'.4, hfix'.5, hfix'.6⟩ hbase' hholds' hbytes' hLJ
            hlow' hb' hts' ?_
        (.inl hstate') hB (by first | rfl | assumption)
      refine ⟨?_, fits_push hfitsX' _⟩
      show TokenAgrees v C.concrete s'.val.state s'.val.tokenStart
        (contentBytes ((s'.val.tokenContent.extendFrom input.byteArray (input.start + X.1)
          (input.start + index)).push c)) _
      rw [contentBytes_push hfitsX', hextX, hstate', h124']
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
      have hf : ∃ f, advance C.concrete ⟨.legacyString, tokenStart,
          contentBytes s'.val.tokenContent ++ bytesOf input X.1 index⟩ (afterColumns locX (index -
              X.1))
          input[index] = .error f := by
        rw [hIc]
        simp [advance, legacyStringByte, h34', h92', htext]
      obtain ⟨f, hf⟩ := hf
      unfold Lexer.Internal.WRustPort.errorAt Lexer.Internal.WRustPort.errorWith
      wp_walk
      refine stepFails_here ?_ hholds'
        ⟨hfix'.1, hfix'.2, hfix'.3, hfix'.4, hfix'.5, hfix'.6⟩ (by first | rfl | assumption)
      rw [hA', feedFrom_advance_error v C.concrete input hIs hf]
  -- the first byte, in the state the string is in
  apply WP.wp_bind; apply WP.wp_getCore
  split
  · -- the quote before the byte ends the string
    rename_i hstate
    obtain ⟨hps, hm, hcont⟩ := token_agrees hagree hstate
    have hm' : q.mode = .legacyQuote := by rw [hm, hv]; rfl
    have hC := feedFrom_end v C.concrete input hlt (q := q) (location := locq)
      (advance_end_legacyQuote hm')
    rw [← hanchor, (get?_eq hfirst).2] at hC
    unfold Lexer.Internal.WRustPort.expectDelimiter Lexer.Internal.WRustPort.finishStringLiteral
    apply WP.wp_bind
    apply WP.wp_ite
    · intro hnd
      have hnd' : Lexer.Internal.VNaive.isDelimiter first = false := by
        rw [← isDelimiter_eq]; simpa using hnd
      rw [hnd'] at hC
      unfold Lexer.Internal.WRustPort.errorAt Lexer.Internal.WRustPort.errorWith
      wp_walk
      refine stepFails_here ?_ hholds
        ⟨hfix.1, hfix.2, hfix.3, hfix.4, hfix.5, hfix.6⟩ (by first | rfl | assumption)
      rw [hC]
      simp only [Bool.false_eq_true, ↓reduceIte]
    · intro hd
      have hd' : Lexer.Internal.VNaive.isDelimiter first = true := by
        rw [← isDelimiter_eq]; simpa using hd
      rw [hd'] at hC
      simp only [↓reduceIte] at hC
      apply WP.wp_pure
      apply WP.wp_bind
      refine sinkStored_wp .string (.mkAtByte _) tokenStart base h held _ hholds coll
        hfix.recovers (token_fits hagree) ?_ ?_
      · intro s1 coll1 hk1 hb1 hc1
        obtain ⟨k1, k2, k3, k4, k5, k6, k7, k8, k9, k10, k11⟩ := key_fields hk1
        unfold Lexer.Internal.WRustPort.setNormal
        apply WP.wp_bind; apply WP.wp_modifyCore
        apply WP.wp_pure
        have hstep := stepLocation_eq' (pos := consumed) hloc (by rw [hbase0]; exact h0) hb
          hlow (Nat.le_refl _)
        refine armPost_finish (s0 := _) hfix hbase0 h0 hbytes
          ⟨k1, k4, k3, k5, rfl, k8, k9, k10, k11, hb1⟩ hloc hc1 ?_
        rw [hC]
        show _ = Prep [⟨.string, contentBytes s.val.tokenContent, tokenStart,
          stepLocation s.val low base consumed⟩] _
        rw [hstep, Nat.sub_self, afterColumns_zero, hts, ← hps, ← hcont]
      · intro e s' p d hn hss
        have hstep := stepLocation_eq' (pos := consumed) hloc (by rw [hbase0]; exact h0) hb
          hlow (Nat.le_refl _)
        have hn' : Stops C s.val.holding s.val.version coll (held ++
            [⟨.string, contentBytes s.val.tokenContent, tokenStart,
            stepLocation s.val low base consumed⟩]) e p d := hn
        rw [hstep, Nat.sub_self, afterColumns_zero, hts, ← hps, ← hcont] at hn'
        exact stepFails_of_stops' (hbytes := by first | assumption | exact hpre.bytes) hss (by
            first
            | exact ⟨hfix.1, hfix.2, hfix.3, hfix.4, hfix.5, hfix.6⟩
            | exact ⟨hpre.fixed.1, hpre.fixed.2, hpre.fixed.3, hpre.fixed.4, hpre.fixed.5,
                hpre.fixed.6⟩)
          ⟨_, by rw [hC, outcome_pending_prep, ← hver0]⟩ hn'
  · -- the backslash before the byte
    rename_i hstate
    obtain ⟨hps, -, hm, hcont⟩ := token_agrees hagree hstate
    apply WP.wp_ite
    · -- an escape: only the escaped byte is in the content
      intro hesc
      have hfc := (get?_eq hfirst).2
      have hesc' : first = 34 ∨ first = 92 := by simpa using hesc
      have hB : feedFrom v C.concrete input st0 loc0 start0 =
          feedFrom v C.concrete input (.token ⟨.legacyString, tokenStart, (contentBytes
              s.val.tokenContent).push first⟩)
            (afterColumns locq 1) (consumed + 1) := by
        rw [hanchor, feedFrom_step hlt (byteStep_token_pending v C.concrete
          (q' := ⟨.legacyString, tokenStart, (contentBytes s.val.tokenContent).push first⟩) ?_),
              prep_nil,
          afterByte_eq_afterColumns' _ _ (by rw [hfc]; rcases hesc' with h | h <;> rw [h] <;>
            decide)]
        obtain ⟨mode, pstart, pcontent⟩ := q
        simp only at hm hps hcont
        rw [hm, hps, hcont, hfc, ← hts]
        rcases hesc' with h | h <;> rw [h] <;> rfl
      unfold Lexer.Internal.WRustPort.pushContent Lexer.Internal.WRustPort.modifyContent
      apply WP.wp_bind; apply WP.wp_modifyCore
      unfold jpSet Lexer.Internal.WRustPort.setTokenState
      dsimp -zeta only
      apply WP.wp_bind; apply WP.wp_modifyBound
      refine hrun c1 _ (afterColumns locq 1) ⟨hfix.1, hfix.2, hfix.3, hfix.4, hfix.5, hfix.6⟩ hbase0
        hholds hbytes ?_ hlow hb rfl rfl (fits_push (token_fits hagree) _)
        (by show start0 ≤ consumed + 1; omega)
        (by show consumed + 1 ≤ input.size; omega)
        (hB.trans (by rw [← contentBytes_push (token_fits hagree)])) (by first | rfl | assumption)
      have := hloc.afterColumns (by rw [hbase0]; exact h0) (show consumed ≤ consumed + 1 by omega)
      rw [Nat.add_sub_cancel_left] at this
      exact this
    · -- not an escape: the backslash is in the content
      intro hesc
      have hfc := (get?_eq hfirst).2
      have hesc' : first ≠ 34 ∧ first ≠ 92 := by simpa using hesc
      have hB : feedFrom v C.concrete input st0 loc0 start0 =
          feedFrom v C.concrete input (.token ⟨.legacyString, tokenStart, (contentBytes
              s.val.tokenContent).push 92⟩)
            locq consumed := by
        rw [hanchor]
        refine feedFrom_advance_congr hlt ?_
        obtain ⟨mode, pstart, pcontent⟩ := q
        simp only at hm hps hcont
        rw [hm, hps, hcont, hfc, ← hts]
        simp [advance, hesc'.1, hesc'.2]
      unfold Lexer.Internal.WRustPort.pushContent Lexer.Internal.WRustPort.modifyContent
      apply WP.wp_bind; apply WP.wp_modifyCore
      unfold jpSet Lexer.Internal.WRustPort.setTokenState
      dsimp -zeta only
      apply WP.wp_bind; apply WP.wp_modifyBound
      exact hrun c0 _ locq ⟨hfix.1, hfix.2, hfix.3, hfix.4, hfix.5, hfix.6⟩ hbase0
          hholds hbytes hloc
        hlow hb rfl rfl (fits_push (token_fits hagree) _) h0 hcs
        (hB.trans (by rw [← contentBytes_push (token_fits hagree)])) (by first | rfl | assumption)
  · -- the string itself
    rename_i hdq hbe
    have hstate : s.val.state = .stringLiteral := by
      rcases hstates with h1 | h1 | h1
      · exact h1
      · exact absurd h1 hdq
      · exact absurd h1 hbe
    obtain ⟨hps, hm, hcont⟩ := token_agrees hagree hstate
    refine hrun c0 s locq hfix hbase0 hholds hbytes hloc hlow hb hts hstate (token_fits hagree) h0
      hcs ?_ (by first | rfl | assumption)
    rw [hanchor]
    obtain ⟨mode, pstart, pcontent⟩ := q
    simp only at hm hps hcont
    rw [hm, hps, hcont, ← hts, hv]
    rfl

/-- What the loop of a string under the versions after 2.0 keeps, from the index `consumed`:
if the lexer state is in the string from `tokenStart`, and the naive lexer's run from the
step's index `start0` is its run from the string `q` at `consumed`, then the loop ends the step
as the naive lexer does. -/
def StringSpec (C : BSmtLibSpec.Lexer.Consumer) (v : Token.Version) (hd : Bool)
    (iv : Token.Version) (ver : Token.Version)
    (input : ByteSlice) (start0 : Nat) (st0 : St) (loc0 : Span.Location)
    (coll : List Handed) (held : List Lexeme) (tokenStart : Span.Location) (base : Nat)
    (h : Lexer.Internal.WRustPort.Started floor low tokenStart) (origin consumed : Nat) : Prop :=
  ∀ (horigin : origin ≤ consumed) (s : WP.BS floor low) (locq : Span.Location) (q : Pending),
    Fixed v hd iv s.val → s.val.base = start0 → Holds s.val.batch held →
    s.val.batch.bytes = input.byteArray → LocAt s.val s.val.offset s.val.base consumed locq →
    low = s.val.offset → base = s.val.base → tokenStart = s.val.tokenStart →
    (v == .v2_0) = false → StAgrees v C.concrete (.token q) s.val →
    (s.val.state = .stringLiteral ∨ s.val.state = .stringLiteralDoubleQuote) →
    start0 ≤ consumed → start0 < input.size → consumed ≤ input.size →
    feedFrom v C.concrete input st0 loc0 start0 = feedFrom v C.concrete input
        (.token q) locq consumed →
    s.val.version = ver →
    WP (Lexer.Internal.WRustPort.lexStringLiteralFrom (H := Answering C) (m := AnswerM)
        (R := C.Result)
        (E := Option C.Error) input consumed origin horigin tokenStart base h) s coll
      (fun r s' coll' => ArmPost C v hd iv input st0 loc0 start0 ver coll held r.1 s'.val coll')
      (fun e s' coll' => StepFails C v hd iv input st0 loc0 start0 ver coll held e s'.val coll')

set_option maxHeartbeats 4000000 in
theorem stringSpec_lt (v : Token.Version) (ver : Token.Version) (input : ByteSlice) (start0 : Nat)
    (st0 : St)
    (loc0 : Span.Location) (coll : List Handed) (held : List Lexeme) (tokenStart : Span.Location)
    (base : Nat) (h : Lexer.Internal.WRustPort.Started floor low tokenStart) (origin : Nat) :
    ∀ (n consumed : Nat), input.size - consumed < n →
      StringSpec C v hd iv ver input start0 st0 loc0 coll held tokenStart base h
          origin consumed := by
  intro n
  induction n with
  | zero => intro consumed hn; omega
  | succ n ih =>
  intro consumed hn horigin s locq q hfix hbase0 hholds hbytes hloc hlow hb hts hv hagree
    hstates h0 hs0 hcs hanchor hver0
  rw [Lexer.Internal.WRustPort.lexStringLiteralFrom]
  split
  rotate_left
  · -- no byte left: the string is left in progress
    rename_i hnone
    have hge := attach_none hnone
    apply WP.wp_pure
    exact armPost_pending (s0 := s.val) hfix hbase0 (show start0 < consumed by omega) hholds
      hbytes ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ hagree hloc hanchor
  rename_i first hfirst _
  extract_lets hlt c0 jpRun c1
  -- the run of the string from the index `X`, in the state `stringLiteral`
  have hrun : ∀ (X : {position // consumed ≤ position}) (s' : WP.BS floor low)
      (locX : Span.Location),
      Fixed v hd iv s'.val → s'.val.base = start0 → Holds s'.val.batch held →
      s'.val.batch.bytes = input.byteArray → LocAt s'.val s'.val.offset s'.val.base X.1 locX →
      low = s'.val.offset → base = s'.val.base → tokenStart = s'.val.tokenStart →
      s'.val.state = .stringLiteral → Fits s'.val.tokenContent → start0 ≤ X.1 → X.1 ≤ input.size →
      feedFrom v C.concrete input st0 loc0 start0 =
        feedFrom v C.concrete input (.token ⟨.string, tokenStart, contentBytes
            s'.val.tokenContent⟩) locX X.1 →
      s'.val.version = ver →
      WP (jpRun () X) s' coll
        (fun r s' coll' => ArmPost C v hd iv input st0 loc0 start0 ver coll held r.1 s'.val coll')
        (fun e s' coll' => StepFails C v hd iv input st0 loc0 start0 ver coll held e
            s'.val coll') := by
    intro X s' locX hfix' hbase' hholds' hbytes' hloc' hlow' hb' hts' hstate' hfitsX hX0 hXs
        hanchor' hverX
    unfold jpRun
    dsimp -zeta only
    extract_lets index hidx1
    have hI : index = runEnd input isStringRun X.1 := runEnd_eq endsRun_string _ _
    have hle : X.1 ≤ index := hidx1
    have hle' : index ≤ input.size := hI ▸ runEnd_le input isStringRun X.1 hXs
    have hstop : ∀ (h : index < input.size), isStringRun input[index] = false := by
      intro h'; have := runEnd_stop input isStringRun X.1 (hI ▸ h'); simp only [← hI] at this
      exact this
    have hA := feedFrom_mode v C.concrete input isStringRun isStringRun_ne .string
      (fun q l c hm hc => advance_string_run C.concrete q l c hm hc) X.1
      ⟨.string, tokenStart, contentBytes s'.val.tokenContent⟩ locX rfl hXs
    rw [← hI] at hA
    have hA' := hanchor'.trans hA
    have hextX : contentBytes (s'.val.tokenContent.extendFrom input.byteArray (input.start + X.1)
        (input.start + index)) = contentBytes s'.val.tokenContent ++ bytesOf input X.1 index :=
      contentBytes_extendSlice input hfitsX (.inl hle')
    have hfitsX' := fits_extendSlice input hfitsX (a := X.1) (.inl hle')
    have hLI := hloc'.afterColumns (by rw [hbase']; omega) hle
    have hLJ := hloc'.afterColumns (by rw [hbase']; omega)
      (show X.1 ≤ index + 1 by omega)
    split
    · rename_i c hc
      have hIs := Lexer.Internal.WRustPort.Slice.lt_size_of_get? hc
      have hIc : input[index] = c := (get?_eq hc).2
      have hIq := hstop hIs
      rw [hIc] at hIq
      apply WP.wp_ite
      · -- a line feed, which is marked and is in the content
        intro h10
        have h10' : c = 10 := by simpa using h10
        have hB : feedFrom v C.concrete input st0 loc0 start0 =
            feedFrom v C.concrete input (.token ⟨.string, tokenStart,
              (contentBytes s'.val.tokenContent ++ bytesOf input X.1 index).push 10⟩)
              ((afterColumns locX (index - X.1)).afterByte 10) (index + 1) := by
          rw [hA', feedFrom_step hIs (byteStep_token_pending v C.concrete (by rw [hIc, h10']; rfl)),
            prep_nil, hIc, h10']
        unfold Lexer.Internal.WRustPort.markLineFeedAt Lexer.Internal.WRustPort.extendContent
          Lexer.Internal.WRustPort.modifyContent
        apply WP.wp_bind; apply WP.wp_modifyCore
        apply WP.wp_bind; apply WP.wp_modifyCore
        refine ih (index + 1) (by omega) _ _ ((afterColumns locX (index - X.1)).afterByte 10)
          ⟨.string, tokenStart, (contentBytes s'.val.tokenContent ++ bytesOf input X.1 index).push
              10⟩
          ⟨hfix'.1, hfix'.2, hfix'.3, hfix'.4, hfix'.5, hfix'.6⟩ hbase' hholds' hbytes'
              ?_ hlow' hb' hts'
          hv ?_
          (.inl hstate') (by omega) hs0 (by omega) hB (by first | rfl | assumption)
        · refine LocAt.lineFeed hLI (by rw [hbase']; omega) rfl ?_
          show Lexer.Internal.WRustPort.LexerCore.offsetAt _ _ + 1 = _
          simp only [Lexer.Internal.WRustPort.LexerCore.offsetAt]
        · refine ⟨?_, fits_extendSlice input hfitsX (a := X.1) (b := index + 1) (.inl (by omega))⟩
          show TokenAgrees v C.concrete s'.val.state s'.val.tokenStart
            (contentBytes (s'.val.tokenContent.extendFrom input.byteArray (input.start + X.1)
              (input.start + (index + 1)))) _
          rw [contentBytes_extendSlice input hfitsX (a := X.1) (b := index + 1) (.inl (by omega)),
            hstate', content_succ input _ hle hIs, hIc, h10']
          exact ⟨hts', by simp [hv], rfl⟩
      intro h10
      have h10' : c ≠ 10 := by simpa using h10
      apply WP.wp_ite
      · -- a quote, which may end the string
        intro h34
        have h34' : c = 34 := by simpa using h34
        have hB : feedFrom v C.concrete input st0 loc0 start0 =
            feedFrom v C.concrete input (.token ⟨.stringQuote, tokenStart,
              contentBytes s'.val.tokenContent ++ bytesOf input X.1 index⟩)
              (afterColumns locX (index + 1 - X.1)) (index + 1) := by
          rw [hA', feedFrom_step hIs (byteStep_token_pending v C.concrete (by rw [hIc, h34']; rfl)),
            prep_nil, hIc, h34', afterByte_eq_afterColumns' _ _ (by decide), afterColumns_add]
          congr 2
          omega
        unfold Lexer.Internal.WRustPort.setTokenState Lexer.Internal.WRustPort.extendContent
          Lexer.Internal.WRustPort.modifyContent
        apply WP.wp_bind; apply WP.wp_modifyCore
        apply WP.wp_bind; apply WP.wp_modifyBound
        refine ih (index + 1) (by omega) _ _ (afterColumns locX (index + 1 - X.1))
          ⟨.stringQuote, tokenStart, contentBytes s'.val.tokenContent ++ bytesOf input X.1 index⟩
          ⟨hfix'.1, hfix'.2, hfix'.3, hfix'.4, hfix'.5, hfix'.6⟩ hbase' hholds' hbytes'
              hLJ hlow' hb' rfl
          hv ?_
          (.inr rfl) (by omega) hs0 (by omega) hB (by first | rfl | assumption)
        exact ⟨⟨rfl, by simp [hv], hextX.symm⟩, hfitsX'⟩
      · -- any other byte is not in a string
        intro h34
        have h34' : c ≠ 34 := by simpa using h34
        have htext : isTextByte c = false := by
          simp only [isStringRun, Bool.and_eq_false_iff, bne_eq_false_iff_eq] at hIq
          rcases hIq with ((h1 | h1) | h1)
          · exact h1
          · exact absurd h1 h34'
          · exact absurd h1 h10'
        have hf : ∃ f, advance C.concrete ⟨.string, tokenStart,
            contentBytes s'.val.tokenContent ++ bytesOf input X.1 index⟩ (afterColumns locX (index -
                X.1))
            input[index] = .error f := by
          rw [hIc]
          simp [advance, h34', htext]
        obtain ⟨f, hf⟩ := hf
        unfold Lexer.Internal.WRustPort.errorAt Lexer.Internal.WRustPort.errorWith
        wp_walk
        refine stepFails_here ?_ hholds'
          ⟨hfix'.1, hfix'.2, hfix'.3, hfix'.4, hfix'.5, hfix'.6⟩ (by first | rfl | assumption)
        rw [hA', feedFrom_advance_error v C.concrete input hIs hf]
    · -- the run reaches the end of the slice: the string is left in progress
      rename_i hnone
      have hge := Lexer.Internal.WRustPort.Slice.size_le_of_get?_none hnone
      have he : index = input.size := by omega
      unfold Lexer.Internal.WRustPort.extendContent Lexer.Internal.WRustPort.modifyContent
      apply WP.wp_bind; apply WP.wp_modifyCore
      apply WP.wp_pure
      rw [he] at hA' hLI hextX hfitsX'
      refine armPost_pending (s0 := s'.val) hfix' hbase' (by omega) hholds' hbytes'
        ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ ?_ hLI hA'
      refine ⟨?_, hfitsX'⟩
      show TokenAgrees v C.concrete s'.val.state s'.val.tokenStart
        (contentBytes (s'.val.tokenContent.extendFrom input.byteArray (input.start + X.1)
            (input.start + input.size))) _
      rw [hextX, hstate']
      exact ⟨hts', by simp [hv], rfl⟩
  -- the first byte, in the state the string is in
  apply WP.wp_bind; apply WP.wp_getCore
  have hfc := (get?_eq hfirst).2
  apply WP.wp_ite
  · -- after a quote
    intro hdq
    have hstate : s.val.state = .stringLiteralDoubleQuote := state_beq_iff.mp hdq
    obtain ⟨hps, hm, hcont⟩ := token_agrees hagree hstate
    have hm' : q.mode = .stringQuote := by rw [hm, hv]; rfl
    apply WP.wp_ite
    · -- the quote ends the string
      intro hne
      have hne' : first ≠ 34 := by simpa using hne
      have hC := feedFrom_end v C.concrete input hlt (q := q) (location := locq)
        (advance_end_stringQuote hm' (by rw [hfc]; exact hne'))
      rw [← hanchor, hfc] at hC
      unfold Lexer.Internal.WRustPort.expectDelimiter Lexer.Internal.WRustPort.finishStringLiteral
      apply WP.wp_bind
      apply WP.wp_ite
      · intro hnd
        have hnd' : Lexer.Internal.VNaive.isDelimiter first = false := by
          rw [← isDelimiter_eq]; simpa using hnd
        rw [hnd'] at hC
        unfold Lexer.Internal.WRustPort.errorAt Lexer.Internal.WRustPort.errorWith
        wp_walk
        refine stepFails_here ?_ hholds
          ⟨hfix.1, hfix.2, hfix.3, hfix.4, hfix.5, hfix.6⟩ (by first | rfl | assumption)
        rw [hC]
        simp only [Bool.false_eq_true, ↓reduceIte]
      · intro hd
        have hd' : Lexer.Internal.VNaive.isDelimiter first = true := by
          rw [← isDelimiter_eq]; simpa using hd
        rw [hd'] at hC
        simp only [↓reduceIte] at hC
        apply WP.wp_pure
        apply WP.wp_bind
        refine sinkStored_wp .string (.mkAtByte _) tokenStart base h held _ hholds coll
          hfix.recovers (token_fits hagree) ?_ ?_
        · intro s1 coll1 hk1 hb1 hc1
          obtain ⟨k1, k2, k3, k4, k5, k6, k7, k8, k9, k10, k11⟩ := key_fields hk1
          unfold Lexer.Internal.WRustPort.setNormal
          apply WP.wp_bind; apply WP.wp_modifyCore
          apply WP.wp_pure
          have hstep := stepLocation_eq' (pos := consumed) hloc (by rw [hbase0]; exact h0) hb
            hlow (Nat.le_refl _)
          refine armPost_finish (s0 := _) hfix hbase0 h0 hbytes
            ⟨k1, k4, k3, k5, rfl, k8, k9, k10, k11, hb1⟩ hloc hc1 ?_
          rw [hC]
          show _ = Prep [⟨.string, contentBytes s.val.tokenContent, tokenStart,
            stepLocation s.val low base consumed⟩] _
          rw [hstep, Nat.sub_self, afterColumns_zero, hts, ← hps, ← hcont]
        · intro e s' p d hn hss
          have hstep := stepLocation_eq' (pos := consumed) hloc (by rw [hbase0]; exact h0) hb
            hlow (Nat.le_refl _)
          have hn' : Stops C s.val.holding s.val.version coll
              (held ++ [⟨.string, contentBytes s.val.tokenContent, tokenStart,
              stepLocation s.val low base consumed⟩]) e p d := hn
          rw [hstep, Nat.sub_self, afterColumns_zero, hts, ← hps, ← hcont] at hn'
          exact stepFails_of_stops' (hbytes := by first | assumption | exact hpre.bytes) hss (by
              first
              | exact ⟨hfix.1, hfix.2, hfix.3, hfix.4, hfix.5, hfix.6⟩
              | exact ⟨hpre.fixed.1, hpre.fixed.2, hpre.fixed.3, hpre.fixed.4, hpre.fixed.5,
                  hpre.fixed.6⟩)
            ⟨_, by rw [hC, outcome_pending_prep, ← hver0]⟩ hn'
    · -- a second quote: a quote in the content
      intro hq
      have hq' : first = 34 := by simpa using hq
      have hB : feedFrom v C.concrete input st0 loc0 start0 =
          feedFrom v C.concrete input (.token ⟨.string, tokenStart,
              (contentBytes s.val.tokenContent).push 34⟩)
            (afterColumns locq 1) (consumed + 1) := by
        rw [hanchor, feedFrom_step hlt (byteStep_token_pending v C.concrete
          (q' := ⟨.string, tokenStart, (contentBytes s.val.tokenContent).push 34⟩) ?_), prep_nil,
          afterByte_eq_afterColumns' _ _ (by rw [hfc, hq']; decide)]
        obtain ⟨mode, pstart, pcontent⟩ := q
        simp only at hm' hps hcont
        rw [hm', hps, hcont, hfc, hq', ← hts]
        rfl
      unfold Lexer.Internal.WRustPort.pushContent Lexer.Internal.WRustPort.modifyContent
          Lexer.Internal.WRustPort.setTokenState
      apply WP.wp_bind; apply WP.wp_modifyCore
      apply WP.wp_bind; apply WP.wp_modifyBound
      refine hrun c1 _ (afterColumns locq 1) ⟨hfix.1, hfix.2, hfix.3, hfix.4, hfix.5, hfix.6⟩ hbase0
        hholds hbytes ?_ hlow hb rfl rfl (fits_push (token_fits hagree) _)
        (by show start0 ≤ consumed + 1; omega)
        (by show consumed + 1 ≤ input.size; omega)
        (hB.trans (by rw [← contentBytes_push (token_fits hagree)])) (by first | rfl | assumption)
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
    refine hrun c0 s locq hfix hbase0 hholds hbytes hloc hlow hb hts hstate (token_fits hagree) h0
      hcs ?_ (by first | rfl | assumption)
    rw [hanchor]
    obtain ⟨mode, pstart, pcontent⟩ := q
    simp only at hm hps hcont
    rw [hm, hps, hcont, ← hts, hv]
    rfl

/-- The arm of `lexStep` for a string literal. -/
theorem arm_stringLiteral (v : Token.Version) (input : ByteSlice) (start : Nat)
    (hstart : start < input.size) (tokenStart : Span.Location) (base : Nat)
    (h : Lexer.Internal.WRustPort.Started floor low tokenStart) (s : WP.BS floor low)
    (coll : List Handed)
    (p : Pending) (location : Span.Location) (held : List Lexeme)
    (hpre : StepPre C v hd iv input (.token p) location held start s.val)
        (hlow : low = s.val.offset)
    (hts : tokenStart = s.val.tokenStart) (hb : base = s.val.base)
    (hstate : s.val.state = .stringLiteral ∨ s.val.state = .stringLiteralDoubleQuote ∨
      s.val.state = .stringLiteralBackslashEscape) :
    WP (Lexer.Internal.WRustPort.lexStringLiteral (H := Answering C) (m := AnswerM) (R := C.Result)
        (E := Option C.Error)
        input start tokenStart base h) s coll
      (fun r s' coll' => ArmPost C v hd iv input (.token p) location start s.val.version coll held
          r.1 s'.val coll')
      (fun e s' coll' => StepFails C v hd iv input (.token p) location start s.val.version coll held
          e s'.val coll') := by
  unfold Lexer.Internal.WRustPort.lexStringLiteral
  apply WP.wp_bind; apply WP.wp_getCore
  apply WP.wp_ite
  · intro hv
    have hv' : v = .v2_0 := by rw [← version_beq_iff, ← hpre.fixed.version]; exact hv
    exact legacySpec_lt (C := C) (hd := hd) (iv := iv) v s.val.version input start (.token p)
        location coll held tokenStart base h start _
      start (Nat.lt_succ_self _) (Nat.le_refl _) s location p hpre.fixed hpre.base hpre.holds
      hpre.bytes hpre.loc hlow hb hts hv' hpre.agrees hstate (Nat.le_refl _) hstart
      (Nat.le_of_lt hstart) rfl rfl
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
    exact stringSpec_lt (C := C) (hd := hd) (iv := iv) v s.val.version input start (.token p)
        location coll held tokenStart base h start _
      start (Nat.lt_succ_self _) (Nat.le_refl _) s location p hpre.fixed hpre.base hpre.holds
      hpre.bytes hpre.loc hlow hb hts hv' hpre.agrees hstate' (Nat.le_refl _) hstart
      (Nat.le_of_lt hstart) rfl rfl

end

end BSmtLib.Facts.Proofs.Lexer.VNaiveWRustPort.ArmsStrings
