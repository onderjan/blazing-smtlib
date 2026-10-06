import BSmtLib.Proofs.V1NaiveWRustPort.ArmsNumbers

/-!
# The arm of the Rust port's `lexStep` for a quoted symbol

The loop `lexQuotedSymbol` takes the run of bytes that a quoted symbol takes as they are, and
acts on the byte after it: a line feed is marked and the loop goes on after it, a pipe closes
the symbol, any other byte is an error, and the end of the slice leaves the symbol in progress.
It is proved by induction on the bytes left in the slice (`QuotedSpec`), with the naive
lexer's pure run from where the step started anchored to the loop's index.
-/

namespace BSmtLib.Proofs.Lexer.V1NaiveWRustPort

open BSmtLib.Proofs.Adapter V1Naive BSmtLib.Proofs.Simulation
open Lexer.Slice (get? get)

section

variable {floor : Option Nat} {low : Nat}

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

/-- What the loop of a quoted symbol keeps, from the index `consumed`: if the lexer state is in
the quoted symbol from `tokenStart`, and the naive lexer's run from the step's index `start0`
is its run from the quoted symbol at `consumed`, then the loop ends the step as the naive lexer
does. -/
def QuotedSpec (v : Version) (input : ByteSlice) (start0 : Nat) (st0 : St) (loc0 : Location)
    (coll : Collector) (held : List Lexeme) (tokenStart : Location) (base : Nat)
    (h : Lexer.WRustPort.Started floor low tokenStart) (origin consumed : Nat) : Prop :=
  ∀ (horigin : origin ≤ consumed) (hconsumed : consumed ≤ input.size) (s : BS floor low)
    (locq : Location), Fixed v s.val → s.val.base = start0 → Holds s.val.batch held →
    s.val.batch.bytes = input.byteArray → LocAt s.val s.val.offset s.val.base consumed locq →
    low = s.val.offset → base = s.val.base → tokenStart = s.val.tokenStart →
    s.val.state = .quotedSymbol → Fits s.val.tokenContent → start0 ≤ consumed → start0 < input.size
        →
    feedFrom v input st0 loc0 start0 =
      feedFrom v input (.token ⟨.quotedSymbol, tokenStart, contentBytes s.val.tokenContent⟩) locq
          consumed →
    WP (Lexer.WRustPort.lexQuotedSymbol (H := Collector) (m := Id) (R := Empty) (E := Unit)
        input consumed origin horigin hconsumed tokenStart base h) s coll
      (fun r s' coll' => ArmPost v input st0 loc0 start0 coll held r.1 s'.val coll')
      (fun _ _ _ => StepFails v input st0 loc0 start0 coll held)

theorem quotedSpec_lt (v : Version) (input : ByteSlice) (start0 : Nat) (st0 : St)
    (loc0 : Location) (coll : Collector) (held : List Lexeme) (tokenStart : Location)
    (base : Nat) (h : Lexer.WRustPort.Started floor low tokenStart) (origin : Nat) :
    ∀ (n consumed : Nat), input.size - consumed < n →
      QuotedSpec v input start0 st0 loc0 coll held tokenStart base h origin consumed := by
  intro n
  induction n with
  | zero => intro consumed hn; omega
  | succ n ih =>
  intro consumed hn horigin hconsumed s locq hfix hbase0 hholds hbytes hloc hlow hb hts hstate hfits
    h0 hs0 hanchor
  have hJ : Lexer.Slice.runEnd input consumed Lexer.RUN_QUOTED_PLAIN =
      runEnd input isQuotedRun consumed := runEnd_eq endsRun_quoted _ _
  have hle := le_runEnd input isQuotedRun consumed
  have hle' := runEnd_le input isQuotedRun consumed hconsumed
  have hstop := fun h => runEnd_stop input isQuotedRun consumed h
  have hA := feedFrom_mode v input isQuotedRun isQuotedRun_ne .quotedSymbol
    (fun q l c hm hc => advance_quotedSymbol_run false q l c hm hc) consumed
    ⟨.quotedSymbol, tokenStart, contentBytes s.val.tokenContent⟩ locq rfl hconsumed
  rw [← hJ] at hA hle hle' hstop
  have hext : contentBytes (s.val.tokenContent.extendFrom input.byteArray (input.start + consumed)
      (input.start + Lexer.Slice.runEnd input consumed Lexer.RUN_QUOTED_PLAIN)) =
      contentBytes s.val.tokenContent ++
        bytesOf input consumed (Lexer.Slice.runEnd input consumed Lexer.RUN_QUOTED_PLAIN) :=
    contentBytes_extendSlice input hfits (.inl hle')
  have hfits' := fits_extendSlice input hfits (a := consumed) (.inl hle')
  have hA' := hanchor.trans hA
  have hLI := hloc.afterColumns (by rw [hbase0]; exact h0) hle
  rw [Lexer.WRustPort.lexQuotedSymbol]
  dsimp only
  split
  · -- a byte ends the run inside the slice
    rename_i c hget
    obtain ⟨hIs, hIc⟩ := get?_eq hget
    have hIq := hstop hIs
    rw [hIc] at hIq
    apply wp_ite
    · -- a pipe closes the symbol
      intro hp
      have hp' : c = 124 := by simpa using hp
      have hB : feedFrom v input st0 loc0 start0 =
          feedFrom v input (.token ⟨.quotedSymbolClosed, tokenStart, contentBytes s.val.tokenContent
              ++
            bytesOf input consumed (Lexer.Slice.runEnd input consumed Lexer.RUN_QUOTED_PLAIN)⟩)
            (afterColumns locq (Lexer.Slice.runEnd input consumed Lexer.RUN_QUOTED_PLAIN + 1 -
              consumed)) (Lexer.Slice.runEnd input consumed Lexer.RUN_QUOTED_PLAIN + 1) := by
        rw [hA', feedFrom_step hIs (byteStep_token_pending v (by rw [hIc, hp']; rfl)), prep_nil,
          hIc, hp', afterByte_eq_afterColumns' _ _ (by decide), afterColumns_add]
        congr 2
        omega
      have hLJ := hloc.afterColumns (by rw [hbase0]; exact h0)
        (show consumed ≤ Lexer.Slice.runEnd input consumed Lexer.RUN_QUOTED_PLAIN + 1 by omega)
      unfold Lexer.WRustPort.extendContent Lexer.WRustPort.modifyContent
      apply wp_bind; apply wp_modifyCore
      split
      · -- the byte after the pipe is in the slice
        rename_i next hnext
        obtain ⟨hNs, hNc⟩ := get?_eq hnext
        have hC := feedFrom_end v input hNs (q := ⟨.quotedSymbolClosed, tokenStart,
            contentBytes s.val.tokenContent ++ bytesOf input consumed
              (Lexer.Slice.runEnd input consumed Lexer.RUN_QUOTED_PLAIN)⟩)
          (location := afterColumns locq (Lexer.Slice.runEnd input consumed
            Lexer.RUN_QUOTED_PLAIN + 1 - consumed)) (advance_end_quotedSymbolClosed rfl)
        rw [← hB, hNc] at hC
        unfold Lexer.WRustPort.expectDelimiter
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
          refine sinkStored_wp v .quotedSymbol (.mkAtByte _) tokenStart base h held _ ?_ coll
            ?_ ?_ ?_ ?_ ?_
          · exact hholds
          · exact hfix.recovers
          · exact hfix.version
          · exact hfits'
          · intro s1 coll1 hk1 hb1 hc1
            obtain ⟨k1, k2, k3, k4, k5, k6, k7, k8, k9, k10, k11⟩ := key_fields hk1
            unfold Lexer.WRustPort.setNormal
            apply wp_bind; apply wp_modifyCore
            apply wp_pure
            have hstep := stepLocation_eq' (pos := Lexer.Slice.runEnd input consumed
              Lexer.RUN_QUOTED_PLAIN + 1) hloc (by rw [hbase0]; exact h0) hb hlow (by omega)
            refine armPost_finish (s0 := _) ⟨hfix.1, hfix.2, hfix.3, hfix.4⟩ hbase0
              (show start0 ≤ Lexer.Slice.runEnd input consumed Lexer.RUN_QUOTED_PLAIN + 1 by
                omega) hbytes ⟨k1, k4, k3, k5, rfl, k8, k9, k10, k11, hb1⟩ hLJ hc1 ?_
            rw [hC]
            show _ = Prep [⟨.quotedSymbol, contentBytes (s.val.tokenContent.extendFrom
                input.byteArray (input.start + consumed)
            (input.start + (Lexer.Slice.runEnd input consumed Lexer.RUN_QUOTED_PLAIN))), tokenStart,
              stepLocation s.val low base
                (Lexer.Slice.runEnd input consumed Lexer.RUN_QUOTED_PLAIN + 1)⟩] _
            rw [hext, hstep]
          · intro hn e s' coll'
            show outcome v _ _ = none
            rw [hC, outcome_prep]
            have hstep := stepLocation_eq' (pos := Lexer.Slice.runEnd input consumed
              Lexer.RUN_QUOTED_PLAIN + 1) hloc (by rw [hbase0]; exact h0) hb hlow (by omega)
            have hn' : pending v coll (held ++ [⟨.quotedSymbol, contentBytes
                (s.val.tokenContent.extendFrom input.byteArray (input.start + consumed)
            (input.start + (Lexer.Slice.runEnd input consumed
                  Lexer.RUN_QUOTED_PLAIN))), tokenStart,
                stepLocation s.val low base
                  (Lexer.Slice.runEnd input consumed Lexer.RUN_QUOTED_PLAIN + 1)⟩]) = none := hn
            rw [hext, hstep] at hn'
            exact (congrArg (fun x => outcome v x _) hn').trans (outcome_none_left v _)
      · -- the pipe is the last byte of the slice: the symbol waits for its delimiter
        rename_i hnext
        have hNe := Lexer.Slice.size_le_of_get?_none hnext
        unfold Lexer.WRustPort.setTokenState
        apply wp_bind; apply wp_modifyBound
        apply wp_pure
        refine armPost_pending (s0 := s.val) hfix hbase0
          (show start0 < Lexer.Slice.runEnd input consumed Lexer.RUN_QUOTED_PLAIN + 1 by omega)
          hholds hbytes ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ ?_ hLJ hB
        exact ⟨⟨rfl, rfl, hext.symm⟩, hfits'⟩
    · intro hp
      have hp' : c ≠ 124 := by simpa using hp
      apply wp_ite
      · -- a backslash
        intro hbs
        have hbs' : c = 92 := by simpa using hbs
        have hf : ∃ f, advance false ⟨.quotedSymbol, tokenStart, contentBytes s.val.tokenContent ++
            bytesOf input consumed (Lexer.Slice.runEnd input consumed Lexer.RUN_QUOTED_PLAIN)⟩
            (afterColumns locq (Lexer.Slice.runEnd input consumed Lexer.RUN_QUOTED_PLAIN -
              consumed)) input[Lexer.Slice.runEnd input consumed Lexer.RUN_QUOTED_PLAIN] =
            .error f := by
          rw [hIc, hbs']; exact ⟨_, rfl⟩
        obtain ⟨f, hf⟩ := hf
        unfold Lexer.WRustPort.errorAt Lexer.WRustPort.errorWith
        wp_walk
        show outcome v _ _ = none
        rw [hA', feedFrom_advance_error v input hIs hf, outcome_none_right]
      · intro hbs
        have hbs' : c ≠ 92 := by simpa using hbs
        apply wp_ite
        · -- a line feed, which is marked; the loop goes on after it
          intro h10
          have h10' : c = 10 := by simpa using h10
          have hB : feedFrom v input st0 loc0 start0 =
              feedFrom v input (.token ⟨.quotedSymbol, tokenStart, (contentBytes s.val.tokenContent
                  ++
                bytesOf input consumed (Lexer.Slice.runEnd input consumed
                  Lexer.RUN_QUOTED_PLAIN)).push 10⟩)
                ((afterColumns locq (Lexer.Slice.runEnd input consumed Lexer.RUN_QUOTED_PLAIN -
                  consumed)).afterByte 10)
                (Lexer.Slice.runEnd input consumed Lexer.RUN_QUOTED_PLAIN + 1) := by
            rw [hA', feedFrom_step hIs (byteStep_token_pending v (by rw [hIc, h10']; rfl)),
              prep_nil, hIc, h10']
          unfold Lexer.WRustPort.markLineFeedAt Lexer.WRustPort.extendContent
            Lexer.WRustPort.modifyContent
          apply wp_bind; apply wp_modifyCore
          apply wp_bind; apply wp_modifyCore
          refine ih (Lexer.Slice.runEnd input consumed Lexer.RUN_QUOTED_PLAIN + 1) (by omega) _ _ _
            ((afterColumns locq (Lexer.Slice.runEnd input consumed Lexer.RUN_QUOTED_PLAIN -
              consumed)).afterByte 10) ⟨hfix.1, hfix.2, hfix.3, hfix.4⟩ hbase0 hholds hbytes
            ?_ hlow hb hts hstate (fits_extendSlice input hfits (a := consumed)
              (b := Lexer.Slice.runEnd input consumed Lexer.RUN_QUOTED_PLAIN + 1) (.inl (by omega)))
                  (by omega) hs0 ?_
          · refine LocAt.lineFeed hLI (by rw [hbase0]; omega) rfl ?_
            show Lexer.WRustPort.LexerCore.offsetAt _ _ + 1 = _
            simp only [Lexer.WRustPort.LexerCore.offsetAt]
          · rw [hB, contentBytes_extendSlice input hfits (a := consumed)
              (b := Lexer.Slice.runEnd input consumed Lexer.RUN_QUOTED_PLAIN + 1) (.inl (by omega)),
              content_succ input _ hle hIs, hIc, h10']
        · -- any other byte is not in a quoted symbol
          intro h10
          have h10' : c ≠ 10 := by simpa using h10
          have htext : isTextByte c = false := by
            simp only [isQuotedRun, Bool.and_eq_false_iff, bne_eq_false_iff_eq] at hIq
            rcases hIq with ((h1 | h1) | h1) | h1
            · exact h1
            · exact absurd h1 hp'
            · exact absurd h1 hbs'
            · exact absurd h1 h10'
          have hf : ∃ f, advance false ⟨.quotedSymbol, tokenStart, contentBytes s.val.tokenContent
              ++
              bytesOf input consumed (Lexer.Slice.runEnd input consumed Lexer.RUN_QUOTED_PLAIN)⟩
              (afterColumns locq (Lexer.Slice.runEnd input consumed Lexer.RUN_QUOTED_PLAIN -
                consumed)) input[Lexer.Slice.runEnd input consumed Lexer.RUN_QUOTED_PLAIN] =
              .error f := by
            rw [hIc]
            simp [advance, hp', hbs', htext]
          obtain ⟨f, hf⟩ := hf
          unfold Lexer.WRustPort.errorAt Lexer.WRustPort.errorWith
          wp_walk
          show outcome v _ _ = none
          rw [hA', feedFrom_advance_error v input hIs hf, outcome_none_right]
  · -- the run reaches the end of the slice: the symbol is left in progress
    rename_i hget
    have hIe := Lexer.Slice.size_le_of_get?_none hget
    have he : Lexer.Slice.runEnd input consumed Lexer.RUN_QUOTED_PLAIN = input.size := by omega
    unfold Lexer.WRustPort.extendContent Lexer.WRustPort.modifyContent
    apply wp_bind; apply wp_modifyCore
    apply wp_pure
    rw [he] at hA' hLI hext hfits'
    refine armPost_pending (s0 := s.val) hfix hbase0 hs0 hholds hbytes
      ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ ?_ hLI hA'
    refine ⟨?_, hfits'⟩
    show TokenAgrees v s.val.state s.val.tokenStart
      (contentBytes (s.val.tokenContent.extendFrom input.byteArray (input.start + consumed)
        (input.start + input.size))) _
    rw [hext, hstate]
    exact ⟨hts, rfl, rfl⟩

/-- The arm of `lexStep` for a quoted symbol. -/
theorem arm_quotedSymbol (v : Version) (input : ByteSlice) (start : Nat)
    (hstart : start < input.size) (tokenStart : Location) (base : Nat)
    (h : Lexer.WRustPort.Started floor low tokenStart) (s : BS floor low) (coll : Collector)
    (p : Pending) (location : Location) (held : List Lexeme)
    (hpre : StepPre v input (.token p) location held start s.val) (hlow : low = s.val.offset)
    (hts : tokenStart = s.val.tokenStart) (hb : base = s.val.base)
    (hstate : s.val.state = .quotedSymbol) :
    WP (Lexer.WRustPort.lexQuotedSymbol (H := Collector) (m := Id) (R := Empty) (E := Unit)
        input start start (Nat.le_refl _) (Nat.le_of_lt hstart) tokenStart base h) s coll
      (fun r s' coll' => ArmPost v input (.token p) location start coll held r.1 s'.val coll')
      (fun _ _ _ => StepFails v input (.token p) location start coll held) := by
  obtain ⟨hps, hm, hcont⟩ := token_agrees hpre.agrees hstate
  refine quotedSpec_lt v input start (.token p) location coll held tokenStart base h start _
    start (Nat.lt_succ_self _) (Nat.le_refl _) (Nat.le_of_lt hstart) s location hpre.fixed
    hpre.base hpre.holds hpre.bytes hpre.loc hlow hb hts hstate (token_fits hpre.agrees)
    (Nat.le_refl _) hstart ?_
  obtain ⟨mode, pstart, pcontent⟩ := p
  simp only at hps hm hcont
  subst hm hps hcont
  rw [hts]

end

end BSmtLib.Proofs.Lexer.V1NaiveWRustPort
