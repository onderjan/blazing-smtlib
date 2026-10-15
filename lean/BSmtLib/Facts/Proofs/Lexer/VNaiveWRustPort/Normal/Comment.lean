module

public import BSmtLib.Facts.Proofs.Lexer.VNaiveWRustPort.Normal.Basic
import all BSmtLib.Lexer.Internal.WRustPort
import all BSmtLib.Lexer.Internal.VNaive

@[expose] public section

/-!
# The normal state on a comment

The step of the Rust port's normal state at the semicolon that starts a comment.
-/

namespace BSmtLib.Facts.Proofs.Lexer.VNaiveWRustPort.Normal.Comment

open BSmtLib.Facts.Proofs.Lexer.Simulation.Bytes
open BSmtLib.Lexer.Internal (CharClass)
open BSmtLib.Lexer.Internal.WRustPort (lexNormalFrom FastState Frame Held Past)
open BSmtLib.Lexer.Internal.WRustPort.Slice (get? get)
open BSmtLib.Facts.Proofs.Lexer.VNaiveWRustPort.Agree
open BSmtLib.Facts.Proofs.Lexer.VNaiveWRustPort.Bytes
open BSmtLib.Facts.Proofs.Lexer.VNaiveWRustPort.Feed
open BSmtLib.Facts.Proofs.Lexer.VNaiveWRustPort.HandOver
open BSmtLib.Facts.Proofs.Lexer.VNaiveWRustPort.Model
open BSmtLib.Facts.Proofs.Lexer.VNaiveWRustPort.Normal.Basic
open BSmtLib.Facts.Proofs.Lexer.VNaiveWRustPort.Pure BSmtLib.Facts.Proofs.Lexer.VNaiveWRustPort.Push
open BSmtLib.Facts.Proofs.Lexer.VNaiveWRustPort.Runs
open BSmtLib.Facts.Proofs.Lexer.VNaiveWRustPort.StartWs
open BSmtLib.Facts.Proofs.Lexer.VNaiveWRustPort.Tables.Start
open BSmtLib.Facts.Proofs.Lexer.VNaiveWRustPort.Tables.TextRuns BSmtLib.Lexer.Internal.VNaive

section

variable {floor : Option Nat} {low : Nat}

variable {C : BSmtLibSpec.Lexer.Consumer} {hd : Bool} {iv : Token.Version}

/-- `normalSpec_lt` at the semicolon that starts a comment. -/
theorem normalSpec_comment (v : Token.Version) (input : ByteSlice) (offset base : Nat)
    (hframe : Frame floor low offset) (n index : Nat)
    (ih : ∀ index, input.size - index < n → NormalSpec C v hd iv input offset base hframe index)
    (hn : input.size - index < n + 1)
    {c₀ : UInt8} (hget₀ : get? input index = some c₀) (hc40₀ : c₀ ≠ 40) (hc41₀ : c₀ ≠ 41)
    (hfoff₀ : (Lexer.Internal.Helpers.fastFlags c₀ &&& Lexer.Internal.Helpers.FAST_ON != 0) = false)
    (hst₀ : Lexer.Internal.Helpers.startOf c₀ = .comment) :
    NormalSpec C v hd iv input offset base hframe index := by
  intro batch locals hindex hbatch origin horigin s coll held location hfix hoff hbase
    hline hlineStart hnormal hloc hheld hbytes
  rw [lexNormalFrom]
  split
  · rename_i hget; rw [hget₀] at hget; cases hget
  rename_i c hget
  have hcc : c = c₀ := Option.some.inj (hget.symm.trans hget₀)
  subst hcc
  obtain ⟨hi, hc⟩ := get?_eq hget
  dsimp only
  apply WP.wp_ite
  · intro hcp; exact absurd (by simpa using hcp) hc41₀
  intro hcp
  apply WP.wp_ite
  · intro hop; exact absurd (by simpa using hop) hc40₀
  intro hop
  have hc40 : c ≠ 40 := by simpa using hop
  have hc41 : c ≠ 41 := by simpa using hcp
  apply WP.wp_bind
  apply WP.wp_pure
  apply WP.wp_ite
  · intro hfast; rw [hfoff₀] at hfast; cases hfast
  -- the slow path
  intro hslow
  have hfoff : (Lexer.Internal.Helpers.fastFlags c &&& Lexer.Internal.Helpers.FAST_ON != 0) = false
      := by simpa using hslow
  obtain ⟨hl1, hl2, hl3⟩ := id hloc
  refine wp_store hline hlineStart ?_
  split
  all_goals first
    | (rename_i hst'; rw [hst₀] at hst'; cases hst'; done)
    | skip
  · -- a comment
    by_cases hcon : C.concrete = true
    · rename_i hst
      have h59 := startOf_comment hst
      simp only [answering_concrete, hcon, ↓reduceIte]
      unfold Lexer.Internal.WRustPort.startToken Lexer.Internal.WRustPort.modifyContent
      apply WP.wp_bind
      apply WP.wp_bind; apply WP.wp_getCore
      apply WP.wp_bind; apply WP.wp_modifyCore
      apply WP.wp_bind; apply WP.wp_modifyCore
      apply WP.wp_pure
      have hE : Lexer.Internal.WRustPort.Slice.runEnd input
          (index + 1) CharClass.RUN_COMMENT_PLAIN =
          runEnd input isCommentRun (index + 1) := runEnd_eq endsRun_comment _ _
      have hle := le_runEnd input isCommentRun (index + 1)
      have hle' := runEnd_le input isCommentRun (index + 1) hi
      have hstop := fun h => runEnd_stop input isCommentRun (index + 1) h
      have hA : feedFrom v C.concrete input .idle location index =
          feedFrom v C.concrete input
            (.token ⟨.comment, location,
              bytesOf input (index + 1) (runEnd input isCommentRun (index + 1))⟩)
            (afterColumns location (runEnd input isCommentRun (index + 1) - index))
            (runEnd input isCommentRun (index + 1)) := by
        rw [feedFrom_startRun v C.concrete input isCommentRun isCommentRun_ne .comment
          (fun q l c hm hc => advance_comment_run C.concrete q l c hm hc) hi
          (q := ⟨.comment, location, .empty⟩) (by rw [hc, h59]; rfl) rfl (by rw [hc, h59]; decide)]
        simp only [empty_append]
      rw [← hE] at hA hle hle' hstop
      split
      · -- the comment ends inside the slice, with its line break, and is handed over
        rename_i c' hgetE
        obtain ⟨hEs, hEc⟩ := get?_eq hgetE
        have hEs' := hstop hEs
        rw [hEc] at hEs'
        have hB : feedFrom v C.concrete input .idle location index =
            Prep [⟨.comment, (bytesOf input (index + 1)
                (Lexer.Internal.WRustPort.Slice.runEnd input
                    (index + 1) CharClass.RUN_COMMENT_PLAIN)).push c', location,
                (afterColumns location (Lexer.Internal.WRustPort.Slice.runEnd input (index + 1)
                  CharClass.RUN_COMMENT_PLAIN - index)).afterByte c'⟩]
              (feedFrom v C.concrete input .idle
                ((afterColumns location (Lexer.Internal.WRustPort.Slice.runEnd input (index + 1)
                  CharClass.RUN_COMMENT_PLAIN - index)).afterByte c')
                (Lexer.Internal.WRustPort.Slice.runEnd input
                    (index + 1) CharClass.RUN_COMMENT_PLAIN + 1)) := by
          have hadv := advance_comment_end_ws location (bytesOf input (index + 1)
            (Lexer.Internal.WRustPort.Slice.runEnd input
                (index + 1) CharClass.RUN_COMMENT_PLAIN))
            (afterColumns location (Lexer.Internal.WRustPort.Slice.runEnd input (index + 1)
              CharClass.RUN_COMMENT_PLAIN - index)) hEs'
          rw [← hEc, ← hcon] at hadv
          rw [hA, feedFrom_step hEs (byteStep_token_with hadv), hEc]
        have hcontent : (input.slice (index + 1)
            (Lexer.Internal.WRustPort.Slice.runEnd input
                (index + 1) CharClass.RUN_COMMENT_PLAIN + 1)).toByteArray =
            (bytesOf input (index + 1)
              (Lexer.Internal.WRustPort.Slice.runEnd input
                  (index + 1) CharClass.RUN_COMMENT_PLAIN)).push c' := by
          have := content_succ input ByteArray.empty hle hEs
          rw [empty_append, empty_append, hEc] at this
          exact this
        apply WP.wp_ite
        · -- a line feed, which is marked
          intro h10
          have h10' : c' = 10 := by simpa using h10
          subst h10'
          have hlex : borrowedLexeme .comment (input.slice (index + 1)
              (Lexer.Internal.WRustPort.Slice.runEnd input
                  (index + 1) CharClass.RUN_COMMENT_PLAIN + 1))
              ⟨offset + (index - base), s.val.line, offset + (index - base) - s.val.lineStart⟩
              (s.val.line + 1)
              (Lexer.Internal.WRustPort.LexerCore.offsetAt s.val
                (Lexer.Internal.WRustPort.Slice.runEnd input
                    (index + 1) CharClass.RUN_COMMENT_PLAIN) + 1)
              (offset + (Lexer.Internal.WRustPort.Slice.runEnd input
                  (index + 1) CharClass.RUN_COMMENT_PLAIN + 1 -
                base)) =
              ⟨.comment, (bytesOf input (index + 1)
                (Lexer.Internal.WRustPort.Slice.runEnd input
                    (index + 1) CharClass.RUN_COMMENT_PLAIN)).push 10,
                location, (afterColumns location (Lexer.Internal.WRustPort.Slice.runEnd input
                    (index + 1)
                  CharClass.RUN_COMMENT_PLAIN - index)).afterByte 10⟩ := by
            simp only [borrowedLexeme, hcontent]
            obtain ⟨h1, h2, h3⟩ := hloc
            cases location
            simp only [afterColumns, Span.Location.afterByte, Lexeme.mk.injEq,
              Span.Location.mk.injEq, true_and,
                  Lexer.Internal.WRustPort.LexerCore.offsetAt] at h1 h2 h3 ⊢
            refine ⟨⟨by omega, h2.symm, by omega⟩, ?_⟩
            have hlf : ((10 : UInt8) == '\n'.toUInt8) = true := rfl
            simp only [hlf, ite_true, Span.Location.mk.injEq]
            refine ⟨by omega, by omega, by omega⟩
          unfold Lexer.Internal.WRustPort.markLineFeedAt
          apply WP.wp_bind; apply WP.wp_modifyCore
          apply WP.wp_bind
          refine pushBorrowed_wp input batch offset base _ _ _ _ _ _ _ _ _ held hheld hbytes.symm
            ?_ ?_ _ coll ?_ ?_ ?_
          · omega
          · omega
          · exact hfix.recovers
          · intro r s' coll' held' hH hb hk hp
            rw [hfix.holding] at hp
            have hp' := hp.trans
              (congrArg (fun l => pending C hd s.val.version coll (held ++ [l])) hlex)
            obtain ⟨k1, k2, k3, k4, k5, k6, k7, k8, k9, k10, k11⟩ := key_fields hk
            rw [WP.rust_loadLocals]
            unfold FastState.load
            apply WP.wp_bind; apply WP.wp_bind; apply WP.wp_getCore; apply WP.wp_pure
            refine wp_recurse (f := fun (r : Past input origin) => r.1)
              (ih _ (by omega) r.val _ _ r.property origin _ s' coll' held'
                ((afterColumns location (Lexer.Internal.WRustPort.Slice.runEnd input (index + 1)
                  CharClass.RUN_COMMENT_PLAIN - index)).afterByte 10)
                (fixed_of_key' hk ⟨hfix.1, hfix.2, hfix.3, hfix.4, hfix.5, hfix.6⟩)
                (hoff.trans k8.symm) (hbase.trans k9.symm) rfl rfl k2
                ((LocAt.lineFeed (hloc.afterColumns hindex (by omega)) (by omega) rfl (by
                  show Lexer.Internal.WRustPort.LexerCore.offsetAt _ _ + 1 = _
                  simp only [Lexer.Internal.WRustPort.LexerCore.offsetAt]
                  rw [← hoff, ← hbase])).congr k10 k11) hH (hb.trans hbytes)) ?_
            rw [hB, outcome_pending_prep, outcome_pending_congr hp']
          · intro e s' p d hn hss
            have hn' := hn
            replace hn' := stops_lexeme hlex hn'
            exact stepFails_of_stops' hss ⟨hfix.1, hfix.2, hfix.3, hfix.4, hfix.5, hfix.6⟩
              ⟨_, by rw [hB, outcome_pending_prep] <;> rfl⟩ hn'
        · -- a carriage return
          intro h10
          have h10' : c' ≠ 10 := by simpa using h10
          have hlex := borrowedLexeme_eq hloc hindex
            (j := Lexer.Internal.WRustPort.Slice.runEnd input
                (index + 1) CharClass.RUN_COMMENT_PLAIN + 1) (by omega)
            .comment (input.slice (index + 1)
              (Lexer.Internal.WRustPort.Slice.runEnd input
                  (index + 1) CharClass.RUN_COMMENT_PLAIN + 1))
          have hendE : (afterColumns location (Lexer.Internal.WRustPort.Slice.runEnd input
              (index + 1)
              CharClass.RUN_COMMENT_PLAIN - index)).afterByte c' =
              afterColumns location (Lexer.Internal.WRustPort.Slice.runEnd input (index + 1)
                CharClass.RUN_COMMENT_PLAIN + 1 - index) := by
            rw [afterByte_eq_afterColumns' _ _ h10', afterColumns_add]
            congr 1
            omega
          rw [hcontent] at hlex
          rw [hendE] at hB
          apply WP.wp_bind
          refine pushBorrowed_wp input batch offset base _ _ _ _ _ _ _ _ _ held hheld hbytes.symm
            ?_ ?_ _ coll ?_ ?_ ?_
          · omega
          · omega
          · exact hfix.recovers
          · intro r s' coll' held' hH hb hk hp
            rw [hfix.holding] at hp
            have hp' := hp.trans
              (congrArg (fun l => pending C hd s.val.version coll (held ++ [l])) hlex)
            obtain ⟨k1, k2, k3, k4, k5, k6, k7, k8, k9, k10, k11⟩ := key_fields hk
            rw [WP.rust_loadLocals]
            unfold FastState.load
            apply WP.wp_bind; apply WP.wp_bind; apply WP.wp_getCore; apply WP.wp_pure
            refine wp_recurse (f := fun (r : Past input origin) => r.1)
              (ih _ (by omega) r.val _ _ r.property origin _ s' coll' held'
                (afterColumns location (Lexer.Internal.WRustPort.Slice.runEnd input (index + 1)
                  CharClass.RUN_COMMENT_PLAIN + 1 - index))
                (fixed_of_key' hk ⟨hfix.1, hfix.2, hfix.3, hfix.4, hfix.5, hfix.6⟩)
                (hoff.trans k8.symm) (hbase.trans k9.symm) rfl rfl k2
                ((hloc.afterColumns hindex (by omega)).congr k10 k11) hH (hb.trans hbytes)) ?_
            rw [hB, outcome_pending_prep, outcome_pending_congr hp']
          · intro e s' p d hn hss
            have hn' := hn
            replace hn' := stops_lexeme hlex hn'
            exact stepFails_of_stops' hss ⟨hfix.1, hfix.2, hfix.3, hfix.4, hfix.5, hfix.6⟩
              ⟨_, by rw [hB, outcome_pending_prep] <;> rfl⟩ hn'
      · -- the comment runs to the end of the slice: it is left in progress, with its content
        rename_i hgetE
        have hsz := Lexer.Internal.WRustPort.Slice.size_le_of_get?_none hgetE
        unfold Lexer.Internal.WRustPort.extendContent Lexer.Internal.WRustPort.modifyContent
          Lexer.Internal.WRustPort.leavePending
        apply WP.wp_bind; apply WP.wp_modifyCore
        apply WP.wp_bind; apply WP.wp_modifyBound
        apply WP.wp_pure
        refine ⟨.token ⟨.comment, location, bytesOf input (index + 1)
            (Lexer.Internal.WRustPort.Slice.runEnd input
                (index + 1) CharClass.RUN_COMMENT_PLAIN)⟩,
          afterColumns location (Lexer.Internal.WRustPort.Slice.runEnd input (index + 1)
            CharClass.RUN_COMMENT_PLAIN - index), held,
          ⟨hfix.1, hfix.2, hfix.3, hfix.4, hfix.5, hfix.6⟩, Nat.le_refl _, ?_, ?_,
              hheld, hbytes, ?_⟩
        · dsimp only [StAgrees, TokenAgrees, TokenAgreesNoWs]
          refine ⟨⟨?_, rfl, fun _ => ?_⟩, ?_⟩
          · rw [locAt_eq hloc]; rfl
          · exact (contentBytes_clear_extendSlice _ _ (by bound_tac)).symm
          · fits_tac
        · dsimp only [LocAt, afterColumns, Past.from]
          refine ⟨?_, ?_, ?_⟩ <;> omega
        · rw [hA]; rfl
    have hcon' : C.concrete = false := by simpa using hcon
    simp only [answering_concrete, hcon', Bool.false_eq_true, ↓reduceIte]
    rename_i hst
    have h59 := startOf_comment hst
    unfold Lexer.Internal.WRustPort.startToken Lexer.Internal.WRustPort.modifyContent
    apply WP.wp_bind
    apply WP.wp_bind; apply WP.wp_getCore
    apply WP.wp_bind; apply WP.wp_modifyCore
    apply WP.wp_bind; apply WP.wp_modifyCore
    apply WP.wp_pure
    have hE : Lexer.Internal.WRustPort.Slice.runEnd input
        (index + 1) CharClass.RUN_COMMENT_PLAIN =
        runEnd input isCommentRun (index + 1) := runEnd_eq endsRun_comment _ _
    have hle := le_runEnd input isCommentRun (index + 1)
    have hle' := runEnd_le input isCommentRun (index + 1) hi
    have hstop := fun h => runEnd_stop input isCommentRun (index + 1) h
    have hA : feedFrom v C.concrete input .idle location index =
        feedFrom v C.concrete input
          (.token ⟨.comment, location,
            bytesOf input (index + 1) (runEnd input isCommentRun (index + 1))⟩)
          (afterColumns location (runEnd input isCommentRun (index + 1) - index))
          (runEnd input isCommentRun (index + 1)) := by
      rw [feedFrom_startRun v C.concrete input isCommentRun isCommentRun_ne .comment
        (fun q l c hm hc => advance_comment_run C.concrete q l c hm hc) hi
        (q := ⟨.comment, location, .empty⟩) (by rw [hc, h59]; rfl) rfl (by rw [hc, h59]; decide)]
      simp only [empty_append]
    rw [← hE] at hA hle hle' hstop
    split
    · -- the comment ends inside the slice, with its line break
      rename_i c' hgetE
      obtain ⟨hEs, hEc⟩ := get?_eq hgetE
      have hEs' := hstop hEs
      rw [hEc] at hEs'
      have hB : feedFrom v C.concrete input .idle location index =
          feedFrom v C.concrete input .idle
            ((afterColumns location (Lexer.Internal.WRustPort.Slice.runEnd input (index + 1)
              CharClass.RUN_COMMENT_PLAIN - index)).afterByte c')
            (Lexer.Internal.WRustPort.Slice.runEnd input
                (index + 1) CharClass.RUN_COMMENT_PLAIN + 1) := by
        have hadv := advance_comment_end location (bytesOf input (index + 1)
          (Lexer.Internal.WRustPort.Slice.runEnd input
              (index + 1) CharClass.RUN_COMMENT_PLAIN))
          (afterColumns location (Lexer.Internal.WRustPort.Slice.runEnd input (index + 1)
            CharClass.RUN_COMMENT_PLAIN - index)) hEs'
        rw [← hEc] at hadv
        rw [hA, feedFrom_step hEs (byteStep_token_idle v C.concrete
            (by rw [hcon']; exact hadv)), prep_nil, hEc]
      apply WP.wp_ite
      · -- a line feed, which is marked
        intro h10
        have h10' : c' = 10 := by simpa using h10
        subst h10'
        rw [WP.rust_loadLocals]
        unfold Lexer.Internal.WRustPort.markLineFeedAt FastState.load
        apply WP.wp_bind; apply WP.wp_modifyCore
        apply WP.wp_bind; apply WP.wp_pure
        apply WP.wp_bind; apply WP.wp_bind; apply WP.wp_getCore; apply WP.wp_pure
        refine wp_recurse (f := fun (r : Past input origin) => r.1)
          (ih _ (by omega) batch _ _ _ origin _ _ coll held
            ((afterColumns location (Lexer.Internal.WRustPort.Slice.runEnd input (index + 1)
              CharClass.RUN_COMMENT_PLAIN - index)).afterByte 10)
            ⟨hfix.1, hfix.2, hfix.3, hfix.4, hfix.5, hfix.6⟩ hoff hbase rfl rfl rfl
            (LocAt.lineFeed (hloc.afterColumns hindex (by omega)) (by omega) rfl (by
              show Lexer.Internal.WRustPort.LexerCore.offsetAt _ _ + 1 = _
              simp only [Lexer.Internal.WRustPort.LexerCore.offsetAt]
              rw [← hoff, ← hbase])) hheld hbytes) ?_
        rw [hB]
      · -- a carriage return
        intro h10
        have h10' : c' ≠ 10 := by simpa using h10
        rw [WP.rust_loadLocals]
        unfold FastState.load
        apply WP.wp_bind; apply WP.wp_pure
        apply WP.wp_bind; apply WP.wp_bind; apply WP.wp_getCore; apply WP.wp_pure
        refine wp_recurse (f := fun (r : Past input origin) => r.1)
          (ih _ (by omega) batch _ _ _ origin _ _ coll held
            (afterColumns location (Lexer.Internal.WRustPort.Slice.runEnd input (index + 1)
              CharClass.RUN_COMMENT_PLAIN + 1 - index))
            ⟨hfix.1, hfix.2, hfix.3, hfix.4, hfix.5, hfix.6⟩ hoff hbase rfl rfl rfl
            (hloc.afterColumns hindex (by omega)) hheld hbytes) ?_
        rw [hB, afterByte_eq_afterColumns' _ _ h10', afterColumns_add]
        congr 3
        omega
    · -- the comment runs to the end of the slice: it is left in progress
      rename_i hgetE
      have hsz := Lexer.Internal.WRustPort.Slice.size_le_of_get?_none hgetE
      unfold Lexer.Internal.WRustPort.leavePending
      apply WP.wp_bind; apply WP.wp_modifyBound
      apply WP.wp_pure
      refine ⟨.token ⟨.comment, location, bytesOf input (index + 1)
          (Lexer.Internal.WRustPort.Slice.runEnd input
              (index + 1) CharClass.RUN_COMMENT_PLAIN)⟩,
        afterColumns location (Lexer.Internal.WRustPort.Slice.runEnd input (index + 1)
          CharClass.RUN_COMMENT_PLAIN - index), held,
        ⟨hfix.1, hfix.2, hfix.3, hfix.4, hfix.5, hfix.6⟩, Nat.le_refl _, ?_, ?_, hheld, hbytes, ?_⟩
      · dsimp only [StAgrees, TokenAgrees, TokenAgreesNoWs]
        refine ⟨⟨?_, rfl, fun h => nomatch h.symm.trans hcon'⟩, ?_⟩
        rw [locAt_eq hloc]; rfl
        · fits_tac
      · dsimp only [LocAt, afterColumns, Past.from]
        refine ⟨?_, ?_, ?_⟩ <;> omega
      · rw [hA]; rfl

end

end BSmtLib.Facts.Proofs.Lexer.VNaiveWRustPort.Normal.Comment
