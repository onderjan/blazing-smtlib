module

public import BSmtLib.Facts.Proofs.Lexer.VNaiveWRustPort.Normal.Basic
import all BSmtLib.Lexer.Internal.Helpers
import all BSmtLib.Lexer.Internal.WRustPort
import all BSmtLib.Lexer.Internal.VNaive

@[expose] public section

/-!
# The normal state on single bytes

The steps of the Rust port's normal state at the end of the slice, at a parenthesis, at a line
feed off the fast path, and at a byte that starts no token.
-/

namespace BSmtLib.Facts.Proofs.Lexer.VNaiveWRustPort.Normal.Single

open BSmtLib.Lexer.Internal.WRustPort (lexNormalFrom FastState Frame Held Past)
open BSmtLib.Lexer.Internal.WRustPort.Slice (get? get)
open BSmtLib.Facts.Proofs.Lexer.Consumers.Pure BSmtLib.Facts.Proofs.Lexer.VNaiveWRustPort.Agree
open BSmtLib.Facts.Proofs.Lexer.VNaiveWRustPort.Bytes
open BSmtLib.Facts.Proofs.Lexer.VNaiveWRustPort.Feed
open BSmtLib.Facts.Proofs.Lexer.VNaiveWRustPort.HandOver
open BSmtLib.Facts.Proofs.Lexer.VNaiveWRustPort.Model
open BSmtLib.Facts.Proofs.Lexer.VNaiveWRustPort.Normal.Basic
open BSmtLib.Facts.Proofs.Lexer.VNaiveWRustPort.Pure BSmtLib.Facts.Proofs.Lexer.VNaiveWRustPort.Push
open BSmtLib.Facts.Proofs.Lexer.VNaiveWRustPort.StartWs
open BSmtLib.Facts.Proofs.Lexer.VNaiveWRustPort.Step
open BSmtLib.Facts.Proofs.Lexer.VNaiveWRustPort.Tables.Start BSmtLib.Lexer.Internal.VNaive

section

variable {floor : Option Nat} {low : Nat}

variable {C : BSmtLibSpec.Lexer.Consumer} {hd : Bool} {iv : Token.Version}

/-- `normalSpec_lt` at the end of the slice. -/
theorem normalSpec_end (v : Token.Version) (input : ByteSlice) (offset base : Nat)
    (hframe : Frame floor low offset) (index : Nat)
    (hget₀ : get? input index = none) :
    NormalSpec C v hd iv input offset base hframe index := by
  intro batch locals hindex hbatch origin horigin s coll held location hfix hoff hbase
    hline hlineStart hnormal hloc hheld hbytes
  rw [lexNormalFrom]
  split
  · -- the end of the slice
    rename_i hget
    rw [WP.rust_storeLocals]
    unfold FastState.store Lexer.Internal.WRustPort.leave
    apply WP.wp_bind
    apply WP.wp_modifyCore
    apply WP.wp_bind
    apply WP.wp_modifyBound
    apply WP.wp_pure
    refine ⟨.idle, location, held, ⟨hfix.1, hfix.2, hfix.3, hfix.4, hfix.5, hfix.6⟩,
        Nat.le_refl _, rfl,
      ?_, hheld,
      hbytes, rfl⟩
    obtain ⟨h1, h2, h3⟩ := hloc
    refine ⟨?_, ?_, ?_⟩
    · show location.offset = offset + (index - base) + (index - index)
      omega
    · show location.line = locals.line
      rw [hline]; exact h2
    · show locals.lineStart + location.column = location.offset
      rw [hlineStart]; exact h3
  rename_i c hget; rw [hget₀] at hget; cases hget

/-- `normalSpec_lt` at a closing parenthesis. -/
theorem normalSpec_parenClose (v : Token.Version) (input : ByteSlice) (offset base : Nat)
    (hframe : Frame floor low offset) (n index : Nat)
    (ih : ∀ index, input.size - index < n → NormalSpec C v hd iv input offset base hframe index)
    (hn : input.size - index < n + 1)
    {c₀ : UInt8} (hget₀ : get? input index = some c₀) (h41 : c₀ = 41) :
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
  · -- a closing parenthesis
    intro hcp
    have hc41 : c = 41 := by simpa using hcp
    apply WP.wp_bind
    apply WP.wp_getCore
    simp only [hfix.recovers, Bool.false_eq_true, ↓reduceIte]
    subst hc41
    have hstep : feedFrom v C.concrete input .idle location index =
        Prep [⟨.parenClose, ByteArray.empty.push 41, location, location.afterByte 41⟩]
          (feedFrom v C.concrete input .idle (location.afterByte 41) (index + 1)) := by
      rw [feedFrom_lt hi, hc]
      simp only [byteStepW, startStepW, start_parenClose]
    have hl : onLine .parenClose (input.slice index (index + 1)) locals.line locals.lineStart
        (offset + (index - base)) (offset + (index + 1 - base)) =
        ⟨.parenClose, ByteArray.empty.push 41, location, location.afterByte 41⟩ := by
      rw [hline, hlineStart, onLine_eq hloc hindex (Nat.le_succ _),
        afterByte_eq_afterColumns' _ _ (by decide)]
      simp only [Lexeme.mk.injEq, true_and]
      refine ⟨?_, by simp⟩
      show bytesOf input index (index + 1) = _
      rw [bytesOf_one input index hi, hc]
    apply WP.wp_bind
    refine pushFast_wp input batch locals offset base _ index (index + 1) index (index + 1) true _
      hindex _ hframe hbatch held hheld hbytes.symm (Nat.le_succ _) hi s coll hfix.recovers

      ?_ ?_
    · intro r s' coll' held' hH hb hk hp
      rw [hfix.holding] at hp
      simp only [↓reduceIte, hl] at hp
      obtain ⟨k1, k2, k3, k4, k5, k6, k7, k8, k9, k10, k11⟩ := key_fields hk
      have heq : outcome C hd (pending C hd s.val.version coll held)
          (feedFrom v C.concrete input .idle location index) =
          outcome C hd (pending C hd s'.val.version coll' held')
            (feedFrom v C.concrete input .idle (location.afterByte 41) (index + 1)) := by
        rw [hstep, outcome_pending_prep, outcome_pending_congr hp]
      refine WP.wp_mono (ih (index + 1) (by omega) r.val locals _
        r.property origin _ s' coll' held' (location.afterByte 41) (fixed_of_key hfix hk)
        (hoff.trans k8.symm) (hbase.trans k9.symm) (hline.trans k10.symm)
        (hlineStart.trans k11.symm) (k2.trans hnormal)
        ((hloc.afterByte hindex (by decide)).congr k10 k11) hH (hb.trans hbytes))
        (fun a s'' coll'' hpost => StepPost.trans heq hpost)
        (fun e s'' coll'' hf => StepFails.trans heq hf)
    · intro e s' p d hn hss
      simp only [↓reduceIte, hl] at hn
      exact stepFails_of_stops' hss ⟨hfix.1, hfix.2, hfix.3, hfix.4, hfix.5, hfix.6⟩
        ⟨_, by rw [hstep, outcome_pending_prep] <;> rfl⟩ hn
  intro hcp; exact absurd (by rw [h41]; decide) hcp

/-- `normalSpec_lt` at an opening parenthesis. -/
theorem normalSpec_parenOpen (v : Token.Version) (input : ByteSlice) (offset base : Nat)
    (hframe : Frame floor low offset) (n index : Nat)
    (ih : ∀ index, input.size - index < n → NormalSpec C v hd iv input offset base hframe index)
    (hn : input.size - index < n + 1)
    {c₀ : UInt8} (hget₀ : get? input index = some c₀) (h40 : c₀ = 40) :
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
  · intro hcp; exact absurd (by simpa using hcp) (show c ≠ 41 by rw [h40]; decide)
  intro hcp
  apply WP.wp_ite
  · -- an opening parenthesis
    intro hop
    have hc40 : c = 40 := by simpa using hop
    apply WP.wp_bind
    apply WP.wp_getCore
    simp only [hfix.recovers, Bool.false_eq_true, ↓reduceIte]
    subst hc40
    have hstep : feedFrom v C.concrete input .idle location index =
        Prep [⟨.parenOpen, ByteArray.empty.push 40, location, location.afterByte 40⟩]
          (feedFrom v C.concrete input .idle (location.afterByte 40) (index + 1)) := by
      rw [feedFrom_lt hi, hc]
      simp only [byteStepW, startStepW, start_parenOpen]
    have hl : onLine .parenOpen (input.slice index (index + 1)) locals.line locals.lineStart
        (offset + (index - base)) (offset + (index + 1 - base)) =
        ⟨.parenOpen, ByteArray.empty.push 40, location, location.afterByte 40⟩ := by
      rw [hline, hlineStart, onLine_eq hloc hindex (Nat.le_succ _),
        afterByte_eq_afterColumns' _ _ (by decide)]
      simp only [Lexeme.mk.injEq, true_and]
      refine ⟨?_, by simp⟩
      show bytesOf input index (index + 1) = _
      rw [bytesOf_one input index hi, hc]
    apply WP.wp_bind
    refine pushFast_wp input batch locals offset base _ index (index + 1) index (index + 1) true _
      hindex _ hframe hbatch held hheld hbytes.symm (Nat.le_succ _) hi s coll hfix.recovers

      ?_ ?_
    · intro r s' coll' held' hH hb hk hp
      rw [hfix.holding] at hp
      simp only [↓reduceIte, hl] at hp
      obtain ⟨k1, k2, k3, k4, k5, k6, k7, k8, k9, k10, k11⟩ := key_fields hk
      have heq : outcome C hd (pending C hd s.val.version coll held)
          (feedFrom v C.concrete input .idle location index) =
          outcome C hd (pending C hd s'.val.version coll' held')
            (feedFrom v C.concrete input .idle (location.afterByte 40) (index + 1)) := by
        rw [hstep, outcome_pending_prep, outcome_pending_congr hp]
      refine WP.wp_mono (ih (index + 1) (by omega) r.val locals _
        r.property origin _ s' coll' held' (location.afterByte 40) (fixed_of_key hfix hk)
        (hoff.trans k8.symm) (hbase.trans k9.symm) (hline.trans k10.symm)
        (hlineStart.trans k11.symm) (k2.trans hnormal)
        ((hloc.afterByte hindex (by decide)).congr k10 k11) hH (hb.trans hbytes))
        (fun a s'' coll'' hpost => StepPost.trans heq hpost)
        (fun e s'' coll'' hf => StepFails.trans heq hf)
    · intro e s' p d hn hss
      simp only [↓reduceIte, hl] at hn
      exact stepFails_of_stops' hss ⟨hfix.1, hfix.2, hfix.3, hfix.4, hfix.5, hfix.6⟩
        ⟨_, by rw [hstep, outcome_pending_prep] <;> rfl⟩ hn
  intro hop; exact absurd (by rw [h40]; decide) hop

/-- `normalSpec_lt` at a line feed off the fast path. -/
theorem normalSpec_lineFeed (v : Token.Version) (input : ByteSlice) (offset base : Nat)
    (hframe : Frame floor low offset) (n index : Nat)
    (ih : ∀ index, input.size - index < n → NormalSpec C v hd iv input offset base hframe index)
    (hn : input.size - index < n + 1)
    {c₀ : UInt8} (hget₀ : get? input index = some c₀) (hc40₀ : c₀ ≠ 40) (hc41₀ : c₀ ≠ 41)
    (hfoff₀ : (Lexer.Internal.Helpers.fastFlags c₀ &&& Lexer.Internal.Helpers.FAST_ON != 0) = false)
    (hst₀ : Lexer.Internal.Helpers.startOf c₀ = .lineFeed) :
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
  · -- a line feed, passed over
    by_cases hcon : C.concrete = true
    · rename_i hst
      have h10 := Lexer.Internal.Helpers.eq_of_startOf_eq_lineFeed hst
      simp only [answering_concrete, hcon, ↓reduceIte]
      apply WP.wp_bind
      refine startWhitespace_wp v input offset base index batch _ hframe hindex hbatch s coll held
        location hfix hoff hbase hloc hheld hbytes hcon hi (by rw [hc, h10]; rfl) ?_ ?_ ?_
      · intro next batch' hnext hbatch' s' coll' held' locN hfix' hoff' hbase' hnormal' hloc'
          hheld' hbytes' heq
        dsimp only
        rw [WP.rust_loadLocals]
        unfold FastState.load
        apply WP.wp_bind; apply WP.wp_bind; apply WP.wp_getCore; apply WP.wp_pure
        exact wp_recurse (f := fun (r : Past input origin) => r.1)
          (ih next (by omega) batch' _ _ hbatch' origin _ s' coll' held' locN hfix' hoff' hbase'
            rfl rfl hnormal' hloc' hheld' hbytes') heq
      · intro s' hpost
        apply WP.wp_pure
        exact hpost
      · intro e s' coll' hf
        exact hf
    have hcon' : C.concrete = false := by simpa using hcon
    simp only [answering_concrete, hcon', Bool.false_eq_true, ↓reduceIte]
    rename_i hst
    have h10 := Lexer.Internal.Helpers.eq_of_startOf_eq_lineFeed hst
    rw [WP.rust_loadLocals]
    unfold Lexer.Internal.WRustPort.markLineFeedAt FastState.load
    apply WP.wp_bind; apply WP.wp_modifyCore
    apply WP.wp_bind; apply WP.wp_bind; apply WP.wp_getCore; apply WP.wp_pure
    have hpure : feedFrom v C.concrete input .idle location index =
        feedFrom v C.concrete input .idle (location.afterByte 10) (index + 1) := by
      rw [feedFrom_step hi (byteStep_idle_idle v C.concrete (by rw [hc, h10, hcon']; rfl)),
          prep_nil, hc, h10]
    refine wp_recurse (f := fun (r : Past input origin) => r.1)
      (ih (index + 1) (by omega) batch _ _ _ origin _ _ coll held (location.afterByte 10)
        ⟨hfix.1, hfix.2, hfix.3, hfix.4, hfix.5, hfix.6⟩ hoff hbase rfl rfl hnormal
        (hloc.lineFeed hindex rfl (by
          show Lexer.Internal.WRustPort.LexerCore.offsetAt _ index + 1 = _
          simp only [Lexer.Internal.WRustPort.LexerCore.offsetAt]
          rw [← hoff, ← hbase])) hheld hbytes) ?_
    rw [hpure]

/-- `normalSpec_lt` at a byte that starts no token. -/
theorem normalSpec_other (v : Token.Version) (input : ByteSlice) (offset base : Nat)
    (hframe : Frame floor low offset) (index : Nat)
    {c₀ : UInt8} (hget₀ : get? input index = some c₀) (hc40₀ : c₀ ≠ 40) (hc41₀ : c₀ ≠ 41)
    (hfoff₀ : (Lexer.Internal.Helpers.fastFlags c₀ &&& Lexer.Internal.Helpers.FAST_ON != 0) = false)
    (hst₀ : (Lexer.Internal.Helpers.startOf c₀ == .other || Lexer.Internal.Helpers.startOf c₀ ==
        .whitespace ||
      Lexer.Internal.Helpers.startOf c₀ == .parenOpen || Lexer.Internal.Helpers.startOf c₀ ==
          .parenClose ||
      Lexer.Internal.Helpers.startOf c₀ == .symbol || Lexer.Internal.Helpers.startOf c₀ == .pipe)
          = true) :
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
    | (rename_i hst'; rw [hst'] at hst₀; exact absurd hst₀ (by decide))
    | skip
  -- a byte that starts no token
  all_goals
    rename_i hst
    have hother := startOf_other c
    have hs1 : (Lexer.Internal.Helpers.startOf c == .other || Lexer.Internal.Helpers.startOf c ==
        .whitespace ||
        Lexer.Internal.Helpers.startOf c == .parenOpen || Lexer.Internal.Helpers.startOf c ==
            .parenClose ||
        Lexer.Internal.Helpers.startOf c == .symbol || Lexer.Internal.Helpers.startOf c == .pipe)
            = true := by
      rw [hst]; rfl
    have h40b : (c == 40) = false := by simpa using hc40
    have h41b : (c == 41) = false := by simpa using hc41
    rw [hs1, hfoff, h40b, h41b] at hother
    simp only [Bool.not_true, Bool.false_or, Bool.and_eq_true, Bool.not_eq_true', bne_iff_ne,
      ne_eq] at hother
    obtain ⟨⟨⟨⟨⟨⟨⟨hw, h59⟩, h35⟩, h34⟩, h58⟩, h124⟩, hdig⟩, hsym⟩ := hother
    have herr : start v C.concrete location input[index] =
        .error (failAtByte .unexpectedCharacter location location) := by
      rw [hc]
      simp [start, hw, h59, h35, h34, h58, h124, hdig, hsym, hc40, hc41]
    unfold Lexer.Internal.WRustPort.startToken Lexer.Internal.WRustPort.modifyContent
        Lexer.Internal.WRustPort.leave
      Lexer.Internal.WRustPort.errorAt Lexer.Internal.WRustPort.errorWith
    wp_walk
    refine stepFails_here ?_ hheld
      ⟨hfix.1, hfix.2, hfix.3, hfix.4, hfix.5, hfix.6⟩ rfl
    rw [feedFrom_start_error v C.concrete input hi herr]

end

end BSmtLib.Facts.Proofs.Lexer.VNaiveWRustPort.Normal.Single
