import BSmtLib.Proofs.VNaiveWRustPort.Pure

/-!
# The Rust port's normal state against the naive lexer

`lexNormalFrom_wp`: the loop of the Rust port's normal state, with its fast paths and its slow
path, keeps the correspondence with the naive lexer's pure run.
-/

namespace BSmtLib.Proofs.Lexer.VNaiveWRustPort

open BSmtLib.Proofs.Adapter VNaive BSmtLib.Proofs.Simulation
open Lexer.WRustPort (lexNormalFrom FastState Frame Held Past)
open Lexer.Slice (get? get)

/-- Takes the steps of the lexer that only read and change the lexer state, and throws. -/
macro "wp_walk" : tactic =>
  `(tactic| repeat (first
    | (apply wp_throw; exact ⟨_, rfl⟩)
    | apply wp_modifyCore
    | apply wp_modifyBound
    | apply wp_getCore
    | apply wp_pure
    | apply wp_bind))

set_option hygiene false in
/-- A string left in progress at the end of its run, in the proof of `normalSpec_lt`. -/
local macro "string_stay" : tactic => `(tactic| (
  unfold Lexer.WRustPort.extendContent Lexer.WRustPort.modifyContent Lexer.WRustPort.leavePending
  apply wp_bind; apply wp_modifyCore
  apply wp_bind; apply wp_modifyBound
  apply wp_pure
  refine ⟨.token ⟨.string, location, bytesOf input (index + 1)
      (Lexer.Slice.runEnd input (index + 1) Lexer.RUN_STRING_PLAIN)⟩,
    afterColumns location (Lexer.Slice.runEnd input (index + 1)
      Lexer.RUN_STRING_PLAIN - index), held, ⟨hfix.1, hfix.2, hfix.3, hfix.4⟩, Nat.le_refl _,
    ?_, ?_, hheld, hbytes, ?_⟩
  · dsimp only [StAgrees, TokenAgrees]
    refine ⟨⟨?_, by simp [hv2'], ?_⟩, ?_⟩
    · rw [locAt_eq hloc]; rfl
    · exact (contentBytes_clear_extendSlice _ _ (by bound_tac)).symm
    · fits_tac
  · dsimp only [LocAt, afterColumns, Past.from]
    refine ⟨?_, ?_, ?_⟩ <;> omega
  · rw [hA]; rfl))

set_option hygiene false in
/-- A token on the slow path into the batch, ending at `hi`, and the loop going on after it, in
the proof of `normalSpec_lt`; `hC` is the naive lexer's run that hands the token over. -/
local macro "borrow_push" cat:term:max lo:term:max hi:term:max : tactic => `(tactic| (
  have hlex := borrowedLexeme_eq hloc hindex (j := $hi) (by omega) $cat (input.slice $lo $hi)
  apply wp_bind
  refine pushBorrowed_wp v input batch offset base _ _ _ _ _ _ _ _ _ held hheld hbytes.symm ?_ ?_ _
    coll ?_ ?_ ?_ ?_
  · omega
  · omega
  · exact hfix.recovers
  · exact hfix.version
  · intro r s' coll' held' hH hb hk hp
    have hp' := hp.trans (congrArg (fun l => pending v coll (held ++ [l])) hlex)
    obtain ⟨k1, k2, k3, k4, k5, k6, k7, k8, k9, k10, k11⟩ := key_fields hk
    rw [rust_loadLocals]
    unfold FastState.load
    apply wp_bind; apply wp_bind; apply wp_getCore; apply wp_pure
    refine wp_recurse (f := fun (r : Past input origin) => r.1)
      (ih _ (by omega) r.val _ _ r.property origin _ s' coll' held'
        (afterColumns location ($hi - index))
        (fixed_of_key' hk ⟨hfix.1, hfix.2, hfix.3, hfix.4⟩) (hoff.trans k8.symm)
        (hbase.trans k9.symm) rfl rfl k2
        ((hloc.afterColumns hindex (by omega)).congr k10 k11) hH (hb.trans hbytes)) ?_
    rw [hC, outcome_prep, outcome_pending_congr hp']
    try rfl
  · intro hn e s' coll'
    have hn' := (congrArg (fun l => pending v coll (held ++ [l])) hlex).symm.trans hn
    apply stepFails_of_none
    show outcome v _ _ = none
    rw [hC, outcome_prep]
    exact (congrArg (fun p => outcome v p _) hn').trans (outcome_none_left v _)))

section

variable {floor : Option Nat} {low : Nat}

/-- The location of the index of the slice, from the offset `offset` of the index `base`. -/
def locOf (c : WCore) (offset base index : Nat) : Location :=
  { offset := offset + (index - base), line := c.line,
    column := offset + (index - base) - c.lineStart }

theorem locAt_eq {c : WCore} {offset base index : Nat} {location : Location}
    (h : LocAt c offset base index location) : location = locOf c offset base index := by
  obtain ⟨h1, h2, h3⟩ := h
  cases location
  simp only [locOf] at h1 h2 h3 ⊢
  subst h1 h2
  congr 1
  omega

/-- A step's postcondition from a later state, whose outcome is that of the earlier one. -/
theorem StepPost.trans {v : Version} {input : ByteSlice} {st st1 : St}
    {location location1 : Location} {start start1 : Nat} {coll coll1 : Collector}
    {held held1 : List Lexeme} {next : Nat}
    {c : WCore} {coll' : Collector}
    (h1 : outcome v (pending v coll held) (feedFrom v input st location start) =
      outcome v (pending v coll1 held1) (feedFrom v input st1 location1 start1))
    (h2 : StepPost v input st1 location1 start1 coll1 held1 next c coll') :
    StepPost v input st location start coll held next c coll' := by
  obtain ⟨st', location', held', h3, h4, h5, h6, h7, h8, h9⟩ := h2
  exact ⟨st', location', held', h3, h4, h5, h6, h7, h8, h1.trans h9⟩

/-- A step's failure from a later state, whose outcome is that of the earlier one. -/
theorem StepFails.trans {v : Version} {input : ByteSlice} {st st1 : St}
    {location location1 : Location} {start start1 : Nat} {coll coll1 : Collector}
    {held held1 : List Lexeme}
    (h1 : outcome v (pending v coll held) (feedFrom v input st location start) =
      outcome v (pending v coll1 held1) (feedFrom v input st1 location1 start1))
    {c : WCore} {coll' : Collector}
    (h2 : StepFails v input st1 location1 start1 coll1 held1 c coll') :
    StepFails v input st location start coll held c coll' := by
  unfold StepFails at h2 ⊢
  rw [h1]
  exact h2

/-- A token on the line of the location of its start, with no line feed in it. -/
theorem onLine_eq {c : WCore} {offset base i j : Nat} {location : Location}
    (h : LocAt c offset base i location) (hi : base ≤ i) (hj : i ≤ j) (ty : TokenCategory)
    (content : ByteSlice) :
    onLine ty content c.line c.lineStart (offset + (i - base)) (offset + (j - base)) =
      { category := ty, content := content.toByteArray, start := location,
        «end» := afterColumns location (j - i) } := by
  rw [locAt_eq h]
  obtain ⟨h1, h2, h3⟩ := h
  simp only [onLine, locOf, afterColumns, Lexeme.mk.injEq, Location.mk.injEq, true_and]
  omega

theorem get?_eq {s : ByteSlice} {i : Nat} {c : UInt8} (h : get? s i = some c) :
    ∃ hi : i < s.size, s[i] = c := by
  unfold get? at h
  split at h
  · exact ⟨‹_›, Option.some.inj h⟩
  · cases h

theorem bytesOf_one (s : ByteSlice) (i : Nat) (hi : i < s.size) :
    bytesOf s i (i + 1) = ByteArray.empty.push s[i] := by
  rw [bytesOf_push s (Nat.le_refl _) hi, bytesOf_self s i (Nat.le_of_lt hi)]

/-- The fields that `key` compares. -/
theorem key_fields {c c' : WCore} (hk : key c' = key c) :
    c'.version = c.version ∧ c'.state = c.state ∧ c'.discard = c.discard ∧
      c'.recovers = c.recovers ∧ c'.recoveryState = c.recoveryState ∧
      c'.tokenStart = c.tokenStart ∧ c'.tokenContent = c.tokenContent ∧ c'.offset = c.offset ∧
      c'.base = c.base ∧ c'.line = c.line ∧ c'.lineStart = c.lineStart := by
  simpa [key] using hk

theorem LocAt.afterByte {c : WCore} {offset base i : Nat} {location : Location}
    (h : LocAt c offset base i location) (hb : base ≤ i) {b : UInt8} (hc : b ≠ 10) :
    LocAt c offset base (i + 1) (location.afterByte b) := by
  rw [afterByte_eq_afterColumns' _ _ hc]
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨?_, h2, ?_⟩ <;> simp only [afterColumns] <;> omega

theorem LocAt.afterColumns {c : WCore} {offset base i j : Nat} {location : Location}
    (h : LocAt c offset base i location) (hb : base ≤ i) (hij : i ≤ j) :
    LocAt c offset base j (afterColumns location (j - i)) := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨?_, h2, ?_⟩ <;> simp only [VNaiveWRustPort.afterColumns] <;> omega

theorem start_parenClose (v : Version) (location : Location) :
    start v false location 41 =
      .token ⟨.parenClose, ByteArray.empty.push 41, location, location.afterByte 41⟩ := rfl

theorem start_parenOpen (v : Version) (location : Location) :
    start v false location 40 =
      .token ⟨.parenOpen, ByteArray.empty.push 40, location, location.afterByte 40⟩ := rfl

theorem outcome_pending_congr {v : Version} {c1 c2 : Collector} {h1 h2 : List Lexeme}
    (h : pending v c1 h1 = pending v c2 h2)
    (e : Except (List Lexeme) (St × Location × List Lexeme)) :
    outcome v (pending v c1 h1) e = outcome v (pending v c2 h2) e := by
  rw [h]

/-- The rest of a step, from a later state whose outcome is that of the earlier one. -/
theorem wp_recurse {α : Type} {x : M floor low α} {f : α → Nat} {v : Version}
    {input : ByteSlice} {st st1 : St} {location location1 : Location} {start start1 : Nat}
    {coll coll1 : Collector} {held held1 : List Lexeme} {s : BS floor low}
    (h : WP x s coll1
      (fun r s' coll' => StepPost v input st1 location1 start1 coll1 held1 (f r) s'.val coll')
      (fun _ s' coll' => StepFails v input st1 location1 start1 coll1 held1 s'.val coll'))
    (heq : outcome v (pending v coll held) (feedFrom v input st location start) =
      outcome v (pending v coll1 held1) (feedFrom v input st1 location1 start1)) :
    WP x s coll1
      (fun r s' coll' => StepPost v input st location start coll held (f r) s'.val coll')
      (fun _ s' coll' => StepFails v input st location start coll held s'.val coll') :=
  wp_mono h (fun _ _ _ hp => StepPost.trans heq hp) (fun _ _ _ hf => StepFails.trans heq hf)

/-- A step from a state with the same value. -/
theorem wp_state_congr {α : Type} {x : M floor low α} {s s' : BS floor low} {coll : Collector}
    {Q : α → BS floor low → Collector → Prop} {QE : Intr floor → BS floor low → Collector → Prop}
    (h : s'.val = s.val) (hw : WP x s coll Q QE) : WP x s' coll Q QE := by
  have : s' = s := Subtype.ext h
  subst this
  exact hw

/-- Writing the loop's copies of the line back, which are the lexer state's. -/
theorem wp_store {β : Type} {locals : FastState} {s : BS floor low} {coll : Collector}
    {f : Unit → M floor low β} {Q : β → BS floor low → Collector → Prop}
    {QE : Intr floor → BS floor low → Collector → Prop}
    (h1 : locals.line = s.val.line) (h2 : locals.lineStart = s.val.lineStart)
    (h : WP (f ()) s coll Q QE) :
    WP (Lexer.WRustPort.Ops.storeLocals (H := Collector) (m := Id) (R := Empty) (E := Unit) locals
      >>= f) s coll Q QE := by
  apply wp_bind
  rw [rust_storeLocals]; unfold FastState.store
  apply wp_modifyCore
  refine wp_state_congr ?_ h
  show { s.val with line := locals.line, lineStart := locals.lineStart } = s.val
  rw [h1, h2]

theorem get_eq {s : ByteSlice} {i : Nat} (h : i < s.size) : Lexer.Slice.get s i = s[i] := by
  simp [Lexer.Slice.get, Lexer.Slice.get?, h]

/-- The location after a line feed, on the line that the lexer state marked after it. -/
theorem LocAt.lineFeed {c c' : WCore} {offset base i : Nat} {location : Location}
    (h : LocAt c offset base i location) (hb : base ≤ i) (hl : c'.line = c.line + 1)
    (hs : c'.lineStart = offset + (i - base) + 1) :
    LocAt c' offset base (i + 1) (location.afterByte 10) := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨?_, ?_, ?_⟩
  · rw [afterByte_offset]; omega
  · show (if (10 : UInt8) == '\n'.toUInt8 then _ else _ : Location).line = _
    simp only [show ((10 : UInt8) == '\n'.toUInt8) = true from rfl, ↓reduceIte]
    rw [hl, h2]
  · rw [afterByte_offset, hs]
    show _ + (if (10 : UInt8) == '\n'.toUInt8 then _ else _ : Location).column = _
    simp only [show ((10 : UInt8) == '\n'.toUInt8) = true from rfl, ↓reduceIte]
    omega

theorem advance_comment_end (start : Location) (content : ByteArray) (location : Location)
    {c : UInt8} (hc : isCommentRun c = false) :
    advance false ⟨.comment, start, content⟩ location c = .idle := by
  simp only [isCommentRun, Bool.and_eq_false_iff, bne_eq_false_iff_eq] at hc
  rcases hc with h | h <;> subst h <;> rfl

/-- A token on the slow path, from the location of `i` to that of `j` on the same line. -/
theorem borrowedLexeme_eq {c : WCore} {offset base i j : Nat} {location : Location}
    (h : LocAt c offset base i location) (hi : base ≤ i) (hj : i ≤ j) (ty : TokenCategory)
    (content : ByteSlice) :
    borrowedLexeme ty content (locOf c offset base i) c.line c.lineStart (offset + (j - base)) =
      ⟨ty, content.toByteArray, location, afterColumns location (j - i)⟩ := by
  rw [locAt_eq h]
  simp only [borrowedLexeme, locOf, afterColumns, Lexeme.mk.injEq, Location.mk.injEq, true_and]
  obtain ⟨h1, h2, h3⟩ := h
  omega

theorem start_whitespaceRun (v : Version) (location : Location) {c : UInt8}
    (h : isWhitespaceRun c = true) : start v false location c = .idle := by
  rw [start_space v false location c h]
  rfl

/-- What the loop of the normal state keeps, from the index `index`: if the lexer state is in
the normal state at `location`, with the loop's copies of its offset, index of the offset and
line, and the loop holds a batch of lexemes, then the loop keeps the correspondence. -/
def NormalSpec (v : Version) (input : ByteSlice) (offset base : Nat)
    (hframe : Frame floor low offset) (index : Nat) : Prop :=
  ∀ (batch : TokenBatch) (locals : FastState) (hindex : base ≤ index)
    (hbatch : Held floor offset base index batch) (origin : Nat) (horigin : origin ≤ index)
    (s : BS floor low) (coll : Collector) (held : List Lexeme) (location : Location),
    Fixed v s.val → offset = s.val.offset → base = s.val.base → locals.line = s.val.line →
    locals.lineStart = s.val.lineStart → s.val.state = .normal →
    LocAt s.val offset base index location → Holds batch held → batch.bytes = input.byteArray →
    WP (lexNormalFrom (H := Collector) (m := Id) (R := Empty) (E := Unit) input offset base
        index batch locals hframe hindex hbatch origin horigin) s coll
      (fun r s' coll' => StepPost v input .idle location index coll held r.1 s'.val coll')
      (fun _ s' coll' => StepFails v input .idle location index coll held s'.val coll')

set_option maxHeartbeats 20000000 in
theorem normalSpec_lt (v : Version) (input : ByteSlice) (offset base : Nat)
    (hframe : Frame floor low offset) :
    ∀ (n index : Nat), input.size - index < n → NormalSpec v input offset base hframe index := by
  intro n
  induction n with
  | zero => intro index h; omega
  | succ n ih =>
  intro index hn batch locals hindex hbatch origin horigin s coll held location hfix hoff hbase
    hline hlineStart hnormal hloc hheld hbytes
  rw [lexNormalFrom]
  split
  · -- the end of the slice
    rename_i hget
    rw [rust_storeLocals]
    unfold FastState.store Lexer.WRustPort.leave
    apply wp_bind
    apply wp_modifyCore
    apply wp_bind
    apply wp_modifyBound
    apply wp_pure
    refine ⟨.idle, location, held, ⟨hfix.1, hfix.2, hfix.3, hfix.4⟩, Nat.le_refl _, rfl, ?_, hheld,
      hbytes, rfl⟩
    obtain ⟨h1, h2, h3⟩ := hloc
    refine ⟨?_, ?_, ?_⟩
    · show location.offset = offset + (index - base) + (index - index)
      omega
    · show location.line = locals.line
      rw [hline]; exact h2
    · show locals.lineStart + location.column = location.offset
      rw [hlineStart]; exact h3
  rename_i c hget
  obtain ⟨hi, hc⟩ := get?_eq hget
  dsimp only
  apply wp_ite
  · -- a closing parenthesis
    intro hcp
    have hc41 : c = 41 := by simpa using hcp
    apply wp_bind
    apply wp_getCore
    simp only [hfix.recovers, Bool.false_eq_true, ↓reduceIte]
    subst hc41
    have hstep : feedFrom v input .idle location index =
        Prep [⟨.parenClose, ByteArray.empty.push 41, location, location.afterByte 41⟩]
          (feedFrom v input .idle (location.afterByte 41) (index + 1)) := by
      rw [feedFrom_lt hi, hc]
      simp only [byteStep, startStep, start_parenClose]
    have hl : onLine .parenClose (input.slice index (index + 1)) locals.line locals.lineStart
        (offset + (index - base)) (offset + (index + 1 - base)) =
        ⟨.parenClose, ByteArray.empty.push 41, location, location.afterByte 41⟩ := by
      rw [hline, hlineStart, onLine_eq hloc hindex (Nat.le_succ _),
        afterByte_eq_afterColumns' _ _ (by decide)]
      simp only [Lexeme.mk.injEq, true_and]
      refine ⟨?_, by simp⟩
      show bytesOf input index (index + 1) = _
      rw [bytesOf_one input index hi, hc]
    apply wp_bind
    refine pushFast_wp v input batch locals offset base _ index (index + 1) index (index + 1) true _
      hindex _ hframe hbatch held hheld hbytes.symm (Nat.le_succ _) hi s coll hfix.recovers
      hfix.version ?_ ?_
    · intro r s' coll' held' hH hb hk hp
      simp only [↓reduceIte, hl] at hp
      obtain ⟨k1, k2, k3, k4, k5, k6, k7, k8, k9, k10, k11⟩ := key_fields hk
      have heq : outcome v (pending v coll held) (feedFrom v input .idle location index) =
          outcome v (pending v coll' held')
            (feedFrom v input .idle (location.afterByte 41) (index + 1)) := by
        rw [hstep, outcome_prep, outcome_pending_congr hp]
      refine wp_mono (ih (index + 1) (by omega) r.val locals _
        r.property origin _ s' coll' held' (location.afterByte 41) (fixed_of_key hfix hk)
        (hoff.trans k8.symm) (hbase.trans k9.symm) (hline.trans k10.symm)
        (hlineStart.trans k11.symm) (k2.trans hnormal)
        ((hloc.afterByte hindex (by decide)).congr k10 k11) hH (hb.trans hbytes))
        (fun a s'' coll'' hpost => StepPost.trans heq hpost)
        (fun e s'' coll'' hf => StepFails.trans heq hf)
    · intro hn e s' coll'
      apply stepFails_of_none
      show outcome v (pending v coll held) (feedFrom v input .idle location index) = none
      rw [hstep, outcome_prep]
      simp only [↓reduceIte, hl] at hn
      rw [hn, outcome_none_left]
  intro hcp
  apply wp_ite
  · -- an opening parenthesis
    intro hop
    have hc40 : c = 40 := by simpa using hop
    apply wp_bind
    apply wp_getCore
    simp only [hfix.recovers, Bool.false_eq_true, ↓reduceIte]
    subst hc40
    have hstep : feedFrom v input .idle location index =
        Prep [⟨.parenOpen, ByteArray.empty.push 40, location, location.afterByte 40⟩]
          (feedFrom v input .idle (location.afterByte 40) (index + 1)) := by
      rw [feedFrom_lt hi, hc]
      simp only [byteStep, startStep, start_parenOpen]
    have hl : onLine .parenOpen (input.slice index (index + 1)) locals.line locals.lineStart
        (offset + (index - base)) (offset + (index + 1 - base)) =
        ⟨.parenOpen, ByteArray.empty.push 40, location, location.afterByte 40⟩ := by
      rw [hline, hlineStart, onLine_eq hloc hindex (Nat.le_succ _),
        afterByte_eq_afterColumns' _ _ (by decide)]
      simp only [Lexeme.mk.injEq, true_and]
      refine ⟨?_, by simp⟩
      show bytesOf input index (index + 1) = _
      rw [bytesOf_one input index hi, hc]
    apply wp_bind
    refine pushFast_wp v input batch locals offset base _ index (index + 1) index (index + 1) true _
      hindex _ hframe hbatch held hheld hbytes.symm (Nat.le_succ _) hi s coll hfix.recovers
      hfix.version ?_ ?_
    · intro r s' coll' held' hH hb hk hp
      simp only [↓reduceIte, hl] at hp
      obtain ⟨k1, k2, k3, k4, k5, k6, k7, k8, k9, k10, k11⟩ := key_fields hk
      have heq : outcome v (pending v coll held) (feedFrom v input .idle location index) =
          outcome v (pending v coll' held')
            (feedFrom v input .idle (location.afterByte 40) (index + 1)) := by
        rw [hstep, outcome_prep, outcome_pending_congr hp]
      refine wp_mono (ih (index + 1) (by omega) r.val locals _
        r.property origin _ s' coll' held' (location.afterByte 40) (fixed_of_key hfix hk)
        (hoff.trans k8.symm) (hbase.trans k9.symm) (hline.trans k10.symm)
        (hlineStart.trans k11.symm) (k2.trans hnormal)
        ((hloc.afterByte hindex (by decide)).congr k10 k11) hH (hb.trans hbytes))
        (fun a s'' coll'' hpost => StepPost.trans heq hpost)
        (fun e s'' coll'' hf => StepFails.trans heq hf)
    · intro hn e s' coll'
      apply stepFails_of_none
      show outcome v (pending v coll held) (feedFrom v input .idle location index) = none
      rw [hstep, outcome_prep]
      simp only [↓reduceIte, hl] at hn
      rw [hn, outcome_none_left]
  intro hop
  have hc40 : c ≠ 40 := by simpa using hop
  have hc41 : c ≠ 41 := by simpa using hcp
  apply wp_bind
  apply wp_pure
  simp only [collector_ws, Bool.false_and, Bool.false_eq_true, ↓reduceIte, dite_false]
  apply wp_ite
  · -- the fast path
    intro hfast
    rcases fastFlags_cases c with hoff' | ⟨hf, hwsr⟩ | ⟨hf, hpipe⟩ | ⟨hf, hsym, hdig⟩
    · rw [hoff'] at hfast; cases hfast
    · -- whitespace other than a line feed
      have hpipe : (Lexer.fastFlags c &&& Lexer.FAST_PIPE != 0) = false := by rw [hf]; decide
      have hsym : (Lexer.fastFlags c &&& Lexer.RUN_SIMPLE_SYMBOL != 0) = false := by
        rw [hf]; decide
      have hemit : (Lexer.fastFlags c &&& Lexer.FAST_EMIT != 0) = false := by rw [hf]; decide
      have hmask : Lexer.fastFlags c &&& Lexer.FAST_RUN_MASK = Lexer.RUN_NON_LF_WHITESPACE := by
        rw [hf]; decide
      have hj : Lexer.Slice.runEnd input (index + 1) (Lexer.fastFlags c &&& Lexer.FAST_RUN_MASK) =
          runEnd input isWhitespaceRun index := by
        rw [hmask, runEnd_eq endsRun_whitespace,
          ← runEnd_succ input _ index hi (by rw [hc]; exact hwsr)]
      have hle := le_runEnd input isWhitespaceRun (index + 1)
      rw [← runEnd_succ input _ index hi (by rw [hc]; exact hwsr)] at hle
      have hpure : feedFrom v input .idle location index =
          feedFrom v input .idle
            (afterColumns location (runEnd input isWhitespaceRun index - index))
            (runEnd input isWhitespaceRun index) :=
        feedFrom_idleRun v input isWhitespaceRun isWhitespaceRun_ne
          (fun location c h => byteStep_idle_idle v (start_whitespaceRun v location h)) _ index rfl
          location (Nat.le_of_lt hi)
      apply wp_dite
      · intro h; simp [hpipe, hsym] at h
      intro _
      apply wp_ite
      · intro h; rw [hemit] at h; cases h
      intro _
      apply wp_bind
      refine pushFast_wp v input batch locals offset base _ _ _ index _ _ _ hindex _ hframe hbatch
        held hheld hbytes.symm ?_ ?_ s coll hfix.recovers hfix.version ?_ ?_
      · simp only [hpipe, Bool.false_eq_true, ↓reduceIte, hj]; omega
      · simp only [hpipe, Bool.false_eq_true, ↓reduceIte, hj]
        exact runEnd_le input _ _ (Nat.le_of_lt hi)
      · intro r s' coll' held' hH hb hk hp
        simp only [hemit, Bool.false_eq_true, ↓reduceIte, List.append_nil] at hp
        obtain ⟨k1, k2, k3, k4, k5, k6, k7, k8, k9, k10, k11⟩ := key_fields hk
        have hidx : (if (Lexer.fastFlags c &&& Lexer.FAST_PIPE != 0) = true then
              Lexer.Slice.runEnd input (index + 1) (Lexer.fastFlags c &&& Lexer.FAST_RUN_MASK) + 1
            else Lexer.Slice.runEnd input (index + 1) (Lexer.fastFlags c &&& Lexer.FAST_RUN_MASK)) =
            runEnd input isWhitespaceRun index := by
          simp only [hpipe, Bool.false_eq_true, ↓reduceIte, hj]
        refine wp_recurse (f := fun (r : Past input origin) => r.1)
          (ih _ (by rw [hidx]; omega) r.val locals _ r.property origin _ s'
            coll' held'
            (afterColumns location (runEnd input isWhitespaceRun index - index))
            (fixed_of_key hfix hk) (hoff.trans k8.symm) (hbase.trans k9.symm)
            (hline.trans k10.symm) (hlineStart.trans k11.symm) (k2.trans hnormal)
            (by rw [hidx]; exact (hloc.afterColumns hindex (by omega)).congr k10 k11) hH
            (hb.trans hbytes)) ?_
        rw [hidx, ← hpure, outcome_pending_congr hp]
      · intro hn e s' coll'
        simp only [hemit, Bool.false_eq_true, ↓reduceIte, List.append_nil] at hn
        apply stepFails_of_none
        show outcome v _ _ = none
        rw [hn, outcome_none_left]
    · -- a quoted symbol
      have hpipeb : (Lexer.fastFlags c &&& Lexer.FAST_PIPE != 0) = true := by rw [hf]; decide
      have hemit : (Lexer.fastFlags c &&& Lexer.FAST_EMIT != 0) = true := by rw [hf]; decide
      have hmask : Lexer.fastFlags c &&& Lexer.FAST_RUN_MASK = Lexer.RUN_QUOTED_PLAIN := by
        rw [hf]; decide
      have hj : Lexer.Slice.runEnd input (index + 1) (Lexer.fastFlags c &&& Lexer.FAST_RUN_MASK) =
          runEnd input isQuotedRun (index + 1) := by
        rw [hmask, runEnd_eq endsRun_quoted]
      have hle := le_runEnd input isQuotedRun (index + 1)
      have hA : feedFrom v input .idle location index =
          feedFrom v input
            (.token ⟨.quotedSymbol, location,
              bytesOf input (index + 1) (runEnd input isQuotedRun (index + 1))⟩)
            (afterColumns location (runEnd input isQuotedRun (index + 1) - index))
            (runEnd input isQuotedRun (index + 1)) := by
        rw [feedFrom_startRun v input isQuotedRun isQuotedRun_ne .quotedSymbol
          (fun q l c hm hc => advance_quotedSymbol_run false q l c hm hc) hi
          (q := ⟨.quotedSymbol, location, .empty⟩) (by rw [hc, hpipe]; exact start_quoted ..) rfl
          (by rw [hc, hpipe]; decide)]
        simp only [empty_append]
      rw [← hj] at hA hle
      apply wp_dite
      · -- the run is not closed by a pipe: the quoted symbol is left in progress
        intro h
        simp only [hpipeb, ↓reduceIte, Bool.or_true, Bool.true_and, bne_iff_ne, ne_eq] at h
        rw [rust_storeLocals]
        unfold FastState.store Lexer.WRustPort.storeUnfinishedSymbolRun Lexer.WRustPort.startToken
          Lexer.WRustPort.extendContent Lexer.WRustPort.modifyContent Lexer.WRustPort.leavePending
        apply wp_bind; apply wp_modifyCore
        apply wp_bind
        apply wp_bind
        apply wp_bind; apply wp_getCore
        apply wp_bind; apply wp_modifyCore
        apply wp_bind; apply wp_modifyCore
        apply wp_pure
        dsimp only
        apply wp_ite
        · intro _
          apply wp_bind; apply wp_modifyCore
          apply wp_modifyBound
          apply wp_pure
          refine ⟨.token ⟨.quotedSymbol, location, bytesOf input (index + 1)
              (Lexer.Slice.runEnd input (index + 1) (Lexer.fastFlags c &&& Lexer.FAST_RUN_MASK))⟩,
            afterColumns location (Lexer.Slice.runEnd input (index + 1)
              (Lexer.fastFlags c &&& Lexer.FAST_RUN_MASK) - index), held,
            ⟨hfix.1, hfix.2, hfix.3, hfix.4⟩, Nat.le_refl _, ?_, ?_, hheld, hbytes, ?_⟩
          · dsimp only [StAgrees, TokenAgrees]
            refine ⟨⟨?_, rfl, ?_⟩, ?_⟩
            · rw [locAt_eq hloc, hline, hlineStart]; rfl
            · exact (contentBytes_clear_extendSlice _ _ (by bound_tac)).symm
            · fits_tac
          · obtain ⟨h1, h2, h3⟩ := hloc
            dsimp only [LocAt, afterColumns, Past.from]
            refine ⟨?_, ?_, ?_⟩ <;> omega
          · rw [hA]; rfl
        · intro h'; exact absurd hpipeb h'
      · -- the run is closed by a pipe
        intro h
        have hget' : get? input
            (Lexer.Slice.runEnd input (index + 1) (Lexer.fastFlags c &&& Lexer.FAST_RUN_MASK)) =
            some 124 := by
          simp only [hpipeb, ↓reduceIte, Bool.or_true, Bool.true_and, bne_iff_ne, ne_eq,
            Decidable.not_not] at h
          exact h
        obtain ⟨hJ, hJc⟩ := get?_eq hget'
        have hB : feedFrom v input .idle location index =
            feedFrom v input
              (.token ⟨.quotedSymbolClosed, location, bytesOf input (index + 1)
                (Lexer.Slice.runEnd input (index + 1) (Lexer.fastFlags c &&& Lexer.FAST_RUN_MASK))⟩)
              (afterColumns location (Lexer.Slice.runEnd input (index + 1)
                (Lexer.fastFlags c &&& Lexer.FAST_RUN_MASK) + 1 - index))
              (Lexer.Slice.runEnd input (index + 1)
                (Lexer.fastFlags c &&& Lexer.FAST_RUN_MASK) + 1) := by
          rw [hA, feedFrom_step hJ (byteStep_token_pending v (by rw [hJc]; rfl)), prep_nil,
            afterByte_eq_afterColumns' _ _ (by rw [hJc]; decide), afterColumns_add]
          congr 2
          omega
        apply wp_ite
        · intro _
          split
          · -- a byte after the closing pipe
            rename_i next heq
            simp only [hpipeb, ↓reduceIte] at heq
            obtain ⟨hJ1, hJ1c⟩ := get?_eq heq
            have hC := feedFrom_end v input hJ1 (q := ⟨.quotedSymbolClosed, location,
              bytesOf input (index + 1)
                (Lexer.Slice.runEnd input (index + 1) (Lexer.fastFlags c &&& Lexer.FAST_RUN_MASK))⟩)
              (location := afterColumns location (Lexer.Slice.runEnd input (index + 1)
                (Lexer.fastFlags c &&& Lexer.FAST_RUN_MASK) + 1 - index))
              (advance_end_quotedSymbolClosed rfl)
            rw [← hB, hJ1c] at hC
            apply wp_ite
            · -- it does not delimit the quoted symbol
              intro hnd
              have hnd' : VNaive.isDelimiter next = false := by
                rw [← isDelimiter_eq]; simpa using hnd
              rw [hnd'] at hC
              rw [rust_storeLocals]
              unfold FastState.store Lexer.WRustPort.leave Lexer.WRustPort.startToken
                Lexer.WRustPort.modifyContent Lexer.WRustPort.errorAt Lexer.WRustPort.errorWith
              wp_walk
              refine stepFails_here ?_ hheld hfix.1 hfix.2
              rw [hC]
              simp only [Bool.false_eq_true, ↓reduceIte]
            · intro hd
              have hd' : VNaive.isDelimiter next = true := by
                rw [← isDelimiter_eq]; simpa using hd
              rw [hd'] at hC
              simp only [↓reduceIte] at hC
              have hidx : (if (Lexer.fastFlags c &&& Lexer.FAST_PIPE != 0) = true then
                  Lexer.Slice.runEnd input (index + 1)
                    (Lexer.fastFlags c &&& Lexer.FAST_RUN_MASK) + 1
                else Lexer.Slice.runEnd input (index + 1)
                  (Lexer.fastFlags c &&& Lexer.FAST_RUN_MASK)) =
                  Lexer.Slice.runEnd input (index + 1)
                    (Lexer.fastFlags c &&& Lexer.FAST_RUN_MASK) + 1 := by
                simp only [hpipeb, ↓reduceIte]
              have hlex : (if (Lexer.fastFlags c &&& Lexer.FAST_EMIT != 0) = true then
                  [onLine (if (Lexer.fastFlags c &&& Lexer.FAST_PIPE != 0) = true then
                      TokenCategory.quotedSymbol
                    else if (false && Lexer.fastFlags c &&& Lexer.RUN_NON_LF_WHITESPACE != 0) = true
                      then TokenCategory.whitespace else TokenCategory.unquotedSymbol)
                    (input.slice (if (Lexer.fastFlags c &&& Lexer.FAST_PIPE != 0) = true then index
                        + 1
                      else index)
                      (if (Lexer.fastFlags c &&& Lexer.FAST_PIPE != 0) = true then
                        Lexer.Slice.runEnd input (index + 1) (Lexer.fastFlags c &&&
                            Lexer.FAST_RUN_MASK)
                      else if (Lexer.fastFlags c &&& Lexer.FAST_PIPE != 0) = true then
                        Lexer.Slice.runEnd input (index + 1)
                          (Lexer.fastFlags c &&& Lexer.FAST_RUN_MASK) + 1
                      else Lexer.Slice.runEnd input (index + 1)
                        (Lexer.fastFlags c &&& Lexer.FAST_RUN_MASK)))
                    locals.line locals.lineStart (offset + (index - base))
                    (offset + ((if (Lexer.fastFlags c &&& Lexer.FAST_PIPE != 0) = true then
                      Lexer.Slice.runEnd input (index + 1)
                        (Lexer.fastFlags c &&& Lexer.FAST_RUN_MASK) + 1
                      else Lexer.Slice.runEnd input (index + 1)
                        (Lexer.fastFlags c &&& Lexer.FAST_RUN_MASK)) - base))]
                  else []) =
                  [⟨.quotedSymbol, bytesOf input (index + 1) (Lexer.Slice.runEnd input (index + 1)
                      (Lexer.fastFlags c &&& Lexer.FAST_RUN_MASK)), location,
                    afterColumns location (Lexer.Slice.runEnd input (index + 1)
                      (Lexer.fastFlags c &&& Lexer.FAST_RUN_MASK) + 1 - index)⟩] := by
                simp only [hpipeb, hemit, ↓reduceIte]
                rw [hline, hlineStart, onLine_eq hloc hindex (by omega)]
                rfl
              apply wp_bind
              refine pushFast_wp v input batch locals offset base _ _ _ index _ _ _ hindex _ hframe
                hbatch held hheld hbytes.symm ?_ ?_ s coll hfix.recovers hfix.version ?_ ?_
              · simp only [hpipeb, ↓reduceIte]; omega
              · simp only [hpipeb, ↓reduceIte]; omega
              · intro r s' coll' held' hH hb hk hp
                rw [hlex] at hp
                obtain ⟨k1, k2, k3, k4, k5, k6, k7, k8, k9, k10, k11⟩ := key_fields hk
                refine wp_recurse (f := fun (r : Past input origin) => r.1)
                  (ih _ (by rw [hidx]; omega) r.val locals _ r.property origin _ s' coll' held'
                    (afterColumns location (Lexer.Slice.runEnd input (index + 1)
                      (Lexer.fastFlags c &&& Lexer.FAST_RUN_MASK) + 1 - index))
                    (fixed_of_key hfix hk) (hoff.trans k8.symm) (hbase.trans k9.symm)
                    (hline.trans k10.symm) (hlineStart.trans k11.symm) (k2.trans hnormal)
                    (by rw [hidx]; exact (hloc.afterColumns hindex (by omega)).congr k10 k11) hH
                    (hb.trans hbytes)) ?_
                rw [hidx, hC, outcome_prep, outcome_pending_congr hp]
              · intro hn e s' coll'
                rw [hlex] at hn
                apply stepFails_of_none
                show outcome v _ _ = none
                rw [hC, outcome_prep, hn, outcome_none_left]
          · -- the closing pipe is the last byte of the slice
            rename_i heq
            simp only [hpipeb, ↓reduceIte] at heq
            have hsz : Lexer.Slice.runEnd input (index + 1)
                (Lexer.fastFlags c &&& Lexer.FAST_RUN_MASK) + 1 = input.size := by
              have := Lexer.Slice.size_le_of_get?_none heq
              omega
            obtain ⟨hl1, hl2, hl3⟩ := id hloc
            rw [rust_storeLocals]
            unfold FastState.store Lexer.WRustPort.startToken Lexer.WRustPort.modifyContent
              Lexer.WRustPort.leavePending
            wp_walk
            refine ⟨.token ⟨.quotedSymbolClosed, location, bytesOf input (index + 1)
                (Lexer.Slice.runEnd input (index + 1) (Lexer.fastFlags c &&& Lexer.FAST_RUN_MASK))⟩,
              afterColumns location (Lexer.Slice.runEnd input (index + 1)
                (Lexer.fastFlags c &&& Lexer.FAST_RUN_MASK) + 1 - index), held,
              ⟨hfix.1, hfix.2, hfix.3, hfix.4⟩, Nat.le_refl _, ?_, ?_, hheld, hbytes, ?_⟩
            · dsimp only [StAgrees, TokenAgrees]
              refine ⟨⟨?_, rfl, ?_⟩, ?_⟩
              · rw [locAt_eq hloc, hline, hlineStart]; rfl
              · simp only [hpipeb, ↓reduceIte]
                exact (contentBytes_clear_extendSlice _ _ (by bound_tac)).symm
              · simp only [hpipeb, ↓reduceIte]
                fits_tac
            · dsimp only [LocAt, afterColumns, Past.from]
              simp only [hpipeb, ↓reduceIte]
              refine ⟨?_, ?_, ?_⟩ <;> omega
            · rw [hB]
              simp only [Past.from, hpipeb, ↓reduceIte]
        · intro h'; rw [hemit] at h'; exact absurd rfl h'
    · -- a simple symbol that does not start with a digit
      have hpipeb : (Lexer.fastFlags c &&& Lexer.FAST_PIPE != 0) = false := by rw [hf]; decide
      have hemit : (Lexer.fastFlags c &&& Lexer.FAST_EMIT != 0) = true := by rw [hf]; decide
      have hsymb : (Lexer.fastFlags c &&& Lexer.RUN_SIMPLE_SYMBOL != 0) = true := by
        rw [hf]; decide
      have hmask : Lexer.fastFlags c &&& Lexer.FAST_RUN_MASK = Lexer.RUN_SIMPLE_SYMBOL := by
        rw [hf]; decide
      have hj : Lexer.Slice.runEnd input (index + 1) (Lexer.fastFlags c &&& Lexer.FAST_RUN_MASK) =
          runEnd input isSymbolByte (index + 1) := by
        rw [hmask, runEnd_eq endsRun_symbol]
      have hle := le_runEnd input isSymbolByte (index + 1)
      have hle' := runEnd_le input isSymbolByte (index + 1) hi
      have hstop := fun h => runEnd_stop input isSymbolByte (index + 1) h
      have hA : feedFrom v input .idle location index =
          feedFrom v input
            (.token ⟨.simpleSymbol, location,
              bytesOf input index (runEnd input isSymbolByte (index + 1))⟩)
            (afterColumns location (runEnd input isSymbolByte (index + 1) - index))
            (runEnd input isSymbolByte (index + 1)) := by
        rw [feedFrom_startRun v input isSymbolByte isSymbolByte_ne .simpleSymbol
          (fun q l c hm hc => advance_simpleSymbol_run false q l c hm hc) hi
          (q := ⟨.simpleSymbol, location, ByteArray.empty.push input[index]⟩)
          (by rw [hc]; exact start_symbol _ _ _ _ hsym hdig) rfl
          (by rw [hc]; exact isSymbolByte_ne _ hsym)]
        simp only
        rw [push_append_bytesOf _ input hi (by omega) hle', empty_append]
      rw [← hj] at hA hle hle' hstop
      apply wp_dite
      · -- the symbol runs to the end of the slice: it is left in progress
        intro h
        have hsz : Lexer.Slice.runEnd input (index + 1)
            (Lexer.fastFlags c &&& Lexer.FAST_RUN_MASK) = input.size := by
          simp only [hpipeb, hsymb, Bool.or_false, Bool.false_eq_true, ↓reduceIte,
            Bool.and_true, beq_iff_eq] at h
          exact h
        obtain ⟨hl1, hl2, hl3⟩ := id hloc
        rw [rust_storeLocals]
        unfold FastState.store Lexer.WRustPort.storeUnfinishedSymbolRun Lexer.WRustPort.startToken
          Lexer.WRustPort.extendContent Lexer.WRustPort.modifyContent Lexer.WRustPort.leavePending
        apply wp_bind; apply wp_modifyCore
        apply wp_bind
        apply wp_bind
        apply wp_bind; apply wp_getCore
        apply wp_bind; apply wp_modifyCore
        apply wp_bind; apply wp_modifyCore
        apply wp_pure
        dsimp only
        apply wp_ite
        · intro h'; rw [hpipeb] at h'; exact absurd h' (by decide)
        · intro _
          apply wp_bind; apply wp_modifyCore
          apply wp_modifyBound
          apply wp_pure
          refine ⟨.token ⟨.simpleSymbol, location, bytesOf input index
              (Lexer.Slice.runEnd input (index + 1) (Lexer.fastFlags c &&& Lexer.FAST_RUN_MASK))⟩,
            afterColumns location (Lexer.Slice.runEnd input (index + 1)
              (Lexer.fastFlags c &&& Lexer.FAST_RUN_MASK) - index), held,
            ⟨hfix.1, hfix.2, hfix.3, hfix.4⟩, Nat.le_refl _, ?_, ?_, hheld, hbytes, ?_⟩
          · dsimp only [StAgrees, TokenAgrees]
            refine ⟨⟨?_, rfl, ?_⟩, ?_⟩
            · rw [locAt_eq hloc, hline, hlineStart]; rfl
            · exact (contentBytes_clear_extendSlice _ _ (by bound_tac)).symm
            · fits_tac
          · dsimp only [LocAt, afterColumns, Past.from]
            refine ⟨?_, ?_, ?_⟩ <;> omega
          · rw [hA]; rfl
      · -- the symbol ends inside the slice
        intro h
        have hJ : Lexer.Slice.runEnd input (index + 1)
            (Lexer.fastFlags c &&& Lexer.FAST_RUN_MASK) < input.size := by
          simp only [hpipeb, hsymb, Bool.or_false, Bool.false_eq_true, ↓reduceIte,
            Bool.and_true, beq_iff_eq] at h
          omega
        have hJs := hstop hJ
        have hidx : (if (Lexer.fastFlags c &&& Lexer.FAST_PIPE != 0) = true then
            Lexer.Slice.runEnd input (index + 1) (Lexer.fastFlags c &&& Lexer.FAST_RUN_MASK) + 1
          else Lexer.Slice.runEnd input (index + 1) (Lexer.fastFlags c &&& Lexer.FAST_RUN_MASK)) =
            Lexer.Slice.runEnd input (index + 1) (Lexer.fastFlags c &&& Lexer.FAST_RUN_MASK) := by
          simp only [hpipeb, Bool.false_eq_true, ↓reduceIte]
        have hC := feedFrom_end v input hJ (q := ⟨.simpleSymbol, location,
            bytesOf input index
              (Lexer.Slice.runEnd input (index + 1) (Lexer.fastFlags c &&& Lexer.FAST_RUN_MASK))⟩)
          (location := afterColumns location (Lexer.Slice.runEnd input (index + 1)
            (Lexer.fastFlags c &&& Lexer.FAST_RUN_MASK) - index))
          (advance_end_simpleSymbol rfl hJs)
        rw [← hA] at hC
        apply wp_ite
        · intro _
          split
          · rename_i next heq
            simp only [hpipeb, Bool.false_eq_true, ↓reduceIte] at heq
            obtain ⟨hJ1, hJ1c⟩ := get?_eq heq
            rw [hJ1c] at hC
            apply wp_ite
            · intro hnd
              have hnd' : VNaive.isDelimiter next = false := by
                rw [← isDelimiter_eq]; simpa using hnd
              rw [hnd'] at hC
              rw [rust_storeLocals]
              unfold FastState.store Lexer.WRustPort.leave Lexer.WRustPort.startToken
                Lexer.WRustPort.modifyContent Lexer.WRustPort.errorAt Lexer.WRustPort.errorWith
              wp_walk
              refine stepFails_here ?_ hheld hfix.1 hfix.2
              rw [hC]
              simp only [Bool.false_eq_true, ↓reduceIte]
            · intro hd
              have hd' : VNaive.isDelimiter next = true := by
                rw [← isDelimiter_eq]; simpa using hd
              rw [hd'] at hC
              simp only [↓reduceIte] at hC
              have hlex : (if (Lexer.fastFlags c &&& Lexer.FAST_EMIT != 0) = true then
                  [onLine (if (Lexer.fastFlags c &&& Lexer.FAST_PIPE != 0) = true then
                      TokenCategory.quotedSymbol
                    else if (false && Lexer.fastFlags c &&& Lexer.RUN_NON_LF_WHITESPACE != 0) = true
                      then TokenCategory.whitespace else TokenCategory.unquotedSymbol)
                    (input.slice (if (Lexer.fastFlags c &&& Lexer.FAST_PIPE != 0) = true then index
                        + 1
                      else index)
                      (if (Lexer.fastFlags c &&& Lexer.FAST_PIPE != 0) = true then
                        Lexer.Slice.runEnd input (index + 1) (Lexer.fastFlags c &&&
                            Lexer.FAST_RUN_MASK)
                      else if (Lexer.fastFlags c &&& Lexer.FAST_PIPE != 0) = true then
                        Lexer.Slice.runEnd input (index + 1)
                          (Lexer.fastFlags c &&& Lexer.FAST_RUN_MASK) + 1
                      else Lexer.Slice.runEnd input (index + 1)
                        (Lexer.fastFlags c &&& Lexer.FAST_RUN_MASK)))
                    locals.line locals.lineStart (offset + (index - base))
                    (offset + ((if (Lexer.fastFlags c &&& Lexer.FAST_PIPE != 0) = true then
                      Lexer.Slice.runEnd input (index + 1)
                        (Lexer.fastFlags c &&& Lexer.FAST_RUN_MASK) + 1
                      else Lexer.Slice.runEnd input (index + 1)
                        (Lexer.fastFlags c &&& Lexer.FAST_RUN_MASK)) - base))]
                  else []) =
                  [⟨.unquotedSymbol, bytesOf input index (Lexer.Slice.runEnd input (index + 1)
                      (Lexer.fastFlags c &&& Lexer.FAST_RUN_MASK)), location,
                    afterColumns location (Lexer.Slice.runEnd input (index + 1)
                      (Lexer.fastFlags c &&& Lexer.FAST_RUN_MASK) - index)⟩] := by
                simp only [hpipeb, hemit, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
                rw [hline, hlineStart, onLine_eq hloc hindex (by omega)]
                rfl
              apply wp_bind
              refine pushFast_wp v input batch locals offset base _ _ _ index _ _ _ hindex _ hframe
                hbatch held hheld hbytes.symm ?_ ?_ s coll hfix.recovers hfix.version ?_ ?_
              · simp only [hpipeb, Bool.false_eq_true, ↓reduceIte]; omega
              · simp only [hpipeb, Bool.false_eq_true, ↓reduceIte]; omega
              · intro r s' coll' held' hH hb hk hp
                rw [hlex] at hp
                obtain ⟨k1, k2, k3, k4, k5, k6, k7, k8, k9, k10, k11⟩ := key_fields hk
                refine wp_recurse (f := fun (r : Past input origin) => r.1)
                  (ih _ (by rw [hidx]; omega) r.val locals _ r.property origin _ s' coll' held'
                    (afterColumns location (Lexer.Slice.runEnd input (index + 1)
                      (Lexer.fastFlags c &&& Lexer.FAST_RUN_MASK) - index))
                    (fixed_of_key hfix hk) (hoff.trans k8.symm) (hbase.trans k9.symm)
                    (hline.trans k10.symm) (hlineStart.trans k11.symm) (k2.trans hnormal)
                    (by rw [hidx]; exact (hloc.afterColumns hindex (by omega)).congr k10 k11) hH
                    (hb.trans hbytes)) ?_
                rw [hidx, hC, outcome_prep, outcome_pending_congr hp]
              · intro hn e s' coll'
                rw [hlex] at hn
                apply stepFails_of_none
                show outcome v _ _ = none
                rw [hC, outcome_prep, hn, outcome_none_left]
          · rename_i heq
            simp only [hpipeb, Bool.false_eq_true, ↓reduceIte] at heq
            have := Lexer.Slice.size_le_of_get?_none heq
            omega
        · intro h'; rw [hemit] at h'; exact absurd rfl h'
  -- the slow path
  intro hslow
  have hfoff : (Lexer.fastFlags c &&& Lexer.FAST_ON != 0) = false := by simpa using hslow
  obtain ⟨hl1, hl2, hl3⟩ := id hloc
  refine wp_store hline hlineStart ?_
  split
  · -- a line feed, passed over
    rename_i hst
    have h10 := Lexer.eq_of_startOf_eq_lineFeed hst
    rw [rust_loadLocals]
    unfold Lexer.WRustPort.markLineFeedAt FastState.load
    apply wp_bind; apply wp_modifyCore
    apply wp_bind; apply wp_bind; apply wp_getCore; apply wp_pure
    have hpure : feedFrom v input .idle location index =
        feedFrom v input .idle (location.afterByte 10) (index + 1) := by
      rw [feedFrom_step hi (byteStep_idle_idle v (by rw [hc, h10]; rfl)), prep_nil, hc, h10]
    refine wp_recurse (f := fun (r : Past input origin) => r.1)
      (ih (index + 1) (by omega) batch _ _ _ origin _ _ coll held (location.afterByte 10)
        ⟨hfix.1, hfix.2, hfix.3, hfix.4⟩ hoff hbase rfl rfl hnormal
        (hloc.lineFeed hindex rfl (by
          show Lexer.WRustPort.LexerCore.offsetAt _ index + 1 = _
          simp only [Lexer.WRustPort.LexerCore.offsetAt]
          rw [← hoff, ← hbase])) hheld hbytes) ?_
    rw [hpure]
  · -- a comment
    rename_i hst
    have h59 := startOf_comment hst
    unfold Lexer.WRustPort.startToken Lexer.WRustPort.modifyContent
    apply wp_bind
    apply wp_bind; apply wp_getCore
    apply wp_bind; apply wp_modifyCore
    apply wp_bind; apply wp_modifyCore
    apply wp_pure
    have hE : Lexer.Slice.runEnd input (index + 1) Lexer.RUN_COMMENT_PLAIN =
        runEnd input isCommentRun (index + 1) := runEnd_eq endsRun_comment _ _
    have hle := le_runEnd input isCommentRun (index + 1)
    have hle' := runEnd_le input isCommentRun (index + 1) hi
    have hstop := fun h => runEnd_stop input isCommentRun (index + 1) h
    have hA : feedFrom v input .idle location index =
        feedFrom v input
          (.token ⟨.comment, location,
            bytesOf input (index + 1) (runEnd input isCommentRun (index + 1))⟩)
          (afterColumns location (runEnd input isCommentRun (index + 1) - index))
          (runEnd input isCommentRun (index + 1)) := by
      rw [feedFrom_startRun v input isCommentRun isCommentRun_ne .comment
        (fun q l c hm hc => advance_comment_run false q l c hm hc) hi
        (q := ⟨.comment, location, .empty⟩) (by rw [hc, h59]; rfl) rfl (by rw [hc, h59]; decide)]
      simp only [empty_append]
    rw [← hE] at hA hle hle' hstop
    split
    · -- the comment ends inside the slice, with its line break
      rename_i c' hgetE
      obtain ⟨hEs, hEc⟩ := get?_eq hgetE
      have hEs' := hstop hEs
      rw [hEc] at hEs'
      have hB : feedFrom v input .idle location index =
          feedFrom v input .idle
            ((afterColumns location (Lexer.Slice.runEnd input (index + 1)
              Lexer.RUN_COMMENT_PLAIN - index)).afterByte c')
            (Lexer.Slice.runEnd input (index + 1) Lexer.RUN_COMMENT_PLAIN + 1) := by
        have hadv := advance_comment_end location (bytesOf input (index + 1)
          (Lexer.Slice.runEnd input (index + 1) Lexer.RUN_COMMENT_PLAIN))
          (afterColumns location (Lexer.Slice.runEnd input (index + 1)
            Lexer.RUN_COMMENT_PLAIN - index)) hEs'
        rw [← hEc] at hadv
        rw [hA, feedFrom_step hEs (byteStep_token_idle v hadv), prep_nil, hEc]
      apply wp_ite
      · -- a line feed, which is marked
        intro h10
        have h10' : c' = 10 := by simpa using h10
        subst h10'
        rw [rust_loadLocals]
        unfold Lexer.WRustPort.markLineFeedAt FastState.load
        apply wp_bind; apply wp_modifyCore
        apply wp_bind; apply wp_pure
        apply wp_bind; apply wp_bind; apply wp_getCore; apply wp_pure
        refine wp_recurse (f := fun (r : Past input origin) => r.1)
          (ih _ (by omega) batch _ _ _ origin _ _ coll held
            ((afterColumns location (Lexer.Slice.runEnd input (index + 1)
              Lexer.RUN_COMMENT_PLAIN - index)).afterByte 10)
            ⟨hfix.1, hfix.2, hfix.3, hfix.4⟩ hoff hbase rfl rfl rfl
            (LocAt.lineFeed (hloc.afterColumns hindex (by omega)) (by omega) rfl (by
              show Lexer.WRustPort.LexerCore.offsetAt _ _ + 1 = _
              simp only [Lexer.WRustPort.LexerCore.offsetAt]
              rw [← hoff, ← hbase])) hheld hbytes) ?_
        rw [hB]
      · -- a carriage return
        intro h10
        have h10' : c' ≠ 10 := by simpa using h10
        rw [rust_loadLocals]
        unfold FastState.load
        apply wp_bind; apply wp_pure
        apply wp_bind; apply wp_bind; apply wp_getCore; apply wp_pure
        refine wp_recurse (f := fun (r : Past input origin) => r.1)
          (ih _ (by omega) batch _ _ _ origin _ _ coll held
            (afterColumns location (Lexer.Slice.runEnd input (index + 1)
              Lexer.RUN_COMMENT_PLAIN + 1 - index))
            ⟨hfix.1, hfix.2, hfix.3, hfix.4⟩ hoff hbase rfl rfl rfl
            (hloc.afterColumns hindex (by omega)) hheld hbytes) ?_
        rw [hB, afterByte_eq_afterColumns' _ _ h10', afterColumns_add]
        congr 3
        omega
    · -- the comment runs to the end of the slice: it is left in progress
      rename_i hgetE
      have hsz := Lexer.Slice.size_le_of_get?_none hgetE
      unfold Lexer.WRustPort.leavePending
      apply wp_bind; apply wp_modifyBound
      apply wp_pure
      refine ⟨.token ⟨.comment, location, bytesOf input (index + 1)
          (Lexer.Slice.runEnd input (index + 1) Lexer.RUN_COMMENT_PLAIN)⟩,
        afterColumns location (Lexer.Slice.runEnd input (index + 1)
          Lexer.RUN_COMMENT_PLAIN - index), held,
        ⟨hfix.1, hfix.2, hfix.3, hfix.4⟩, Nat.le_refl _, ?_, ?_, hheld, hbytes, ?_⟩
      · dsimp only [StAgrees, TokenAgrees]
        refine ⟨⟨?_, rfl⟩, ?_⟩
        rw [locAt_eq hloc]; rfl
        · fits_tac
      · dsimp only [LocAt, afterColumns, Past.from]
        refine ⟨?_, ?_, ?_⟩ <;> omega
      · rw [hA]; rfl
  · -- a hash: a hexadecimal or binary literal
    rename_i hst
    have h35 := startOf_hash hst
    unfold Lexer.WRustPort.startToken Lexer.WRustPort.modifyContent
    apply wp_bind
    apply wp_bind; apply wp_getCore
    apply wp_bind; apply wp_modifyCore
    apply wp_bind; apply wp_modifyCore
    apply wp_pure
    have hhash : feedFrom v input .idle location index =
        feedFrom v input (.token ⟨.hash, location, .empty⟩) (location.afterByte 35)
          (index + 1) := by
      rw [feedFrom_step hi (byteStep_idle_pending v (by rw [hc, h35]; rfl)), prep_nil, hc, h35]
    split
    · -- the base is selected
      rename_i run hrun heqm
      obtain ⟨b, hb, hsel⟩ := Option.bind_eq_some_iff.mp hrun
      obtain ⟨hi1, hb'⟩ := get?_eq hb
      obtain ⟨radix, hadv, h10', hflag, hstate, htyp⟩ : ∃ radix : Radix,
          advance false ⟨.hash, location, .empty⟩ (location.afterByte 35) input[index + 1] =
            .pending ⟨.digits radix, location, .empty⟩ ∧ input[index + 1] ≠ 10 ∧
          (∀ c, Lexer.endsRun c run.flag = !radix.allows c) ∧
          (∀ (p : Pending) start content, p.mode = .digits radix → p.start = start →
            p.content = content → TokenAgrees v run.state start content p) ∧
          run.tokenType = radix.category := by
        rw [hb']
        by_cases hx : (b == 120) = true
        · simp only [hx, ↓reduceIte, Option.some.injEq] at hsel
          subst hsel
          have hx' : b = 120 := by simpa using hx
          subst hx'
          exact ⟨.hexadecimal, rfl, by decide, endsRun_hex,
            fun _ _ _ hm hs hc => ⟨hs, hm, hc⟩, rfl⟩
        · simp only [hx, Bool.false_eq_true, ↓reduceIte] at hsel
          by_cases hy : (b == 98) = true
          · simp only [hy, ↓reduceIte, Option.some.injEq] at hsel
            subst hsel
            have hy' : b = 98 := by simpa using hy
            subst hy'
            exact ⟨.binary, rfl, by decide, endsRun_binary,
              fun _ _ _ hm hs hc => ⟨hs, hm, hc⟩, rfl⟩
          · simp only [hy, Bool.false_eq_true, ↓reduceIte] at hsel
            cases hsel
      have hJ : Lexer.Slice.runEnd input (index + 1 + 1) run.flag =
          runEnd input radix.allows (index + 1 + 1) := runEnd_eq hflag _ _
      have hle := le_runEnd input radix.allows (index + 1 + 1)
      have hle' := runEnd_le input radix.allows (index + 1 + 1) hi1
      have hstop := fun h => runEnd_stop input radix.allows (index + 1 + 1) h
      have hB : feedFrom v input .idle location index =
          feedFrom v input
            (.token ⟨.digits radix, location,
              bytesOf input (index + 1 + 1) (runEnd input radix.allows (index + 1 + 1))⟩)
            (afterColumns location
              (runEnd input radix.allows (index + 1 + 1) - index))
            (runEnd input radix.allows (index + 1 + 1)) := by
        rw [hhash, feedFrom_step hi1 (byteStep_token_pending v hadv), prep_nil,
          feedFrom_mode v input radix.allows (allows_ne radix) (.digits radix)
            (fun q l c hm hc => advance_digits_run radix false q l c hm hc) (index + 1 + 1) _ _ rfl
            hi1, afterByte_eq_afterColumns' _ _ h10', afterByte_eq_afterColumns' _ _ (by decide),
          afterColumns_add, afterColumns_add]
        simp only [empty_append]
        congr 2
        omega
      rw [← hJ] at hB hle hle' hstop
      apply wp_ite
      · -- the digits run to the end of the slice: the literal is left in progress
        intro hsz
        have hsz' : Lexer.Slice.runEnd input (index + 1 + 1) run.flag = input.size := by
          simpa using hsz
        unfold Lexer.WRustPort.extendContent Lexer.WRustPort.modifyContent
          Lexer.WRustPort.leavePending
        apply wp_bind; apply wp_modifyCore
        apply wp_bind; apply wp_modifyBound
        apply wp_pure
        refine ⟨.token ⟨.digits radix, location, bytesOf input (index + 1 + 1)
            (Lexer.Slice.runEnd input (index + 1 + 1) run.flag)⟩,
          afterColumns location (Lexer.Slice.runEnd input (index + 1 + 1) run.flag - index),
          held, ⟨hfix.1, hfix.2, hfix.3, hfix.4⟩, Nat.le_refl _, ?_, ?_, hheld, hbytes, ?_⟩
        · refine ⟨hstate _ _ _ rfl (locAt_eq hloc) ?_, ?_⟩
          · exact (contentBytes_clear_extendSlice _ _ (by bound_tac)).symm
          · fits_tac
        · dsimp only [LocAt, afterColumns, Past.from]
          refine ⟨?_, ?_, ?_⟩ <;> omega
        · rw [hB]; rfl
      · intro hsz
        have hJs : Lexer.Slice.runEnd input (index + 1 + 1) run.flag < input.size := by
          simp only [beq_iff_eq] at hsz
          omega
        have hstop' := hstop hJs
        apply wp_bind; apply wp_getCore
        have hsize : ∀ buf, (Lexer.Slice.borrow input (index + 1 + 1)
            (Lexer.Slice.runEnd input (index + 1 + 1) run.flag)).size buf =
              Lexer.Slice.runEnd input (index + 1 + 1) run.flag - (index + 1 + 1) := fun _ => by
          simp only [Lexer.Slice.borrow, BSmtLib.Lexer.Content.size]; omega
        apply wp_ite
        · -- no digit: the literal fails
          intro hempty
          have he : Lexer.Slice.runEnd input (index + 1 + 1) run.flag = index + 1 + 1 := by
            have : (Lexer.Slice.runEnd input (index + 1 + 1) run.flag) - (index + 1 + 1) = 0 := by
              simpa [hsize] using hempty
            omega
          obtain ⟨f, hf⟩ := advance_end_digits_empty (location := afterColumns location
            (Lexer.Slice.runEnd input (index + 1 + 1) run.flag - index))
            (q := ⟨.digits radix, location, bytesOf input (index + 1 + 1)
              (Lexer.Slice.runEnd input (index + 1 + 1) run.flag)⟩) rfl hstop'
            (by rw [he, bytesOf_self input _ hi1]; rfl)
          unfold Lexer.WRustPort.leave Lexer.WRustPort.error Lexer.WRustPort.errorWith
          wp_walk
          refine stepFails_here ?_ hheld hfix.1 hfix.2
          rw [hB, feedFrom_advance_error v input hJs hf]
        · intro hne
          have hne' : (bytesOf input (index + 1 + 1)
              (Lexer.Slice.runEnd input (index + 1 + 1) run.flag)).isEmpty = false := by
            have : (Lexer.Slice.runEnd input (index + 1 + 1) run.flag) - (index + 1 + 1) ≠ 0 := by
              simpa [hsize] using hne
            have hpos : (bytesOf input (index + 1 + 1)
                (Lexer.Slice.runEnd input (index + 1 + 1) run.flag)).size ≠ 0 := by
              show (input.slice _ _).toByteArray.size ≠ 0
              rw [size_toByteArray, slice_size input hle (Nat.le_of_lt hJs)]
              exact this
            simp [ByteArray.isEmpty, hpos]
          have hC := feedFrom_end v input hJs (q := ⟨.digits radix, location,
              bytesOf input (index + 1 + 1) (Lexer.Slice.runEnd input (index + 1 + 1) run.flag)⟩)
            (location := afterColumns location
              (Lexer.Slice.runEnd input (index + 1 + 1) run.flag - index))
            (advance_end_digits rfl hstop' hne')
          rw [← hB] at hC
          rw [get_eq hJs]
          apply wp_ite
          · intro hnd
            have hnd' : VNaive.isDelimiter
                input[Lexer.Slice.runEnd input (index + 1 + 1) run.flag] = false := by
              rw [← isDelimiter_eq]; simpa using hnd
            rw [hnd'] at hC
            unfold Lexer.WRustPort.leave Lexer.WRustPort.errorAt Lexer.WRustPort.errorWith
            wp_walk
            refine stepFails_here ?_ hheld hfix.1 hfix.2
            rw [hC]
            simp only [Bool.false_eq_true, ↓reduceIte]
          · intro hd
            have hd' : VNaive.isDelimiter
                input[Lexer.Slice.runEnd input (index + 1 + 1) run.flag] = true := by
              rw [← isDelimiter_eq]; simpa using hd
            rw [hd'] at hC
            simp only [↓reduceIte] at hC
            have hlex := borrowedLexeme_eq hloc hindex
              (j := Lexer.Slice.runEnd input (index + 1 + 1) run.flag) (by omega) run.tokenType
              (input.slice (index + 1 + 1) (Lexer.Slice.runEnd input (index + 1 + 1) run.flag))
            apply wp_bind
            refine pushBorrowed_wp v input batch offset base _ _ _ _ _ _ _ _ _ held hheld
                hbytes.symm ?_ ?_
              _ coll ?_ ?_ ?_ ?_
            · omega
            · omega
            · exact hfix.recovers
            · exact hfix.version
            · intro r s' coll' held' hH hb hk hp
              have hp' : pending v coll' held' = pending v coll (held ++
                  [⟨radix.category, bytesOf input (index + 1 + 1)
                    (Lexer.Slice.runEnd input (index + 1 + 1) run.flag), location,
                    afterColumns location (Lexer.Slice.runEnd input (index + 1 + 1)
                      run.flag - index)⟩]) := by
                have := hp.trans (congrArg (fun l => pending v coll (held ++ [l])) hlex)
                rw [htyp] at this; exact this
              obtain ⟨k1, k2, k3, k4, k5, k6, k7, k8, k9, k10, k11⟩ := key_fields hk
              rw [rust_loadLocals]
              unfold FastState.load
              apply wp_bind; apply wp_bind; apply wp_getCore; apply wp_pure
              refine wp_recurse (f := fun (r : Past input origin) => r.1)
                (ih _ (by omega) r.val _ _ r.property origin _ s' coll' held'
                  (afterColumns location (Lexer.Slice.runEnd input (index + 1 + 1)
                    run.flag - index))
                  (fixed_of_key' hk ⟨hfix.1, hfix.2, hfix.3, hfix.4⟩) (hoff.trans k8.symm)
                  (hbase.trans k9.symm) rfl rfl k2
                  ((hloc.afterColumns hindex (by omega)).congr k10 k11) hH
                  (hb.trans hbytes)) ?_
              rw [hC, outcome_prep, outcome_pending_congr hp']
            · intro hn e s' coll'
              have hn' : pending v coll (held ++
                  [⟨radix.category, bytesOf input (index + 1 + 1)
                    (Lexer.Slice.runEnd input (index + 1 + 1) run.flag), location,
                    afterColumns location (Lexer.Slice.runEnd input (index + 1 + 1)
                      run.flag - index)⟩]) = none := by
                have := (congrArg (fun l => pending v coll (held ++ [l])) hlex).symm.trans hn
                rw [htyp] at this; exact this
              apply stepFails_of_none
              show outcome v _ _ = none
              rw [hC, outcome_prep, hn', outcome_none_left]
    · -- no base is selected: the hash is left in progress
      unfold Lexer.WRustPort.leavePending
      apply wp_bind; apply wp_modifyBound
      apply wp_pure
      refine ⟨.token ⟨.hash, location, .empty⟩, location.afterByte 35, held,
        ⟨hfix.1, hfix.2, hfix.3, hfix.4⟩, Nat.le_refl _, ?_, ?_, hheld, hbytes, ?_⟩
      · dsimp only [StAgrees, TokenAgrees]
        refine ⟨⟨?_, rfl, (contentBytes_clear _).symm⟩, ?_⟩
        rw [locAt_eq hloc]; rfl
        · fits_tac
      · have := hloc.afterByte hindex (b := 35) (by decide)
        obtain ⟨h1, h2, h3⟩ := this
        dsimp only [LocAt, Past.from]
        refine ⟨?_, h2, h3⟩
        omega
      · rw [hhash]; rfl
  · -- a quote: a string literal
    rename_i hst
    have h34 := startOf_quote hst
    unfold Lexer.WRustPort.startToken Lexer.WRustPort.modifyContent
    apply wp_bind
    apply wp_bind; apply wp_getCore
    apply wp_bind; apply wp_modifyCore
    apply wp_bind; apply wp_modifyCore
    apply wp_pure
    apply wp_bind; apply wp_getCore
    have hq : feedFrom v input .idle location index =
        feedFrom v input
          (.token ⟨if v == .v2_0 then .legacyString else .string, location, .empty⟩)
          (location.afterByte 34) (index + 1) := by
      rw [feedFrom_step hi (byteStep_idle_pending v (by rw [hc, h34]; rfl)), prep_nil, hc, h34]
    apply wp_ite
    · -- under version 2.0 the string is left in progress at once
      intro hv2
      unfold Lexer.WRustPort.leavePending
      apply wp_bind; apply wp_modifyBound
      apply wp_pure
      refine ⟨.token ⟨if v == .v2_0 then .legacyString else .string, location, .empty⟩,
        location.afterByte 34, held, ⟨hfix.1, hfix.2, hfix.3, hfix.4⟩, Nat.le_refl _, ?_, ?_,
        hheld, hbytes, ?_⟩
      · dsimp only [StAgrees, TokenAgrees]
        refine ⟨⟨?_, rfl, (contentBytes_clear _).symm⟩, ?_⟩
        rw [locAt_eq hloc]; rfl
        · fits_tac
      · have := hloc.afterByte hindex (b := 34) (by decide)
        obtain ⟨h1, h2, h3⟩ := this
        dsimp only [LocAt, Past.from]
        refine ⟨?_, h2, h3⟩
        omega
      · rw [hq]; rfl
    · intro hv2
      have hv2' : (v == .v2_0) = false := by
        have : (s.val.version == .v2_0) = false := by simpa using hv2
        rw [← hfix.version]; exact this
      have hS : Lexer.Slice.runEnd input (index + 1) Lexer.RUN_STRING_PLAIN =
          runEnd input isStringRun (index + 1) := runEnd_eq endsRun_string _ _
      have hle := le_runEnd input isStringRun (index + 1)
      have hle' := runEnd_le input isStringRun (index + 1) hi
      have hstop := fun h => runEnd_stop input isStringRun (index + 1) h
      have hA : feedFrom v input .idle location index =
          feedFrom v input
            (.token ⟨.string, location,
              bytesOf input (index + 1) (runEnd input isStringRun (index + 1))⟩)
            (afterColumns location (runEnd input isStringRun (index + 1) - index))
            (runEnd input isStringRun (index + 1)) := by
        rw [feedFrom_startRun v input isStringRun isStringRun_ne .string
          (fun q l c hm hc => advance_string_run false q l c hm hc) hi
          (q := ⟨.string, location, .empty⟩)
          (by
            rw [hc, h34]
            show start v false location 34 = _
            simp [start, hv2', show isWhitespace 34 = false from rfl]) rfl
          (by rw [hc, h34]; decide)]
        simp only [empty_append]
      rw [← hS] at hA hle hle' hstop
      split
      · rename_i quote next hwq hwn
        apply wp_ite
        · -- closed by a quote that no quote follows
          intro hclose
          simp only [Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq] at hclose
          obtain ⟨hq34, hn34⟩ := hclose
          obtain ⟨hA1, hAc⟩ := get?_eq hwq
          obtain ⟨hA2, hA2c⟩ := get?_eq hwn
          have hB : feedFrom v input .idle location index =
              feedFrom v input
                (.token ⟨.stringQuote, location, bytesOf input (index + 1)
                  (Lexer.Slice.runEnd input (index + 1) Lexer.RUN_STRING_PLAIN)⟩)
                (afterColumns location (Lexer.Slice.runEnd input (index + 1)
                  Lexer.RUN_STRING_PLAIN + 1 - index))
                (Lexer.Slice.runEnd input (index + 1) Lexer.RUN_STRING_PLAIN + 1) := by
            rw [hA, feedFrom_step hA1 (byteStep_token_pending v (by rw [hAc, hq34]; rfl)),
              prep_nil, afterByte_eq_afterColumns' _ _ (by rw [hAc, hq34]; decide),
              afterColumns_add]
            congr 2
            omega
          have hC := feedFrom_end v input hA2 (q := ⟨.stringQuote, location,
              bytesOf input (index + 1)
                (Lexer.Slice.runEnd input (index + 1) Lexer.RUN_STRING_PLAIN)⟩)
            (location := afterColumns location (Lexer.Slice.runEnd input (index + 1)
              Lexer.RUN_STRING_PLAIN + 1 - index))
            (advance_end_stringQuote rfl (by rw [hA2c]; exact hn34))
          rw [← hB, hA2c] at hC
          apply wp_ite
          · intro hnd
            have hnd' : VNaive.isDelimiter next = false := by
              rw [← isDelimiter_eq]; simpa using hnd
            rw [hnd'] at hC
            unfold Lexer.WRustPort.leave Lexer.WRustPort.errorAt Lexer.WRustPort.errorWith
            wp_walk
            refine stepFails_here ?_ hheld hfix.1 hfix.2
            rw [hC]
            simp only [Bool.false_eq_true, ↓reduceIte]
          · intro hd
            have hd' : VNaive.isDelimiter next = true := by
              rw [← isDelimiter_eq]; simpa using hd
            rw [hd'] at hC
            simp only [↓reduceIte] at hC
            have hlex := borrowedLexeme_eq hloc hindex
              (j := Lexer.Slice.runEnd input (index + 1) Lexer.RUN_STRING_PLAIN + 1) (by omega)
              .string (input.slice (index + 1)
                (Lexer.Slice.runEnd input (index + 1) Lexer.RUN_STRING_PLAIN))
            apply wp_bind
            refine pushBorrowed_wp v input batch offset base _ _ _ _ _ _ _ _ _ held hheld
                hbytes.symm ?_ ?_
              _ coll ?_ ?_ ?_ ?_
            · omega
            · omega
            · exact hfix.recovers
            · exact hfix.version
            · intro r s' coll' held' hH hb hk hp
              have hp' : pending v coll' held' = pending v coll (held ++
                  [⟨.string, bytesOf input (index + 1)
                    (Lexer.Slice.runEnd input (index + 1) Lexer.RUN_STRING_PLAIN), location,
                    afterColumns location (Lexer.Slice.runEnd input (index + 1)
                      Lexer.RUN_STRING_PLAIN + 1 - index)⟩]) :=
                hp.trans (congrArg (fun l => pending v coll (held ++ [l])) hlex)
              obtain ⟨k1, k2, k3, k4, k5, k6, k7, k8, k9, k10, k11⟩ := key_fields hk
              rw [rust_loadLocals]
              unfold FastState.load
              apply wp_bind; apply wp_bind; apply wp_getCore; apply wp_pure
              refine wp_recurse (f := fun (r : Past input origin) => r.1)
                (ih _ (by omega) r.val _ _ r.property origin _ s' coll' held'
                  (afterColumns location (Lexer.Slice.runEnd input (index + 1)
                    Lexer.RUN_STRING_PLAIN + 1 - index))
                  (fixed_of_key' hk ⟨hfix.1, hfix.2, hfix.3, hfix.4⟩) (hoff.trans k8.symm)
                  (hbase.trans k9.symm) rfl rfl k2
                  ((hloc.afterColumns hindex (by omega)).congr k10 k11) hH
                  (hb.trans hbytes)) ?_
              rw [hC, outcome_prep, outcome_pending_congr hp']
            · intro hn e s' coll'
              have hn' : pending v coll (held ++
                  [⟨.string, bytesOf input (index + 1)
                    (Lexer.Slice.runEnd input (index + 1) Lexer.RUN_STRING_PLAIN), location,
                    afterColumns location (Lexer.Slice.runEnd input (index + 1)
                      Lexer.RUN_STRING_PLAIN + 1 - index)⟩]) = none :=
                (congrArg (fun l => pending v coll (held ++ [l])) hlex).symm.trans hn
              apply stepFails_of_none
              show outcome v _ _ = none
              rw [hC, outcome_prep, hn', outcome_none_left]
        · intro _
          string_stay
      · string_stay
  · -- a colon: a keyword
    rename_i hst
    have h58 := startOf_colon hst
    unfold Lexer.WRustPort.startToken Lexer.WRustPort.modifyContent
    apply wp_bind
    apply wp_bind; apply wp_getCore
    apply wp_bind; apply wp_modifyCore
    apply wp_bind; apply wp_modifyCore
    apply wp_pure
    have hK : Lexer.Slice.runEnd input (index + 1) Lexer.RUN_SIMPLE_SYMBOL =
        runEnd input isSymbolByte (index + 1) := runEnd_eq endsRun_symbol _ _
    have hle := le_runEnd input isSymbolByte (index + 1)
    have hle' := runEnd_le input isSymbolByte (index + 1) hi
    have hstop := fun h => runEnd_stop input isSymbolByte (index + 1) h
    have hA : feedFrom v input .idle location index =
        feedFrom v input
          (.token ⟨.keyword, location,
            bytesOf input (index + 1) (runEnd input isSymbolByte (index + 1))⟩)
          (afterColumns location (runEnd input isSymbolByte (index + 1) - index))
          (runEnd input isSymbolByte (index + 1)) := by
      rw [feedFrom_startRun v input isSymbolByte isSymbolByte_ne .keyword
        (fun q l c hm hc => advance_keyword_run false q l c hm hc) hi
        (q := ⟨.keyword, location, .empty⟩) (by rw [hc, h58]; rfl) rfl
        (by rw [hc, h58]; decide)]
      simp only [empty_append]
    rw [← hK] at hA hle hle' hstop
    apply wp_ite
    · -- the keyword runs to the end of the slice: it is left in progress
      intro hsz
      have hsz' : Lexer.Slice.runEnd input (index + 1) Lexer.RUN_SIMPLE_SYMBOL = input.size := by
        simpa using hsz
      unfold Lexer.WRustPort.extendContent Lexer.WRustPort.modifyContent
        Lexer.WRustPort.leavePending
      apply wp_bind; apply wp_modifyCore
      apply wp_bind; apply wp_modifyBound
      apply wp_pure
      refine ⟨.token ⟨.keyword, location, bytesOf input (index + 1)
          (Lexer.Slice.runEnd input (index + 1) Lexer.RUN_SIMPLE_SYMBOL)⟩,
        afterColumns location (Lexer.Slice.runEnd input (index + 1)
          Lexer.RUN_SIMPLE_SYMBOL - index),
        held, ⟨hfix.1, hfix.2, hfix.3, hfix.4⟩, Nat.le_refl _, ?_, ?_, hheld, hbytes, ?_⟩
      · dsimp only [StAgrees, TokenAgrees]
        refine ⟨⟨?_, rfl, ?_⟩, ?_⟩
        · rw [locAt_eq hloc]; rfl
        · exact (contentBytes_clear_extendSlice _ _ (by bound_tac)).symm
        · fits_tac
      · dsimp only [LocAt, afterColumns, Past.from]
        refine ⟨?_, ?_, ?_⟩ <;> omega
      · rw [hA]; rfl
    · intro hsz
      have hJs : Lexer.Slice.runEnd input (index + 1) Lexer.RUN_SIMPLE_SYMBOL < input.size := by
        simp only [beq_iff_eq] at hsz
        omega
      have hstop' := hstop hJs
      apply wp_bind; apply wp_getCore
      have hsize : ∀ buf, (Lexer.Slice.borrow input (index + 1)
          (Lexer.Slice.runEnd input (index + 1) Lexer.RUN_SIMPLE_SYMBOL)).size buf =
            Lexer.Slice.runEnd input (index + 1) Lexer.RUN_SIMPLE_SYMBOL - (index + 1) := fun _ =>
                by
        simp only [Lexer.Slice.borrow, BSmtLib.Lexer.Content.size]; omega
      apply wp_ite
      · -- an empty keyword
        intro hempty
        have he : Lexer.Slice.runEnd input (index + 1) Lexer.RUN_SIMPLE_SYMBOL = index + 1 := by
          have : (Lexer.Slice.runEnd input (index + 1) Lexer.RUN_SIMPLE_SYMBOL) - (index + 1) = 0 :=
              by
            simpa [hsize] using hempty
          omega
        obtain ⟨f, hf⟩ := advance_end_keyword_empty (location := afterColumns location
          (Lexer.Slice.runEnd input (index + 1) Lexer.RUN_SIMPLE_SYMBOL - index))
          (q := ⟨.keyword, location, bytesOf input (index + 1)
            (Lexer.Slice.runEnd input (index + 1) Lexer.RUN_SIMPLE_SYMBOL)⟩) rfl hstop'
          (by rw [he, bytesOf_self input _ hi]; rfl)
        unfold Lexer.WRustPort.leave Lexer.WRustPort.error Lexer.WRustPort.errorWith
        wp_walk
        refine stepFails_here ?_ hheld hfix.1 hfix.2
        rw [hA, feedFrom_advance_error v input hJs hf]
      · intro hne
        have hne' : (bytesOf input (index + 1)
            (Lexer.Slice.runEnd input (index + 1) Lexer.RUN_SIMPLE_SYMBOL)).isEmpty = false := by
          have : (Lexer.Slice.runEnd input (index + 1) Lexer.RUN_SIMPLE_SYMBOL) - (index + 1) ≠ 0 :=
              by
            simpa [hsize] using hne
          have hpos : (bytesOf input (index + 1)
              (Lexer.Slice.runEnd input (index + 1) Lexer.RUN_SIMPLE_SYMBOL)).size ≠ 0 := by
            show (input.slice _ _).toByteArray.size ≠ 0
            rw [size_toByteArray, slice_size input hle (Nat.le_of_lt hJs)]
            exact this
          simp [ByteArray.isEmpty, hpos]
        have hC := feedFrom_end v input hJs (q := ⟨.keyword, location,
            bytesOf input (index + 1)
              (Lexer.Slice.runEnd input (index + 1) Lexer.RUN_SIMPLE_SYMBOL)⟩)
          (location := afterColumns location
            (Lexer.Slice.runEnd input (index + 1) Lexer.RUN_SIMPLE_SYMBOL - index))
          (advance_end_keyword rfl hstop' hne')
        rw [← hA] at hC
        rw [get_eq hJs]
        apply wp_ite
        · intro hnd
          have hnd' : VNaive.isDelimiter
              input[Lexer.Slice.runEnd input (index + 1) Lexer.RUN_SIMPLE_SYMBOL] = false := by
            rw [← isDelimiter_eq]; simpa using hnd
          rw [hnd'] at hC
          unfold Lexer.WRustPort.leave Lexer.WRustPort.errorAt Lexer.WRustPort.errorWith
          wp_walk
          refine stepFails_here ?_ hheld hfix.1 hfix.2
          rw [hC]
          simp only [Bool.false_eq_true, ↓reduceIte]
        · intro hd
          have hd' : VNaive.isDelimiter
              input[Lexer.Slice.runEnd input (index + 1) Lexer.RUN_SIMPLE_SYMBOL] = true := by
            rw [← isDelimiter_eq]; simpa using hd
          rw [hd'] at hC
          simp only [↓reduceIte] at hC
          have hlex := borrowedLexeme_eq hloc hindex
            (j := Lexer.Slice.runEnd input (index + 1) Lexer.RUN_SIMPLE_SYMBOL) (by omega)
            .keyword (input.slice (index + 1)
              (Lexer.Slice.runEnd input (index + 1) Lexer.RUN_SIMPLE_SYMBOL))
          apply wp_bind
          refine pushBorrowed_wp v input batch offset base _ _ _ _ _ _ _ _ _ held hheld hbytes.symm
              ?_ ?_
            _ coll ?_ ?_ ?_ ?_
          · omega
          · omega
          · exact hfix.recovers
          · exact hfix.version
          · intro r s' coll' held' hH hb hk hp
            have hp' : pending v coll' held' = pending v coll (held ++
                [⟨.keyword, bytesOf input (index + 1)
                  (Lexer.Slice.runEnd input (index + 1) Lexer.RUN_SIMPLE_SYMBOL), location,
                  afterColumns location (Lexer.Slice.runEnd input (index + 1)
                    Lexer.RUN_SIMPLE_SYMBOL - index)⟩]) :=
              hp.trans (congrArg (fun l => pending v coll (held ++ [l])) hlex)
            obtain ⟨k1, k2, k3, k4, k5, k6, k7, k8, k9, k10, k11⟩ := key_fields hk
            rw [rust_loadLocals]
            unfold FastState.load
            apply wp_bind; apply wp_bind; apply wp_getCore; apply wp_pure
            refine wp_recurse (f := fun (r : Past input origin) => r.1)
              (ih _ (by omega) r.val _ _ r.property origin _ s' coll' held'
                (afterColumns location (Lexer.Slice.runEnd input (index + 1)
                  Lexer.RUN_SIMPLE_SYMBOL - index))
                (fixed_of_key' hk ⟨hfix.1, hfix.2, hfix.3, hfix.4⟩) (hoff.trans k8.symm)
                (hbase.trans k9.symm) rfl rfl k2
                ((hloc.afterColumns hindex (by omega)).congr k10 k11) hH
                (hb.trans hbytes)) ?_
            rw [hC, outcome_prep, outcome_pending_congr hp']
          · intro hn e s' coll'
            have hn' : pending v coll (held ++
                [⟨.keyword, bytesOf input (index + 1)
                  (Lexer.Slice.runEnd input (index + 1) Lexer.RUN_SIMPLE_SYMBOL), location,
                  afterColumns location (Lexer.Slice.runEnd input (index + 1)
                    Lexer.RUN_SIMPLE_SYMBOL - index)⟩]) = none :=
              (congrArg (fun l => pending v coll (held ++ [l])) hlex).symm.trans hn
            apply stepFails_of_none
            show outcome v _ _ = none
            rw [hC, outcome_prep, hn', outcome_none_left]
  · -- a digit: a numeral or a decimal
    rename_i hst
    have hd := startOf_digit hst
    have hstart : start v false location input[index] =
        .pending ⟨.numeral (c == 48), location, ByteArray.empty.push c⟩ := by
      rw [hc]; exact start_digit v location hd
    unfold Lexer.WRustPort.startToken Lexer.WRustPort.modifyContent
    apply wp_bind
    apply wp_bind; apply wp_getCore
    apply wp_bind; apply wp_modifyCore
    apply wp_bind; apply wp_modifyCore
    apply wp_pure
    have hE : Lexer.Slice.runEnd input (index + 1) Lexer.RUN_DIGIT =
        runEnd input isDigit (index + 1) := runEnd_eq endsRun_digit _ _
    have hle := le_runEnd input isDigit (index + 1)
    have hle' := runEnd_le input isDigit (index + 1) hi
    have hstop := fun h => runEnd_stop input isDigit (index + 1) h
    have hmem := runEnd_mem input isDigit (index + 1)
    rw [← hE] at hle hle' hstop hmem
    have h10 : c ≠ 10 := isDigit_ne c hd
    apply wp_ite
    · -- a numeral with a leading zero
      intro hz
      simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hz
      obtain ⟨hz0, hlt⟩ := hz
      have hi1 : index + 1 < input.size := by omega
      have hd1 := hmem (index + 1) hi1 (Nat.le_refl _) hlt
      have hadv : ∃ f, advance false ⟨.numeral true, location, ByteArray.empty.push c⟩
          (location.afterByte c) input[index + 1] = .error f := by
        simp [advance, hd1]
      obtain ⟨f, hf⟩ := hadv
      unfold Lexer.WRustPort.leave Lexer.WRustPort.errorAt Lexer.WRustPort.errorWith
      wp_walk
      refine stepFails_here ?_ hheld hfix.1 hfix.2
      rw [feedFrom_step hi (byteStep_idle_pending v hstart), hc, hz0]
      simp only [beq_self_eq_true]
      rw [hz0] at hf
      rw [feedFrom_advance_error v input hi1 hf]
      rfl
    intro hz
    have hz' : c = 48 → Lexer.Slice.runEnd input (index + 1) Lexer.RUN_DIGIT = index + 1 := by
      intro h0
      simp only [h0, beq_self_eq_true, Bool.true_and, decide_eq_true_eq] at hz
      omega
    have hA : feedFrom v input .idle location index =
        feedFrom v input
          (.token ⟨.numeral (c == 48), location, bytesOf input index
            (Lexer.Slice.runEnd input (index + 1) Lexer.RUN_DIGIT)⟩)
          (afterColumns location
            (Lexer.Slice.runEnd input (index + 1) Lexer.RUN_DIGIT - index))
          (Lexer.Slice.runEnd input (index + 1) Lexer.RUN_DIGIT) := by
      rw [feedFrom_step hi (byteStep_idle_pending v hstart), prep_nil]
      by_cases hz0 : c = 48
      · have he := hz' hz0
        rw [he, bytesOf_one input index hi, hc, afterByte_eq_afterColumns' _ _ h10]
        simp
      · have hfalse : (c == 48) = false := by simpa using hz0
        rw [hfalse, feedFrom_mode v input isDigit isDigit_ne (.numeral false)
          (fun q l c hm hc => advance_numeral_run false q l c hm hc) (index + 1) _ _ rfl hi, ← hE]
        simp only
        rw [← hc, push_append_bytesOf _ input hi (by omega) hle', empty_append,
          afterByte_eq_afterColumns' _ _ (by rw [hc]; exact h10), afterColumns_add]
        congr 2
        omega
    split
    · -- a byte ends the digits inside the slice
      rename_i next hgetE
      obtain ⟨hEs, hEc⟩ := get?_eq hgetE
      have hEd := hstop hEs
      rw [hEc] at hEd
      apply wp_ite
      · -- a dot: a decimal
        intro hdot
        have hdot' : next = 46 := by simpa using hdot
        have hF : Lexer.Slice.runEnd input
            (Lexer.Slice.runEnd input (index + 1) Lexer.RUN_DIGIT + 1) Lexer.RUN_DIGIT =
            runEnd input isDigit
              (Lexer.Slice.runEnd input (index + 1) Lexer.RUN_DIGIT + 1) :=
          runEnd_eq endsRun_digit _ _
        have hlf := le_runEnd input isDigit
          (Lexer.Slice.runEnd input (index + 1) Lexer.RUN_DIGIT + 1)
        have hlf' := runEnd_le input isDigit
          (Lexer.Slice.runEnd input (index + 1) Lexer.RUN_DIGIT + 1) hEs
        have hstopF := fun h => runEnd_stop input isDigit
          (Lexer.Slice.runEnd input (index + 1) Lexer.RUN_DIGIT + 1) h
        have hmemF := runEnd_mem input isDigit
          (Lexer.Slice.runEnd input (index + 1) Lexer.RUN_DIGIT + 1)
        have hB : feedFrom v input .idle location index =
            feedFrom v input
              (.token ⟨.fraction (false || decide
                  (Lexer.Slice.runEnd input (index + 1) Lexer.RUN_DIGIT + 1 <
                    runEnd input isDigit
                      (Lexer.Slice.runEnd input (index + 1) Lexer.RUN_DIGIT + 1))),
                location, bytesOf input index (runEnd input isDigit
                  (Lexer.Slice.runEnd input (index + 1) Lexer.RUN_DIGIT + 1))⟩)
              (afterColumns location (runEnd input isDigit
                (Lexer.Slice.runEnd input (index + 1) Lexer.RUN_DIGIT + 1) - index))
              (runEnd input isDigit
                (Lexer.Slice.runEnd input (index + 1) Lexer.RUN_DIGIT + 1)) := by
          have hadv : advance false ⟨.numeral (c == 48), location, bytesOf input index
              (Lexer.Slice.runEnd input (index + 1) Lexer.RUN_DIGIT)⟩
              (afterColumns location
                (Lexer.Slice.runEnd input (index + 1) Lexer.RUN_DIGIT - index))
              input[Lexer.Slice.runEnd input (index + 1) Lexer.RUN_DIGIT] =
              .pending ⟨.fraction false, location, (bytesOf input index
                (Lexer.Slice.runEnd input (index + 1) Lexer.RUN_DIGIT)).push 46⟩ := by
            rw [hEc, hdot']; rfl
          rw [hA, feedFrom_step hEs (byteStep_token_pending v hadv), prep_nil,
            feedFrom_fraction v input _ _ _ false rfl hEs, hEc, hdot',
            afterByte_eq_afterColumns' _ _ (by decide), afterColumns_add]
          simp only
          rw [← hdot', ← hEc, push_append_bytesOf _ input hEs (by omega) hlf',
            bytesOf_append input (by omega) (by omega) hlf', afterColumns_add]
          congr 2
          simp only [Nat.succ_eq_add_one] at *; omega
        rw [← hF] at hB hlf hlf' hstopF hmemF
        -- the last byte of the decimal so far: its dot, or a digit after it
        have hlastF : (input[Lexer.Slice.runEnd input (Lexer.Slice.runEnd input (index + 1)
              Lexer.RUN_DIGIT + 1) Lexer.RUN_DIGIT - 1]'(by omega) == 46) =
            !decide (Lexer.Slice.runEnd input (index + 1) Lexer.RUN_DIGIT + 1 <
              Lexer.Slice.runEnd input (Lexer.Slice.runEnd input (index + 1) Lexer.RUN_DIGIT + 1)
                Lexer.RUN_DIGIT) := by
          by_cases hlt : Lexer.Slice.runEnd input (index + 1) Lexer.RUN_DIGIT + 1 <
              Lexer.Slice.runEnd input (Lexer.Slice.runEnd input (index + 1) Lexer.RUN_DIGIT + 1)
                Lexer.RUN_DIGIT
          · have hdg := hmemF (Lexer.Slice.runEnd input (Lexer.Slice.runEnd input (index + 1)
              Lexer.RUN_DIGIT + 1) Lexer.RUN_DIGIT - 1) (by omega) (by omega) (by omega)
            simp only [hlt, decide_true, Bool.not_true]
            have : input[Lexer.Slice.runEnd input (Lexer.Slice.runEnd input (index + 1)
                Lexer.RUN_DIGIT + 1) Lexer.RUN_DIGIT - 1]'(by omega) ≠ 46 := by
              intro h; rw [h] at hdg; exact absurd hdg (by decide)
            simpa using this
          · have heq : Lexer.Slice.runEnd input (Lexer.Slice.runEnd input (index + 1)
                Lexer.RUN_DIGIT + 1) Lexer.RUN_DIGIT - 1 =
                Lexer.Slice.runEnd input (index + 1) Lexer.RUN_DIGIT := by omega
            simp only [hlt, decide_false, Bool.not_false]
            simp only [heq, hEc, hdot']
            rfl
        apply wp_ite
        · -- the fraction runs to the end of the slice: the decimal is left in progress
          intro hsz
          have hsz' : Lexer.Slice.runEnd input (Lexer.Slice.runEnd input (index + 1)
              Lexer.RUN_DIGIT + 1) Lexer.RUN_DIGIT = input.size := by simpa using hsz
          unfold Lexer.WRustPort.extendContent Lexer.WRustPort.modifyContent
            Lexer.WRustPort.leavePending
          apply wp_bind; apply wp_modifyCore
          apply wp_bind; apply wp_modifyBound
          apply wp_pure
          refine ⟨.token ⟨.fraction (false || decide
              (Lexer.Slice.runEnd input (index + 1) Lexer.RUN_DIGIT + 1 <
                Lexer.Slice.runEnd input (Lexer.Slice.runEnd input (index + 1) Lexer.RUN_DIGIT + 1)
                  Lexer.RUN_DIGIT)), location, bytesOf input index
              (Lexer.Slice.runEnd input (Lexer.Slice.runEnd input (index + 1) Lexer.RUN_DIGIT + 1)
                Lexer.RUN_DIGIT)⟩,
            afterColumns location (Lexer.Slice.runEnd input
              (Lexer.Slice.runEnd input (index + 1) Lexer.RUN_DIGIT + 1) Lexer.RUN_DIGIT - index),
            held, ⟨hfix.1, hfix.2, hfix.3, hfix.4⟩, Nat.le_refl _, ?_, ?_, hheld, hbytes, ?_⟩
          · dsimp only [StAgrees, TokenAgrees]
            refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
            · rw [locAt_eq hloc]; rfl
            · rw [contentBytes_clear_extendSlice _ _ ?_, show ∀ a b, (input.slice a b).toByteArray =
                bytesOf input a b from fun _ _ => rfl, stored_last input (by omega) (by omega)]
              · simp only [Option.isNone_some, Bool.false_or]
                congr 1
                have hs : ∀ x : UInt8, (some x == some (46 : UInt8)) = (x == 46) := by
                  intro x; cases h : x == 46 <;> simp_all
                rw [hs, hlastF, Bool.not_not]
              · bound_tac
            · exact (contentBytes_clear_extendSlice _ _ (by bound_tac)).symm
            · fits_tac
          · dsimp only [LocAt, afterColumns, Past.from]
            refine ⟨?_, ?_, ?_⟩ <;> omega
          · rw [hB]; rfl
        · intro hsz
          have hFs : Lexer.Slice.runEnd input (Lexer.Slice.runEnd input (index + 1)
              Lexer.RUN_DIGIT + 1) Lexer.RUN_DIGIT < input.size := by
            simp only [beq_iff_eq] at hsz; omega
          have hstopF' := hstopF hFs
          apply wp_bind; apply wp_getCore
          rw [borrowed_last input (by omega) (by omega)]
          apply wp_ite
          · -- no digit after the dot
            intro hnone
            have hlt : ¬ (Lexer.Slice.runEnd input (index + 1) Lexer.RUN_DIGIT + 1 <
                Lexer.Slice.runEnd input (Lexer.Slice.runEnd input (index + 1) Lexer.RUN_DIGIT + 1)
                  Lexer.RUN_DIGIT) := by
              intro hlt
              have := hlastF
              simp only [hlt, decide_true, Bool.not_true] at this
              simp [this] at hnone
            obtain ⟨f, hf⟩ := advance_end_fraction_none (location := afterColumns location
              (Lexer.Slice.runEnd input (Lexer.Slice.runEnd input (index + 1) Lexer.RUN_DIGIT + 1)
                Lexer.RUN_DIGIT - index))
              (q := ⟨.fraction (false || decide
                (Lexer.Slice.runEnd input (index + 1) Lexer.RUN_DIGIT + 1 <
                  Lexer.Slice.runEnd input
                    (Lexer.Slice.runEnd input (index + 1) Lexer.RUN_DIGIT + 1)
                    Lexer.RUN_DIGIT)), location, bytesOf input index
                (Lexer.Slice.runEnd input (Lexer.Slice.runEnd input (index + 1) Lexer.RUN_DIGIT + 1)
                  Lexer.RUN_DIGIT)⟩) (by simp [hlt]) hstopF'
            unfold Lexer.WRustPort.leave Lexer.WRustPort.error Lexer.WRustPort.errorWith
            wp_walk
            refine stepFails_here ?_ hheld hfix.1 hfix.2
            rw [hB, feedFrom_advance_error v input hFs hf]
          · intro hsome
            have hlt : Lexer.Slice.runEnd input (index + 1) Lexer.RUN_DIGIT + 1 <
                Lexer.Slice.runEnd input (Lexer.Slice.runEnd input (index + 1) Lexer.RUN_DIGIT + 1)
                  Lexer.RUN_DIGIT := by
              apply Classical.byContradiction
              intro hlt
              have := hlastF
              simp only [hlt, decide_false, Bool.not_false] at this
              simp [this] at hsome
            have hC := feedFrom_end v input hFs (q := ⟨.fraction (false || decide
                (Lexer.Slice.runEnd input (index + 1) Lexer.RUN_DIGIT + 1 <
                  Lexer.Slice.runEnd input
                    (Lexer.Slice.runEnd input (index + 1) Lexer.RUN_DIGIT + 1)
                    Lexer.RUN_DIGIT)), location, bytesOf input index
                (Lexer.Slice.runEnd input (Lexer.Slice.runEnd input (index + 1) Lexer.RUN_DIGIT + 1)
                  Lexer.RUN_DIGIT)⟩)
              (location := afterColumns location (Lexer.Slice.runEnd input
                (Lexer.Slice.runEnd input (index + 1) Lexer.RUN_DIGIT + 1) Lexer.RUN_DIGIT - index))
              (advance_end_fraction (by simp [hlt]) hstopF')
            rw [← hB] at hC
            rw [get_eq hFs]
            apply wp_ite
            · intro hnd
              have hnd' : VNaive.isDelimiter input[Lexer.Slice.runEnd input
                  (Lexer.Slice.runEnd input (index + 1) Lexer.RUN_DIGIT + 1) Lexer.RUN_DIGIT] =
                  false := by
                rw [← isDelimiter_eq]; simpa using hnd
              rw [hnd'] at hC
              unfold Lexer.WRustPort.leave Lexer.WRustPort.errorAt Lexer.WRustPort.errorWith
              wp_walk
              refine stepFails_here ?_ hheld hfix.1 hfix.2
              rw [hC]
              simp only [Bool.false_eq_true, ↓reduceIte]
            · intro hd'
              have hd'' : VNaive.isDelimiter input[Lexer.Slice.runEnd input
                  (Lexer.Slice.runEnd input (index + 1) Lexer.RUN_DIGIT + 1) Lexer.RUN_DIGIT] =
                  true := by
                rw [← isDelimiter_eq]; simpa using hd'
              rw [hd''] at hC
              simp only [↓reduceIte] at hC
              borrow_push TokenCategory.decimal index (Lexer.Slice.runEnd input
                (Lexer.Slice.runEnd input (index + 1) Lexer.RUN_DIGIT + 1) Lexer.RUN_DIGIT)
      · -- the numeral ends before the byte
        intro hdot
        have hdot' : next ≠ 46 := by simpa using hdot
        have hC := feedFrom_end v input hEs (q := ⟨.numeral (c == 48), location,
            bytesOf input index (Lexer.Slice.runEnd input (index + 1) Lexer.RUN_DIGIT)⟩)
          (location := afterColumns location
            (Lexer.Slice.runEnd input (index + 1) Lexer.RUN_DIGIT - index))
          (advance_end_numeral rfl (by rw [hEc]; exact hEd) (by rw [hEc]; exact hdot'))
        rw [← hA, hEc] at hC
        apply wp_ite
        · intro hnd
          have hnd' : VNaive.isDelimiter next = false := by
            rw [← isDelimiter_eq]; simpa using hnd
          rw [hnd'] at hC
          unfold Lexer.WRustPort.leave Lexer.WRustPort.errorAt Lexer.WRustPort.errorWith
          wp_walk
          refine stepFails_here ?_ hheld hfix.1 hfix.2
          rw [hC]
          simp only [Bool.false_eq_true, ↓reduceIte]
        · intro hd'
          have hd'' : VNaive.isDelimiter next = true := by
            rw [← isDelimiter_eq]; simpa using hd'
          rw [hd''] at hC
          simp only [↓reduceIte] at hC
          borrow_push TokenCategory.numeral index
            (Lexer.Slice.runEnd input (index + 1) Lexer.RUN_DIGIT)
    · -- the digits run to the end of the slice: the numeral is left in progress
      rename_i hgetE
      have hsz := Lexer.Slice.size_le_of_get?_none hgetE
      have hzero : (c == 48) = ((bytesOf input index
          (Lexer.Slice.runEnd input (index + 1) Lexer.RUN_DIGIT)).size == 1 &&
          (bytesOf input index (Lexer.Slice.runEnd input (index + 1) Lexer.RUN_DIGIT)).get! 0 ==
            48) := by
        rw [bytesOf_size input (by omega) hle',
          bytesOf_get! input (by omega) hle' (k := 0) (by omega)]
        simp only [Nat.add_zero, hc]
        by_cases hz0 : c = 48
        · have he := hz' hz0
          simp [hz0, he]
        · simp [hz0]
      unfold Lexer.WRustPort.extendContent Lexer.WRustPort.modifyContent
        Lexer.WRustPort.leavePending
      apply wp_bind; apply wp_modifyCore
      apply wp_bind; apply wp_modifyBound
      apply wp_pure
      refine ⟨.token ⟨.numeral (c == 48), location, bytesOf input index
          (Lexer.Slice.runEnd input (index + 1) Lexer.RUN_DIGIT)⟩,
        afterColumns location
          (Lexer.Slice.runEnd input (index + 1) Lexer.RUN_DIGIT - index),
        held, ⟨hfix.1, hfix.2, hfix.3, hfix.4⟩, Nat.le_refl _, ?_, ?_, hheld, hbytes, ?_⟩
      · dsimp only [StAgrees, TokenAgrees]
        refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_⟩
        · rw [locAt_eq hloc]; rfl
        · rw [contentBytes_clear_extendSlice _ _ ?_]
          · exact congrArg Mode.numeral hzero
          · bound_tac
        · exact (contentBytes_clear_extendSlice _ _ (by bound_tac)).symm
        · rw [contentBytes_clear_extendSlice _ _ ?_, show ∀ a b, (input.slice a b).toByteArray =
            bytesOf input a b from fun _ _ => rfl, bytesOf_size input (by omega) hle']
          · omega
          · bound_tac
        · fits_tac
      · dsimp only [LocAt, afterColumns, Past.from]
        refine ⟨?_, ?_, ?_⟩ <;> omega
      · rw [hA]; rfl
  -- a byte that starts no token
  all_goals
    rename_i hst
    have hother := startOf_other c
    have hs1 : (Lexer.startOf c == .other || Lexer.startOf c == .whitespace ||
        Lexer.startOf c == .parenOpen || Lexer.startOf c == .parenClose ||
        Lexer.startOf c == .symbol || Lexer.startOf c == .pipe) = true := by
      rw [hst]; rfl
    have h40b : (c == 40) = false := by simpa using hc40
    have h41b : (c == 41) = false := by simpa using hc41
    rw [hs1, hfoff, h40b, h41b] at hother
    simp only [Bool.not_true, Bool.false_or, Bool.and_eq_true, Bool.not_eq_true', bne_iff_ne,
      ne_eq] at hother
    obtain ⟨⟨⟨⟨⟨⟨⟨hw, h59⟩, h35⟩, h34⟩, h58⟩, h124⟩, hdig⟩, hsym⟩ := hother
    have herr : start v false location input[index] =
        .error (failAtByte .unexpectedCharacter location location) := by
      rw [hc]
      simp [start, hw, h59, h35, h34, h58, h124, hdig, hsym, hc40, hc41]
    unfold Lexer.WRustPort.startToken Lexer.WRustPort.modifyContent Lexer.WRustPort.leave
      Lexer.WRustPort.errorAt Lexer.WRustPort.errorWith
    wp_walk
    refine stepFails_here ?_ hheld hfix.1 hfix.2
    rw [feedFrom_start_error v input hi herr]


end

end BSmtLib.Proofs.Lexer.VNaiveWRustPort
