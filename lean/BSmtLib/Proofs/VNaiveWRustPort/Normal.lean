import BSmtLib.Proofs.VNaiveWRustPort.StartWs

/-!
# The Rust port's normal state against the naive lexer

`lexNormalFrom_wp`: the loop of the Rust port's normal state, with its fast paths and its slow
path, keeps the correspondence with the naive lexer's pure run.
-/

namespace BSmtLib.Proofs.Lexer.VNaiveWRustPort

open BSmtLib.Proofs.Adapter VNaive BSmtLib.Proofs.Simulation
open BSmtLibSpec.Lexer (Handed)
open Lexer.WRustPort (lexNormalFrom FastState Frame Held Past)
open Lexer.Slice (get? get)

/-- Takes the steps of the lexer that only read and change the lexer state, and throws. -/
macro "wp_walk" : tactic =>
  `(tactic| repeat (first
    | apply wp_throw
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
      Lexer.RUN_STRING_PLAIN - index), held, ⟨hfix.1, hfix.2, hfix.3, hfix.4, hfix.5, hfix.6⟩,
    Nat.le_refl _,
    ?_, ?_, hheld, hbytes, ?_⟩
  · dsimp only [StAgrees, TokenAgrees, TokenAgreesNoWs]
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
  refine pushBorrowed_wp input batch offset base _ _ _ _ _ _ _ _ _ held hheld hbytes.symm ?_ ?_ _
    coll ?_ ?_ ?_
  · omega
  · omega
  · exact hfix.recovers
  · intro r s' coll' held' hH hb hk hp
    rw [hfix.holding] at hp
    have hp' := hp.trans
      (congrArg (fun l => pending C hd s.val.version coll (held ++ [l])) hlex)
    obtain ⟨k1, k2, k3, k4, k5, k6, k7, k8, k9, k10, k11⟩ := key_fields hk
    rw [rust_loadLocals]
    unfold FastState.load
    apply wp_bind; apply wp_bind; apply wp_getCore; apply wp_pure
    refine wp_recurse (f := fun (r : Past input origin) => r.1)
      (ih _ (by omega) r.val _ _ r.property origin _ s' coll' held'
        (afterColumns location ($hi - index))
        (fixed_of_key' hk ⟨hfix.1, hfix.2, hfix.3, hfix.4, hfix.5, hfix.6⟩) (hoff.trans k8.symm)
        (hbase.trans k9.symm) rfl rfl k2
        ((hloc.afterColumns hindex (by omega)).congr k10 k11) hH (hb.trans hbytes)) ?_
    rw [hC, outcome_pending_prep, outcome_pending_congr hp']
    try rfl
  · intro e s' p d hn hss
    have hn' := hn
    replace hn' := stops_lexeme hlex hn'
    exact stepFails_of_stops' hss ⟨hfix.1, hfix.2, hfix.3, hfix.4, hfix.5, hfix.6⟩
      ⟨_, by rw [hC, outcome_pending_prep] <;> rfl⟩ hn'))

section

variable {floor : Option Nat} {low : Nat}

variable {C : BSmtLibSpec.Lexer.Consumer} {hd : Bool} {iv : Version}

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

/-- The line break that ends a comment the consumer takes is the last byte of its content. -/
theorem advance_comment_end_ws (start : Location) (content : ByteArray) (location : Location)
    {c : UInt8} (hc : isCommentRun c = false) :
    advance true ⟨.comment, start, content⟩ location c =
      .tokenWith ⟨.comment, content.push c, start, location.afterByte c⟩ := by
  simp only [isCommentRun, Bool.and_eq_false_iff, bne_eq_false_iff_eq] at hc
  rcases hc with h | h <;> subst h <;> rfl

theorem byteStep_token_with {v : Version} {ws : Bool} {q : Pending} {location : Location}
    {c : UInt8} {l : Lexeme} (h : advance ws q location c = .tokenWith l) :
    byteStepW v ws (.token q) location c = some (.idle, [l]) := by
  simp [byteStepW, h]

theorem answering_concrete : Consume.isConcrete (H := Answering C) = C.concrete := rfl

theorem start_parenClose (v : Version) (ws : Bool) (location : Location) :
    start v ws location 41 =
      .token ⟨.parenClose, ByteArray.empty.push 41, location, location.afterByte 41⟩ := rfl

theorem start_parenOpen (v : Version) (ws : Bool) (location : Location) :
    start v ws location 40 =
      .token ⟨.parenOpen, ByteArray.empty.push 40, location, location.afterByte 40⟩ := rfl

/-- The rest of a step, from a later state whose outcome is that of the earlier one. -/
theorem wp_recurse {α : Type} {x : M C floor low α} {f : α → Nat} {v : Version}
    {input : ByteSlice} {st st1 : St} {location location1 : Location} {start start1 : Nat}
    {ver ver1 : Version} {coll coll1 : List Handed} {held held1 : List Lexeme} {s : BS floor low}
    (h : WP x s coll1
      (fun r s' coll' =>
        StepPost C v hd iv input st1 location1 start1 ver1 coll1 held1 (f r) s'.val coll')
      (fun e s' coll' =>
        StepFails C v hd iv input st1 location1 start1 ver1 coll1 held1 e s'.val coll'))
    (heq : outcome C hd (pending C hd ver coll held)
        (feedFrom v C.concrete input st location start) =
      outcome C hd (pending C hd ver1 coll1 held1)
        (feedFrom v C.concrete input st1 location1 start1)) :
    WP x s coll1
      (fun r s' coll' => StepPost C v hd iv input st location start ver coll held
          (f r) s'.val coll')
      (fun e s' coll' => StepFails C v hd iv input st location start ver coll held e
          s'.val coll') :=
  wp_mono h (fun _ _ _ hp => StepPost.trans heq hp) (fun _ _ _ hf => StepFails.trans heq hf)

/-- A step from a state with the same value. -/
theorem wp_state_congr {α : Type} {x : M C floor low α} {s s' : BS floor low}
    {coll : List Handed} {Q : α → BS floor low → List Handed → Prop}
    {QE : Intr C floor → BS floor low → List Handed → Prop}
    (h : s'.val = s.val) (hw : WP x s coll Q QE) : WP x s' coll Q QE := by
  have : s' = s := Subtype.ext h
  subst this
  exact hw

/-- Writing the loop's copies of the line back, which are the lexer state's. -/
theorem wp_store {β : Type} {locals : FastState} {s : BS floor low} {coll : List Handed}
    {f : Unit → M C floor low β} {Q : β → BS floor low → List Handed → Prop}
    {QE : Intr C floor → BS floor low → List Handed → Prop}
    (h1 : locals.line = s.val.line) (h2 : locals.lineStart = s.val.lineStart)
    (h : WP (f ()) s coll Q QE) :
    WP (Lexer.WRustPort.Ops.storeLocals (H := Answering C) (m := AnswerM) (R := C.Result)
      (E := Option C.Error) locals >>= f) s coll Q QE := by
  apply wp_bind
  rw [rust_storeLocals]; unfold FastState.store
  apply wp_modifyCore
  refine wp_state_congr ?_ h
  show { s.val with line := locals.line, lineStart := locals.lineStart } = s.val
  rw [h1, h2]

/-- What the loop of the normal state keeps, from the index `index`: if the lexer state is in
the normal state at `location`, with the loop's copies of its offset, index of the offset and
line, and the loop holds a batch of lexemes, then the loop keeps the correspondence. -/
def NormalSpec (C : BSmtLibSpec.Lexer.Consumer) (v : Version) (hd : Bool) (iv : Version)
    (input : ByteSlice) (offset base : Nat)
    (hframe : Frame floor low offset) (index : Nat) : Prop :=
  ∀ (batch : TokenBatch) (locals : FastState) (hindex : base ≤ index)
    (hbatch : Held floor offset base index batch) (origin : Nat) (horigin : origin ≤ index)
    (s : BS floor low) (coll : List Handed) (held : List Lexeme) (location : Location),
    Fixed v hd iv s.val → offset = s.val.offset → base = s.val.base → locals.line = s.val.line →
    locals.lineStart = s.val.lineStart → s.val.state = .normal →
    LocAt s.val offset base index location → Holds batch held → batch.bytes = input.byteArray →
    WP (lexNormalFrom (H := Answering C) (m := AnswerM) (R := C.Result) (E := Option C.Error)
        input offset base index batch locals hframe hindex hbatch origin horigin) s coll
      (fun r s' coll' =>
        StepPost C v hd iv input .idle location index s.val.version coll held r.1 s'.val coll')
      (fun e s' coll' =>
        StepFails C v hd iv input .idle location index s.val.version coll held e s'.val coll')

set_option maxHeartbeats 20000000 in
set_option maxRecDepth 20000 in
theorem normalSpec_lt (v : Version) (input : ByteSlice) (offset base : Nat)
    (hframe : Frame floor low offset) :
    ∀ (n index : Nat), input.size - index < n →
      NormalSpec C v hd iv input offset base hframe index := by
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
    apply wp_bind
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
      refine wp_mono (ih (index + 1) (by omega) r.val locals _
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
  intro hcp
  apply wp_ite
  · -- an opening parenthesis
    intro hop
    have hc40 : c = 40 := by simpa using hop
    apply wp_bind
    apply wp_getCore
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
    apply wp_bind
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
      refine wp_mono (ih (index + 1) (by omega) r.val locals _
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
  intro hop
  have hc40 : c ≠ 40 := by simpa using hop
  have hc41 : c ≠ 41 := by simpa using hcp
  apply wp_bind
  apply wp_pure
  apply wp_ite
  · -- the fast path
    intro hfast
    rcases fastFlags_cases c with hoff' | ⟨hf, hwsr⟩ | ⟨hf, hpipe⟩ | ⟨hf, hsym, hdig⟩
    · rw [hoff'] at hfast; cases hfast
    · -- whitespace other than a line feed
      by_cases hcon : C.concrete = true
      · simp only [answering_concrete, hcon, Bool.true_and]
        have hpipe : (Lexer.fastFlags c &&& Lexer.FAST_PIPE != 0) = false := by rw [hf]; decide
        have hsym : (Lexer.fastFlags c &&& Lexer.RUN_SIMPLE_SYMBOL != 0) = false := by
          rw [hf]; decide
        have hemit : (Lexer.fastFlags c &&& Lexer.FAST_EMIT != 0) = false := by rw [hf]; decide
        have hwsb : (Lexer.fastFlags c &&& Lexer.RUN_NON_LF_WHITESPACE != 0) = true := by
          rw [hf]; decide
        have hmask : Lexer.fastFlags c &&& Lexer.FAST_RUN_MASK = Lexer.RUN_NON_LF_WHITESPACE := by
          rw [hf]; decide
        have hw : isWhitespace input[index] = true := by
          rw [hc]
          simp only [isWhitespaceRun, Bool.and_eq_true] at hwsr
          exact hwsr.1
        have hj : Lexer.Slice.runEnd input (index + 1) (Lexer.fastFlags c &&& Lexer.FAST_RUN_MASK) =
            runEnd input isWhitespaceRun index := by
          rw [hmask, runEnd_eq endsRun_whitespace,
            ← runEnd_succ input _ index hi (by rw [hc]; exact hwsr)]
        have hle := le_runEnd input isWhitespaceRun (index + 1)
        rw [← runEnd_succ input _ index hi (by rw [hc]; exact hwsr)] at hle
        have hle' := runEnd_le input isWhitespaceRun index (Nat.le_of_lt hi)
        have hstop := fun h => runEnd_stop input isWhitespaceRun index h
        have hA := feedFrom_mode v true input isWhitespaceRun isWhitespaceRun_ne .whitespace
          (fun q l c hm hc => advance_whitespace_run true q l c hm hc) index
          ⟨.whitespace, location, .empty⟩ location rfl (Nat.le_of_lt hi)
        rw [← feedFrom_wsStart v input hi hw location, ← hcon, ← hj] at hA
        rw [← hj] at hle hle' hstop
        apply wp_dite
        · -- the whitespace does not end on this line inside the slice
          intro _
          refine wp_store hline hlineStart ?_
          apply wp_bind
          refine startWhitespace_wp v input offset base index batch _ hframe hindex hbatch s coll
            held location hfix hoff hbase hloc hheld hbytes hcon hi hw ?_ ?_ ?_
          · intro next batch' hnext hbatch' s' coll' held' locN hfix' hoff' hbase' hnormal' hloc'
              hheld' hbytes' heq
            dsimp only
            rw [rust_loadLocals]
            unfold FastState.load
            apply wp_bind; apply wp_bind; apply wp_getCore; apply wp_pure
            refine wp_recurse (f := fun (r : Past input origin) => r.1)
              (ih next (by omega) batch' _ _ hbatch' origin _ s' coll' held' locN hfix' hoff'
                hbase' rfl rfl hnormal' hloc' hheld' hbytes') heq
          · intro s' hpost
            apply wp_pure
            exact hpost
          · intro e s' coll' hf
            exact hf
        intro hws
        -- the whitespace ends inside the slice before a byte that is not a line feed
        obtain ⟨c', hgetR, hc'10⟩ : ∃ c', get? input (Lexer.Slice.runEnd input (index + 1)
            (Lexer.fastFlags c &&& Lexer.FAST_RUN_MASK)) = some c' ∧ c' ≠ 10 := by
          simp only [hwsb, Bool.true_and] at hws
          revert hws
          cases get? input (Lexer.Slice.runEnd input (index + 1)
            (Lexer.fastFlags c &&& Lexer.FAST_RUN_MASK)) with
          | none => intro h; exact absurd rfl h
          | some c' => intro h; exact ⟨c', rfl, by simpa using h⟩
        obtain ⟨hRs, hRc⟩ := get?_eq hgetR
        have hRq := hstop hRs
        have hadv := advance_whitespace_end true ⟨.whitespace, location,
          ByteArray.empty ++ bytesOf input index
            (Lexer.Slice.runEnd input (index + 1) (Lexer.fastFlags c &&& Lexer.FAST_RUN_MASK))⟩
          (afterColumns location (Lexer.Slice.runEnd input (index + 1)
            (Lexer.fastFlags c &&& Lexer.FAST_RUN_MASK) - index))
          (c := input[Lexer.Slice.runEnd input (index + 1)
            (Lexer.fastFlags c &&& Lexer.FAST_RUN_MASK)]) rfl hRq (by rw [hRc]; exact hc'10)
        have hC : feedFrom v C.concrete input .idle location index =
            Prep [⟨.whitespace, bytesOf input index (Lexer.Slice.runEnd input (index + 1)
                (Lexer.fastFlags c &&& Lexer.FAST_RUN_MASK)), location,
                afterColumns location (Lexer.Slice.runEnd input (index + 1)
                  (Lexer.fastFlags c &&& Lexer.FAST_RUN_MASK) - index)⟩]
              (feedFrom v C.concrete input .idle
                (afterColumns location (Lexer.Slice.runEnd input (index + 1)
                  (Lexer.fastFlags c &&& Lexer.FAST_RUN_MASK) - index))
                (Lexer.Slice.runEnd input (index + 1) (Lexer.fastFlags c &&& Lexer.FAST_RUN_MASK)))
            := by
          rw [hA, hcon, feedFrom_tokenBefore v true input hRs hadv, empty_append]
        have hidx : (if (Lexer.fastFlags c &&& Lexer.FAST_PIPE != 0) = true then
            Lexer.Slice.runEnd input (index + 1) (Lexer.fastFlags c &&& Lexer.FAST_RUN_MASK) + 1
          else Lexer.Slice.runEnd input (index + 1) (Lexer.fastFlags c &&& Lexer.FAST_RUN_MASK)) =
            Lexer.Slice.runEnd input (index + 1) (Lexer.fastFlags c &&& Lexer.FAST_RUN_MASK) := by
          simp only [hpipe, Bool.false_eq_true, ↓reduceIte]
        apply wp_dite
        · intro h; simp [hpipe, hsym] at h
        intro _
        apply wp_ite
        · intro h; rw [hemit] at h; cases h
        intro _
        apply wp_bind
        refine pushFast_wp input batch locals offset base _ _ _ index _ _ _ hindex _ hframe hbatch
          held hheld hbytes.symm ?_ ?_ s coll hfix.recovers ?_ ?_
        · simp only [hpipe, Bool.false_eq_true, ↓reduceIte]; omega
        · simp only [hpipe, Bool.false_eq_true, ↓reduceIte]; omega
        · intro r s' coll' held' hH hb hk hp
          rw [hfix.holding] at hp
          simp only [hpipe, hwsb, hemit, Bool.false_eq_true, Bool.false_or,
            hcon, Bool.and_true, ↓reduceIte] at hp
          rw [hline, hlineStart, onLine_eq hloc hindex (by omega)] at hp
          obtain ⟨k1, k2, k3, k4, k5, k6, k7, k8, k9, k10, k11⟩ := key_fields hk
          refine wp_recurse (f := fun (r : Past input origin) => r.1)
            (ih _ (by rw [hidx]; omega) r.val locals _ r.property origin _ s' coll' held'
              (afterColumns location (Lexer.Slice.runEnd input (index + 1)
                (Lexer.fastFlags c &&& Lexer.FAST_RUN_MASK) - index))
              (fixed_of_key hfix hk) (hoff.trans k8.symm) (hbase.trans k9.symm)
              (hline.trans k10.symm) (hlineStart.trans k11.symm) (k2.trans hnormal)
              (by rw [hidx]; exact (hloc.afterColumns hindex (by omega)).congr k10 k11) hH
              (hb.trans hbytes)) ?_
          rw [hidx, hC, outcome_pending_prep, outcome_pending_congr hp]
          rfl
        · intro e s' p d hn hss
          simp only [hpipe, hwsb, hemit, Bool.false_eq_true, Bool.false_or,
            hcon, Bool.and_true, ↓reduceIte] at hn
          rw [hline, hlineStart, onLine_eq hloc hindex (by omega)] at hn
          exact stepFails_of_stops' hss ⟨hfix.1, hfix.2, hfix.3, hfix.4, hfix.5, hfix.6⟩
            ⟨_, by rw [hC, outcome_pending_prep] <;> rfl⟩ hn
      have hcon' : C.concrete = false := by simpa using hcon
      simp only [answering_concrete, hcon', Bool.false_and, Bool.false_eq_true,
          ↓reduceIte, dite_false]
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
      have hpure : feedFrom v C.concrete input .idle location index =
          feedFrom v C.concrete input .idle
            (afterColumns location (runEnd input isWhitespaceRun index - index))
            (runEnd input isWhitespaceRun index) :=
        feedFrom_idleRun v C.concrete input isWhitespaceRun isWhitespaceRun_ne
          (fun location c h => byteStep_idle_idle v C.concrete
            (by rw [hcon']; exact start_whitespaceRun v location h)) _ index rfl
          location (Nat.le_of_lt hi)
      apply wp_dite
      · intro h; simp [hpipe, hsym] at h
      intro _
      apply wp_ite
      · intro h; rw [hemit] at h; cases h
      intro _
      apply wp_bind
      refine pushFast_wp input batch locals offset base _ _ _ index _ _ _ hindex _ hframe hbatch
        held hheld hbytes.symm ?_ ?_ s coll hfix.recovers ?_ ?_
      · simp only [hpipe, Bool.false_eq_true, ↓reduceIte, hj]; omega
      · simp only [hpipe, Bool.false_eq_true, ↓reduceIte, hj]
        exact runEnd_le input _ _ (Nat.le_of_lt hi)
      · intro r s' coll' held' hH hb hk hp
        rw [hfix.holding] at hp
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
      · intro e s' p d hn hss
        simp only [hemit, Bool.false_eq_true, ↓reduceIte, List.append_nil] at hn
        exact stepFails_of_stops' hss ⟨hfix.1, hfix.2, hfix.3, hfix.4, hfix.5, hfix.6⟩
          ⟨_, rfl⟩ hn
    · -- a quoted symbol
      have hnw : (Lexer.fastFlags c &&& Lexer.RUN_NON_LF_WHITESPACE != 0) = false := by
        rw [hf]; decide
      simp only [answering_concrete, hnw, Bool.and_false, Bool.false_and,
          Bool.false_eq_true, dite_false,
        Bool.or_false, ite_self]
      have hpipeb : (Lexer.fastFlags c &&& Lexer.FAST_PIPE != 0) = true := by rw [hf]; decide
      have hemit : (Lexer.fastFlags c &&& Lexer.FAST_EMIT != 0) = true := by rw [hf]; decide
      have hmask : Lexer.fastFlags c &&& Lexer.FAST_RUN_MASK = Lexer.RUN_QUOTED_PLAIN := by
        rw [hf]; decide
      have hj : Lexer.Slice.runEnd input (index + 1) (Lexer.fastFlags c &&& Lexer.FAST_RUN_MASK) =
          runEnd input isQuotedRun (index + 1) := by
        rw [hmask, runEnd_eq endsRun_quoted]
      have hle := le_runEnd input isQuotedRun (index + 1)
      have hA : feedFrom v C.concrete input .idle location index =
          feedFrom v C.concrete input
            (.token ⟨.quotedSymbol, location,
              bytesOf input (index + 1) (runEnd input isQuotedRun (index + 1))⟩)
            (afterColumns location (runEnd input isQuotedRun (index + 1) - index))
            (runEnd input isQuotedRun (index + 1)) := by
        rw [feedFrom_startRun v C.concrete input isQuotedRun isQuotedRun_ne .quotedSymbol
          (fun q l c hm hc => advance_quotedSymbol_run C.concrete q l c hm hc) hi
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
            ⟨hfix.1, hfix.2, hfix.3, hfix.4, hfix.5, hfix.6⟩, Nat.le_refl _, ?_, ?_,
                hheld, hbytes, ?_⟩
          · dsimp only [StAgrees, TokenAgrees, TokenAgreesNoWs]
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
        have hB : feedFrom v C.concrete input .idle location index =
            feedFrom v C.concrete input
              (.token ⟨.quotedSymbolClosed, location, bytesOf input (index + 1)
                (Lexer.Slice.runEnd input (index + 1) (Lexer.fastFlags c &&& Lexer.FAST_RUN_MASK))⟩)
              (afterColumns location (Lexer.Slice.runEnd input (index + 1)
                (Lexer.fastFlags c &&& Lexer.FAST_RUN_MASK) + 1 - index))
              (Lexer.Slice.runEnd input (index + 1)
                (Lexer.fastFlags c &&& Lexer.FAST_RUN_MASK) + 1) := by
          rw [hA, feedFrom_step hJ (byteStep_token_pending v C.concrete
              (by rw [hJc]; rfl)), prep_nil,
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
            have hC := feedFrom_end v C.concrete input hJ1 (q := ⟨.quotedSymbolClosed, location,
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
              refine stepFails_here ?_ hheld
                ⟨hfix.1, hfix.2, hfix.3, hfix.4, hfix.5, hfix.6⟩ rfl
              rw [hC]
              simp only [Bool.false_eq_true, ↓reduceIte]
            · intro hdl
              have hd' : VNaive.isDelimiter next = true := by
                rw [← isDelimiter_eq]; simpa using hdl
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
                    else TokenCategory.unquotedSymbol)
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
              refine pushFast_wp input batch locals offset base _ _ _ index _ _ _ hindex _ hframe
                hbatch held hheld hbytes.symm ?_ ?_ s coll hfix.recovers
                ?_ ?_
              · simp only [hpipeb, ↓reduceIte]; omega
              · simp only [hpipeb, ↓reduceIte]; omega
              · intro r s' coll' held' hH hb hk hp
                rw [hfix.holding] at hp
                simp only [hnw, Bool.and_false, Bool.false_eq_true, ↓reduceIte] at hp
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
                rw [hidx, hC, outcome_pending_prep, outcome_pending_congr hp]
              · intro e s' p d hn hss
                simp only [hnw, Bool.and_false, Bool.false_eq_true, ↓reduceIte] at hn
                rw [hlex] at hn
                exact stepFails_of_stops' hss ⟨hfix.1, hfix.2, hfix.3, hfix.4, hfix.5, hfix.6⟩
                  ⟨_, by rw [hC, outcome_pending_prep] <;> rfl⟩ hn
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
              ⟨hfix.1, hfix.2, hfix.3, hfix.4, hfix.5, hfix.6⟩, Nat.le_refl _, ?_, ?_,
                  hheld, hbytes, ?_⟩
            · dsimp only [StAgrees, TokenAgrees, TokenAgreesNoWs]
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
              rfl
        · intro h'; rw [hemit] at h'; exact absurd rfl h'
    · -- a simple symbol that does not start with a digit
      have hnw : (Lexer.fastFlags c &&& Lexer.RUN_NON_LF_WHITESPACE != 0) = false := by
        rw [hf]; decide
      simp only [answering_concrete, hnw, Bool.and_false, Bool.false_and,
          Bool.false_eq_true, dite_false,
        Bool.or_false, ite_self]
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
      have hA : feedFrom v C.concrete input .idle location index =
          feedFrom v C.concrete input
            (.token ⟨.simpleSymbol, location,
              bytesOf input index (runEnd input isSymbolByte (index + 1))⟩)
            (afterColumns location (runEnd input isSymbolByte (index + 1) - index))
            (runEnd input isSymbolByte (index + 1)) := by
        rw [feedFrom_startRun v C.concrete input isSymbolByte isSymbolByte_ne .simpleSymbol
          (fun q l c hm hc => advance_simpleSymbol_run C.concrete q l c hm hc) hi
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
            ⟨hfix.1, hfix.2, hfix.3, hfix.4, hfix.5, hfix.6⟩, Nat.le_refl _, ?_, ?_,
                hheld, hbytes, ?_⟩
          · dsimp only [StAgrees, TokenAgrees, TokenAgreesNoWs]
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
        have hC := feedFrom_end v C.concrete input hJ (q := ⟨.simpleSymbol, location,
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
              refine stepFails_here ?_ hheld
                ⟨hfix.1, hfix.2, hfix.3, hfix.4, hfix.5, hfix.6⟩ rfl
              rw [hC]
              simp only [Bool.false_eq_true, ↓reduceIte]
            · intro hdl
              have hd' : VNaive.isDelimiter next = true := by
                rw [← isDelimiter_eq]; simpa using hdl
              rw [hd'] at hC
              simp only [↓reduceIte] at hC
              have hlex : (if (Lexer.fastFlags c &&& Lexer.FAST_EMIT != 0) = true then
                  [onLine (if (Lexer.fastFlags c &&& Lexer.FAST_PIPE != 0) = true then
                      TokenCategory.quotedSymbol
                    else TokenCategory.unquotedSymbol)
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
                simp only [hpipeb, hemit, Bool.false_eq_true, ↓reduceIte]
                rw [hline, hlineStart, onLine_eq hloc hindex (by omega)]
                rfl
              apply wp_bind
              refine pushFast_wp input batch locals offset base _ _ _ index _ _ _ hindex _ hframe
                hbatch held hheld hbytes.symm ?_ ?_ s coll hfix.recovers
                ?_ ?_
              · simp only [hpipeb, Bool.false_eq_true, ↓reduceIte]; omega
              · simp only [hpipeb, Bool.false_eq_true, ↓reduceIte]; omega
              · intro r s' coll' held' hH hb hk hp
                rw [hfix.holding] at hp
                simp only [hnw, Bool.and_false, Bool.false_eq_true, ↓reduceIte] at hp
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
                rw [hidx, hC, outcome_pending_prep, outcome_pending_congr hp]
              · intro e s' p d hn hss
                simp only [hnw, Bool.and_false, Bool.false_eq_true, ↓reduceIte] at hn
                rw [hlex] at hn
                exact stepFails_of_stops' hss ⟨hfix.1, hfix.2, hfix.3, hfix.4, hfix.5, hfix.6⟩
                  ⟨_, by rw [hC, outcome_pending_prep] <;> rfl⟩ hn
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
    by_cases hcon : C.concrete = true
    · rename_i hst
      have h10 := Lexer.eq_of_startOf_eq_lineFeed hst
      simp only [answering_concrete, hcon, ↓reduceIte]
      apply wp_bind
      refine startWhitespace_wp v input offset base index batch _ hframe hindex hbatch s coll held
        location hfix hoff hbase hloc hheld hbytes hcon hi (by rw [hc, h10]; rfl) ?_ ?_ ?_
      · intro next batch' hnext hbatch' s' coll' held' locN hfix' hoff' hbase' hnormal' hloc'
          hheld' hbytes' heq
        dsimp only
        rw [rust_loadLocals]
        unfold FastState.load
        apply wp_bind; apply wp_bind; apply wp_getCore; apply wp_pure
        exact wp_recurse (f := fun (r : Past input origin) => r.1)
          (ih next (by omega) batch' _ _ hbatch' origin _ s' coll' held' locN hfix' hoff' hbase'
            rfl rfl hnormal' hloc' hheld' hbytes') heq
      · intro s' hpost
        apply wp_pure
        exact hpost
      · intro e s' coll' hf
        exact hf
    have hcon' : C.concrete = false := by simpa using hcon
    simp only [answering_concrete, hcon', Bool.false_eq_true, ↓reduceIte]
    rename_i hst
    have h10 := Lexer.eq_of_startOf_eq_lineFeed hst
    rw [rust_loadLocals]
    unfold Lexer.WRustPort.markLineFeedAt FastState.load
    apply wp_bind; apply wp_modifyCore
    apply wp_bind; apply wp_bind; apply wp_getCore; apply wp_pure
    have hpure : feedFrom v C.concrete input .idle location index =
        feedFrom v C.concrete input .idle (location.afterByte 10) (index + 1) := by
      rw [feedFrom_step hi (byteStep_idle_idle v C.concrete (by rw [hc, h10, hcon']; rfl)),
          prep_nil, hc, h10]
    refine wp_recurse (f := fun (r : Past input origin) => r.1)
      (ih (index + 1) (by omega) batch _ _ _ origin _ _ coll held (location.afterByte 10)
        ⟨hfix.1, hfix.2, hfix.3, hfix.4, hfix.5, hfix.6⟩ hoff hbase rfl rfl hnormal
        (hloc.lineFeed hindex rfl (by
          show Lexer.WRustPort.LexerCore.offsetAt _ index + 1 = _
          simp only [Lexer.WRustPort.LexerCore.offsetAt]
          rw [← hoff, ← hbase])) hheld hbytes) ?_
    rw [hpure]
  · -- a comment
    by_cases hcon : C.concrete = true
    · rename_i hst
      have h59 := startOf_comment hst
      simp only [answering_concrete, hcon, ↓reduceIte]
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
                (Lexer.Slice.runEnd input (index + 1) Lexer.RUN_COMMENT_PLAIN)).push c', location,
                (afterColumns location (Lexer.Slice.runEnd input (index + 1)
                  Lexer.RUN_COMMENT_PLAIN - index)).afterByte c'⟩]
              (feedFrom v C.concrete input .idle
                ((afterColumns location (Lexer.Slice.runEnd input (index + 1)
                  Lexer.RUN_COMMENT_PLAIN - index)).afterByte c')
                (Lexer.Slice.runEnd input (index + 1) Lexer.RUN_COMMENT_PLAIN + 1)) := by
          have hadv := advance_comment_end_ws location (bytesOf input (index + 1)
            (Lexer.Slice.runEnd input (index + 1) Lexer.RUN_COMMENT_PLAIN))
            (afterColumns location (Lexer.Slice.runEnd input (index + 1)
              Lexer.RUN_COMMENT_PLAIN - index)) hEs'
          rw [← hEc, ← hcon] at hadv
          rw [hA, feedFrom_step hEs (byteStep_token_with hadv), hEc]
        have hcontent : (input.slice (index + 1)
            (Lexer.Slice.runEnd input (index + 1) Lexer.RUN_COMMENT_PLAIN + 1)).toByteArray =
            (bytesOf input (index + 1)
              (Lexer.Slice.runEnd input (index + 1) Lexer.RUN_COMMENT_PLAIN)).push c' := by
          have := content_succ input ByteArray.empty hle hEs
          rw [empty_append, empty_append, hEc] at this
          exact this
        apply wp_ite
        · -- a line feed, which is marked
          intro h10
          have h10' : c' = 10 := by simpa using h10
          subst h10'
          have hlex : borrowedLexeme .comment (input.slice (index + 1)
              (Lexer.Slice.runEnd input (index + 1) Lexer.RUN_COMMENT_PLAIN + 1))
              ⟨offset + (index - base), s.val.line, offset + (index - base) - s.val.lineStart⟩
              (s.val.line + 1)
              (Lexer.WRustPort.LexerCore.offsetAt s.val
                (Lexer.Slice.runEnd input (index + 1) Lexer.RUN_COMMENT_PLAIN) + 1)
              (offset + (Lexer.Slice.runEnd input (index + 1) Lexer.RUN_COMMENT_PLAIN + 1 -
                base)) =
              ⟨.comment, (bytesOf input (index + 1)
                (Lexer.Slice.runEnd input (index + 1) Lexer.RUN_COMMENT_PLAIN)).push 10,
                location, (afterColumns location (Lexer.Slice.runEnd input (index + 1)
                  Lexer.RUN_COMMENT_PLAIN - index)).afterByte 10⟩ := by
            simp only [borrowedLexeme, hcontent]
            obtain ⟨h1, h2, h3⟩ := hloc
            cases location
            simp only [afterColumns, Location.afterByte, Lexeme.mk.injEq,
              Location.mk.injEq, true_and, Lexer.WRustPort.LexerCore.offsetAt] at h1 h2 h3 ⊢
            refine ⟨⟨by omega, h2.symm, by omega⟩, ?_⟩
            have hlf : ((10 : UInt8) == '\n'.toUInt8) = true := rfl
            simp only [hlf, ite_true, Location.mk.injEq]
            refine ⟨by omega, by omega, by omega⟩
          unfold Lexer.WRustPort.markLineFeedAt
          apply wp_bind; apply wp_modifyCore
          apply wp_bind
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
            rw [rust_loadLocals]
            unfold FastState.load
            apply wp_bind; apply wp_bind; apply wp_getCore; apply wp_pure
            refine wp_recurse (f := fun (r : Past input origin) => r.1)
              (ih _ (by omega) r.val _ _ r.property origin _ s' coll' held'
                ((afterColumns location (Lexer.Slice.runEnd input (index + 1)
                  Lexer.RUN_COMMENT_PLAIN - index)).afterByte 10)
                (fixed_of_key' hk ⟨hfix.1, hfix.2, hfix.3, hfix.4, hfix.5, hfix.6⟩)
                (hoff.trans k8.symm) (hbase.trans k9.symm) rfl rfl k2
                ((LocAt.lineFeed (hloc.afterColumns hindex (by omega)) (by omega) rfl (by
                  show Lexer.WRustPort.LexerCore.offsetAt _ _ + 1 = _
                  simp only [Lexer.WRustPort.LexerCore.offsetAt]
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
            (j := Lexer.Slice.runEnd input (index + 1) Lexer.RUN_COMMENT_PLAIN + 1) (by omega)
            .comment (input.slice (index + 1)
              (Lexer.Slice.runEnd input (index + 1) Lexer.RUN_COMMENT_PLAIN + 1))
          have hendE : (afterColumns location (Lexer.Slice.runEnd input (index + 1)
              Lexer.RUN_COMMENT_PLAIN - index)).afterByte c' =
              afterColumns location (Lexer.Slice.runEnd input (index + 1)
                Lexer.RUN_COMMENT_PLAIN + 1 - index) := by
            rw [afterByte_eq_afterColumns' _ _ h10', afterColumns_add]
            congr 1
            omega
          rw [hcontent] at hlex
          rw [hendE] at hB
          apply wp_bind
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
            rw [rust_loadLocals]
            unfold FastState.load
            apply wp_bind; apply wp_bind; apply wp_getCore; apply wp_pure
            refine wp_recurse (f := fun (r : Past input origin) => r.1)
              (ih _ (by omega) r.val _ _ r.property origin _ s' coll' held'
                (afterColumns location (Lexer.Slice.runEnd input (index + 1)
                  Lexer.RUN_COMMENT_PLAIN + 1 - index))
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
        have hsz := Lexer.Slice.size_le_of_get?_none hgetE
        unfold Lexer.WRustPort.extendContent Lexer.WRustPort.modifyContent
          Lexer.WRustPort.leavePending
        apply wp_bind; apply wp_modifyCore
        apply wp_bind; apply wp_modifyBound
        apply wp_pure
        refine ⟨.token ⟨.comment, location, bytesOf input (index + 1)
            (Lexer.Slice.runEnd input (index + 1) Lexer.RUN_COMMENT_PLAIN)⟩,
          afterColumns location (Lexer.Slice.runEnd input (index + 1)
            Lexer.RUN_COMMENT_PLAIN - index), held,
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
            ((afterColumns location (Lexer.Slice.runEnd input (index + 1)
              Lexer.RUN_COMMENT_PLAIN - index)).afterByte c')
            (Lexer.Slice.runEnd input (index + 1) Lexer.RUN_COMMENT_PLAIN + 1) := by
        have hadv := advance_comment_end location (bytesOf input (index + 1)
          (Lexer.Slice.runEnd input (index + 1) Lexer.RUN_COMMENT_PLAIN))
          (afterColumns location (Lexer.Slice.runEnd input (index + 1)
            Lexer.RUN_COMMENT_PLAIN - index)) hEs'
        rw [← hEc] at hadv
        rw [hA, feedFrom_step hEs (byteStep_token_idle v C.concrete
            (by rw [hcon']; exact hadv)), prep_nil, hEc]
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
            ⟨hfix.1, hfix.2, hfix.3, hfix.4, hfix.5, hfix.6⟩ hoff hbase rfl rfl rfl
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
            ⟨hfix.1, hfix.2, hfix.3, hfix.4, hfix.5, hfix.6⟩ hoff hbase rfl rfl rfl
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
        ⟨hfix.1, hfix.2, hfix.3, hfix.4, hfix.5, hfix.6⟩, Nat.le_refl _, ?_, ?_, hheld, hbytes, ?_⟩
      · dsimp only [StAgrees, TokenAgrees, TokenAgreesNoWs]
        refine ⟨⟨?_, rfl, fun h => nomatch h.symm.trans hcon'⟩, ?_⟩
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
    have hhash : feedFrom v C.concrete input .idle location index =
        feedFrom v C.concrete input (.token ⟨.hash, location, .empty⟩) (location.afterByte 35)
          (index + 1) := by
      rw [feedFrom_step hi (byteStep_idle_pending v C.concrete (by rw [hc, h35]; rfl)),
          prep_nil, hc, h35]
    split
    · -- the base is selected
      rename_i run hrun heqm
      obtain ⟨b, hb, hsel⟩ := Option.bind_eq_some_iff.mp hrun
      obtain ⟨hi1, hb'⟩ := get?_eq hb
      obtain ⟨radix, hadv, h10', hflag, hstate, htyp, hnotr⟩ : ∃ radix : Radix,
          advance C.concrete ⟨.hash, location, .empty⟩ (location.afterByte 35) input[index + 1] =
            .pending ⟨.digits radix, location, .empty⟩ ∧ input[index + 1] ≠ 10 ∧
          (∀ c, Lexer.endsRun c run.flag = !radix.allows c) ∧
          (∀ (p : Pending) start content, p.mode = .digits radix → p.start = start →
            p.content = content → TokenAgrees v C.concrete run.state start content p) ∧
          run.tokenType = radix.category ∧ run.emptyError ≠ .unexpectedTrailingToken := by
        rw [hb']
        by_cases hx : (b == 120) = true
        · simp only [hx, ↓reduceIte, Option.some.injEq] at hsel
          subst hsel
          have hx' : b = 120 := by simpa using hx
          subst hx'
          exact ⟨.hexadecimal, rfl, by decide, endsRun_hex,
            fun _ _ _ hm hs hc => ⟨hs, hm, hc⟩, rfl, nofun⟩
        · simp only [hx, Bool.false_eq_true, ↓reduceIte] at hsel
          by_cases hy : (b == 98) = true
          · simp only [hy, ↓reduceIte, Option.some.injEq] at hsel
            subst hsel
            have hy' : b = 98 := by simpa using hy
            subst hy'
            exact ⟨.binary, rfl, by decide, endsRun_binary,
              fun _ _ _ hm hs hc => ⟨hs, hm, hc⟩, rfl, nofun⟩
          · simp only [hy, Bool.false_eq_true, ↓reduceIte] at hsel
            cases hsel
      have hJ : Lexer.Slice.runEnd input (index + 1 + 1) run.flag =
          runEnd input radix.allows (index + 1 + 1) := runEnd_eq hflag _ _
      have hle := le_runEnd input radix.allows (index + 1 + 1)
      have hle' := runEnd_le input radix.allows (index + 1 + 1) hi1
      have hstop := fun h => runEnd_stop input radix.allows (index + 1 + 1) h
      have hB : feedFrom v C.concrete input .idle location index =
          feedFrom v C.concrete input
            (.token ⟨.digits radix, location,
              bytesOf input (index + 1 + 1) (runEnd input radix.allows (index + 1 + 1))⟩)
            (afterColumns location
              (runEnd input radix.allows (index + 1 + 1) - index))
            (runEnd input radix.allows (index + 1 + 1)) := by
        rw [hhash, feedFrom_step hi1 (byteStep_token_pending v C.concrete hadv), prep_nil,
          feedFrom_mode v C.concrete input radix.allows (allows_ne radix) (.digits radix)
            (fun q l c hm hc => advance_digits_run radix C.concrete q l c hm hc)
                (index + 1 + 1) _ _ rfl
            hi1, afterByte_eq_afterColumns' _ _ h10', afterByte_eq_afterColumns' _ _ (by decide),
          afterColumns_add, afterColumns_add]
        simp only [empty_append]
        congr 2
        omega
      rw [← hJ] at hB hle hle' hstop
      apply wp_dite
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
          held, ⟨hfix.1, hfix.2, hfix.3, hfix.4, hfix.5, hfix.6⟩, Nat.le_refl _, ?_, ?_,
              hheld, hbytes, ?_⟩
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
        have hsize : ∀ buf h1 h2, (Lexer.Slice.borrow input (index + 1 + 1)
            (Lexer.Slice.runEnd input (index + 1 + 1) run.flag) h1 h2).size buf =
              Lexer.Slice.runEnd input (index + 1 + 1) run.flag - (index + 1 + 1) := fun _ _ _ => by
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
          refine stepFails_here (he := ⟨_, rfl, hnotr⟩) ?_ hheld
            ⟨hfix.1, hfix.2, hfix.3, hfix.4, hfix.5, hfix.6⟩ rfl
          rw [hB, feedFrom_advance_error v C.concrete input hJs hf]
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
          have hC := feedFrom_end v C.concrete input hJs (q := ⟨.digits radix, location,
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
            refine stepFails_here ?_ hheld
              ⟨hfix.1, hfix.2, hfix.3, hfix.4, hfix.5, hfix.6⟩ rfl
            rw [hC]
            simp only [Bool.false_eq_true, ↓reduceIte]
          · intro hdl
            have hd' : VNaive.isDelimiter
                input[Lexer.Slice.runEnd input (index + 1 + 1) run.flag] = true := by
              rw [← isDelimiter_eq]; simpa using hdl
            rw [hd'] at hC
            simp only [↓reduceIte] at hC
            have hlex := borrowedLexeme_eq hloc hindex
              (j := Lexer.Slice.runEnd input (index + 1 + 1) run.flag) (by omega) run.tokenType
              (input.slice (index + 1 + 1) (Lexer.Slice.runEnd input (index + 1 + 1) run.flag))
            apply wp_bind
            refine pushBorrowed_wp input batch offset base _ _ _ _ _ _ _ _ _ held hheld
                hbytes.symm ?_ ?_
              _ coll ?_ ?_ ?_
            · omega
            · omega
            · exact hfix.recovers
            · intro r s' coll' held' hH hb hk hp
              rw [hfix.holding] at hp
              have hp' : pending C hd s'.val.version coll' held' = pending C hd
                  s.val.version coll (held ++
                  [⟨radix.category, bytesOf input (index + 1 + 1)
                    (Lexer.Slice.runEnd input (index + 1 + 1) run.flag), location,
                    afterColumns location (Lexer.Slice.runEnd input (index + 1 + 1)
                      run.flag - index)⟩]) := by
                have := hp.trans (congrArg (fun l => pending C hd s.val.version coll
                    (held ++ [l])) hlex)
                rw [htyp] at this; exact this
              obtain ⟨k1, k2, k3, k4, k5, k6, k7, k8, k9, k10, k11⟩ := key_fields hk
              rw [rust_loadLocals]
              unfold FastState.load
              apply wp_bind; apply wp_bind; apply wp_getCore; apply wp_pure
              refine wp_recurse (f := fun (r : Past input origin) => r.1)
                (ih _ (by omega) r.val _ _ r.property origin _ s' coll' held'
                  (afterColumns location (Lexer.Slice.runEnd input (index + 1 + 1)
                    run.flag - index))
                  (fixed_of_key' hk ⟨hfix.1, hfix.2, hfix.3, hfix.4, hfix.5, hfix.6⟩)
                      (hoff.trans k8.symm)
                  (hbase.trans k9.symm) rfl rfl k2
                  ((hloc.afterColumns hindex (by omega)).congr k10 k11) hH
                  (hb.trans hbytes)) ?_
              rw [hC, outcome_pending_prep, outcome_pending_congr hp']
            · intro e s' p d hn hss
              have hn' := hn
              replace hn' := stops_lexeme hlex hn'
              rw [htyp] at hn'
              exact stepFails_of_stops' hss ⟨hfix.1, hfix.2, hfix.3, hfix.4, hfix.5, hfix.6⟩
                ⟨_, by rw [hC, outcome_pending_prep] <;> rfl⟩ hn'
    · -- no base is selected: the hash is left in progress
      unfold Lexer.WRustPort.leavePending
      apply wp_bind; apply wp_modifyBound
      apply wp_pure
      refine ⟨.token ⟨.hash, location, .empty⟩, location.afterByte 35, held,
        ⟨hfix.1, hfix.2, hfix.3, hfix.4, hfix.5, hfix.6⟩, Nat.le_refl _, ?_, ?_, hheld, hbytes, ?_⟩
      · dsimp only [StAgrees, TokenAgrees, TokenAgreesNoWs]
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
    have hq : feedFrom v C.concrete input .idle location index =
        feedFrom v C.concrete input
          (.token ⟨if v == .v2_0 then .legacyString else .string, location, .empty⟩)
          (location.afterByte 34) (index + 1) := by
      rw [feedFrom_step hi (byteStep_idle_pending v C.concrete (by rw [hc, h34]; rfl)),
          prep_nil, hc, h34]
    apply wp_ite
    · -- under version 2.0 the string is left in progress at once
      intro hv2
      unfold Lexer.WRustPort.leavePending
      apply wp_bind; apply wp_modifyBound
      apply wp_pure
      refine ⟨.token ⟨if v == .v2_0 then .legacyString else .string, location, .empty⟩,
        location.afterByte 34, held, ⟨hfix.1, hfix.2, hfix.3, hfix.4, hfix.5,
            hfix.6⟩, Nat.le_refl _,
        ?_, ?_,
        hheld, hbytes, ?_⟩
      · dsimp only [StAgrees, TokenAgrees, TokenAgreesNoWs]
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
      have hA : feedFrom v C.concrete input .idle location index =
          feedFrom v C.concrete input
            (.token ⟨.string, location,
              bytesOf input (index + 1) (runEnd input isStringRun (index + 1))⟩)
            (afterColumns location (runEnd input isStringRun (index + 1) - index))
            (runEnd input isStringRun (index + 1)) := by
        rw [feedFrom_startRun v C.concrete input isStringRun isStringRun_ne .string
          (fun q l c hm hc => advance_string_run C.concrete q l c hm hc) hi
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
          have hB : feedFrom v C.concrete input .idle location index =
              feedFrom v C.concrete input
                (.token ⟨.stringQuote, location, bytesOf input (index + 1)
                  (Lexer.Slice.runEnd input (index + 1) Lexer.RUN_STRING_PLAIN)⟩)
                (afterColumns location (Lexer.Slice.runEnd input (index + 1)
                  Lexer.RUN_STRING_PLAIN + 1 - index))
                (Lexer.Slice.runEnd input (index + 1) Lexer.RUN_STRING_PLAIN + 1) := by
            rw [hA, feedFrom_step hA1 (byteStep_token_pending v C.concrete
                (by rw [hAc, hq34]; rfl)),
              prep_nil, afterByte_eq_afterColumns' _ _ (by rw [hAc, hq34]; decide),
              afterColumns_add]
            congr 2
            omega
          have hC := feedFrom_end v C.concrete input hA2 (q := ⟨.stringQuote, location,
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
            refine stepFails_here ?_ hheld
              ⟨hfix.1, hfix.2, hfix.3, hfix.4, hfix.5, hfix.6⟩ rfl
            rw [hC]
            simp only [Bool.false_eq_true, ↓reduceIte]
          · intro hdl
            have hd' : VNaive.isDelimiter next = true := by
              rw [← isDelimiter_eq]; simpa using hdl
            rw [hd'] at hC
            simp only [↓reduceIte] at hC
            have hlex := borrowedLexeme_eq hloc hindex
              (j := Lexer.Slice.runEnd input (index + 1) Lexer.RUN_STRING_PLAIN + 1) (by omega)
              .string (input.slice (index + 1)
                (Lexer.Slice.runEnd input (index + 1) Lexer.RUN_STRING_PLAIN))
            apply wp_bind
            refine pushBorrowed_wp input batch offset base _ _ _ _ _ _ _ _ _ held hheld
                hbytes.symm ?_ ?_
              _ coll ?_ ?_ ?_
            · omega
            · omega
            · exact hfix.recovers
            · intro r s' coll' held' hH hb hk hp
              rw [hfix.holding] at hp
              have hp' : pending C hd s'.val.version coll' held' = pending C hd
                  s.val.version coll (held ++
                  [⟨.string, bytesOf input (index + 1)
                    (Lexer.Slice.runEnd input (index + 1) Lexer.RUN_STRING_PLAIN), location,
                    afterColumns location (Lexer.Slice.runEnd input (index + 1)
                      Lexer.RUN_STRING_PLAIN + 1 - index)⟩]) :=
                hp.trans (congrArg (fun l => pending C hd s.val.version coll (held ++ [l])) hlex)
              obtain ⟨k1, k2, k3, k4, k5, k6, k7, k8, k9, k10, k11⟩ := key_fields hk
              rw [rust_loadLocals]
              unfold FastState.load
              apply wp_bind; apply wp_bind; apply wp_getCore; apply wp_pure
              refine wp_recurse (f := fun (r : Past input origin) => r.1)
                (ih _ (by omega) r.val _ _ r.property origin _ s' coll' held'
                  (afterColumns location (Lexer.Slice.runEnd input (index + 1)
                    Lexer.RUN_STRING_PLAIN + 1 - index))
                  (fixed_of_key' hk ⟨hfix.1, hfix.2, hfix.3, hfix.4, hfix.5, hfix.6⟩)
                      (hoff.trans k8.symm)
                  (hbase.trans k9.symm) rfl rfl k2
                  ((hloc.afterColumns hindex (by omega)).congr k10 k11) hH
                  (hb.trans hbytes)) ?_
              rw [hC, outcome_pending_prep, outcome_pending_congr hp']
            · intro e s' p d hn hss
              have hn' := hn
              replace hn' := stops_lexeme hlex hn'
              exact stepFails_of_stops' hss ⟨hfix.1, hfix.2, hfix.3, hfix.4, hfix.5, hfix.6⟩
                ⟨_, by rw [hC, outcome_pending_prep] <;> rfl⟩ hn'
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
    have hA : feedFrom v C.concrete input .idle location index =
        feedFrom v C.concrete input
          (.token ⟨.keyword, location,
            bytesOf input (index + 1) (runEnd input isSymbolByte (index + 1))⟩)
          (afterColumns location (runEnd input isSymbolByte (index + 1) - index))
          (runEnd input isSymbolByte (index + 1)) := by
      rw [feedFrom_startRun v C.concrete input isSymbolByte isSymbolByte_ne .keyword
        (fun q l c hm hc => advance_keyword_run C.concrete q l c hm hc) hi
        (q := ⟨.keyword, location, .empty⟩) (by rw [hc, h58]; rfl) rfl
        (by rw [hc, h58]; decide)]
      simp only [empty_append]
    rw [← hK] at hA hle hle' hstop
    apply wp_dite
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
        held, ⟨hfix.1, hfix.2, hfix.3, hfix.4, hfix.5, hfix.6⟩, Nat.le_refl _, ?_, ?_,
            hheld, hbytes, ?_⟩
      · dsimp only [StAgrees, TokenAgrees, TokenAgreesNoWs]
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
      have hsize : ∀ buf h1 h2, (Lexer.Slice.borrow input (index + 1)
          (Lexer.Slice.runEnd input (index + 1) Lexer.RUN_SIMPLE_SYMBOL) h1 h2).size buf =
            Lexer.Slice.runEnd input (index + 1) Lexer.RUN_SIMPLE_SYMBOL - (index + 1) := by
        intro _ _ _
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
        refine stepFails_here ?_ hheld
          ⟨hfix.1, hfix.2, hfix.3, hfix.4, hfix.5, hfix.6⟩ rfl
        rw [hA, feedFrom_advance_error v C.concrete input hJs hf]
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
        have hC := feedFrom_end v C.concrete input hJs (q := ⟨.keyword, location,
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
          refine stepFails_here ?_ hheld
            ⟨hfix.1, hfix.2, hfix.3, hfix.4, hfix.5, hfix.6⟩ rfl
          rw [hC]
          simp only [Bool.false_eq_true, ↓reduceIte]
        · intro hdl
          have hd' : VNaive.isDelimiter
              input[Lexer.Slice.runEnd input (index + 1) Lexer.RUN_SIMPLE_SYMBOL] = true := by
            rw [← isDelimiter_eq]; simpa using hdl
          rw [hd'] at hC
          simp only [↓reduceIte] at hC
          have hlex := borrowedLexeme_eq hloc hindex
            (j := Lexer.Slice.runEnd input (index + 1) Lexer.RUN_SIMPLE_SYMBOL) (by omega)
            .keyword (input.slice (index + 1)
              (Lexer.Slice.runEnd input (index + 1) Lexer.RUN_SIMPLE_SYMBOL))
          apply wp_bind
          refine pushBorrowed_wp input batch offset base _ _ _ _ _ _ _ _ _ held hheld hbytes.symm
              ?_ ?_
            _ coll ?_ ?_ ?_
          · omega
          · omega
          · exact hfix.recovers
          · intro r s' coll' held' hH hb hk hp
            rw [hfix.holding] at hp
            have hp' : pending C hd s'.val.version coll' held' = pending C hd
                s.val.version coll (held ++
                [⟨.keyword, bytesOf input (index + 1)
                  (Lexer.Slice.runEnd input (index + 1) Lexer.RUN_SIMPLE_SYMBOL), location,
                  afterColumns location (Lexer.Slice.runEnd input (index + 1)
                    Lexer.RUN_SIMPLE_SYMBOL - index)⟩]) :=
              hp.trans (congrArg (fun l => pending C hd s.val.version coll (held ++ [l])) hlex)
            obtain ⟨k1, k2, k3, k4, k5, k6, k7, k8, k9, k10, k11⟩ := key_fields hk
            rw [rust_loadLocals]
            unfold FastState.load
            apply wp_bind; apply wp_bind; apply wp_getCore; apply wp_pure
            refine wp_recurse (f := fun (r : Past input origin) => r.1)
              (ih _ (by omega) r.val _ _ r.property origin _ s' coll' held'
                (afterColumns location (Lexer.Slice.runEnd input (index + 1)
                  Lexer.RUN_SIMPLE_SYMBOL - index))
                (fixed_of_key' hk ⟨hfix.1, hfix.2, hfix.3, hfix.4, hfix.5, hfix.6⟩)
                    (hoff.trans k8.symm)
                (hbase.trans k9.symm) rfl rfl k2
                ((hloc.afterColumns hindex (by omega)).congr k10 k11) hH
                (hb.trans hbytes)) ?_
            rw [hC, outcome_pending_prep, outcome_pending_congr hp']
          · intro e s' p d hn hss
            have hn' := hn
            replace hn' := stops_lexeme hlex hn'
            exact stepFails_of_stops' hss ⟨hfix.1, hfix.2, hfix.3, hfix.4, hfix.5, hfix.6⟩
              ⟨_, by rw [hC, outcome_pending_prep] <;> rfl⟩ hn'
  · -- a digit: a numeral or a decimal
    rename_i hst
    have hdg := startOf_digit hst
    have hstart : start v C.concrete location input[index] =
        .pending ⟨.numeral (c == 48), location, ByteArray.empty.push c⟩ := by
      rw [hc]; exact start_digit v C.concrete location hdg
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
    have h10 : c ≠ 10 := isDigit_ne c hdg
    apply wp_ite
    · -- a numeral with a leading zero
      intro hz
      simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hz
      obtain ⟨hz0, hlt⟩ := hz
      have hi1 : index + 1 < input.size := by omega
      have hd1 := hmem (index + 1) hi1 (Nat.le_refl _) hlt
      have hadv : ∃ f, advance C.concrete ⟨.numeral true, location, ByteArray.empty.push c⟩
          (location.afterByte c) input[index + 1] = .error f := by
        simp [advance, hd1]
      obtain ⟨f, hf⟩ := hadv
      unfold Lexer.WRustPort.leave Lexer.WRustPort.errorAt Lexer.WRustPort.errorWith
      wp_walk
      refine stepFails_here ?_ hheld
        ⟨hfix.1, hfix.2, hfix.3, hfix.4, hfix.5, hfix.6⟩ rfl
      rw [feedFrom_step hi (byteStep_idle_pending v C.concrete hstart), hc, hz0]
      simp only [beq_self_eq_true]
      rw [hz0] at hf
      rw [feedFrom_advance_error v C.concrete input hi1 hf]
      rfl
    intro hz
    have hz' : c = 48 → Lexer.Slice.runEnd input (index + 1) Lexer.RUN_DIGIT = index + 1 := by
      intro h0
      simp only [h0, beq_self_eq_true, Bool.true_and, decide_eq_true_eq] at hz
      omega
    have hA : feedFrom v C.concrete input .idle location index =
        feedFrom v C.concrete input
          (.token ⟨.numeral (c == 48), location, bytesOf input index
            (Lexer.Slice.runEnd input (index + 1) Lexer.RUN_DIGIT)⟩)
          (afterColumns location
            (Lexer.Slice.runEnd input (index + 1) Lexer.RUN_DIGIT - index))
          (Lexer.Slice.runEnd input (index + 1) Lexer.RUN_DIGIT) := by
      rw [feedFrom_step hi (byteStep_idle_pending v C.concrete hstart), prep_nil]
      by_cases hz0 : c = 48
      · have he := hz' hz0
        rw [he, bytesOf_one input index hi, hc, afterByte_eq_afterColumns' _ _ h10]
        simp
      · have hfalse : (c == 48) = false := by simpa using hz0
        rw [hfalse, feedFrom_mode v C.concrete input isDigit isDigit_ne (.numeral false)
          (fun q l c hm hc => advance_numeral_run C.concrete q l c hm hc) (index + 1)
              _ _ rfl hi, ← hE]
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
        have hB : feedFrom v C.concrete input .idle location index =
            feedFrom v C.concrete input
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
          have hadv : advance C.concrete ⟨.numeral (c == 48), location, bytesOf input index
              (Lexer.Slice.runEnd input (index + 1) Lexer.RUN_DIGIT)⟩
              (afterColumns location
                (Lexer.Slice.runEnd input (index + 1) Lexer.RUN_DIGIT - index))
              input[Lexer.Slice.runEnd input (index + 1) Lexer.RUN_DIGIT] =
              .pending ⟨.fraction false, location, (bytesOf input index
                (Lexer.Slice.runEnd input (index + 1) Lexer.RUN_DIGIT)).push 46⟩ := by
            rw [hEc, hdot']; rfl
          rw [hA, feedFrom_step hEs (byteStep_token_pending v C.concrete hadv), prep_nil,
            feedFrom_fraction v C.concrete input _ _ _ false rfl hEs, hEc, hdot',
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
        apply wp_dite
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
            held, ⟨hfix.1, hfix.2, hfix.3, hfix.4, hfix.5, hfix.6⟩, Nat.le_refl _, ?_,
                ?_, hheld, hbytes,
            ?_⟩
          · dsimp only [StAgrees, TokenAgrees, TokenAgreesNoWs]
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
            refine stepFails_here ?_ hheld
              ⟨hfix.1, hfix.2, hfix.3, hfix.4, hfix.5, hfix.6⟩ rfl
            rw [hB, feedFrom_advance_error v C.concrete input hFs hf]
          · intro hsome
            have hlt : Lexer.Slice.runEnd input (index + 1) Lexer.RUN_DIGIT + 1 <
                Lexer.Slice.runEnd input (Lexer.Slice.runEnd input (index + 1) Lexer.RUN_DIGIT + 1)
                  Lexer.RUN_DIGIT := by
              apply Classical.byContradiction
              intro hlt
              have := hlastF
              simp only [hlt, decide_false, Bool.not_false] at this
              simp [this] at hsome
            have hC := feedFrom_end v C.concrete input hFs (q := ⟨.fraction (false || decide
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
              refine stepFails_here ?_ hheld
                ⟨hfix.1, hfix.2, hfix.3, hfix.4, hfix.5, hfix.6⟩ rfl
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
        have hC := feedFrom_end v C.concrete input hEs (q := ⟨.numeral (c == 48), location,
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
          refine stepFails_here ?_ hheld
            ⟨hfix.1, hfix.2, hfix.3, hfix.4, hfix.5, hfix.6⟩ rfl
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
        held, ⟨hfix.1, hfix.2, hfix.3, hfix.4, hfix.5, hfix.6⟩, Nat.le_refl _, ?_, ?_,
            hheld, hbytes, ?_⟩
      · dsimp only [StAgrees, TokenAgrees, TokenAgreesNoWs]
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
    have herr : start v C.concrete location input[index] =
        .error (failAtByte .unexpectedCharacter location location) := by
      rw [hc]
      simp [start, hw, h59, h35, h34, h58, h124, hdig, hsym, hc40, hc41]
    unfold Lexer.WRustPort.startToken Lexer.WRustPort.modifyContent Lexer.WRustPort.leave
      Lexer.WRustPort.errorAt Lexer.WRustPort.errorWith
    wp_walk
    refine stepFails_here ?_ hheld
      ⟨hfix.1, hfix.2, hfix.3, hfix.4, hfix.5, hfix.6⟩ rfl
    rw [feedFrom_start_error v C.concrete input hi herr]

end

end BSmtLib.Proofs.Lexer.VNaiveWRustPort
