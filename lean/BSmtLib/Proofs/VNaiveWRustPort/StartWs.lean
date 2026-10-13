import BSmtLib.Proofs.VNaiveWRustPort.Push
import BSmtLib.Proofs.VNaiveWRustPort.Pure

/-!
# The Rust port's whitespace from the normal state, with a consumer that takes it

`wsStart_lt`: the loop of the normal state starts whitespace for a consumer that takes it with
`startWhitespaceFrom`, which goes over the run of whitespace other than line feeds, marks a line
feed and goes on after it, and ends the whitespace at the first byte that is not whitespace,
putting it into the batch the loop holds, or leaves it in progress at the end of the slice. It
does what the naive lexer's run does with the whitespace (`WsStartSpec`).
-/

namespace BSmtLib.Proofs.Lexer.VNaiveWRustPort

open BSmtLib.Proofs.Adapter VNaive BSmtLib.Proofs.Simulation
open BSmtLibSpec.Lexer (Handed)
open Lexer.WRustPort (FastState Frame Held Past)
open Lexer.Slice (get? get)

theorem advance_whitespace_run (ws : Bool) (q : Pending) (location : Location) (c : UInt8)
    (hm : q.mode = .whitespace) (hc : isWhitespaceRun c = true) :
    advance ws q location c = .pending { q with content := q.content.push c } := by
  obtain ⟨mode, start, content⟩ := q
  subst hm
  simp only [isWhitespaceRun, Bool.and_eq_true, bne_iff_ne, ne_eq] at hc
  simp [advance, hc.1]

theorem advance_whitespace_lf (ws : Bool) (q : Pending) (location : Location)
    (hm : q.mode = .whitespace) :
    advance ws q location 10 = .pending { q with content := q.content.push 10 } := by
  obtain ⟨mode, start, content⟩ := q
  subst hm
  rfl

theorem advance_whitespace_end (ws : Bool) (q : Pending) (location : Location) {c : UInt8}
    (hm : q.mode = .whitespace) (hc : isWhitespaceRun c = false) (h10 : c ≠ 10) :
    advance ws q location c =
      .tokenBefore ⟨.whitespace, q.content, q.start, location⟩ := by
  obtain ⟨mode, start, content⟩ := q
  subst hm
  have hw : isWhitespace c = false := by
    simp only [isWhitespaceRun, Bool.and_eq_false_iff, bne_eq_false_iff_eq] at hc
    rcases hc with h | h
    · exact h
    · exact absurd h h10
  simp [advance, hw]

theorem bytesOf_append (s : ByteSlice) {i j k : Nat} (hij : i ≤ j) (hjk : j ≤ k) (hk : k ≤ s.size) :
    bytesOf s i j ++ bytesOf s j k = bytesOf s i k := by
  apply ByteArray.ext
  rw [ByteArray.data_append, data_bytesOf s hij (by omega), data_bytesOf s hjk hk,
    data_bytesOf s (by omega) hk, Array.extract_append_extract]
  congr 1 <;> omega

section

variable {C : BSmtLibSpec.Lexer.Consumer} {floor : Option Nat} {low : Nat} {hd : Bool} {iv : Version}

theorem outcome_pending_congr {ver1 ver2 : Version} {c1 c2 : List Handed} {h1 h2 : List Lexeme}
    (h : pending C hd ver1 c1 h1 = pending C hd ver2 c2 h2)
    (e : Except (List Lexeme) (St × Location × List Lexeme)) :
    outcome C hd (pending C hd ver1 c1 h1) e = outcome C hd (pending C hd ver2 c2 h2) e := by
  rw [h]

theorem stops_lexeme {hold : Bool} {ver : Version} {coll : List Handed} {held : List Lexeme}
    {a b : Lexeme} (hab : a = b) {e : Intr C floor} {p : Prog} {d : Option Location}
    (hn : Stops C hold ver coll (held ++ [a]) e p d) :
    Stops C hold ver coll (held ++ [b]) e p d := by
  subst hab; exact hn

/-- The lexer state `c` is `s` but for the line and where it starts. -/
structure SameLine (s c : WCore) : Prop where
  version : c.version = s.version
  initialVersion : c.initialVersion = s.initialVersion
  state : c.state = s.state
  discardedFrom : c.discardedFrom = s.discardedFrom
  holding : c.holding = s.holding
  recovers : c.recovers = s.recovers
  recoveryState : c.recoveryState = s.recoveryState
  tokenStart : c.tokenStart = s.tokenStart
  tokenContent : c.tokenContent = s.tokenContent
  offset : c.offset = s.offset
  base : c.base = s.base
  batch : c.batch = s.batch

/-- What `startWhitespaceFrom` from the index `«end»` keeps, for whitespace started at `index`
at `location` from the lexer state `s` with the tokens taken `coll` and the batch of the lexemes
`held` the loop holds: the lexer state `s1` it runs in is `s` but for the line, and the naive
lexer's run from `index` is, at `«end»`, the whitespace in progress at `locE`. -/
def WsStartSpec (C : BSmtLibSpec.Lexer.Consumer) (v : Version)
    (input : ByteSlice) (offset base index : Nat) (start : Location) (batch : TokenBatch)
    (hframe : Frame floor low offset) (hstart : start.offset = offset + (index - base))
    (hbatch : Held floor offset base index batch) (s : BS floor low) (coll : List Handed)
    (location : Location)
    (Q : Option {next : Nat × TokenBatch // index < next.1 ∧ Held floor offset base next.1 next.2} →
      BS floor low → List Handed → Prop)
    (QE : Intr C floor → BS floor low → List Handed → Prop) («end» : Nat) : Prop :=
  ∀ (hend : base ≤ index ∧ index ≤ «end» ∧ «end» ≤ input.size)
    (hrun : index < «end» ∨ Lexer.WRustPort.ContinuesWhitespace input «end»)
    (s1 : BS floor low) (locE : Location),
    SameLine s.val s1.val →
    LocAt s1.val offset base «end» locE →
    feedFrom v C.concrete input .idle location index =
      feedFrom v C.concrete input (.token ⟨.whitespace, location, bytesOf input index «end»⟩)
        locE «end» →
    WP (Lexer.WRustPort.startWhitespaceFrom (H := Answering C) (m := AnswerM) (R := C.Result)
        (E := Option C.Error) input offset base index «end» start batch hframe hstart hend hrun
        hbatch) s1 coll Q QE

set_option maxHeartbeats 1000000 in
theorem wsStart_lt (v : Version) (input : ByteSlice) (offset base index : Nat) (start : Location)
    (batch : TokenBatch) (hframe : Frame floor low offset)
    (hstart : start.offset = offset + (index - base)) (hbatch : Held floor offset base index batch)
    (s : BS floor low) (coll : List Handed) (held : List Lexeme) (location : Location)
    (hfix : Fixed v hd iv s.val) (hoff : offset = s.val.offset) (hbase : base = s.val.base)
    (hnormal : s.val.state = .normal) (hsl : start = location) (hheld : Holds batch held)
    (hbytes : batch.bytes = input.byteArray) (hcon : C.concrete = true)
    (hcontent : contentBytes s.val.tokenContent = .empty) (hfits : Fits s.val.tokenContent)
    {Q : Option {next : Nat × TokenBatch // index < next.1 ∧ Held floor offset base next.1 next.2} →
      BS floor low → List Handed → Prop}
    {QE : Intr C floor → BS floor low → List Handed → Prop}
    (hsome : ∀ (next : Nat) (batch' : TokenBatch) (hnext : index < next)
      (hbatch' : Held floor offset base next batch') (s' : BS floor low) (coll' : List Handed)
      (held' : List Lexeme) (locN : Location),
      Fixed v hd iv s'.val → offset = s'.val.offset → base = s'.val.base →
      s'.val.state = .normal → LocAt s'.val offset base next locN → Holds batch' held' →
      batch'.bytes = input.byteArray →
      outcome C hd (pending C hd s.val.version coll held)
          (feedFrom v C.concrete input .idle location index) =
        outcome C hd (pending C hd s'.val.version coll' held')
          (feedFrom v C.concrete input .idle locN next) →
      Q (some ⟨(next, batch'), hnext, hbatch'⟩) s' coll')
    (hnone : ∀ s' : BS floor low,
      StepPost C v hd iv input .idle location index s.val.version coll held input.size s'.val
        coll → Q none s' coll)
    (herr : ∀ e s' coll', StepFails C v hd iv input .idle location index s.val.version coll held e
      s'.val coll' → QE e s' coll') :
    ∀ (n «end» : Nat), input.size - «end» < n →
      WsStartSpec C v input offset base index start batch hframe hstart hbatch s coll location Q
        QE «end» := by
  intro n
  induction n with
  | zero => intro e hn; omega
  | succ n ih =>
  intro e hn hend hrun s1 locE hs1 hlocE hanchor
  have hI : Lexer.Slice.runEnd input e Lexer.RUN_NON_LF_WHITESPACE =
      runEnd input isWhitespaceRun e := runEnd_eq endsRun_whitespace _ _
  have hle := le_runEnd input isWhitespaceRun e
  have hle' := runEnd_le input isWhitespaceRun e hend.2.2
  have hstop := fun h => runEnd_stop input isWhitespaceRun e h
  have hA := feedFrom_mode v C.concrete input isWhitespaceRun isWhitespaceRun_ne .whitespace
    (fun q l c hm hc => advance_whitespace_run C.concrete q l c hm hc) e
    ⟨.whitespace, location, bytesOf input index e⟩ locE rfl hend.2.2
  rw [← hI] at hA hle hle' hstop
  have hcat : bytesOf input index e ++ bytesOf input e
      (Lexer.Slice.runEnd input e Lexer.RUN_NON_LF_WHITESPACE) =
      bytesOf input index (Lexer.Slice.runEnd input e Lexer.RUN_NON_LF_WHITESPACE) :=
    bytesOf_append input hend.2.1 hle hle'
  have hLI := hlocE.afterColumns (by omega) hle
  have hfix1 : Fixed v hd iv s1.val :=
    ⟨by rw [hs1.version]; exact hfix.1, hs1.recovers.trans hfix.2,
      hs1.discardedFrom.trans hfix.3, hs1.holding.trans hfix.4,
      hs1.recoveryState.trans hfix.5, hs1.initialVersion.trans hfix.6⟩
  rw [Lexer.WRustPort.startWhitespaceFrom]
  split
  · rename_i c hget
    obtain ⟨hIs, hIc⟩ := get?_eq hget
    have hIq := hstop hIs
    rw [hIc] at hIq
    split
    · -- a line feed, which is marked and is a part of the whitespace
      rename_i h10
      have h10' : c = 10 := by simpa using h10
      unfold Lexer.WRustPort.markLineFeedAt
      apply wp_bind; apply wp_modifyCore
      refine ih (Lexer.Slice.runEnd input e Lexer.RUN_NON_LF_WHITESPACE + 1) (by omega) _ _ _
        ((afterColumns locE (Lexer.Slice.runEnd input e Lexer.RUN_NON_LF_WHITESPACE - e)).afterByte
          10) ⟨hs1.1, hs1.2, hs1.3, hs1.4, hs1.5, hs1.6, hs1.7, hs1.8, hs1.9, hs1.10, hs1.11,
          hs1.12⟩ ?_ ?_
      · refine LocAt.lineFeed hLI (by omega) rfl ?_
        show Lexer.WRustPort.LexerCore.offsetAt _ _ + 1 = _
        simp only [Lexer.WRustPort.LexerCore.offsetAt]
        rw [hs1.offset, hs1.base, ← hoff, ← hbase]
      · rw [hanchor, hA, feedFrom_step hIs (byteStep_token_pending v C.concrete (by
          rw [hIc, h10']; exact advance_whitespace_lf C.concrete _ _ rfl)), prep_nil, hIc, h10']
        dsimp only
        rw [hcat, bytesOf_push input (by omega) hIs, hIc, h10']
    · -- any other byte ends the whitespace, which goes into the batch
      rename_i h10
      have h10' : c ≠ 10 := by simpa using h10
      have hadv := advance_whitespace_end C.concrete ⟨.whitespace, location,
        bytesOf input index e ++ bytesOf input e
          (Lexer.Slice.runEnd input e Lexer.RUN_NON_LF_WHITESPACE)⟩
        (afterColumns locE (Lexer.Slice.runEnd input e Lexer.RUN_NON_LF_WHITESPACE - e))
        (c := input[Lexer.Slice.runEnd input e Lexer.RUN_NON_LF_WHITESPACE]) rfl
        (by rw [hIc]; exact hIq) (by rw [hIc]; exact h10')
      rw [hcat] at hadv
      have hC : feedFrom v C.concrete input .idle location index =
          Prep [⟨.whitespace, bytesOf input index
              (Lexer.Slice.runEnd input e Lexer.RUN_NON_LF_WHITESPACE), location,
              afterColumns locE (Lexer.Slice.runEnd input e Lexer.RUN_NON_LF_WHITESPACE - e)⟩]
            (feedFrom v C.concrete input .idle
              (afterColumns locE (Lexer.Slice.runEnd input e Lexer.RUN_NON_LF_WHITESPACE - e))
              (Lexer.Slice.runEnd input e Lexer.RUN_NON_LF_WHITESPACE)) := by
        rw [hanchor, hA]
        dsimp only
        rw [hcat]
        exact feedFrom_tokenBefore v C.concrete input hIs hadv
      have hlex : borrowedLexeme .whitespace (input.slice index
          (Lexer.Slice.runEnd input e Lexer.RUN_NON_LF_WHITESPACE)) start s1.val.line
          s1.val.lineStart (offset + (Lexer.Slice.runEnd input e Lexer.RUN_NON_LF_WHITESPACE -
            base)) =
          ⟨.whitespace, bytesOf input index
              (Lexer.Slice.runEnd input e Lexer.RUN_NON_LF_WHITESPACE), location,
              afterColumns locE (Lexer.Slice.runEnd input e Lexer.RUN_NON_LF_WHITESPACE - e)⟩ := by
        obtain ⟨h1, h2, h3⟩ := hLI
        simp only [borrowedLexeme, Lexeme.mk.injEq, true_and]
        refine ⟨rfl, hsl, ?_⟩
        cases hl : afterColumns locE (Lexer.Slice.runEnd input e Lexer.RUN_NON_LF_WHITESPACE - e)
        rw [hl] at h1 h2 h3
        simp only [Location.mk.injEq] at h1 h2 h3 ⊢
        refine ⟨by omega, h2.symm, by omega⟩
      apply wp_bind
      refine pushBorrowed_wp input batch offset base _ _ _ _ _ _ _ _ _ held hheld hbytes.symm
        ?_ ?_ _ coll ?_ ?_ ?_
      · omega
      · omega
      · exact hfix1.recovers
      · intro r s' coll' held' hH hb hk hp
        rw [hfix1.holding] at hp
        have hp' := hp.trans
          (congrArg (fun l => pending C hd s1.val.version coll (held ++ [l])) hlex)
        obtain ⟨k1, k2, k3, k4, k5, k6, k7, k8, k9, k10, k11⟩ := key_fields hk
        apply wp_pure
        refine hsome _ r.val (Lexer.WRustPort.lt_whitespaceRunEnd hend.2.1 hrun hget
            h10) r.property s'
          coll' held' _ (fixed_of_key' hk hfix1)
          (hoff.trans (by rw [k8, hs1.offset])) (hbase.trans (by rw [k9, hs1.base]))
          (by rw [k2, hs1.state]; exact hnormal) (hLI.congr k10 k11) hH (hb.trans hbytes) ?_
        rw [hC, outcome_pending_prep, ← hs1.version, outcome_pending_congr hp']
      · intro e' s' p d hn hss
        exact herr e' s' p.taken (stepFails_of_stops' hss hfix1
          ⟨_, by rw [hC, outcome_pending_prep, hs1.version]⟩ (stops_lexeme hlex hn))
  · -- the run reaches the end of the slice: the whitespace is left in progress
    rename_i hgetn
    have hge := Lexer.Slice.size_le_of_get?_none hgetn
    have he : Lexer.Slice.runEnd input e Lexer.RUN_NON_LF_WHITESPACE = input.size := by omega
    unfold Lexer.WRustPort.extendContent Lexer.WRustPort.modifyContent
      Lexer.WRustPort.leavePending
    apply wp_bind; apply wp_modifyCore
    apply wp_bind; apply wp_modifyBound
    apply wp_pure
    apply hnone
    rw [he] at hA hLI hcat
    have hfits1 : Fits s1.val.tokenContent := by rw [hs1.tokenContent]; exact hfits
    refine ⟨.token ⟨.whitespace, location, bytesOf input index input.size⟩,
      afterColumns locE (input.size - e), held, ⟨hfix1.1, hfix1.2, hfix1.3, hfix1.4, hfix1.5,
        hfix1.6⟩, by show input.size ≤ input.size; omega, ?_, ?_, hheld, hbytes, ?_⟩
    · refine ⟨⟨hsl.symm, hcon, rfl, ?_⟩, fits_extendSlice input hfits1 (.inl (Nat.le_refl _))⟩
      show bytesOf input index input.size = contentBytes (s1.val.tokenContent.extendFrom
        input.byteArray (input.start + index) (input.start + input.size))
      rw [contentBytes_extendSlice input hfits1 (.inl (Nat.le_refl _)), hs1.tokenContent,
        hcontent, empty_append]
      rfl
    · obtain ⟨h1, h2, h3⟩ := hLI
      refine ⟨?_, h2, h3⟩
      show _ = offset + (input.size - base) + (input.size - input.size)
      omega
    · show _ = outcome C hd (pending C hd s1.val.version coll held) _
      rw [hs1.version, hanchor, hA, hcat]


/-- Whitespace a consumer takes starts with its first byte, as it goes on with it. -/
theorem feedFrom_wsStart (v : Version) (input : ByteSlice) {i : Nat} (hi : i < input.size)
    (hw : isWhitespace input[i] = true) (location : Location) :
    feedFrom v true input .idle location i =
      feedFrom v true input (.token ⟨.whitespace, location, .empty⟩) location i := by
  have hs : start v true location input[i] =
      .pending ⟨.whitespace, location, ByteArray.empty.push input[i]⟩ := by
    simp only [start, hw, ite_true]
  have ha : advance true ⟨.whitespace, location, .empty⟩ location input[i] =
      .pending ⟨.whitespace, location, ByteArray.empty.push input[i]⟩ := by
    simp [advance, hw]
  rw [feedFrom_step hi (byteStep_idle_pending v true hs),
    feedFrom_step hi (byteStep_token_pending v true ha)]

theorem wp_state {α : Type} {x : M C floor low α} {s : BS floor low} {coll : List Handed}
    {Q : α → BS floor low → List Handed → Prop} {QE : Intr C floor → BS floor low →
        List Handed → Prop}
    (h : ∀ s', s' = s → WP x s' coll Q QE) : WP x s coll Q QE := h s rfl

/-- `startWhitespace` for a consumer that takes whitespace, from the normal state at `index`
at `location`, with whitespace at `index`. -/
theorem startWhitespace_wp (v : Version) (input : ByteSlice) (offset base index : Nat)
    (batch : TokenBatch) (hrun : Lexer.WRustPort.ContinuesWhitespace input index)
    (hframe : Frame floor low offset) (hindex : base ≤ index)
    (hbatch : Held floor offset base index batch)
    (s : BS floor low) (coll : List Handed) (held : List Lexeme) (location : Location)
    (hfix : Fixed v hd iv s.val) (hoff : offset = s.val.offset) (hbase : base = s.val.base)
    (hloc : LocAt s.val offset base index location) (hheld : Holds batch held)
    (hbytes : batch.bytes = input.byteArray) (hcon : C.concrete = true)
    (hi : index < input.size) (hw : isWhitespace input[index] = true)
    {Q : Option {next : Nat × TokenBatch // index < next.1 ∧ Held floor offset base next.1 next.2} →
      BS floor low → List Handed → Prop}
    {QE : Intr C floor → BS floor low → List Handed → Prop}
    (hsome : ∀ (next : Nat) (batch' : TokenBatch) (hnext : index < next)
      (hbatch' : Held floor offset base next batch') (s' : BS floor low) (coll' : List Handed)
      (held' : List Lexeme) (locN : Location),
      Fixed v hd iv s'.val → offset = s'.val.offset → base = s'.val.base →
      s'.val.state = .normal → LocAt s'.val offset base next locN → Holds batch' held' →
      batch'.bytes = input.byteArray →
      outcome C hd (pending C hd s.val.version coll held)
          (feedFrom v C.concrete input .idle location index) =
        outcome C hd (pending C hd s'.val.version coll' held')
          (feedFrom v C.concrete input .idle locN next) →
      Q (some ⟨(next, batch'), hnext, hbatch'⟩) s' coll')
    (hnone : ∀ s' : BS floor low,
      StepPost C v hd iv input .idle location index s.val.version coll held input.size s'.val
        coll → Q none s' coll)
    (herr : ∀ e s' coll', StepFails C v hd iv input .idle location index s.val.version coll held e
      s'.val coll' → QE e s' coll') :
    WP (Lexer.WRustPort.startWhitespace (H := Answering C) (m := AnswerM) (R := C.Result)
        (E := Option C.Error) input offset base index batch hrun hframe hindex hbatch) s coll Q
      QE := by
  obtain ⟨h1, h2, h3⟩ := hloc
  unfold Lexer.WRustPort.startWhitespace Lexer.WRustPort.startToken Lexer.WRustPort.modifyContent
  apply wp_bind
  apply wp_bind; apply wp_getCore
  apply wp_bind; apply wp_modifyCore
  apply wp_bind; apply wp_modifyCore
  apply wp_pure
  apply wp_state
  intro s2 hs2
  have hsl : (⟨offset + (index - base), s.val.line, offset + (index - base) - s.val.lineStart⟩ :
      Location) = location := by
    cases location
    simp only [Location.mk.injEq] at h1 h2 h3 ⊢
    exact ⟨h1.symm, h2.symm, by omega⟩
  refine wsStart_lt v input offset base index _ batch hframe _ hbatch s2 coll held location
    (by subst hs2; exact ⟨hfix.1, hfix.2, hfix.3, hfix.4, hfix.5, hfix.6⟩)
        (by subst hs2; exact hoff)
    (by subst hs2; exact hbase) (by subst hs2; rfl) hsl hheld hbytes hcon
    (by subst hs2; exact contentBytes_clear _) (by subst hs2; exact fits_clear _)
    (by subst hs2; exact hsome) (by subst hs2; exact hnone) (by subst hs2; exact herr)
    (input.size - index + 1) index (by omega) _ _ _ location
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
        (by subst hs2; exact ⟨h1, h2, h3⟩) ?_
  rw [hcon, bytesOf_self input index (Nat.le_of_lt hi)]
  exact feedFrom_wsStart v input hi hw location

end

end BSmtLib.Proofs.Lexer.VNaiveWRustPort
