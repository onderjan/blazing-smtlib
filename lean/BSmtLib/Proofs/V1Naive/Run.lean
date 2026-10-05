import BSmtLib.Proofs.V1Naive.Spec

/-!
# The pure run of the naive lexer

The naive lexer of `V1Naive` lexes an input by a pure step over one byte at a time, and hands
each finished token over to its consumer in a monad. For the consumer of `V1Spec.lex`, which
takes every token and does not take whitespace and comments, this module states the lexing as
a pure run over the bytes of the whole input (`run`) and proves that `V1Spec.lex` gives what
the run gives, whatever slices the input is cut into (`lex_eq_run`).
-/

namespace BSmtLib.Proofs.Lexer.V1Naive

open BSmtLib.Proofs.Lexer.V1Spec

/-! ## The pure run -/

/-- What the lexer is doing between two bytes, when its consumer takes every token. -/
inductive St where
  | idle
  | token (pending : Pending)

/-- The lexer's activity for the state. -/
def St.activity : St → Activity
  | .idle => .idle
  | .token p => .token p

/-- The byte `c` at `location` with no token in progress: the state after it and the
lexemes it finishes, or none on an error. -/
def startStep (version : Version) (location : Location) (c : UInt8) :
    Option (St × List Lexeme) :=
  match start version false location c with
  | .idle => some (.idle, [])
  | .pending p => some (.token p, [])
  | .token l => some (.idle, [l])
  | .error _ => none

/-- The byte `c` at `location` in the state: the state after it and the lexemes it finishes,
or none on an error. A byte that delimits a token is lexed again with no token in
progress. -/
def byteStep (version : Version) : St → Location → UInt8 → Option (St × List Lexeme)
  | .idle, location, c => startStep version location c
  | .token p, location, c =>
    match advance false p location c with
    | .pending p => some (.token p, [])
    | .idle => some (.idle, [])
    | .tokenWith l => some (.idle, [l])
    | .tokenBefore l => (startStep version location c).map fun (st, ls) => (st, l :: ls)
    | .error _ => none

/-- The bytes from the state at `location`: the state and the location after them and the
lexemes they finish, or none on an error. -/
def feedBytes (version : Version) : St → Location → List UInt8 →
    Option (St × Location × List Lexeme)
  | st, location, [] => some (st, location, [])
  | st, location, c :: cs =>
    match byteStep version st location c with
    | none => none
    | some (st', ls) =>
      (feedBytes version st' (location.afterByte c) cs).map fun (st'', location', ls') =>
        (st'', location', ls ++ ls')

/-- The end-of-file lexeme at `location`. -/
def eofLexeme (location : Location) : Lexeme :=
  { category := .endOfFile, content := .empty, start := location, «end» := location }

/-- The end of the input in the state at `location`: the lexemes it finishes, the end-of-file
one last, or none on an error. -/
def endStep : St → Location → Option (List Lexeme)
  | .idle, location => some [eofLexeme location]
  | .token p, location =>
    match finish false p location with
    | .none => some [eofLexeme location]
    | .token l => some [l, eofLexeme location]
    | .error _ => none

/-- The bytes and then the end of the input, from the state at `location`. -/
def runFrom (version : Version) (st : St) (location : Location) (bytes : List UInt8) :
    Option (List Lexeme) :=
  (feedBytes version st location bytes).bind fun (st, location, ls) =>
    (endStep st location).map (ls ++ ·)

/-- The lexemes of the whole input, or none on an error. -/
def run (version : Version) (bytes : List UInt8) : Option (List Lexeme) :=
  runFrom version .idle Location.initial bytes

/-- The lexeme as the consumer of `V1Spec.lex` records it, when it is handed over alone in a
cursor under the version. -/
def lexemeHanded (version : Version) (l : Lexeme) : Option Spec.Lexer.Handed :=
  toHanded (BatchCursor.new version l.batch) ((BatchCursor.new version l.batch).peek
    (l.hasNext version))

/-! ## Feeding in pieces -/

theorem feedBytes_append (version : Version) (st : St) (location : Location)
    (a b : List UInt8) :
    feedBytes version st location (a ++ b) =
      (feedBytes version st location a).bind fun (st', location', ls) =>
        (feedBytes version st' location' b).map fun (st'', location'', ls') =>
          (st'', location'', ls ++ ls') := by
  induction a generalizing st location with
  | nil =>
    simp only [List.nil_append, feedBytes, Option.bind_some, List.nil_append]
    cases feedBytes version st location b <;> rfl
  | cons c a ih =>
    simp only [List.cons_append, feedBytes]
    cases byteStep version st location c with
    | none => rfl
    | some r =>
      obtain ⟨st', ls⟩ := r
      simp only [ih]
      cases feedBytes version st' (location.afterByte c) a with
      | none => rfl
      | some r =>
        obtain ⟨st'', location'', ls'⟩ := r
        simp only [Option.bind_some, Option.map_some]
        cases feedBytes version st'' location'' b with
        | none => rfl
        | some r => simp [List.append_assoc]

/-! ## The hand-overs -/

/-- The lexer's state is the state of the pure run, under the version. -/
def Agrees (version : Version) (st : St) (location : Location) (core : Core) : Prop :=
  core.version = version ∧ core.activity = st.activity ∧ core.location = location

theorem handOverAt_run (core : Core) (l : Lexeme) (c : Collector) :
    (handOverAt (H := Collector) core l).run c =
      match lexemeHanded core.version l with
      | some h => ((.ok none, { core with depth := depthAfter core.depth l.category }),
          { handed := c.handed ++ [h] })
      | none => ((.error { cause := .consumer (), location := l.end },
          { core with depth := depthAfter core.depth l.category }), c) := by
  simp only [handOverAt, handOver, Consume.consume, BatchCursor.next]
  split
  next handed heq =>
    have : lexemeHanded core.version l = some handed := heq
    rw [this]
    rfl
  next heq =>
    have : lexemeHanded core.version l = none := heq
    rw [this]
    rfl

/-- The lexemes as the consumer of `V1Spec.lex` records them, or none if it fails on one. -/
def handedAll (version : Version) (ls : List Lexeme) : Option (List Spec.Lexer.Handed) :=
  ls.mapM (lexemeHanded version)

/--
`Steps version expected coll result`: a monadic step, run on the consumer `coll`, has the
`result` that the pure step predicts with `expected`: it fails if the pure step fails or the
consumer fails on a lexeme; otherwise it goes on in the predicted state, and the consumer has
recorded the lexemes.
-/
def Steps (version : Version) (expected : Option (St × Location × List Lexeme))
    (coll : Collector)
    (result : (Except (Failure Unit) (Option (Located Empty)) × Core) × Collector) : Prop :=
  match expected.bind fun (st, location, ls) =>
      (handedAll version ls).map fun hs => (st, location, hs) with
  | some (st, location, hs) =>
    result.1.1 = .ok none ∧ Agrees version st location result.1.2 ∧
      result.2.handed = coll.handed ++ hs
  | none => ∃ f, result.1.1 = .error f

/-- A step that hands over a lexeme the consumer records, and then steps as predicted. -/
theorem steps_cons {version : Version} {l : Lexeme} {x : Spec.Lexer.Handed}
    {expected : Option (St × List Lexeme)} {location : Location} {coll : Collector}
    {result : (Except (Failure Unit) (Option (Located Empty)) × Core) × Collector}
    (hl : lexemeHanded version l = some x)
    (h : Steps version (expected.map fun (st, ls) => (st, location, ls))
      { handed := coll.handed ++ [x] } result) :
    Steps version ((expected.map fun (st, ls) => (st, l :: ls)).map
      fun (st, ls) => (st, location, ls)) coll result := by
  cases expected with
  | none => exact h
  | some e =>
    obtain ⟨st, ls⟩ := e
    simp only [Steps, Option.map_some, Option.bind_some, handedAll, List.mapM_cons, hl] at h ⊢
    cases hls : ls.mapM (lexemeHanded version) with
    | none =>
      simp only [hls, Option.map_none] at h ⊢
      exact h
    | some hs =>
      simp only [hls, Option.map_some, Option.pure_def] at h ⊢
      exact ⟨h.1, h.2.1, by rw [h.2.2, List.append_assoc]; rfl⟩

/-- A step that hands over a lexeme the consumer fails on. -/
theorem steps_cons_none {version : Version} {l : Lexeme}
    {expected : Option (St × List Lexeme)} {location : Location} {coll : Collector}
    {result : (Except (Failure Unit) (Option (Located Empty)) × Core) × Collector}
    (hl : lexemeHanded version l = none) (h : ∃ f, result.1.1 = .error f) :
    Steps version ((expected.map fun (st, ls) => (st, l :: ls)).map
      fun (st, ls) => (st, location, ls)) coll result := by
  cases expected with
  | none => exact h
  | some e =>
    obtain ⟨st, ls⟩ := e
    simp only [Steps, Option.map_some, Option.bind_some, handedAll, List.mapM_cons, hl]
    exact h

theorem lexStart_run {version : Version} {location : Location} {core : Core}
    (hv : core.version = version) (hl : core.location = location) (coll : Collector)
    (c : UInt8) :
    Steps version
      ((startStep version location c).map fun (st, ls) => (st, location.afterByte c, ls))
      coll ((lexStart (H := Collector) core c).run coll) := by
  have hw : Consume.consumesWhitespaceAndComments (H := Collector) = false := rfl
  subst hv hl
  simp only [lexStart, startStep, hw]
  cases hs : start core.version false core.location c with
  | idle =>
    simp only [Steps, handedAll, Agrees, St.activity, Option.map_some, Option.bind_some,
      List.mapM_nil]
    exact ⟨rfl, ⟨rfl, rfl, rfl⟩, by simp; rfl⟩
  | pending p =>
    simp only [Steps, handedAll, Agrees, St.activity, Option.map_some, Option.bind_some,
      List.mapM_nil]
    exact ⟨rfl, ⟨rfl, rfl, rfl⟩, by simp; rfl⟩
  | token l =>
    simp only [Steps, handedAll, Agrees, St.activity, Option.map_some, Option.bind_some]
    have := handOverAt_run { core with activity := .idle, location := core.location.afterByte c }
      l coll
    simp only [StateT.run] at this
    simp only [StateT.run, this]
    cases h : lexemeHanded core.version l with
    | none => simp [h]
    | some x => simp [h]
  | error f =>
    simp only [Steps, Option.map_none, Option.bind_none]
    exact ⟨_, rfl⟩

theorem lexByte_run {version : Version} {st : St} {location : Location} {core : Core}
    (h : Agrees version st location core) (recover : Location → StateT Collector Id Unit)
    (coll : Collector) (c : UInt8) :
    Steps version
      ((byteStep version st location c).map fun (st', ls) => (st', location.afterByte c, ls))
      coll ((lexByte (H := Collector) recover core c).run coll) := by
  have hw : Consume.consumesWhitespaceAndComments (H := Collector) = false := rfl
  obtain ⟨hv, ha, hl⟩ := h
  cases st with
  | idle =>
    simp only [St.activity] at ha
    simp only [lexByte, ha, byteStep]
    exact lexStart_run hv hl coll c
  | token p =>
    simp only [St.activity] at ha
    subst hv hl
    simp only [lexByte, ha, hw, byteStep]
    cases hadv : advance false p core.location c with
    | pending p' =>
      simp only [Steps, handedAll, Agrees, St.activity, Option.map_some, Option.bind_some,
        List.mapM_nil]
      exact ⟨rfl, ⟨rfl, rfl, rfl⟩, by simp; rfl⟩
    | idle =>
      simp only [Steps, handedAll, Agrees, St.activity, Option.map_some, Option.bind_some,
        List.mapM_nil]
      exact ⟨rfl, ⟨rfl, rfl, rfl⟩, by simp; rfl⟩
    | tokenWith l =>
      simp only [Steps, handedAll, Agrees, St.activity, Option.map_some, Option.bind_some]
      have := handOverAt_run
        { core with activity := .idle, location := core.location.afterByte c } l coll
      simp only [StateT.run] at this
      simp only [StateT.run, this]
      cases h : lexemeHanded core.version l with
      | none => simp [h]
      | some x => simp [h]
    | tokenBefore l =>
      have hh := handOverAt_run { core with activity := .idle } l coll
      simp only [StateT.run] at hh ⊢
      simp only [bind, StateT.bind, hh]
      cases hlh : lexemeHanded core.version l with
      | none =>
        refine steps_cons_none hlh ?_
        exact ⟨_, rfl⟩
      | some x =>
        refine steps_cons hlh ?_
        let core' : Core := { core with activity := .idle }
        exact lexStart_run (core := { core' with depth := depthAfter core.depth l.category })
          rfl rfl _ c
    | error f =>
      simp only [Steps, Option.map_none, Option.bind_none]
      exact ⟨_, rfl⟩

/-! ## Slices -/

theorem size_toByteSlice (l : List UInt8) : l.toByteArray.toByteSlice.size = l.length := by
  simp [ByteArray.toByteSlice, ByteSlice.size, ByteSlice.stop, ByteSlice.start,
    List.size_toByteArray]

theorem getElem_toByteSlice (l : List UInt8) (i : Nat) (h : i < l.toByteArray.toByteSlice.size) :
    l.toByteArray.toByteSlice[i] = l[i]'(by rw [size_toByteSlice] at h; exact h) := by
  show ByteSlice.get _ ⟨i, h⟩ = _
  unfold ByteSlice.get
  simp only [ByteArray.toByteSlice, Nat.le_refl, Nat.zero_le, dite_true, ByteSlice.byteArray,
    ByteSlice.start, Nat.zero_add]
  exact List.getElem_toByteArray

/--
`Feeds version ok expected coll result`: a monadic call, run on the consumer `coll`, has the
`result` that the pure run predicts with `expected`: it fails if the pure run fails or the
consumer fails on a lexeme; otherwise it returns `ok` in the predicted state, and the consumer
has recorded the lexemes.
-/
def Feeds {ε α : Type} (version : Version) (ok : α)
    (expected : Option (St × Location × List Lexeme)) (coll : Collector)
    (result : (Except ε α × Core) × Collector) : Prop :=
  match expected.bind fun (st, location, ls) =>
      (handedAll version ls).map fun hs => (st, location, hs) with
  | some (st, location, hs) =>
    result.1.1 = .ok ok ∧ Agrees version st location result.1.2 ∧
      result.2.handed = coll.handed ++ hs
  | none => ∃ f, result.1.1 = .error f

theorem handedAll_append (version : Version) (ls ls' : List Lexeme) :
    handedAll version (ls ++ ls') =
      (handedAll version ls).bind fun hs => (handedAll version ls').map (hs ++ ·) := by
  simp only [handedAll, List.mapM_append]
  cases ls.mapM (lexemeHanded version) <;> cases ls'.mapM (lexemeHanded version) <;> rfl

/-- A call that follows lexemes the consumer has recorded. -/
theorem feeds_prepend {ε α : Type} {version : Version} {ok : α} {ls : List Lexeme}
    {hs : List Spec.Lexer.Handed} {expected : Option (St × Location × List Lexeme)}
    {coll coll' : Collector} {result : (Except ε α × Core) × Collector}
    (hls : handedAll version ls = some hs) (hcoll : coll'.handed = coll.handed ++ hs)
    (h : Feeds version ok expected coll' result) :
    Feeds version ok (expected.map fun (st, location, ls') => (st, location, ls ++ ls')) coll
      result := by
  cases expected with
  | none => exact h
  | some e =>
    obtain ⟨st, location, ls'⟩ := e
    simp only [Feeds, Option.map_some, Option.bind_some, handedAll_append, hls] at h ⊢
    cases hls' : handedAll version ls' with
    | none =>
      simp only [hls', Option.map_none] at h ⊢
      exact h
    | some hs' =>
      simp only [hls', Option.map_some] at h ⊢
      exact ⟨h.1, h.2.1, by rw [h.2.2, hcoll, List.append_assoc]⟩

theorem lexFrom_run {version : Version} (bytes : List UInt8)
    (recover : Location → StateT Collector Id Unit) (n : Nat) :
    ∀ (index : Nat), bytes.length - index = n → ∀ {st : St} {location : Location} {core : Core},
      Agrees version st location core → ∀ (coll : Collector),
      Feeds version (ControlFlow.continue : ControlFlow (Located Empty))
        (feedBytes version st location (bytes.drop index)) coll
        ((lexFrom (H := Collector) recover bytes.toByteArray.toByteSlice index core
          .continue).run coll) := by
  induction n with
  | zero =>
    intro index hn st location core h coll
    have hle : bytes.length ≤ index := by omega
    rw [lexFrom]
    have hns : ¬ index < bytes.toByteArray.toByteSlice.size := by
      rw [size_toByteSlice]; omega
    simp only [hns, dite_false, List.drop_eq_nil_of_le hle, feedBytes, Feeds, handedAll,
      List.mapM_nil, Option.bind_some]
    exact ⟨rfl, h, by simp; rfl⟩
  | succ n ih =>
    intro index hn st location core h coll
    have hlt : index < bytes.length := by omega
    rw [lexFrom]
    have hs : index < bytes.toByteArray.toByteSlice.size := by
      rw [size_toByteSlice]; exact hlt
    simp only [hs, dite_true, getElem_toByteSlice, List.drop_eq_getElem_cons hlt, feedBytes]
    have hb := lexByte_run h recover coll bytes[index]
    simp only [StateT.run] at hb ⊢
    simp only [bind, StateT.bind]
    generalize lexByte recover core bytes[index] coll = r at hb ⊢
    obtain ⟨⟨res, core'⟩, coll'⟩ := r
    cases hstep : byteStep version st location bytes[index] with
    | none =>
      simp only [Steps, hstep, Option.map_none, Option.bind_none] at hb
      obtain ⟨f, hf⟩ := hb
      subst hf
      exact ⟨f, rfl⟩
    | some e =>
      obtain ⟨st', ls⟩ := e
      dsimp only
      simp only [Steps, hstep, Option.map_some, Option.bind_some] at hb
      cases hls : handedAll version ls with
      | none =>
        simp only [hls, Option.map_none] at hb
        obtain ⟨f, hf⟩ := hb
        subst hf
        cases hrest : feedBytes version st' (location.afterByte bytes[index])
            (List.drop (index + 1) bytes) with
        | none =>
          simp only [Feeds, Option.map_none, Option.bind_none]
          exact ⟨f, rfl⟩
        | some e' =>
          obtain ⟨st'', location'', ls'⟩ := e'
          simp only [Feeds, Option.map_some, Option.bind_some, handedAll_append, hls,
            Option.bind_none]
          exact ⟨f, rfl⟩
      | some hs =>
        simp only [hls, Option.map_some] at hb
        obtain ⟨hok, hag, hcoll⟩ := hb
        subst hok
        exact feeds_prepend hls hcoll (ih (index + 1) (by omega) hag coll')

/-- A call that fails, whatever its error, as a call that predictably fails. -/
theorem feeds_error {ε ε' α : Type} {version : Version} {ok : α}
    {expected : Option (St × Location × List Lexeme)} {coll coll' coll'' : Collector}
    {core core' : Core} {f : ε} (f' : ε')
    (h : Feeds version ok expected coll ((.error f, core), coll')) :
    Feeds version ok expected coll ((.error f', core'), coll'') := by
  unfold Feeds at h ⊢
  split
  next heq =>
    rw [heq] at h
    exact absurd h.1 (by simp)
  next => exact ⟨f', rfl⟩

/-- A call that goes on, whatever its type of errors. -/
theorem feeds_ok {ε ε' α : Type} {version : Version} {ok : α}
    {expected : Option (St × Location × List Lexeme)} {coll coll' : Collector}
    {core : Core} {a : α} (h : Feeds (ε := ε) version ok expected coll ((.ok a, core), coll')) :
    Feeds (ε := ε') version ok expected coll ((.ok a, core), coll') := by
  unfold Feeds at h ⊢
  split
  next heq =>
    rw [heq] at h
    exact ⟨by simpa using h.1, h.2⟩
  next heq =>
    rw [heq] at h
    simp at h

theorem lexSliceStep_run {version : Version} {st : St} {location : Location} {core : Core}
    (h : Agrees version st location core) (bytes : List UInt8) (coll : Collector) :
    Feeds version (ControlFlow.continue : ControlFlow (Located Empty))
      (feedBytes version st location bytes) coll
      ((lexSliceStep (H := Collector) false (fun _ => pure ()) (fun _ => pure ())
        bytes.toByteArray.toByteSlice core).run coll) := by
  have hf := lexFrom_run bytes (fun _ => pure ()) _ 0 rfl h coll
  simp only [List.drop_zero] at hf
  have ha : core.activity = st.activity := h.2.1
  have hst : ∀ x : Activity, x = st.activity →
      (match x with | .ended => true | _ => false) = false := by
    intro x hx; subst hx; cases st <;> rfl
  simp only [StateT.run] at hf
  cases st with
  | idle =>
    simp only [St.activity] at ha
    simp only [lexSliceStep, StateT.run, ha, StateT.bind, pure, StateT.pure, bind, failCall]
    generalize lexFrom (fun _ => pure ()) bytes.toByteArray.toByteSlice 0 core .continue coll
      = r at hf ⊢
    obtain ⟨⟨res, core'⟩, coll'⟩ := r
    cases res with
    | ok a => exact feeds_ok hf
    | error f => exact feeds_error _ hf
  | token p =>
    simp only [St.activity] at ha
    simp only [lexSliceStep, StateT.run, ha, StateT.bind, pure, StateT.pure, bind, failCall]
    generalize lexFrom (fun _ => pure ()) bytes.toByteArray.toByteSlice 0 core .continue coll
      = r at hf ⊢
    obtain ⟨⟨res, core'⟩, coll'⟩ := r
    cases res with
    | ok a => exact feeds_ok hf
    | error f => exact feeds_error _ hf


/-- The end of the input, run on the consumer `coll`, has the `result` that the pure run
predicts with `expected`, as `Feeds` states for a slice. -/
def Ends {ε : Type} (version : Version) (expected : Option (List Lexeme)) (coll : Collector)
    (result : (Except ε (ControlFlow (Located Empty)) × Core) × Collector) : Prop :=
  match expected.bind (handedAll version) with
  | some hs => result.1.1 = .ok .continue ∧ result.2.handed = coll.handed ++ hs
  | none => ∃ f, result.1.1 = .error f

theorem id_bind {α β : Type} (x : α) (f : α → Id β) : (x >>= f : Id β) = f x := rfl

theorem lexEnd_run {version : Version} {st : St} {location : Location} {core : Core}
    (h : Agrees version st location core) (coll : Collector) :
    Ends version (endStep st location) coll ((lexEnd (H := Collector) core).run coll) := by
  have hw : Consume.consumesWhitespaceAndComments (H := Collector) = false := rfl
  obtain ⟨hv, ha, hl⟩ := h
  subst hv hl
  have heof : ∀ (core' : Core) (coll' : Collector),
      (handOverAt core' (eofLexeme core.location)).run coll' = _ :=
    fun core' coll' => handOverAt_run core' (eofLexeme core.location) coll'
  simp only [StateT.run] at heof
  have he : ∀ loc : Location, (⟨.endOfFile, .empty, loc, loc⟩ : Lexeme) = eofLexeme loc :=
    fun _ => rfl
  cases st with
  | idle =>
    simp only [St.activity] at ha
    simp only [lexEnd, StateT.run, ha, bind, StateT.bind, pure, StateT.pure, he, heof]
    cases hx : lexemeHanded core.version (eofLexeme core.location) with
    | none => simp [Ends, endStep, handedAll, hx]
    | some x => simp [Ends, endStep, handedAll, hx]
  | token p =>
    simp only [St.activity] at ha
    simp only [lexEnd, StateT.run, ha, hw, bind, pure, he]
    cases hf : finish false p core.location with
    | none =>
      dsimp only
      simp only [StateT.bind, StateT.pure, pure_bind]
      simp only [heof]
      cases hx : lexemeHanded core.version (eofLexeme core.location) with
      | none =>
        have e : (endStep (.token p) core.location).bind (handedAll core.version) = none := by
          simp [endStep, hf, handedAll, hx]
        unfold Ends; rw [e]
        exact ⟨_, rfl⟩
      | some x =>
        have e : (endStep (.token p) core.location).bind (handedAll core.version) = some [x] := by
          simp [endStep, hf, handedAll, hx]
        unfold Ends; rw [e]
        exact ⟨rfl, rfl⟩
    | token l =>
      have hl := handOverAt_run { core with activity := .idle } l coll
      simp only [StateT.run] at hl
      dsimp only
      simp only [StateT.bind]
      simp only [hl]
      cases hy : lexemeHanded core.version l with
      | none =>
        have e : (endStep (.token p) core.location).bind (handedAll core.version) = none := by
          simp [endStep, hf, handedAll, hy]
        unfold Ends; rw [e]
        exact ⟨_, rfl⟩
      | some y =>
        dsimp only
        simp only [id_bind]
        simp only [StateT.bind, StateT.pure, id_bind, heof]
        cases hx : lexemeHanded core.version (eofLexeme core.location) with
        | none =>
          have e : (endStep (.token p) core.location).bind (handedAll core.version) = none := by
            simp [endStep, hf, handedAll, hx, hy]
          unfold Ends; rw [e]
          exact ⟨_, rfl⟩
        | some x =>
          have e : (endStep (.token p) core.location).bind (handedAll core.version) =
              some [y, x] := by
            simp [endStep, hf, handedAll, hx, hy]
          unfold Ends; rw [e]
          exact ⟨rfl, List.append_assoc _ _ _⟩
    | error f =>
      simp only [Ends, endStep, hf]
      exact ⟨_, rfl⟩

/-- An end of the input that fails, whatever its error, as one that predictably fails. -/
theorem ends_error {ε ε' : Type} {version : Version} {expected : Option (List Lexeme)}
    {coll coll' coll'' : Collector} {core core' : Core} {f : ε} (f' : ε')
    (h : Ends version expected coll ((.error f, core), coll')) :
    Ends version expected coll ((.error f', core'), coll'') := by
  unfold Ends at h ⊢
  split
  next heq =>
    rw [heq] at h
    exact absurd h.1 (by simp)
  next => exact ⟨f', rfl⟩

/-- An end of the input that goes on, whatever its type of errors and its state after. -/
theorem ends_ok {ε ε' : Type} {version : Version} {expected : Option (List Lexeme)}
    {coll coll' : Collector} {core core' : Core} {a : ControlFlow (Located Empty)}
    (h : Ends (ε := ε) version expected coll ((.ok a, core), coll')) :
    Ends (ε := ε') version expected coll ((.ok a, core'), coll') := by
  unfold Ends at h ⊢
  split
  next heq =>
    rw [heq] at h
    exact ⟨by simpa using h.1, h.2⟩
  next heq =>
    rw [heq] at h
    simp at h

theorem lexEofStep_run {version : Version} {st : St} {location : Location} {core : Core}
    (h : Agrees version st location core) (coll : Collector) :
    Ends version (endStep st location) coll
      ((lexEofStep (H := Collector) false (fun _ => pure ()) (fun _ => pure ()) core).run
        coll) := by
  have he := lexEnd_run h coll
  have ha : core.activity = st.activity := h.2.1
  simp only [StateT.run] at he
  cases st with
  | idle =>
    simp only [St.activity] at ha
    simp only [lexEofStep, StateT.run, ha, StateT.bind, pure, StateT.pure, bind, failCall,
      Bool.false_eq_true, ↓reduceIte, Bool.not_false]
    generalize lexEnd core coll = r at he ⊢
    obtain ⟨⟨res, core'⟩, coll'⟩ := r
    cases res with
    | ok a => exact ends_ok he
    | error f => exact ends_error _ he
  | token p =>
    simp only [St.activity] at ha
    simp only [lexEofStep, StateT.run, ha, StateT.bind, pure, StateT.pure, bind, failCall,
      Bool.false_eq_true, ↓reduceIte, Bool.not_false]
    generalize lexEnd core coll = r at he ⊢
    obtain ⟨⟨res, core'⟩, coll'⟩ := r
    cases res with
    | ok a => exact ends_ok he
    | error f => exact ends_error _ he

/-! ## The lexer's calls -/

theorem lexSlice_eq (handler : Collector) (core : Core) (slice : ByteSlice) :
    (Lexer.lexSlice (⟨handler, core⟩ : Lexer Collector) slice : Id _) =
      match (lexSliceStep (H := Collector) false (fun _ => pure ()) (fun _ => pure ()) slice
          core).run handler with
      | ((.ok flow, core), handler) => .ok (flow, { handler, core })
      | ((.error err, _), _) => .error (err, ()) := by
  unfold Lexer.lexSlice
  delta Lexer.run Lexer.afterError Lexer.afterEofError
  simp only [bind, pure, StateT.run]
  rw [show (Recovery.failFast == Recovery.recovering) = false from rfl,
    show LexRecovery.abandon (H := Collector) (m := Id) Recovery.failFast =
      fun _ => StateT.pure () from rfl,
    show LexRecovery.recover (H := Collector) (m := Id) Recovery.failFast =
      fun _ => StateT.pure () from rfl]
  generalize lexSliceStep (H := Collector) false (fun _ => StateT.pure ())
    (fun _ => StateT.pure ()) slice core handler = r
  obtain ⟨⟨res, core'⟩, h'⟩ := r
  cases res <;> rfl

theorem lexEof_eq (handler : Collector) (core : Core) :
    (Lexer.lexEof (⟨handler, core⟩ : Lexer Collector) : Id _) =
      match (lexEofStep (H := Collector) false (fun _ => pure ()) (fun _ => pure ())
          core).run handler with
      | ((.ok flow, core), handler) => .ok (flow, { handler, core })
      | ((.error err, _), _) => .error (err, ()) := by
  unfold Lexer.lexEof
  delta Lexer.run Lexer.afterError Lexer.afterEofError
  simp only [bind, pure, StateT.run]
  rw [show (Recovery.failFast == Recovery.recovering) = false from rfl,
    show LexRecovery.abandon (H := Collector) (m := Id) Recovery.failFast =
      fun _ => StateT.pure () from rfl,
    show LexRecovery.recover (H := Collector) (m := Id) Recovery.failFast =
      fun _ => StateT.pure () from rfl]
  generalize lexEofStep (H := Collector) false (fun _ => StateT.pure ())
    (fun _ => StateT.pure ()) core handler = r
  obtain ⟨⟨res, core'⟩, h'⟩ := r
  cases res <;> rfl

theorem runFrom_append (version : Version) (st : St) (location : Location) (a b : List UInt8) :
    runFrom version st location (a ++ b) =
      (feedBytes version st location a).bind fun (st', location', ls) =>
        (runFrom version st' location' b).map (ls ++ ·) := by
  simp only [runFrom, feedBytes_append]
  cases feedBytes version st location a with
  | none => rfl
  | some e =>
    obtain ⟨st', location', ls⟩ := e
    simp only [Option.bind_some]
    cases feedBytes version st' location' b with
    | none => rfl
    | some e' =>
      obtain ⟨st'', location'', ls'⟩ := e'
      simp only [Option.map_some, Option.bind_some]
      cases endStep st'' location'' <;> simp [List.append_assoc]

theorem feed_eq {version : Version} (slices : List Spec.Lexicon.Chars) :
    ∀ {st : St} {location : Location} (handler : Collector) (core : Core),
      Agrees version st location core →
      feed ⟨handler, core⟩ slices =
        (runFrom version st location slices.flatten).bind fun ls =>
          (handedAll version ls).map (handler.handed ++ ·) := by
  induction slices with
  | nil =>
    intro st location handler core h
    have he := lexEofStep_run h handler
    simp only [feed, lexEof_eq, List.flatten_nil, runFrom, feedBytes, Option.bind_some,
      List.nil_append]
    generalize (lexEofStep (H := Collector) false (fun _ => pure ()) (fun _ => pure ())
      core).run handler = r at he ⊢
    obtain ⟨⟨res, core'⟩, handler'⟩ := r
    unfold Ends at he
    cases hx : (endStep st location).bind (handedAll version) with
    | none =>
      rw [hx] at he
      obtain ⟨f, hf⟩ := he
      simp only at hf
      subst hf
      cases hend : endStep st location with
      | none => rfl
      | some ls =>
        rw [hend] at hx
        simp only [Option.bind_some] at hx
        simp [hx]
    | some hs =>
      rw [hx] at he
      obtain ⟨hok, hhs⟩ := he
      simp only at hok hhs
      subst hok
      cases hend : endStep st location with
      | none => rw [hend] at hx; simp at hx
      | some ls =>
        rw [hend] at hx
        simp only [Option.bind_some] at hx
        simp [hx, hhs]
  | cons slice slices ih =>
    intro st location handler core h
    have hf := lexSliceStep_run h slice handler
    simp only [feed, lexSlice_eq, List.flatten_cons, runFrom_append]
    generalize (lexSliceStep (H := Collector) false (fun _ => pure ()) (fun _ => pure ())
      slice.toByteArray.toByteSlice core).run handler = r at hf ⊢
    obtain ⟨⟨res, core'⟩, handler'⟩ := r
    unfold Feeds at hf
    cases hx : feedBytes version st location slice with
    | none =>
      rw [hx] at hf
      obtain ⟨f, hf⟩ := hf
      simp only at hf
      subst hf
      rfl
    | some e =>
      obtain ⟨st', location', ls⟩ := e
      rw [hx] at hf
      simp only [Option.bind_some] at hf
      cases hls : handedAll version ls with
      | none =>
        rw [hls] at hf
        obtain ⟨f, hf⟩ := hf
        subst hf
        simp only [Option.bind_some]
        cases runFrom version st' location' slices.flatten with
        | none => rfl
        | some ls' => simp [handedAll_append, hls]
      | some hs =>
        rw [hls] at hf
        obtain ⟨hok, hag, hhs⟩ := hf
        subst hok
        simp only [Option.bind_some]
        rw [ih handler' core' hag]
        cases runFrom version st' location' slices.flatten with
        | none => rfl
        | some ls' =>
          simp only [Option.bind_some, Option.map_some, handedAll_append, hls, hhs]
          cases handedAll version ls' <;> simp [List.append_assoc]

/-- `V1Spec.lex` gives what the pure run of the whole input gives, as the consumer records
it, however the input is cut into slices. -/
theorem lex_eq_run (version : Spec.Lexicon.Version) (slices : List Spec.Lexicon.Chars) :
    lex version slices =
      (run (toVersion version) slices.flatten).bind (handedAll (toVersion version)) := by
  rw [lex, Lexer.new, run, feed_eq (st := .idle) slices { handed := [] }
    (Core.initial (toVersion version))
    ⟨rfl, rfl, rfl⟩]
  simp only [Core.initial, List.nil_append]
  cases runFrom (toVersion version) .idle Location.initial slices.flatten with
  | none => rfl
  | some ls => simp
