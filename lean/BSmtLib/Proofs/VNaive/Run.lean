import BSmtLib.Proofs.Adapter

/-!
# The pure run of the naive lexer

The naive lexer of `VNaive` lexes an input by a pure step over one byte at a time, and hands
each finished token over to its consumer in a monad. For the adapter's consumer `Collector`,
which takes every token and does not take whitespace and comments, this module states the
lexing as a pure run over the bytes, also up to an error (`lexBytes`), followed by the end of
the input (`endStep`; `run` for the whole input), and proves that `fedInput VNaive.ops` gives
what the run gives, before the end of the input and after it, whatever slices the input is cut
into (`fedInput_eq_run`), if the consumer takes the lexemes.
-/

namespace BSmtLib.Proofs.Lexer.VNaive

open BSmtLib.Proofs.Adapter

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

/-! ## The pure run up to an error

`feedBytes` gives none on an error. A lexer fed the bytes has handed over the lexemes finished
before the error by then; `lexBytes` gives them.
-/

/-- The lexemes that the byte `c` at `location` finishes in the state before the pure step
fails at it: the token in progress, if the byte ends it and then fails to start a token. -/
def failedBefore : St → Location → UInt8 → List Lexeme
  | .idle, _, _ => []
  | .token p, location, c =>
    match advance false p location c with
    | .tokenBefore l => [l]
    | _ => []

/-- The outcome of a pure step that ends at `location`, or on an error, the lexemes `before`
finished before it. -/
def liftStep (before : List Lexeme) (location : Location) :
    Option (St × List Lexeme) → Except (List Lexeme) (St × Location × List Lexeme)
  | some (st, ls) => .ok (st, location, ls)
  | none => .error before

/-- The run with the lexemes `ls` before the ones it finishes, also before an error. -/
def withBefore (ls : List Lexeme) :
    Except (List Lexeme) (St × Location × List Lexeme) →
      Except (List Lexeme) (St × Location × List Lexeme)
  | .ok (st, location, ls') => .ok (st, location, ls ++ ls')
  | .error ls' => .error (ls ++ ls')

/-- The bytes from the state at `location`: the state and the location after them and the
lexemes they finish, or on an error, the lexemes finished before it. -/
def lexBytes (version : Version) : St → Location → List UInt8 →
    Except (List Lexeme) (St × Location × List Lexeme)
  | st, location, [] => .ok (st, location, [])
  | st, location, c :: cs =>
    match byteStep version st location c with
    | none => .error (failedBefore st location c)
    | some (st', ls) => withBefore ls (lexBytes version st' (location.afterByte c) cs)

/-- `feedBytes` is `lexBytes` without the lexemes finished before an error. -/
theorem lexBytes_toOption (version : Version) (st : St) (location : Location)
    (bytes : List UInt8) :
    (lexBytes version st location bytes).toOption = feedBytes version st location bytes := by
  induction bytes generalizing st location with
  | nil => rfl
  | cons c bytes ih =>
    simp only [lexBytes, feedBytes]
    cases byteStep version st location c with
    | none => rfl
    | some r =>
      obtain ⟨st', ls⟩ := r
      simp only
      rw [← ih]
      cases lexBytes version st' (location.afterByte c) bytes <;> rfl

theorem withBefore_nil (e : Except (List Lexeme) (St × Location × List Lexeme)) :
    withBefore [] e = e := by
  cases e with
  | ok r => obtain ⟨st, location, ls⟩ := r; rfl
  | error ls => rfl

theorem withBefore_withBefore (ls ls' : List Lexeme)
    (e : Except (List Lexeme) (St × Location × List Lexeme)) :
    withBefore ls (withBefore ls' e) = withBefore (ls ++ ls') e := by
  cases e with
  | ok r => obtain ⟨st, location, ls''⟩ := r; simp [withBefore, List.append_assoc]
  | error ls'' => simp [withBefore, List.append_assoc]

theorem lexBytes_append (version : Version) (st : St) (location : Location)
    (a b : List UInt8) :
    lexBytes version st location (a ++ b) =
      match lexBytes version st location a with
      | .ok (st', location', ls) => withBefore ls (lexBytes version st' location' b)
      | .error ls => .error ls := by
  induction a generalizing st location with
  | nil =>
    simp only [List.nil_append, lexBytes, withBefore_nil]
  | cons c a ih =>
    simp only [List.cons_append, lexBytes]
    cases byteStep version st location c with
    | none => rfl
    | some r =>
      obtain ⟨st', ls⟩ := r
      simp only [ih]
      cases lexBytes version st' (location.afterByte c) a with
      | error ls' => rfl
      | ok r' =>
        obtain ⟨st'', location'', ls'⟩ := r'
        exact withBefore_withBefore ls ls' _

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

/-- The lexeme as the consumer `Collector` records it, when it is handed over alone in a
cursor under the version (see `toHanded_batch`). -/
def lexemeHanded (version : Version) (l : Lexeme) : Option Spec.Lexer.Handed :=
  (toTokenType l.category).map fun type =>
    { type
      start := toLocation l.start
      «end» := toLocation l.end
      reserved := match l.category with
        | .unquotedSymbol => (Reserved.fromBytes? l.content.toByteSlice version).map fun word =>
          if word.isCommandName then .command else .general
        | _ => none
      content := toContent l.content.toByteSlice }

/-- The consumer `Collector` records the lexeme handed over alone in a cursor as
`lexemeHanded` gives it. -/
theorem toHanded_batch (version : Version) (l : Lexeme) (h : l.Valid) :
    toHanded (BatchCursor.new version (l.batch h))
      ((BatchCursor.new version (l.batch h)).peek (l.hasNext h version)) =
      lexemeHanded version l := by
  have hcat : (BatchCursor.new version (l.batch h)).category
      ((BatchCursor.new version (l.batch h)).peek (l.hasNext h version)) = l.category := by
    obtain ⟨category, content, start, «end»⟩ := l
    cases category <;> rfl
  have hstart : ((BatchCursor.new version (l.batch h)).span
      ((BatchCursor.new version (l.batch h)).peek (l.hasNext h version))).start = l.start := rfl
  have hend : ((BatchCursor.new version (l.batch h)).span
      ((BatchCursor.new version (l.batch h)).peek (l.hasNext h version))).end = l.end := rfl
  have hcontent : (BatchCursor.new version (l.batch h)).content
      ((BatchCursor.new version (l.batch h)).peek (l.hasNext h version)) =
        l.content.toByteSlice := rfl
  have hversion : (BatchCursor.new version (l.batch h)).version = version := rfl
  unfold lexemeHanded toHanded
  simp only [BatchCursor.syntax, SyntaxToken.fromToken, hcat, hstart, hend, hcontent, hversion]
  cases hc : l.category <;> simp [toTokenType, toReservedKind]
  cases Reserved.fromBytes? l.content.toByteSlice version <;> rfl

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

theorem handOverAt_run (core : Core) (l : Lexeme) (hl : l.Valid) (c : Collector) :
    (handOverAt (H := Collector) core l hl).run c =
      match lexemeHanded core.version l with
      | some h => ((.ok none, { core with depth := depthAfter core.depth l.category }),
          { handed := c.handed ++ [h] })
      | none => ((.error { cause := .consumer (), location := l.end },
          { core with depth := depthAfter core.depth l.category }), c) := by
  have hnone :
      ¬ ((BatchCursor.new core.version (l.batch hl)).next
        (l.hasNext hl core.version)).2.1.HasNext :=
    Nat.lt_irrefl _
  have ht : takeRest ((BatchCursor.new core.version (l.batch hl)).next
      (l.hasNext hl core.version)).2.1 = (some [], ⟨_, .refl _⟩) := by
    rw [takeRest]
    simp only [hnone, dite_false]
  have hk : toHanded (BatchCursor.new core.version (l.batch hl))
      ((BatchCursor.new core.version (l.batch hl)).next (l.hasNext hl core.version)).1 =
      lexemeHanded core.version l := toHanded_batch core.version l hl
  simp only [handOverAt, handOver, Consume.consume]
  rw [ht, hk]
  cases lexemeHanded core.version l <;> rfl

/-- The lexemes as the consumer `Collector` records them, or none if it fails on one. -/
def handedAll (version : Version) (ls : List Lexeme) : Option (List Spec.Lexer.Handed) :=
  ls.mapM (lexemeHanded version)

/--
`Lexes version ok expected coll result`: a monadic call, run on the consumer `coll`, has the
`result` that the pure run predicts with `expected`. If the pure run goes on, the call returns
`ok` in the predicted state and the consumer has recorded the lexemes, unless it fails on one of
them, when the call fails. If the pure run fails, the call fails, and the consumer has recorded
the lexemes finished before the failure, if it takes them.
-/
def Lexes {ε α : Type} (version : Version) (ok : α)
    (expected : Except (List Lexeme) (St × Location × List Lexeme)) (coll : Collector)
    (result : (Except ε α × Core) × Collector) : Prop :=
  match expected with
  | .ok (st, location, ls) =>
    match handedAll version ls with
    | some hs =>
      result.1.1 = .ok ok ∧ Agrees version st location result.1.2 ∧
        result.2.handed = coll.handed ++ hs
    | none => ∃ f, result.1.1 = .error f
  | .error ls =>
    (∃ f, result.1.1 = .error f) ∧
      ∀ hs, handedAll version ls = some hs → result.2.handed = coll.handed ++ hs

theorem handedAll_cons_some {version : Version} {l : Lexeme} {x : Spec.Lexer.Handed}
    (hl : lexemeHanded version l = some x) (ls : List Lexeme) :
    handedAll version (l :: ls) = (handedAll version ls).map (x :: ·) := by
  simp only [handedAll, List.mapM_cons, hl]
  cases ls.mapM (lexemeHanded version) <;> rfl

theorem handedAll_cons_none {version : Version} {l : Lexeme}
    (hl : lexemeHanded version l = none) (ls : List Lexeme) :
    handedAll version (l :: ls) = none := by
  simp only [handedAll, List.mapM_cons, hl]
  rfl

theorem handedAll_nil (version : Version) : handedAll version [] = some [] := rfl

/-- A step that hands over a lexeme the consumer records, and then steps as predicted. -/
theorem lexes_cons {version : Version} {l : Lexeme} {x : Spec.Lexer.Handed}
    {expected : Option (St × List Lexeme)} {location : Location} {coll : Collector}
    {result : (Except (Failure Unit) (Option (Located Empty)) × Core) × Collector}
    (hl : lexemeHanded version l = some x)
    (h : Lexes version (none : Option (Located Empty)) (liftStep [] location expected)
      { handed := coll.handed ++ [x] } result) :
    Lexes version (none : Option (Located Empty))
      (liftStep [l] location (expected.map fun (st, ls) => (st, l :: ls))) coll result := by
  cases expected with
  | none =>
    simp only [Lexes, liftStep, Option.map_none, handedAll_cons_some hl, handedAll_nil,
      Option.map_some] at h ⊢
    obtain ⟨hf, hh⟩ := h
    refine ⟨hf, fun hs hhs => ?_⟩
    simp only [Option.some.injEq] at hhs
    rw [hh [] rfl, ← hhs]
    simp
  | some e =>
    obtain ⟨st, ls⟩ := e
    simp only [Lexes, liftStep, Option.map_some, handedAll_cons_some hl] at h ⊢
    cases hls : handedAll version ls with
    | none =>
      simp only [hls, Option.map_none] at h ⊢
      exact h
    | some hs =>
      simp only [hls, Option.map_some] at h ⊢
      exact ⟨h.1, h.2.1, by rw [h.2.2, List.append_assoc]; rfl⟩

/-- A step that hands over a lexeme the consumer fails on. -/
theorem lexes_cons_none {version : Version} {l : Lexeme}
    {expected : Option (St × List Lexeme)} {location : Location} {coll : Collector}
    {result : (Except (Failure Unit) (Option (Located Empty)) × Core) × Collector}
    (hl : lexemeHanded version l = none) (h : ∃ f, result.1.1 = .error f) :
    Lexes version (none : Option (Located Empty))
      (liftStep [l] location (expected.map fun (st, ls) => (st, l :: ls))) coll result := by
  cases expected with
  | none =>
    simp only [Lexes, liftStep, Option.map_none, handedAll_cons_none hl]
    exact ⟨h, fun _ hhs => nomatch hhs⟩
  | some e =>
    obtain ⟨st, ls⟩ := e
    simp only [Lexes, liftStep, Option.map_some, handedAll_cons_none hl]
    exact h

theorem lexStart_run {version : Version} {location : Location} {core : Core}
    (hv : core.version = version) (hl : core.location = location) (coll : Collector)
    (c : UInt8) :
    Lexes version (none : Option (Located Empty))
      (liftStep [] (location.afterByte c) (startStep version location c))
      coll ((lexStart (H := Collector) core c).run coll) := by
  have hw : Consume.consumesWhitespaceAndComments (H := Collector) = false := rfl
  subst hv hl
  simp only [lexStart, startStep, hw]
  cases hs : start core.version false core.location c with
  | idle =>
    simp only [startS, hs]
    simp only [Lexes, liftStep, handedAll, Agrees, St.activity, List.mapM_nil]
    exact ⟨rfl, ⟨rfl, rfl, rfl⟩, by simp; rfl⟩
  | pending p =>
    simp only [startS, hs]
    simp only [Lexes, liftStep, handedAll, Agrees, St.activity, List.mapM_nil]
    exact ⟨rfl, ⟨rfl, rfl, rfl⟩, by simp; rfl⟩
  | token l =>
    simp only [startS, hs]
    simp only [Lexes, liftStep]
    have := handOverAt_run
      { core with
        activity := .idle, location := core.location.afterByte c, startedBefore := trivial }
      l (start_token hs) coll
    simp only [StateT.run] at this
    simp only [StateT.run, this]
    cases h : lexemeHanded core.version l with
    | none => simp [handedAll_cons_none h]
    | some x => simp [handedAll_cons_some h, handedAll_nil, Agrees, St.activity]
  | error f =>
    simp only [startS, hs]
    simp only [Lexes, liftStep]
    exact ⟨⟨_, rfl⟩, fun hs hhs => by
      simp only [handedAll_nil, Option.some.injEq] at hhs
      subst hhs
      simp
      rfl⟩

theorem lexByte_run {version : Version} {st : St} {location : Location} {core : Core}
    (h : Agrees version st location core) (recover : Location → StateT Collector Id Unit)
    (coll : Collector) (c : UInt8) :
    Lexes version (none : Option (Located Empty))
      (liftStep (failedBefore st location c) (location.afterByte c)
        (byteStep version st location c))
      coll ((lexByte (H := Collector) recover core c).run coll) := by
  have hw : Consume.consumesWhitespaceAndComments (H := Collector) = false := rfl
  obtain ⟨hv, ha, hl⟩ := h
  cases st with
  | idle =>
    simp only [St.activity] at ha
    simp only [lexByte, withEq, ha, byteStep, failedBefore]
    exact lexStart_run hv hl coll c
  | token p =>
    simp only [St.activity] at ha
    subst hv hl
    have hp : p.start.offset < core.location.offset := core.started ha
    simp only [lexByte, withEq, ha, hw, byteStep, failedBefore]
    cases hadv : advance false p core.location c with
    | pending p' =>
      simp only [advanceS, hadv]
      simp only [Lexes, liftStep, handedAll, Agrees, St.activity, List.mapM_nil]
      exact ⟨rfl, ⟨rfl, rfl, rfl⟩, by simp; rfl⟩
    | idle =>
      simp only [advanceS, hadv]
      simp only [Lexes, liftStep, handedAll, Agrees, St.activity, List.mapM_nil]
      exact ⟨rfl, ⟨rfl, rfl, rfl⟩, by simp; rfl⟩
    | tokenWith l =>
      simp only [advanceS, hadv]
      simp only [Lexes, liftStep]
      have := handOverAt_run
        { core with
          activity := .idle, location := core.location.afterByte c, startedBefore := trivial }
        l (.inl (by
          rw [(advance_tokenWith hadv).1, (advance_tokenWith hadv).2, afterByte_offset]; omega))
        coll
      simp only [StateT.run] at this
      simp only [StateT.run, this]
      cases h : lexemeHanded core.version l with
      | none => simp [handedAll_cons_none h]
      | some x => simp [handedAll_cons_some h, handedAll_nil, Agrees, St.activity]
    | tokenBefore l =>
      simp only [advanceS, hadv]
      have hh := handOverAt_run { core with activity := .idle, startedBefore := trivial } l
        (.inl (by rw [(advance_tokenBefore hadv).1, (advance_tokenBefore hadv).2]; exact hp)) coll
      simp only [StateT.run] at hh ⊢
      simp only [bind, StateT.bind, hh]
      cases hlh : lexemeHanded core.version l with
      | none =>
        refine lexes_cons_none hlh ?_
        exact ⟨_, rfl⟩
      | some x =>
        refine lexes_cons hlh ?_
        let core' : Core := { core with activity := .idle, startedBefore := trivial }
        exact lexStart_run (core := { core' with depth := depthAfter core.depth l.category })
          rfl rfl _ c
    | error f =>
      simp only [advanceS, hadv]
      simp only [Lexes, liftStep]
      exact ⟨⟨_, rfl⟩, fun hs hhs => by
        simp only [handedAll_nil, Option.some.injEq] at hhs
        subst hhs
        simp
        rfl⟩

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
theorem lexes_withBefore {ε α : Type} {version : Version} {ok : α} {ls : List Lexeme}
    {hs : List Spec.Lexer.Handed} {expected : Except (List Lexeme) (St × Location × List Lexeme)}
    {coll coll' : Collector} {result : (Except ε α × Core) × Collector}
    (hls : handedAll version ls = some hs) (hcoll : coll'.handed = coll.handed ++ hs)
    (h : Lexes version ok expected coll' result) :
    Lexes version ok (withBefore ls expected) coll result := by
  cases expected with
  | ok e =>
    obtain ⟨st, location, ls'⟩ := e
    simp only [Lexes, withBefore, handedAll_append, hls, Option.bind_some] at h ⊢
    cases hls' : handedAll version ls' with
    | none =>
      simp only [hls', Option.map_none] at h ⊢
      exact h
    | some hs' =>
      simp only [hls', Option.map_some] at h ⊢
      exact ⟨h.1, h.2.1, by rw [h.2.2, hcoll, List.append_assoc]⟩
  | error ls' =>
    simp only [Lexes, withBefore, handedAll_append, hls, Option.bind_some] at h ⊢
    refine ⟨h.1, fun hs'' hhs => ?_⟩
    cases hls' : handedAll version ls' with
    | none => simp [hls'] at hhs
    | some hs' =>
      simp only [hls', Option.map_some, Option.some.injEq] at hhs
      rw [h.2 hs' hls', hcoll, ← hhs, List.append_assoc]

theorem lexFrom_run {version : Version} (bytes : List UInt8)
    (recover : Location → StateT Collector Id Unit) (n : Nat) :
    ∀ (index : Nat), bytes.length - index = n → ∀ {st : St} {location : Location} {core : Core},
      Agrees version st location core → ∀ (coll : Collector),
      Lexes version (ControlFlow.continue : ControlFlow (Located Empty))
        (lexBytes version st location (bytes.drop index)) coll
        ((lexFrom (H := Collector) recover bytes.toByteArray.toByteSlice index core
          .continue).run coll) := by
  induction n with
  | zero =>
    intro index hn st location core h coll
    have hle : bytes.length ≤ index := by omega
    rw [lexFrom]
    have hns : ¬ index < bytes.toByteArray.toByteSlice.size := by
      rw [size_toByteSlice]; omega
    simp only [hns, dite_false, List.drop_eq_nil_of_le hle, lexBytes, Lexes, handedAll,
      List.mapM_nil]
    exact ⟨rfl, h, by simp; rfl⟩
  | succ n ih =>
    intro index hn st location core h coll
    have hlt : index < bytes.length := by omega
    rw [lexFrom]
    have hs : index < bytes.toByteArray.toByteSlice.size := by
      rw [size_toByteSlice]; exact hlt
    simp only [hs, dite_true, getElem_toByteSlice, List.drop_eq_getElem_cons hlt, lexBytes]
    have hb := lexByte_run h recover coll bytes[index]
    simp only [StateT.run] at hb ⊢
    simp only [bind, StateT.bind]
    generalize lexByte recover core bytes[index] coll = r at hb ⊢
    obtain ⟨⟨res, core'⟩, coll'⟩ := r
    cases hstep : byteStep version st location bytes[index] with
    | none =>
      simp only [Lexes, liftStep, hstep] at hb
      obtain ⟨⟨f, hf⟩, hh⟩ := hb
      subst hf
      exact ⟨⟨f, rfl⟩, hh⟩
    | some e =>
      obtain ⟨st', ls⟩ := e
      dsimp only
      simp only [Lexes, liftStep, hstep] at hb
      cases hls : handedAll version ls with
      | none =>
        simp only [hls] at hb
        obtain ⟨f, hf⟩ := hb
        subst hf
        cases hrest : lexBytes version st' (location.afterByte bytes[index])
            (List.drop (index + 1) bytes) with
        | ok e' =>
          obtain ⟨st'', location'', ls'⟩ := e'
          simp only [Lexes, withBefore, handedAll_append, hls, Option.bind_none]
          exact ⟨f, rfl⟩
        | error ls' =>
          simp only [Lexes, withBefore, handedAll_append, hls, Option.bind_none]
          exact ⟨⟨f, rfl⟩, fun _ hhs => nomatch hhs⟩
      | some hs =>
        simp only [hls] at hb
        obtain ⟨hok, hag, hcoll⟩ := hb
        subst hok
        exact lexes_withBefore hls hcoll (ih (index + 1) (by omega) hag coll')

/-- A call that fails, whatever its error, as a call that predictably fails. -/
theorem lexes_error {ε ε' α : Type} {version : Version} {ok : α}
    {expected : Except (List Lexeme) (St × Location × List Lexeme)} {coll coll' : Collector}
    {core core' : Core} {f : ε} (f' : ε')
    (h : Lexes version ok expected coll ((.error f, core), coll')) :
    Lexes version ok expected coll ((.error f', core'), coll') := by
  unfold Lexes at h ⊢
  split
  next =>
    split
    next heq =>
      simp only [heq] at h
      exact absurd h.1 (by simp)
    next => exact ⟨f', rfl⟩
  next => exact ⟨⟨f', rfl⟩, h.2⟩

/-- A call that goes on, whatever its type of errors. -/
theorem lexes_ok {ε ε' α : Type} {version : Version} {ok : α}
    {expected : Except (List Lexeme) (St × Location × List Lexeme)} {coll coll' : Collector}
    {core : Core} {a : α} (h : Lexes (ε := ε) version ok expected coll ((.ok a, core), coll')) :
    Lexes (ε := ε') version ok expected coll ((.ok a, core), coll') := by
  unfold Lexes at h ⊢
  split
  next =>
    split
    next heq =>
      simp only [heq] at h
      exact ⟨by simpa using h.1, h.2⟩
    next heq =>
      simp only [heq] at h
      simp at h
  next => simp at h

/-- A call that lexes a slice, from the lexer state that is the pure state at `location`, lexes
it as the pure run over its bytes, also up to an error. -/
theorem lexSliceStep_lexes {version : Version} {st : St} {location : Location} {core : Core}
    (h : Agrees version st location core) (bytes : List UInt8) (coll : Collector) :
    Lexes version (ControlFlow.continue : ControlFlow (Located Empty))
      (lexBytes version st location bytes) coll
      ((lexSliceStep (H := Collector) false (fun _ => pure ()) (fun _ => pure ())
        bytes.toByteArray.toByteSlice core).run coll) := by
  have hf := lexFrom_run bytes (fun _ => pure ()) _ 0 rfl h coll
  simp only [List.drop_zero] at hf
  have ha : core.activity = st.activity := h.2.1
  simp only [StateT.run] at hf
  cases st with
  | idle =>
    simp only [St.activity] at ha
    simp only [lexSliceStep, StateT.run, ha, StateT.bind, pure, StateT.pure, bind, failCall]
    generalize lexFrom (fun _ => pure ()) bytes.toByteArray.toByteSlice 0 core .continue coll
      = r at hf ⊢
    obtain ⟨⟨res, core'⟩, coll'⟩ := r
    cases res with
    | ok a => exact lexes_ok hf
    | error f => exact lexes_error _ hf
  | token p =>
    simp only [St.activity] at ha
    simp only [lexSliceStep, StateT.run, ha, StateT.bind, pure, StateT.pure, bind, failCall]
    generalize lexFrom (fun _ => pure ()) bytes.toByteArray.toByteSlice 0 core .continue coll
      = r at hf ⊢
    obtain ⟨⟨res, core'⟩, coll'⟩ := r
    cases res with
    | ok a => exact lexes_ok hf
    | error f => exact lexes_error _ hf

/-- What a call predicts up to an error, without the error's lexemes. -/
theorem feeds_of_lexes {ε α : Type} {version : Version} {ok : α}
    {expected : Except (List Lexeme) (St × Location × List Lexeme)} {coll : Collector}
    {result : (Except ε α × Core) × Collector} (h : Lexes version ok expected coll result) :
    Feeds version ok expected.toOption coll result := by
  cases expected with
  | ok e =>
    obtain ⟨st, location, ls⟩ := e
    simp only [Lexes] at h
    simp only [Feeds, Except.toOption, Option.bind_some]
    cases hls : handedAll version ls with
    | none => simp only [hls] at h ⊢; exact h
    | some hs => simp only [hls] at h ⊢; exact h
  | error ls =>
    simp only [Lexes] at h
    simp only [Feeds, Except.toOption, Option.bind_none]
    exact h.1

theorem lexSliceStep_run {version : Version} {st : St} {location : Location} {core : Core}
    (h : Agrees version st location core) (bytes : List UInt8) (coll : Collector) :
    Feeds version (ControlFlow.continue : ControlFlow (Located Empty))
      (feedBytes version st location bytes) coll
      ((lexSliceStep (H := Collector) false (fun _ => pure ()) (fun _ => pure ())
        bytes.toByteArray.toByteSlice core).run coll) := by
  rw [← lexBytes_toOption]
  exact feeds_of_lexes (lexSliceStep_lexes h bytes coll)

/-- The end of the input, run on the consumer `coll`, has the `result` that the pure run
predicts with `expected`, as `Feeds` states for a slice. If the pure run fails, the call fails
and the consumer has recorded nothing more. -/
def Ends {ε : Type} (version : Version) (expected : Option (List Lexeme)) (coll : Collector)
    (result : (Except ε (ControlFlow (Located Empty)) × Core) × Collector) : Prop :=
  match expected with
  | none => (∃ f, result.1.1 = .error f) ∧ result.2.handed = coll.handed
  | some ls =>
    match handedAll version ls with
    | some hs => result.1.1 = .ok .continue ∧ result.2.handed = coll.handed ++ hs
    | none => ∃ f, result.1.1 = .error f

theorem ends_some_some {ε : Type} {version : Version} {ls : List Lexeme}
    {hs : List Spec.Lexer.Handed} {coll : Collector}
    {result : (Except ε (ControlFlow (Located Empty)) × Core) × Collector}
    (h : handedAll version ls = some hs) :
    Ends version (some ls) coll result ↔
      result.1.1 = .ok .continue ∧ result.2.handed = coll.handed ++ hs := by
  simp only [Ends, h]

theorem ends_some_none {ε : Type} {version : Version} {ls : List Lexeme} {coll : Collector}
    {result : (Except ε (ControlFlow (Located Empty)) × Core) × Collector}
    (h : handedAll version ls = none) :
    Ends version (some ls) coll result ↔ ∃ f, result.1.1 = .error f := by
  simp only [Ends, h]

theorem id_bind {α β : Type} (x : α) (f : α → Id β) : (x >>= f : Id β) = f x := rfl

theorem lexEnd_run {version : Version} {st : St} {location : Location} {core : Core}
    (h : Agrees version st location core) (coll : Collector) :
    Ends version (endStep st location) coll ((lexEnd (H := Collector) core).run coll) := by
  have hw : Consume.consumesWhitespaceAndComments (H := Collector) = false := rfl
  obtain ⟨hv, ha, hl⟩ := h
  subst hv hl
  have heof : ∀ (core' : Core) (coll' : Collector)
      (hv : Lexeme.Valid ⟨.endOfFile, .empty, core.location, core.location⟩),
      (handOverAt core' ⟨.endOfFile, .empty, core.location, core.location⟩ hv).run coll' = _ :=
    fun core' coll' hv => handOverAt_run core' (eofLexeme core.location) hv coll'
  simp only [StateT.run] at heof
  have he : ∀ loc : Location, (⟨.endOfFile, .empty, loc, loc⟩ : Lexeme) = eofLexeme loc :=
    fun _ => rfl
  cases st with
  | idle =>
    simp only [St.activity] at ha
    simp only [lexEnd, withEq, StateT.run, ha, bind, StateT.bind, pure, StateT.pure, heof]
    cases hx : lexemeHanded core.version (eofLexeme core.location) with
    | none => simp [Ends, endStep, handedAll, hx]
    | some x => simp [Ends, endStep, handedAll, hx]
  | token p =>
    simp only [St.activity] at ha
    simp only [lexEnd, withEq, StateT.run, ha, hw, bind, pure]
    cases hf : finish false p core.location with
    | none =>
      simp only [finishS, hf]
      try dsimp only
      simp only [StateT.bind, StateT.pure, pure_bind]
      simp only [heof]
      have e : endStep (.token p) core.location = some [eofLexeme core.location] := by
        simp [endStep, hf]
      rw [e]
      cases hx : lexemeHanded core.version (eofLexeme core.location) with
      | none =>
        rw [ends_some_none (by simp [handedAll, hx])]
        exact ⟨_, rfl⟩
      | some x =>
        rw [ends_some_some (hs := [x]) (by simp [handedAll, hx])]
        exact ⟨rfl, rfl⟩
    | token l =>
      simp only [finishS, hf]
      have hl := handOverAt_run { core with activity := .idle, startedBefore := trivial } l
        (.inl (by rw [(finish_token hf).1, (finish_token hf).2]; exact core.started ha)) coll
      simp only [StateT.run] at hl
      try dsimp only
      simp only [StateT.bind]
      simp only [hl]
      have e : endStep (.token p) core.location = some [l, eofLexeme core.location] := by
        simp [endStep, hf]
      rw [e]
      cases hy : lexemeHanded core.version l with
      | none =>
        rw [ends_some_none (by simp [handedAll, hy])]
        exact ⟨_, rfl⟩
      | some y =>
        dsimp only
        simp only [id_bind]
        simp only [StateT.bind, StateT.pure, id_bind, heof]
        cases hx : lexemeHanded core.version (eofLexeme core.location) with
        | none =>
          rw [ends_some_none (by simp [handedAll, hx, hy])]
          exact ⟨_, rfl⟩
        | some x =>
          rw [ends_some_some (hs := [y, x]) (by simp [handedAll, hx, hy])]
          exact ⟨rfl, List.append_assoc _ _ _⟩
    | error f =>
      simp only [finishS, hf]
      simp only [Ends, endStep, hf]
      exact ⟨⟨_, rfl⟩, rfl⟩

/-- An end of the input that fails, whatever its error, as one that predictably fails. -/
theorem ends_error {ε ε' : Type} {version : Version} {expected : Option (List Lexeme)}
    {coll coll' : Collector} {core core' : Core} {f : ε} (f' : ε')
    (h : Ends version expected coll ((.error f, core), coll')) :
    Ends version expected coll ((.error f', core'), coll') := by
  cases expected with
  | none => exact ⟨⟨f', rfl⟩, h.2⟩
  | some ls =>
    cases hh : handedAll version ls with
    | none => exact (ends_some_none hh).mpr ⟨f', rfl⟩
    | some hs =>
      have := ((ends_some_some hh).mp h).1
      cases this

/-- An end of the input that goes on, whatever its type of errors and its state after. -/
theorem ends_ok {ε ε' : Type} {version : Version} {expected : Option (List Lexeme)}
    {coll coll' : Collector} {core core' : Core} {a : ControlFlow (Located Empty)}
    (h : Ends (ε := ε) version expected coll ((.ok a, core), coll')) :
    Ends (ε := ε') version expected coll ((.ok a, core'), coll') := by
  cases expected with
  | none =>
    obtain ⟨f, hf⟩ := h.1
    cases hf
  | some ls =>
    cases hh : handedAll version ls with
    | none =>
      obtain ⟨f, hf⟩ := (ends_some_none hh).mp h
      cases hf
    | some hs =>
      have h' := (ends_some_some hh).mp h
      exact (ends_some_some hh).mpr ⟨by simpa using h'.1, h'.2⟩

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

/-! ## The slices and the end of the input -/

/-- What the consumer has recorded after the pure run over the bytes and then, if the input has
ended and the run has not failed, the end of the input, as it records the lexemes, and whether
the run failed; none if the consumer fails on a lexeme. -/
def fedOf (version : Version) (ended : Bool) :
    Except (List Lexeme) (St × Location × List Lexeme) → Option (List Spec.Lexer.Handed × Bool)
  | .ok (st, location, ls) =>
    if ended then
      match endStep st location with
      | some ls' => (handedAll version (ls ++ ls')).map (·, false)
      | none => (handedAll version ls).map (·, true)
    else
      (handedAll version ls).map (·, false)
  | .error ls => (handedAll version ls).map (·, true)

theorem fedOf_withBefore {version : Version} {ended : Bool} {ls : List Lexeme}
    {hs : List Spec.Lexer.Handed} (hls : handedAll version ls = some hs)
    (e : Except (List Lexeme) (St × Location × List Lexeme)) :
    fedOf version ended (withBefore ls e) =
      (fedOf version ended e).map fun (hs', b) => (hs ++ hs', b) := by
  cases e with
  | ok r =>
    obtain ⟨st, location, ls'⟩ := r
    cases ended with
    | false =>
      simp only [withBefore, fedOf, Bool.false_eq_true, ↓reduceIte, handedAll_append, hls,
        Option.bind_some]
      cases handedAll version ls' <;> rfl
    | true =>
      simp only [withBefore, fedOf, ↓reduceIte]
      cases endStep st location with
      | none =>
        simp only [handedAll_append, hls, Option.bind_some]
        cases handedAll version ls' <;> rfl
      | some ls'' =>
        dsimp only
        rw [List.append_assoc, handedAll_append version ls, hls, Option.bind_some]
        cases handedAll version (ls' ++ ls'') <;> rfl
  | error ls' =>
    simp only [withBefore, fedOf, handedAll_append, hls, Option.bind_some]
    cases handedAll version ls' <;> rfl

theorem ops_lexSliceStep (handler : Collector) (core : Core) (slice : ByteSlice) :
    VNaive.ops.lexSliceStep ⟨handler, core⟩ slice =
      match (lexSliceStep (H := Collector) false (fun _ => pure ()) (fun _ => pure ()) slice
          core).run handler with
      | ((res, core), handler) => (res, ⟨handler, core⟩) := rfl

theorem ops_lexEofStep (handler : Collector) (core : Core) :
    VNaive.ops.lexEofStep ⟨handler, core⟩ =
      match (lexEofStep (H := Collector) false (fun _ => pure ()) (fun _ => pure ())
          core).run handler with
      | ((res, core), handler) => (res, ⟨handler, core⟩) := rfl

/-- The naive lexer fed the end of the input by the step of `lexEof`, from the pure state at
`location`, has recorded what the pure end of the input finishes, and has failed exactly when
it fails, if the consumer takes the lexemes. -/
theorem feedEnd_eq {version : Version} {st : St} {location : Location} (handler : Collector)
    (core : Core) (hag : Agrees version st location core) (hs : List Spec.Lexer.Handed)
    (failed : Bool)
    (h : fedOf version true (.ok (st, location, [])) = some (hs, failed)) :
    (feedEnd VNaive.ops ⟨handler, core⟩).1.handed = handler.handed ++ hs ∧
      (feedEnd VNaive.ops ⟨handler, core⟩).2 = failed := by
  have he := lexEofStep_run hag handler
  simp only [feedEnd, ops_lexEofStep]
  generalize (lexEofStep (H := Collector) false (fun _ => pure ()) (fun _ => pure ())
    core).run handler = r at he ⊢
  obtain ⟨⟨res, core'⟩, handler'⟩ := r
  simp only [fedOf, ↓reduceIte, List.nil_append] at h
  cases hend : endStep st location with
  | none =>
    rw [hend] at he h
    dsimp only at h
    simp only [handedAll_nil, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    obtain ⟨⟨f, hf⟩, hh⟩ := he
    simp only at hf
    subst hf
    exact ⟨by rw [List.append_nil]; exact hh, rfl⟩
  | some ls =>
    rw [hend] at he h
    dsimp only at h
    cases hls : handedAll version ls with
    | none => rw [hls] at h; cases h
    | some hs' =>
      rw [hls] at h
      simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      obtain ⟨hok, hh⟩ := (ends_some_some hls).mp he
      simp only at hok
      subst hok
      exact ⟨hh, rfl⟩

/-- The naive lexer fed the slices by the step of `lexSlice` and then, if the input has ended,
the end of the input by the step of `lexEof`, from the pure state at `location`, has recorded
what the pure run over their bytes and then the pure end of the input finish, also up to an
error, and has failed exactly when the run fails, if the consumer takes the lexemes. -/
theorem feedInput_eq {version : Version} (ended : Bool) (slices : List Spec.Lexicon.Chars) :
    ∀ {st : St} {location : Location} (handler : Collector) (core : Core),
      Agrees version st location core → ∀ hs failed,
      fedOf version ended (lexBytes version st location slices.flatten) = some (hs, failed) →
      (feedInput VNaive.ops ⟨handler, core⟩ ended slices).1.handed = handler.handed ++ hs ∧
        (feedInput VNaive.ops ⟨handler, core⟩ ended slices).2 = failed := by
  induction slices with
  | nil =>
    intro st location handler core hag hs failed h
    simp only [List.flatten_nil, lexBytes] at h
    cases ended with
    | true => exact feedEnd_eq handler core hag hs failed h
    | false =>
      simp only [fedOf, Bool.false_eq_true, ↓reduceIte, handedAll_nil, Option.map_some,
        Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨by simp; rfl, rfl⟩
  | cons slice slices ih =>
    intro st location handler core hag hs failed h
    have hf := lexSliceStep_lexes hag slice handler
    simp only [feedInput, ops_lexSliceStep]
    rw [List.flatten_cons, lexBytes_append] at h
    generalize (lexSliceStep (H := Collector) false (fun _ => pure ()) (fun _ => pure ())
      slice.toByteArray.toByteSlice core).run handler = r at hf ⊢
    obtain ⟨⟨res, core'⟩, handler'⟩ := r
    cases hx : lexBytes version st location slice with
    | error ls =>
      rw [hx] at hf h
      obtain ⟨⟨f, hres⟩, hh⟩ := hf
      simp only at hres
      subst hres
      cases hls : handedAll version ls with
      | none => simp [fedOf, hls] at h
      | some hs' =>
        simp only [fedOf, hls, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact ⟨hh hs' hls, rfl⟩
    | ok e =>
      obtain ⟨st', location', ls⟩ := e
      rw [hx] at hf h
      simp only at h
      simp only [Lexes] at hf
      cases hls : handedAll version ls with
      | none =>
        have : ∀ e : Except (List Lexeme) (St × Location × List Lexeme),
            fedOf version ended (withBefore ls e) = none := by
          intro e
          cases e with
          | ok r =>
            obtain ⟨st'', location'', ls'⟩ := r
            cases ended with
            | false => simp [withBefore, fedOf, handedAll_append, hls]
            | true =>
              simp only [withBefore, fedOf, ↓reduceIte]
              cases endStep st'' location'' <;>
                simp [List.append_assoc, handedAll_append, hls]
          | error ls' => simp [withBefore, fedOf, handedAll_append, hls]
        rw [this] at h
        cases h
      | some hs1 =>
        simp only [hls] at hf
        obtain ⟨hres, hag', hh⟩ := hf
        subst hres
        rw [fedOf_withBefore hls] at h
        cases e' : fedOf version ended (lexBytes version st' location' slices.flatten) with
        | none => rw [e'] at h; simp at h
        | some r =>
          obtain ⟨hs2, b⟩ := r
          rw [e'] at h
          simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          obtain ⟨h1, h2⟩ := ih handler' core' hag' hs2 b e'
          refine ⟨?_, h2⟩
          rw [h1, hh, List.append_assoc]

/-- `fedInput VNaive.ops` gives what the pure run of the bytes of the slices and then, if the
input has ended, the pure end of the input give, also up to an error, if the consumer takes the
lexemes. -/
theorem fedInput_eq_run (version : Spec.Lexicon.Version) (slices : List Spec.Lexicon.Chars)
    (ended : Bool) (hs : List Spec.Lexer.Handed) (failed : Bool)
    (h : fedOf (toVersion version) ended (lexBytes (toVersion version) .idle Location.initial
      slices.flatten) = some (hs, failed)) :
    fedInput VNaive.ops version slices ended = { handed := hs, failed } := by
  have := feedInput_eq (st := .idle) ended slices { handed := [] }
    (Core.initial (toVersion version)) ⟨rfl, rfl, rfl⟩ hs failed h
  simp only [List.nil_append] at this
  simp only [fedInput, show VNaive.ops.new = Lexer.new from rfl, Lexer.new]
  rw [this.1, this.2]

end BSmtLib.Proofs.Lexer.VNaive
