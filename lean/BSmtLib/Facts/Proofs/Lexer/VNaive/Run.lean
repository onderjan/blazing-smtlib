module

public import BSmtLib.Facts.Lexer.Adapters
import all BSmtLib.Lexer.Internal.VNaive
import all BSmtLib.Span
import all BSmtLib.Token
import all BSmtLib.Version
import all BSmtLib.Lexicon.Reserved
import all BSmtLib.Lexer.Cursor

@[expose] public section

/-!
# The pure run of the naive lexer

The naive lexer of `VNaive` lexes an input by a pure step over one byte at a time, and hands each
finished token over to its consumer in a monad. This module states the lexing as a pure run over the
bytes, also up to an error (`lexBytes`), followed by the end of the input (`endStep`; `run` for the
whole input), and what the run hands over in the form of the specification formalism (`BSmtLibSpec`)
(`fedOf`, `fedRun`), with each lexeme in the form the adapter records it in (`lexemeHanded`,
`toHanded_batch`).
-/

namespace BSmtLib.Facts.Proofs.Lexer.VNaive.Run

open BSmtLib.Facts.Lexer.Adapters
open BSmtLib.Lexer.Internal.VNaive

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
def startStep (version : Version) (location : Span.Location) (c : UInt8) :
    Option (St × List Lexeme) :=
  match start version false location c with
  | .idle => some (.idle, [])
  | .pending p => some (.token p, [])
  | .token l => some (.idle, [l])
  | .error _ => none

/-- The byte `c` at `location` in the state: the state after it and the lexemes it finishes,
or none on an error. A byte that delimits a token is lexed again with no token in
progress. -/
def byteStep (version : Version) : St → Span.Location → UInt8 → Option (St × List Lexeme)
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
def feedBytes (version : Version) : St → Span.Location → List UInt8 →
    Option (St × Span.Location × List Lexeme)
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
def failedBefore : St → Span.Location → UInt8 → List Lexeme
  | .idle, _, _ => []
  | .token p, location, c =>
    match advance false p location c with
    | .tokenBefore l => [l]
    | _ => []

/-- The run with the lexemes `ls` before the ones it finishes, also before an error. -/
def withBefore (ls : List Lexeme) :
    Except (List Lexeme) (St × Span.Location × List Lexeme) →
      Except (List Lexeme) (St × Span.Location × List Lexeme)
  | .ok (st, location, ls') => .ok (st, location, ls ++ ls')
  | .error ls' => .error (ls ++ ls')

/-- The bytes from the state at `location`: the state and the location after them and the
lexemes they finish, or on an error, the lexemes finished before it. -/
def lexBytes (version : Version) : St → Span.Location → List UInt8 →
    Except (List Lexeme) (St × Span.Location × List Lexeme)
  | st, location, [] => .ok (st, location, [])
  | st, location, c :: cs =>
    match byteStep version st location c with
    | none => .error (failedBefore st location c)
    | some (st', ls) => withBefore ls (lexBytes version st' (location.afterByte c) cs)

/-- `feedBytes` is `lexBytes` without the lexemes finished before an error. -/
theorem lexBytes_toOption (version : Version) (st : St) (location : Span.Location)
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

theorem withBefore_nil (e : Except (List Lexeme) (St × Span.Location × List Lexeme)) :
    withBefore [] e = e := by
  cases e with
  | ok r => obtain ⟨st, location, ls⟩ := r; rfl
  | error ls => rfl

theorem withBefore_withBefore (ls ls' : List Lexeme)
    (e : Except (List Lexeme) (St × Span.Location × List Lexeme)) :
    withBefore ls (withBefore ls' e) = withBefore (ls ++ ls') e := by
  cases e with
  | ok r => obtain ⟨st, location, ls''⟩ := r; simp [withBefore, List.append_assoc]
  | error ls'' => simp [withBefore, List.append_assoc]

/-- The end-of-file lexeme at `location`. -/
def eofLexeme (location : Span.Location) : Lexeme :=
  { category := .endOfFile, content := .empty, start := location, «end» := location }

/-- The end of the input in the state at `location`: the lexemes it finishes, the end-of-file
one last, or none on an error. -/
def endStep : St → Span.Location → Option (List Lexeme)
  | .idle, location => some [eofLexeme location]
  | .token p, location =>
    match finish false p location with
    | .none => some [eofLexeme location]
    | .token l => some [l, eofLexeme location]
    | .error _ => none

/-- The bytes and then the end of the input, from the state at `location`. -/
def runFrom (version : Version) (st : St) (location : Span.Location) (bytes : List UInt8) :
    Option (List Lexeme) :=
  (feedBytes version st location bytes).bind fun (st, location, ls) =>
    (endStep st location).map (ls ++ ·)

/-- The lexemes of the whole input, or none on an error. -/
def run (version : Version) (bytes : List UInt8) : Option (List Lexeme) :=
  runFrom version .idle Span.Location.initial bytes

/-- The lexeme in the formalism's form, as the adapter records it (`toHanded`) when it is handed
over alone in a cursor under the version (see `toHanded_batch`); none for whitespace and
comments. -/
def lexemeHanded (version : Version) (l : Lexeme) : Option BSmtLibSpec.Lexer.Handed :=
  (toTokenType l.category).map fun type =>
    { type
      start := toLocation l.start
      «end» := toLocation l.end
      reserved := match l.category with
        | .unquotedSymbol =>
          (Lexicon.Reserved.fromBytes? l.content.toByteSlice version).map fun word =>
            if word.isCommandName then .command else .general
        | _ => none
      content := toContent l.content.toByteSlice }

/-- The adapter records the lexeme handed over alone in a cursor as `lexemeHanded` gives it. -/
theorem toHanded_batch (version : Version) (l : Lexeme) (h : l.Valid) :
    toHanded (Lexer.Cursor.LexerCursor.Internal.new version (l.batch h))
      ((Lexer.Cursor.LexerCursor.Internal.new version (l.batch h)).peek (l.hasNext h version)) =
      lexemeHanded version l := by
  have hcat :
      (Lexer.Cursor.LexerCursor.Internal.new version (l.batch h)).category
      ((Lexer.Cursor.LexerCursor.Internal.new version (l.batch h)).peek (l.hasNext h version))
          = l.category := by
    obtain ⟨category, content, start, «end»⟩ := l
    cases category <;> rfl
  have hstart :
      ((Lexer.Cursor.LexerCursor.Internal.new version (l.batch h)).span
      ((Lexer.Cursor.LexerCursor.Internal.new version (l.batch h)).peek
          (l.hasNext h version))).start = l.start :=
          rfl
  have hend :
      ((Lexer.Cursor.LexerCursor.Internal.new version (l.batch h)).span
      ((Lexer.Cursor.LexerCursor.Internal.new version (l.batch h)).peek
          (l.hasNext h version))).end = l.end := rfl
  have hcontent :
      (Lexer.Cursor.LexerCursor.Internal.new version (l.batch h)).content
      ((Lexer.Cursor.LexerCursor.Internal.new version (l.batch h)).peek (l.hasNext h version)) =
        l.content.toByteSlice := rfl
  have hversion : (Lexer.Cursor.LexerCursor.Internal.new version (l.batch h)).version = version := rfl
  unfold lexemeHanded toHanded
  simp only [Lexer.Cursor.LexerCursor.«syntax», Token.fromLexerToken,
      Token.Internal.fromParts,
      hcat, hstart, hend,
    hcontent, hversion]
  cases hc : l.category <;> simp [toTokenType, toReservedKind]
  cases Lexicon.Reserved.fromBytes? l.content.toByteSlice version <;> rfl

/-- The lexeme in the formalism's form as a piece of layout, as the adapter records it (`toLayout`).
-/
def lexemeLayout (l : Lexeme) : BSmtLibSpec.Lexer.Handed :=
  { type := if l.category == .comment then .comment else .whitespace
    start := toLocation l.start
    «end» := toLocation l.end
    reserved := none
    content := toContent l.content.toByteSlice }

/-- The entry a consumer takes for the lexeme, as the adapter records it (`Answering.entry`): the
token, or whitespace or a comment for a concrete consumer; none for whitespace or a comment
otherwise. -/
def lexemeEntry (concrete : Bool) (version : Version)
    (l : Lexeme) : Option BSmtLibSpec.Lexer.Handed :=
  match lexemeHanded version l with
  | some handed => some handed
  | none => if concrete then some (lexemeLayout l) else none

/-- The adapter's consumer takes the lexeme handed over alone in a cursor as `lexemeEntry`
gives it. -/
theorem entry_batch (consumer : BSmtLibSpec.Lexer.Consumer) (version : Version) (l : Lexeme)
    (h : l.Valid) :
    Answering.entry consumer (Lexer.Cursor.LexerCursor.Internal.new version (l.batch h))
      ((Lexer.Cursor.LexerCursor.Internal.new version (l.batch h)).peek (l.hasNext h version)) =
      lexemeEntry consumer.concrete version l := by
  have hcat :
      (Lexer.Cursor.LexerCursor.Internal.new version (l.batch h)).category
      ((Lexer.Cursor.LexerCursor.Internal.new version (l.batch h)).peek (l.hasNext h version))
          = l.category := by
    obtain ⟨category, content, start, «end»⟩ := l
    cases category <;> rfl
  unfold Answering.entry lexemeEntry
  rw [toHanded_batch]
  cases lexemeHanded version l with
  | some _ => rfl
  | none =>
    simp only [toLayout, lexemeLayout, hcat]
    rfl

/-! ## Feeding in pieces -/

theorem feedBytes_append (version : Version) (st : St) (location : Span.Location)
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

theorem runFrom_append (version : Version) (st : St) (location : Span.Location)
    (a b : List UInt8) :
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

/-! ## The lexemes in the formalism's form -/

/-- The lexemes in the formalism's form, or none if one of them is whitespace or a comment. -/
def handedAll (version : Version) (ls : List Lexeme) : Option
    (List BSmtLibSpec.Lexer.Handed) :=
  ls.mapM (lexemeHanded version)

theorem handedAll_cons_some {version : Version} {l : Lexeme} {x : BSmtLibSpec.Lexer.Handed}
    (hl : lexemeHanded version l = some x) (ls : List Lexeme) :
    handedAll version (l :: ls) = (handedAll version ls).map (x :: ·) := by
  simp only [handedAll, List.mapM_cons, hl]
  cases ls.mapM (lexemeHanded version) <;> rfl

/-! ## Helpers -/

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

/-- A bind in `Id` applies the function. -/
theorem id_bind {α β : Type} (x : α) (f : α → Id β) : (x >>= f : Id β) = f x := rfl

/-! ## The slices and the end of the input -/

/-- The lexemes of the pure run over the bytes and then, if the input has ended and the run has
not failed, of the end of the input, in the formalism's form, and whether the run failed; none if a
lexeme is whitespace or a comment. -/
def fedOf (version : Version) (ended : Bool) :
    Except (List Lexeme) (St × Span.Location × List Lexeme) → Option
        (List BSmtLibSpec.Lexer.Handed × Bool)
  | .ok (st, location, ls) =>
    if ended then
      match endStep st location with
      | some ls' => (handedAll version (ls ++ ls')).map (·, false)
      | none => (handedAll version ls).map (·, true)
    else
      (handedAll version ls).map (·, false)
  | .error ls => (handedAll version ls).map (·, true)

/--
What the naive lexer has done after being fed the slices under the version and then, if the input
has ended, the end of the input, as the pure run gives it: what it has handed over, and whether
it has failed. `fedOf` gives this for every input (`fedOf_isSome`); the `none` case is never
taken.
-/
def fedRun (version : BSmtLibSpec.Lexicon.Version) (slices : List BSmtLibSpec.Regex.Chars)
    (ended : Bool) :
    BSmtLibSpec.Lexer.Fed :=
  match fedOf (toVersion version) ended
      (lexBytes (toVersion version) .idle Span.Location.initial slices.flatten) with
  | some (handed, failed) => { handed, failed }
  | none => { handed := [], failed := true }

/-- `fedRun` gives what the pure run of the bytes of the slices and then, if the input has ended,
the pure end of the input give, also up to an error. -/
theorem fedRun_eq_run (version : BSmtLibSpec.Lexicon.Version)
    (slices : List BSmtLibSpec.Regex.Chars)
    (ended : Bool) (hs : List BSmtLibSpec.Lexer.Handed) (failed : Bool)
    (h : fedOf (toVersion version) ended (lexBytes (toVersion version) .idle Span.Location.initial
      slices.flatten) = some (hs, failed)) :
    fedRun version slices ended = { handed := hs, failed } := by
  simp only [fedRun, h]

end BSmtLib.Facts.Proofs.Lexer.VNaive.Run
