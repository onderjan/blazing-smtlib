import BSmtLib.Proofs.V1NaiveWRustPort.Cursor
import BSmtLib.Proofs.V1NaiveWRustPort.Bytes

/-!
# The naive lexer's pure run over a slice from an index

`feedFrom` is the naive lexer's pure run up to an error `V1Naive.lexBytes` over the bytes of a
slice from an index on (`feedFrom_toByteSlice`), stated by indices, as the Rust port reads a
slice: the state and the location after the bytes and the lexemes they finish, or on an error,
the lexemes finished before it. A step of the Rust port that consumes the bytes from one index to
another is compared with it by an equation between the run from the first index and the run from
the second (`Prep`).

`outcome` is what the run of the rest of the slice leaves the adapter's consumer with, given
what the consumer has recorded and will record so far: what it has recorded at the end of the
slice, or what it has recorded when the run fails.
-/

namespace BSmtLib.Proofs.Lexer.V1NaiveWRustPort

open BSmtLib.Proofs.Adapter V1Naive BSmtLib.Proofs.Simulation

/-- The run with the lexemes `ls` before the ones it finishes, also before an error. -/
abbrev Prep (ls : List Lexeme) (e : Except (List Lexeme) (St × Location × List Lexeme)) :
    Except (List Lexeme) (St × Location × List Lexeme) :=
  withBefore ls e

/-- The bytes of the slice from `i` on, from the state at `location`: the state and the location
after them and the lexemes they finish, or on an error, the lexemes finished before it. -/
def feedFrom (version : Version) (s : ByteSlice) (st : St) (location : Location) (i : Nat) :
    Except (List Lexeme) (St × Location × List Lexeme) :=
  if h : i < s.size then
    match byteStep version st location s[i] with
    | none => .error (failedBefore st location s[i])
    | some (st', ls) => Prep ls (feedFrom version s st' (location.afterByte s[i]) (i + 1))
  else
    .ok (st, location, [])
termination_by s.size - i

theorem prep_nil (e : Except (List Lexeme) (St × Location × List Lexeme)) : Prep [] e = e :=
  withBefore_nil e

theorem prep_prep (ls ls' : List Lexeme) (e : Except (List Lexeme) (St × Location × List Lexeme)) :
    Prep ls (Prep ls' e) = Prep (ls ++ ls') e :=
  withBefore_withBefore ls ls' e

theorem prep_error (ls ls' : List Lexeme) : Prep ls (.error ls') = .error (ls ++ ls') := rfl

theorem feedFrom_lt {version : Version} {s : ByteSlice} {i : Nat} (h : i < s.size) (st : St)
    (location : Location) :
    feedFrom version s st location i =
      match byteStep version st location s[i] with
      | none => .error (failedBefore st location s[i])
      | some (st', ls) => Prep ls (feedFrom version s st' (location.afterByte s[i]) (i + 1)) := by
  rw [feedFrom]
  simp only [h, dite_true]

theorem feedFrom_ge {version : Version} {s : ByteSlice} {i : Nat} (h : ¬ i < s.size) (st : St)
    (location : Location) : feedFrom version s st location i = .ok (st, location, []) := by
  rw [feedFrom]
  simp only [h, dite_false]

/-- A byte that the pure step takes with the lexemes `ls`. -/
theorem feedFrom_step {version : Version} {s : ByteSlice} {i : Nat} (h : i < s.size) {st st' : St}
    {location : Location} {ls : List Lexeme}
    (hstep : byteStep version st location s[i] = some (st', ls)) :
    feedFrom version s st location i =
      Prep ls (feedFrom version s st' (location.afterByte s[i]) (i + 1)) := by
  rw [feedFrom_lt h, hstep]

/-- A byte that the pure step fails at. -/
theorem feedFrom_fail {version : Version} {s : ByteSlice} {i : Nat} (h : i < s.size) {st : St}
    {location : Location} (hstep : byteStep version st location s[i] = none) :
    feedFrom version s st location i = .error (failedBefore st location s[i]) := by
  rw [feedFrom_lt h, hstep]

theorem size_toByteSlice' (l : List UInt8) : l.toByteArray.toByteSlice.size = l.length :=
  size_toByteSlice l

/-- The run over a slice of the bytes of a list is the run over the list from the index on. -/
theorem feedFrom_toByteSlice (version : Version) (bytes : List UInt8) :
    ∀ (n i : Nat), bytes.length - i = n → ∀ (st : St) (location : Location),
      feedFrom version bytes.toByteArray.toByteSlice st location i =
        lexBytes version st location (bytes.drop i) := by
  intro n
  induction n with
  | zero =>
    intro i hn st location
    have hle : bytes.length ≤ i := by omega
    rw [feedFrom_ge (by rw [size_toByteSlice]; omega), List.drop_eq_nil_of_le hle]
    rfl
  | succ n ih =>
    intro i hn st location
    have hlt : i < bytes.length := by omega
    have hs : i < bytes.toByteArray.toByteSlice.size := by rw [size_toByteSlice]; exact hlt
    rw [feedFrom_lt hs, getElem_toByteSlice, List.drop_eq_getElem_cons hlt]
    simp only [lexBytes]
    cases byteStep version st location bytes[i] with
    | none => rfl
    | some e =>
      obtain ⟨st', ls⟩ := e
      simp only
      rw [← getElem_toByteSlice bytes i hs, ih (i + 1) (by omega), getElem_toByteSlice]

/-! ## What the consumer is left with -/

/--
What the adapter's consumer is left with, if it has recorded or will record `before` and the
rest of the slice runs as `e`: at the end of the slice, the state and the location after it and
everything recorded; or, if the run fails, everything recorded before the failure; or none if
the consumer fails on a lexeme.
-/
def outcome (version : Version) (before : Option (List Spec.Lexer.Handed))
    (e : Except (List Lexeme) (St × Location × List Lexeme)) :
    Option (Except (List Spec.Lexer.Handed) (St × Location × List Spec.Lexer.Handed)) :=
  before.bind fun hs =>
    match e with
    | .ok (st, location, ls) => (handedAll version ls).map fun hs' => .ok (st, location, hs ++ hs')
    | .error ls => (handedAll version ls).map fun hs' => .error (hs ++ hs')

theorem outcome_none_left (version : Version)
    (e : Except (List Lexeme) (St × Location × List Lexeme)) : outcome version none e = none :=
  rfl

/-- A run that fails at once leaves the consumer with what it has recorded or will record. -/
theorem outcome_error_nil (version : Version) (before : Option (List Spec.Lexer.Handed)) :
    outcome version before (.error []) = before.map .error := by
  cases before <;> simp [outcome, handedAll]

/-- Lexemes moved from the run to what the consumer will record. -/
theorem outcome_prep (version : Version) (coll : Collector) (held ls : List Lexeme)
    (e : Except (List Lexeme) (St × Location × List Lexeme)) :
    outcome version (pending version coll held) (Prep ls e) =
      outcome version (pending version coll (held ++ ls)) e := by
  cases e with
  | ok e =>
    obtain ⟨st, location, ls'⟩ := e
    simp only [outcome, pending, Prep, withBefore, handedAll_append]
    cases h1 : handedAll version held <;> cases h2 : handedAll version ls <;>
      cases h3 : handedAll version ls' <;> simp [List.append_assoc]
  | error ls' =>
    simp only [outcome, pending, Prep, withBefore, handedAll_append]
    cases h1 : handedAll version held <;> cases h2 : handedAll version ls <;>
      cases h3 : handedAll version ls' <;> simp [List.append_assoc]

end BSmtLib.Proofs.Lexer.V1NaiveWRustPort
