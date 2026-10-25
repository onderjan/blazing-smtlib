module

public import BSmtLib.Token.Cursor

public section

/- LEAN: in Rust, `SmtTokensCursor` is in `token` with the tokens it gives; here it has a module
of its own next to `Cursor`'s, whose class it is an instance of, and the root module `BSmtLib`
imports it. -/

namespace BSmtLib.Token.TokensCursor

/- LEAN: Rust's `VecDeque` of the tokens is an array and the position `head` of the first token
not consumed; a push onto a cursor whose tokens are all consumed starts the array anew. Rust's
lifetime of the tokens' bytes is the views' own: a view keeps the bytes it views. -/
/--
A cursor over a dynamic array of tokens.

The cursor is consumed under a given version: it accepts a request
for that version and refuses a switch to any other. If the consumer
requests discarding, currently present tokens are discarded up to
before the first EOF.
If no EOF is currently present, the cursor switches to a discarding mode
and no new tokens are pushed until a pushed EOF token resets
the discarding mode. EOF tokens are never discarded themselves.
-/
structure _root_.BSmtLib.Token.TokensCursor where
  private mk ::
  private tokens : Array Token
  private head : Nat
  /-- Whether the tokens are discarded until an end-of-file token is pushed. -/
  private discarding : Bool
  private versionInForce : Version
  deriving Repr

/-- Constructs an empty cursor. -/
def new (version : Version) : TokensCursor := ⟨#[], 0, false, version⟩

/--
Pushes a new token to the end of the cursor.

If the cursor is currently discarding, any token
other than EOF is silently dropped, so the cursor
remains empty.
-/
@[inline]
def push (self : TokensCursor) (token : Token) : TokensCursor :=
  let append (self : TokensCursor) : TokensCursor :=
    -- the tokens are all consumed, so the array starts anew
    if self.head == self.tokens.size then { self with tokens := #[token], head := 0 }
    else { self with tokens := self.tokens.push token }
  if self.discarding then
    match token with
    -- the end-of-file token ends discarding and it is not discarded
    | .endOfFile => append { self with discarding := false }
    -- discard the token
    | _ => self
  else append self

/-- Removes all tokens and resets discarding mode. -/
def clear (self : TokensCursor) : TokensCursor :=
  { self with tokens := #[], head := 0, discarding := false }

/- LEAN: the operations of the cursor's `Cursor` instance, which Rust's `impl SmtCursor` holds;
they are declared here, so that the instance, whose types its users read, names no private
field. -/

/-- The number of tokens not consumed. -/
def Internal.remaining (self : TokensCursor) : Nat := self.tokens.size - self.head

/-- Whether a token remains to be consumed. -/
def Internal.HasNext (self : TokensCursor) : Prop := self.head < self.tokens.size

@[no_expose] instance (self : TokensCursor) : Decidable (Internal.HasNext self) :=
  inferInstanceAs (Decidable (self.head < self.tokens.size))

/-- The first producer has fewer tokens left than the second one. -/
@[expose]
def Internal.Consumed (next cursor : TokensCursor) : Prop :=
  Internal.remaining next < Internal.remaining cursor

/-- The next token, if any, without consuming it. -/
def Internal.peek? (self : TokensCursor) : Option Token := self.tokens[self.head]?

/-- Consumes the next token, if any. -/
def Internal.next? (self : TokensCursor) :
    Option (Token × { next : TokensCursor // Internal.Consumed next self }) :=
  if h : self.head < self.tokens.size then
    some (self.tokens[self.head],
      ⟨{ self with head := self.head + 1 },
        by simp only [Internal.Consumed, Internal.remaining]; omega⟩)
  else none

theorem Internal.isSome_next? {self : TokensCursor} (h : Internal.HasNext self) :
    (Internal.next? self).isSome := by
  simp only [Internal.HasNext] at h
  simp [Internal.next?, h]

/-- The version the tokens were classified in. -/
def Internal.version (self : TokensCursor) : Version := self.versionInForce

/-- The position of the first end-of-file token from `i` on, if there is one. -/
private def eofFrom (tokens : Array Token) (i : Nat) : Option { j : Nat // i ≤ j } :=
  if h : i < tokens.size then
    match tokens[i] with
    | .endOfFile => some ⟨i, Nat.le_refl i⟩
    | _ => (eofFrom tokens (i + 1)).map fun j => ⟨j.1, Nat.le_of_succ_le j.2⟩
  else none
termination_by tokens.size - i

/-- Drops the tokens before the next end-of-file token, which stays; discards the tokens pushed
until an end-of-file token if there is none. -/
def Internal.discardRest (self : TokensCursor) : TokensCursor :=
  match eofFrom self.tokens self.head with
  -- stop discarding, keep EOF
  | some j => { self with head := j.1 }
  -- no EOF encountered, switch to discarding mode
  | none => { self with tokens := #[], head := 0, discarding := true }

theorem Internal.remaining_discardRest_le (self : TokensCursor) :
    Internal.remaining (Internal.discardRest self) ≤ Internal.remaining self := by
  unfold Internal.discardRest
  split
  · next j _ => simp only [Internal.remaining]; have := j.2; omega
  · simp [Internal.remaining]

/-- Consumes all tokens. -/
def Internal.consumeAll (self : TokensCursor) :
    { next : TokensCursor //
      ¬ Internal.HasNext next ∧ (Internal.HasNext self → Internal.Consumed next self) } :=
  ⟨{ self with tokens := #[], head := 0 }, by simp [Internal.HasNext],
    fun h => by
      simp only [Internal.HasNext] at h
      simp only [Internal.Consumed, Internal.remaining, List.size_toArray, List.length_nil]
      omega⟩

instance : Cursor TokensCursor where
  Token := Token
  «syntax» _ token := token
  HasNext := Internal.HasNext
  decideHasNext cursor := inferInstanceAs (Decidable (Internal.HasNext cursor))
  Consumed := Internal.Consumed
  peek? := Internal.peek?
  next? := Internal.next?
  version := Internal.version
  -- the tokens were put in already classified under the cursor's
  -- version, so they cannot be read under any other
  setVersion self version := if version == Internal.version self then .ok self else .error {}
  discardRest := Internal.discardRest
  next?_isSome := Internal.isSome_next?
  consumed_trans h₁ h₂ := Nat.lt_trans h₁ h₂
  consumed_wf := (measure Internal.remaining).wf
  setVersion_consumed consumed h := by
    split at h
    · cases h; exact consumed
    · cases h
  discardRest_consumed h := Nat.lt_of_le_of_lt (Internal.remaining_discardRest_le _) h
  consumeAll := Internal.consumeAll

end BSmtLib.Token.TokensCursor
