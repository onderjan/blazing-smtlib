module

public import BSmtLib.Token
public import BSmtLib.Lexer.Cursor
public import BSmtLib.Token.Lookahead

public section

/- LEAN: in Rust, `SmtCursor` and `SmtConsumeFrom` are in `token` with the cursor. The class
`Cursor` names the lexer's cursor (`Internal.BatchView`), whose module imports `BSmtLib.Token`,
so the two classes have modules of their own here; the root module `BSmtLib` imports them. -/

namespace BSmtLib.Token.Cursor

open BSmtLib.Lexer.Cursor

/--
A producer seen as a cursor of a batch of the library's lexer: the cursor, which is the producer
itself, and the producer that a cursor after it stands for, which is that cursor itself.
-/
/- LEAN: not in Rust. The library's fused script reader reads a batch cursor directly; a
producer that is one gives itself as one through `Cursor.asBatch?`. The proofs that the
producer's type is the batch cursor's and that `cursor` and `back` are the producer and the
cursor themselves make sure that no producer can give the reader tokens other than its own;
being proofs, they take no room in the view. -/
structure Internal.BatchView (Z : Type) (HasNext : Z → Prop) (Consumed : Z → Z → Prop)
    (z : Z) where
  /-- The tag of the cursor's batch. -/
  tag : BatchTag
  /-- The producer as a cursor. -/
  cursor : LexerCursor tag
  /-- The producer that a cursor after `cursor` stands for. -/
  back : LexerCursor tag → Z
  /-- The producer's type is the batch cursor's. -/
  isCursor : Z = LexerCursor tag
  /-- The cursor is the producer itself. -/
  cursor_eq : cursor = cast isCursor z
  /-- A cursor after `cursor` stands for itself. -/
  back_eq (next : LexerCursor tag) : back next = cast isCursor.symm next
  /-- The cursor has a token if the producer has. -/
  hasNext : HasNext z → cursor.HasNext
  /-- A cursor that consumed tokens of `cursor` stands for a producer that consumed tokens. -/
  consumed {next : LexerCursor tag} : next.Consumed cursor → Consumed (back next) z

/-- A producer, ordered by consumption with the relation `Consumed`, which `wf` shows to be
well-founded: a loop over its tokens descends by it. -/
structure Internal.Draining {Z : Type} (Consumed : Z → Z → Prop) (wf : WellFounded Consumed) where
  cursor : Z

instance {Z : Type} {Consumed : Z → Z → Prop} {wf : WellFounded Consumed} :
    WellFoundedRelation (Internal.Draining Consumed wf) :=
  invImage Internal.Draining.cursor ⟨Consumed, wf⟩

/--
Consumes the tokens of `producer` with `next?` until it gives none: the default of
`Cursor.consumeAll`, over the producer's operations and laws. The producer it leaves has no
token left, and is `producer` itself or comes from it by consuming tokens.
-/
def Internal.drain {Z T : Type} {HasNext : Z → Prop} {Consumed : Z → Z → Prop}
    (next? : (cursor : Z) → Option (T × { next : Z // Consumed next cursor }))
    (isSome : ∀ {cursor : Z}, HasNext cursor → (next? cursor).isSome)
    (trans : ∀ {a b c : Z}, Consumed a b → Consumed b c → Consumed a c)
    (wf : WellFounded Consumed) (cursor : Z) :
    { next : Z // ¬ HasNext next ∧ (next = cursor ∨ Consumed next cursor) } :=
  match h : next? cursor with
  | none => ⟨cursor, fun hn => by simpa [h] using isSome hn, .inl rfl⟩
  | some (_, ⟨next, consumed⟩) =>
    let ⟨last, empty, after⟩ := drain next? isSome trans wf next
    ⟨last, empty, .inr (after.elim (fun e => e ▸ consumed) (fun d => trans d consumed))⟩
termination_by (⟨cursor⟩ : Internal.Draining Consumed wf)
decreasing_by exact consumed

/- LEAN: a class is Lean's trait; the Rust associated types `Token` and `Lookahead` are fields,
and the lookahead window's instance of `Lookahead` is a field filled in by instance search.
Methods taking `&mut self` return the updated producer, `next?` with the proof that it consumed
the token, `attempt` with the proof that the extractor took a token. The default methods are
fields with defaults: `isEmpty`, with the law that it is true exactly if no token remains, and
`consumeAll`, with the proof that it leaves no token, which comes after the laws its default
needs. -/
/-- A sequential producer of tokens. -/
class _root_.BSmtLib.Token.Cursor (Z : Type) where
  /--
  The user type of the token.

  The producer must implement `syntax` to view the user token type as a library type.
  -/
  Token : Type
  /-- Views the user token as a library token under the version in force. -/
  «syntax» : Z → Token → _root_.BSmtLib.Token
  /-- Whether a token remains to be consumed. -/
  HasNext : Z → Prop
  /-- Whether a token remains to be consumed, decided. -/
  decideHasNext : (cursor : Z) → Decidable (HasNext cursor)
  /--
  Whether the first producer comes from the second one by consuming at least one more token.
  -/
  Consumed : Z → Z → Prop
  /--
  Returns the next token (if any) without consuming it.

  Peeking must return `some` containing the next token that would be consumed if there is some
  such token waiting.
  -/
  peek? : Z → Option Token
  /-- Consumes the next token (if any). -/
  next? : (cursor : Z) → Option (Token × { next : Z // Consumed next cursor })
  /- LEAN: Rust's default is `peek().is_none()`. Lean's `peek?` has no law that ties it to the
  tokens that remain, so the default decides `HasNext`, which `next?_isSome` ties to `next?`;
  `isEmpty_iff` is the law of a producer that gives its own. -/
  /--
  Returns whether the producer has no tokens left to consume.

  This must be true exactly if `peek?` or `next?` would produce `none`.
  -/
  isEmpty : Z → Bool := fun cursor => !@decide (HasNext cursor) (decideHasNext cursor)
  /-- The lookahead window of `attempt`. -/
  Lookahead : Type := Unit
  /-- The window takes tokens of the producer's type. -/
  [lookahead : _root_.BSmtLib.Token.Lookahead Lookahead Token]
  /--
  Attempts to consume several tokens at once (lookahead).

  The extractor takes tokens from the window ahead of the cursor, in order.
  If it returns `some`, exactly the tokens it took are consumed, which must be at least one.
  If it returns `none`, nothing is consumed.
  An extractor that runs out of tokens must return `none`.
  The window may end after any token.

  This function can be provided for ultra-fast processing,
  and the caller must ensure that a successful attempt results in
  the same observable behaviour as when it failed one.
  Use standard `next?` processing unless
  absolutely necessary and supported by measurements.
  -/
  attempt {α : Type} : (cursor : Z) →
    ((window : Lookahead) →
      Option (α × { next : Lookahead //
        _root_.BSmtLib.Token.Lookahead.Consumed (T := Token) next window })) →
    Option (α × { next : Z // Consumed next cursor }) := fun _ _ => none
  /--
  The SMT-LIB version that applies for currently consumed tokens.

  The version is guaranteed not to change during a call to the consumer except as a result of
  the consumer calling `setVersion` and the producer accepting.
  -/
  version : Z → Version
  /--
  Sets the SMT-LIB version that should apply from now on.

  If the producer returns `.ok`, it has switched to the new version, and will return it in
  subsequent calls of `version`. The version change applies between the last consumed and first
  unconsumed token, and the producer can adjust the non-consumed tokens so they correspond to
  the set version. There is no guarantee on their shape or whether any remain at all; the caller
  must not use any information gathered on them beforehand.

  If the producer returns `.error`, it has refused the version set request. It guarantees that
  no changes were made, as if the method was never called.
  -/
  setVersion : Z → Version → Except VersionRefused Z
  /- LEAN: a producer that cannot discard, which Rust's panics with a message, is an obligation on
  the caller: the caller does not call it on such a producer. -/
  /--
  Puts the producer into discarding: it drops everything it is fed and does not call its consumer
  again, except once with the end of the input, which lies outside the discarded bytes.

  Discarding is separate from the version, which the producer still answers, and lasts until the
  end of the input.
  -/
  discardRest : Z → Z
  /- LEAN: not in Rust. Lean has no namespaces for fields, so this field of the library's own is
  named plainly; its type is in `Internal`. A view can only be given for a producer whose type is
  the batch cursor's, so a producer of another type cannot give one. -/
  /--
  For the library's own producer only: the producer as a cursor of a batch of the library's
  lexer, if it is one, which the library's script parser reads directly.

  Leave it at its default, `none`.
  -/
  asBatch? : (cursor : Z) → Option (Internal.BatchView Z HasNext Consumed cursor) :=
    fun _ => none
  /- LEAN: not in Rust. The facts that a consumer generic in its producer needs to take a token
  of a producer that has one, to give back the proof that it consumed a token after it took
  more or acted on the producer, and to take tokens until none remains. Rust states all but the
  last in words, and needs no proof that a loop ends. -/
  /-- A producer that has a token gives it. -/
  next?_isSome {cursor : Z} : HasNext cursor → (next? cursor).isSome
  /-- Consuming more tokens after some were consumed consumes those too. -/
  consumed_trans {a b c : Z} : Consumed a b → Consumed b c → Consumed a c
  /-- A producer cannot consume tokens without end. -/
  consumed_wf : WellFounded Consumed
  /-- A switch of the version keeps the tokens consumed. -/
  setVersion_consumed {cursor origin next : Z} {version : Version} :
    Consumed cursor origin → setVersion cursor version = .ok next → Consumed next origin
  /-- Discarding keeps the tokens consumed. -/
  discardRest_consumed {cursor origin : Z} :
    Consumed cursor origin → Consumed (discardRest cursor) origin
  /- LEAN: not in Rust, which states it in words: the law of `isEmpty`. -/
  /-- Whether the producer has no tokens left is whether no token remains. -/
  isEmpty_iff (cursor : Z) : isEmpty cursor = true ↔ ¬ HasNext cursor := by
    intro cursor; simp
  /- LEAN: Rust's `consume_all(&mut self)`, which returns the updated producer with the proof that
  no token is left, and that it consumed the tokens if there were any. Its default, Rust's loop
  over `next`, needs the laws above, so it comes after them. -/
  /-- Consumes all tokens the producer has left to hand over. -/
  consumeAll : (cursor : Z) →
      { next : Z // ¬ HasNext next ∧ (HasNext cursor → Consumed next cursor) } :=
    fun cursor =>
      let ⟨next, empty, after⟩ :=
        Internal.drain next? next?_isSome consumed_trans consumed_wf cursor
      ⟨next, empty, fun has => after.elim (fun e => absurd (e ▸ has) empty) id⟩

instance {batch : BatchTag} : Cursor (LexerCursor batch) where
  Token := LexerToken batch
  «syntax» := LexerCursor.«syntax»
  HasNext := LexerCursor.HasNext
  decideHasNext cursor := inferInstanceAs (Decidable cursor.HasNext)
  Consumed := LexerCursor.Consumed
  peek? := LexerCursor.peek?
  next? := LexerCursor.next?
  isEmpty := LexerCursor.isEmpty
  Lookahead := LexerWindow batch
  attempt := LexerCursor.attempt
  version := LexerCursor.version
  setVersion := LexerCursor.setVersion
  discardRest := LexerCursor.discardRest
  asBatch? cursor :=
    some
      { tag := batch, cursor, back := id, isCursor := rfl, cursor_eq := rfl,
        back_eq := fun _ => rfl, hasNext := id, consumed := id }
  next?_isSome := LexerCursor.isSome_next?
  consumed_trans := LexerCursor.Consumed.trans
  consumed_wf :=
    Subrelation.wf (fun h => LexerCursor.Consumed.remaining_lt h)
      (measure LexerCursor.Internal.remaining).wf
  setVersion_consumed consumed h := (LexerCursor.setVersion_follows h).trans_consumed consumed
  discardRest_consumed consumed := (LexerCursor.discardRest_follows _).trans_consumed consumed
  isEmpty_iff := LexerCursor.isEmpty_iff
  consumeAll cursor :=
    ⟨cursor.consumeAll, cursor.not_hasNext_consumeAll, LexerCursor.consumeAll_consumed⟩

end BSmtLib.Token.Cursor
