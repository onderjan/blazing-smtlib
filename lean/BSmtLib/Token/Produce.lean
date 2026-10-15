module

public import BSmtLib.Token
public import BSmtLib.Token.SyntaxToken
public import BSmtLib.Token.Lookahead

public section

/- LEAN: in Rust, `SmtProduce` and `SmtConsumeFrom` are in `token` with the cursor. The producer
views its tokens as `SyntaxToken`s, whose module imports `BSmtLib.Token`, so the two classes
have modules of their own here; the root module `BSmtLib` imports them. -/

namespace BSmtLib.Token.Produce

/--
A producer seen as a cursor of a batch of the library's lexer: the cursor, and the producer that
a cursor after it stands for.
-/
/- LEAN: not in Rust. The library's fused script reader reads a batch cursor directly; a
producer that is one gives itself as one through `Produce.asBatch?`. -/
structure Internal.BatchView (Z : Type) (HasNext : Z → Prop) (Consumed : Z → Z → Prop)
    (producer : Z) where
  /-- The tag of the cursor's batch. -/
  tag : BatchTag
  /-- The producer as a cursor. -/
  cursor : BatchCursor tag
  /-- The producer that a cursor after `cursor` stands for. -/
  back : BatchCursor tag → Z
  /-- The cursor has a token if the producer has. -/
  hasNext : HasNext producer → cursor.HasNext
  /-- A cursor that consumed tokens of `cursor` stands for a producer that consumed tokens. -/
  consumed {next : BatchCursor tag} : next.Consumed cursor → Consumed (back next) producer

/- LEAN: a class is Lean's trait; the Rust associated types `Token` and `Lookahead` are fields,
and the lookahead window's instance of `Lookahead` is a field filled in by instance search.
Methods taking `&mut self` return the updated producer, `next?` with the proof that it consumed
the token, `attempt` with the proof that the extractor took a token. The defaults `is_empty` and
`consume_all` are left to the producers. -/
/-- A sequential producer of tokens. -/
class _root_.BSmtLib.Token.Produce (Z : Type) where
  /--
  The user type of the token.

  The producer must implement `syntax` to view the user token type as a library type.
  -/
  Token : Type
  /-- Views the user token as a library token under the version in force. -/
  «syntax» : Z → Token → SyntaxToken
  /-- Whether a token remains to be consumed. -/
  HasNext : Z → Prop
  /-- Whether a token remains to be consumed, decided. -/
  decideHasNext : (producer : Z) → Decidable (HasNext producer)
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
  next? : (producer : Z) → Option (Token × { next : Z // Consumed next producer })
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
  attempt {α : Type} : (producer : Z) →
    ((window : Lookahead) →
      Option (α × { next : Lookahead //
        _root_.BSmtLib.Token.Lookahead.Consumed (T := Token) next window })) →
    Option (α × { next : Z // Consumed next producer }) := fun _ _ => none
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
  named plainly; its type is in `Internal`. Producers other than the library's batch cursor
  leave it at its default. -/
  /-- For the library's own producers: the producer as a cursor of a batch of the library's
  lexer, if it is one. -/
  asBatch? : (producer : Z) → Option (Internal.BatchView Z HasNext Consumed producer) :=
    fun _ => none
  /- LEAN: not in Rust. The facts that a consumer generic in its producer needs to take a token
  of a producer that has one, to give back the proof that it consumed a token after it took
  more or acted on the producer, and to take tokens until none remains. Rust states all but the
  last in words, and needs no proof that a loop ends. -/
  /-- A producer that has a token gives it. -/
  next?_isSome {producer : Z} : HasNext producer → (next? producer).isSome
  /-- Consuming more tokens after some were consumed consumes those too. -/
  consumed_trans {a b c : Z} : Consumed a b → Consumed b c → Consumed a c
  /-- A producer cannot consume tokens without end. -/
  consumed_wf : WellFounded Consumed
  /-- A switch of the version keeps the tokens consumed. -/
  setVersion_consumed {producer origin next : Z} {version : Version} :
    Consumed producer origin → setVersion producer version = .ok next → Consumed next origin
  /-- Discarding keeps the tokens consumed. -/
  discardRest_consumed {producer origin : Z} :
    Consumed producer origin → Consumed (discardRest producer) origin

instance {batch : BatchTag} : Produce (BatchCursor batch) where
  Token := BSmtLib.Token batch
  «syntax» := BatchCursor.«syntax»
  HasNext := BatchCursor.HasNext
  decideHasNext cursor := inferInstanceAs (Decidable cursor.HasNext)
  Consumed := BatchCursor.Consumed
  peek? := BatchCursor.peek?
  next? := BatchCursor.next?
  Lookahead := BatchCursor.TokenWindow batch
  attempt := BatchCursor.attempt
  version := BatchCursor.version
  setVersion := BatchCursor.setVersion
  discardRest := BatchCursor.discardRest
  asBatch? cursor :=
    some { tag := batch, cursor, back := id, hasNext := id, consumed := id }
  next?_isSome := BatchCursor.isSome_next?
  consumed_trans := BatchCursor.Consumed.trans
  consumed_wf :=
    Subrelation.wf (fun h => BatchCursor.Consumed.remaining_lt h) (measure BatchCursor.remaining).wf
  setVersion_consumed consumed h := (BatchCursor.setVersion_follows h).trans_consumed consumed
  discardRest_consumed consumed := (BatchCursor.discardRest_follows _).trans_consumed consumed

end BSmtLib.Token.Produce
