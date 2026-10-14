module

public import BSmtLib.Token
public import BSmtLib.Token.SyntaxToken

public section

/- LEAN: in Rust, `SmtProduce` and `SmtConsumeFrom` are in `token` with the cursor. The producer
views its tokens as `SyntaxToken`s, whose module imports `BSmtLib.Token`, so the two classes
have modules of their own here; the root module `BSmtLib` imports them. -/

namespace BSmtLib.Token.Produce

/- LEAN: a class is Lean's trait; the Rust associated type `Token` is a field. Methods taking
`&mut self` return the updated producer, `next?` with the proof that it consumed the token.
Rust's `attempt` with its associated `Lookahead` is a method of `BatchCursor` only: its window
is given back with the proof that the extractor took a token, which a class would have to state
for every producer; Rust's default `attempt` takes nothing. The defaults `is_empty` and
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
  version := BatchCursor.version
  setVersion := BatchCursor.setVersion
  discardRest := BatchCursor.discardRest
  next?_isSome := BatchCursor.isSome_next?
  consumed_trans := BatchCursor.Consumed.trans
  consumed_wf :=
    Subrelation.wf (fun h => BatchCursor.Consumed.remaining_lt h) (measure BatchCursor.remaining).wf
  setVersion_consumed consumed h := (BatchCursor.setVersion_follows h).trans_consumed consumed
  discardRest_consumed consumed := (BatchCursor.discardRest_follows _).trans_consumed consumed

end BSmtLib.Token.Produce
