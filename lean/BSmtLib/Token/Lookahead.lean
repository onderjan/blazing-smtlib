module

public import BSmtLib.Token.SyntaxToken

public section

/- LEAN: in Rust, `SmtLookahead` is in `token` with the producer. Its tokens are viewed as
`SyntaxToken`s, whose module imports `BSmtLib.Token`, so the class has a module of its own here;
the root module `BSmtLib` imports it. -/

namespace BSmtLib.Token.Lookahead

/- LEAN: Rust's `next(&mut self)` returns the token and advances the window in place; here the
window after the token is returned, with the proof that it took the token, so that an extractor
gives back the window it took its tokens from (`Produce.attempt`). -/
/-- A lookahead window for `Produce.attempt` (`SmtLookahead`). -/
class _root_.BSmtLib.Token.Lookahead (W T : Type) where
  /-- Whether the first window comes from the second one by taking at least one more token. -/
  Consumed : W → W → Prop
  /-- Looks at the next token and advances the window. -/
  next? : (window : W) → Option (T × { next : W // Consumed next window })
  /-- Views the user token as a library token. -/
  «syntax» : W → T → SyntaxToken

/- LEAN: Rust's `impl SmtLookahead<T> for ()`, whose `syntax` panics: the window gives no token
to view. Here it views every token as the end of the file. -/
/-- The window that gives no token, for producers without lookahead. -/
instance {T : Type} : Lookahead Unit T where
  Consumed _ _ := False
  next? _ := none
  «syntax» _ _ := .endOfFile

/-- The window of a batch cursor takes the tokens of the batch after the cursor, in order. -/
instance {batch : BatchTag} : Lookahead (BatchCursor.TokenWindow batch) (BSmtLib.Token batch) where
  Consumed := BatchCursor.TokenWindow.Consumed
  next? := BatchCursor.TokenWindow.next?
  «syntax» := BatchCursor.TokenWindow.«syntax»

end BSmtLib.Token.Lookahead
