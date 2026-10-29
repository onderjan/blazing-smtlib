module

public import BSmtLib.Lexer.Cursor

public section

/- LEAN: in Rust, `SmtLookahead` is in `token` with the producer. Its instance for the lexer's
window names `Lexer.Cursor.LexerWindow`, whose module imports `BSmtLib.Token`, so the class has
a module of its own here; the root module `BSmtLib` imports it. -/

namespace BSmtLib.Token.Lookahead

open BSmtLib.Lexer.Cursor

/- LEAN: Rust's `next(&mut self)` returns the token and advances the window in place; here the
window after the token is returned, with the proof that it took the token, so that an extractor
gives back the window it took its tokens from (`Cursor.attempt`). -/
/-- Lookahead window for `Cursor.attempt`. -/
class _root_.BSmtLib.Token.Lookahead (W T : Type) where
  /-- Whether the first window comes from the second one by taking at least one more token. -/
  Consumed : W → W → Prop
  /-- Looks at the next token and advances the window. -/
  next? : (window : W) → Option (T × { next : W // Consumed next window })
  /-- Views the user token as a syntax token. -/
  «syntax» : W → T → Token

/- LEAN: Rust's `impl SmtLookahead<T> for ()`, whose `syntax` panics: the window gives no token
to view. Here it views every token as the end of the file. -/
instance {T : Type} : Lookahead Unit T where
  Consumed _ _ := False
  next? _ := none
  «syntax» _ _ := .endOfFile

instance {batch : BatchTag} : Lookahead (LexerWindow batch) (LexerToken batch) where
  Consumed := LexerWindow.Consumed
  next? := LexerWindow.next?
  «syntax» := LexerWindow.«syntax»

end BSmtLib.Token.Lookahead
