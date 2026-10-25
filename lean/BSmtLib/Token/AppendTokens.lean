module

public import BSmtLib.Token.SyntaxTokenBuf
public import BSmtLib.Token.TokensBuf
public import BSmtLib.Token.TokensCursor

public section

/- LEAN: in Rust, `SmtAppendTokens` is in `token` with the cursor it fills; here it has a module
of its own next to the cursor's, which the root module `BSmtLib` imports. -/

open BSmtLib.Plain

namespace BSmtLib.Token.AppendTokens

/- LEAN: Rust's `append_tokens(&self, &mut tokens)` returns the cursor with the tokens after
those it had. -/
/-- A value whose tokens can be put into a cursor. -/
class _root_.BSmtLib.Token.AppendTokens (α : Type) where
  /-- Puts the tokens of the value after those in the cursor. -/
  appendTokens : α → TokensCursor → TokensCursor

@[no_expose] instance : AppendTokens SyntaxToken := ⟨fun self tokens => tokens.push self⟩

@[no_expose] instance : AppendTokens SyntaxTokenBuf := ⟨fun self tokens => tokens.push self.view⟩

@[no_expose] instance : AppendTokens TokensBuf where
  appendTokens self tokens := Id.run do
    let mut tokens := tokens
    for token in self do
      tokens := tokens.push token
    return tokens

/- LEAN: Rust's implementation for the slice `[T]`; here for the array. -/
@[no_expose] instance {α : Type} [AppendTokens α] : AppendTokens (Array α) where
  appendTokens self tokens := self.foldl (fun tokens value => appendTokens value tokens) tokens

@[no_expose] instance : AppendTokens Reserved := ⟨fun self tokens => tokens.push (.reserved self)⟩

/- LEAN: the counterpart of the Rust macro `plain_append_tokens!`: the appending of a plain value,
viewed or owned, as the token of its variant. -/
set_option hygiene false in
local macro "plain_append_tokens " view:ident buf:ident variant:ident : command => do
  let constructor := Lean.mkIdent (`BSmtLib.Token.SyntaxToken ++ variant.getId)
  `(@[no_expose] instance : AppendTokens $view :=
      ⟨fun self tokens => tokens.push ($constructor self)⟩

    @[no_expose] instance : AppendTokens $buf :=
      ⟨fun self tokens => tokens.push ($constructor self.view)⟩)

plain_append_tokens Numeral NumeralBuf numeral
plain_append_tokens Decimal DecimalBuf decimal
plain_append_tokens HexDigits HexDigitsBuf hexadecimal
plain_append_tokens BinDigits BinDigitsBuf binary
plain_append_tokens StringContent StringContentBuf string
plain_append_tokens Keyword KeywordBuf keyword
plain_append_tokens Symbol SymbolBuf symbol
plain_append_tokens Whitespace WhitespaceBuf whitespace
plain_append_tokens Comment CommentBuf comment

end BSmtLib.Token.AppendTokens
