# The lexer driver protocol

The Rust tests are the only set of tests. To run them against the Lean port,
the Lean side provides a driver: an executable that runs the Lean lexer on
request and prints what it produced. The Rust test helpers
(`rust/tests/lex_backend`) start it, send the input of a test, and compare the
answer with the same expectations they use for the Rust lexer.

This document is the contract between the two sides. It covers the lexer.
The parser will add request kinds of its own later; nothing here is to be
changed without the maintainer.

## The executable

- It reads requests from the standard input, one per line, and writes the
  response to each to the standard output before it reads the next one. It
  flushes the output after every response.
- It serves any number of requests and exits with status 0 when the input
  ends. Requests are independent: nothing carries over from one to the next.
- Lines end with a line feed. Requests and responses are ASCII; fields are
  separated by single spaces.
- Bytes are written in hexadecimal, two lower-case digits per byte, with no
  separators. They are arbitrary: they may contain zero bytes, line breaks
  and bytes that are not UTF-8.

## Request

```
lex <version> <feed> <feed> ...
```

- `<version>` is the SMT-LIB version the lexer starts in: `2.0`, `2.5`, `2.6`
  or `2.7`.
- A feed is one of:
  - `s<hex>`: these bytes, fed to the lexer as one slice. `s` alone is an
    empty slice.
  - `e`: the end of the input.
- There may be no feeds at all.

The driver creates one lexer for the request and applies the feeds to it in
order. The lexer keeps going after an `e`, as the Rust lexer does: the feeds
after it are a new input, whose locations start again at the origin. The
handler behind the lexer takes every token and always continues; it never
asks for a relex and never finishes or fails.

## Response

For each feed, in order: one line per token handed to the handler while the
feed is applied, then one line for the feed itself. After the last feed, one
closing line.

A location is written as `offset:line:column`, all zero-based, in decimal.

```
t <type> <start> <end> <reserved> x<hex>
```

A token, the end-of-file token included.

- `<type>` is the token type, spelled as the Rust `TokenType` variant:
  `ParenOpen`, `ParenClose`, `Numeral`, `Decimal`, `Hexadecimal`, `Binary`,
  `String`, `Keyword`, `UnquotedSymbol`, `QuotedSymbol`, `EndOfFile`.
- `<start>` and `<end>` are the two ends of the token's span.
- `<reserved>` says what the token is as a reserved word under the request's
  version: `general` for a general reserved word, `command` for a command
  name, `-` for anything else.
- `x<hex>` is the token's content, as the Rust token carries it. `x` alone is
  empty content.

```
at <location>
```

The feed was applied without an error, and this is the lexer's current
location afterwards (the Rust `current_location`). After an `e` it is the
origin.

```
err <kind> <start> <end>
```

The feed raised a lexer error, with this kind and span. The response ends
here: the feeds after it are not applied and there is no closing line.
`<kind>` is the Rust `LexerErrorKind` variant: `UnexpectedCharacter`,
`FractionDigitExpected`, `HexadecimalDigitExpected`, `BinaryDigitExpected`,
`BaseSelectionExpected`, `UnclosedStringLiteral`, `ForbiddenCharInString`,
`ForbiddenKeywordName`, `BackslashInQuotedSymbol`,
`ForbiddenCharInQuotedSymbol`, `UnclosedQuotedSymbol`, `NumeralLeadingZero`,
`MissingDelimiter`.

```
ok
```

The closing line: every feed was applied.

```
fail <message>
```

The request could not be read (unknown request, version or feed, bad
hexadecimal digits). It is the whole response; the message is free text for a
human. The driver then goes on with the next request.

So the number of `at` lines before an `err` line tells which feed failed, and
the token lines before each `at` line are the tokens that feed handed over.

## Examples

These are the answers of the Rust lexer.

`(assert x)` and the end of the input, in 2.7:

```
lex 2.7 s28617373657274207829 e
t ParenOpen 0:0:0 1:0:1 - x28
t UnquotedSymbol 1:0:1 7:0:7 command x617373657274
t UnquotedSymbol 8:0:8 9:0:9 - x78
t ParenClose 9:0:9 10:0:10 - x29
at 10:0:10
t EndOfFile 10:0:10 10:0:10 - x
at 0:0:0
ok
```

`(assert 1.)`: the tokens before the error, then the error. The first feed
failed, so there is no `at` line.

```
lex 2.7 s2861737365727420312e29 e
t ParenOpen 0:0:0 1:0:1 - x28
t UnquotedSymbol 1:0:1 7:0:7 command x617373657274
err FractionDigitExpected 8:0:8 11:0:11
```

Two slices that cut a quoted symbol, the end of the input, and a second input:
`(push 1) |a`, ` b| "s""t"`, end, `x`, end. The quoted symbol is handed over
with the second slice; the string and the `x` wait for the end of their input,
which is what delimits them.

```
lex 2.7 s2870757368203129207c61 s20627c20227322227422 e s78 e
t ParenOpen 0:0:0 1:0:1 - x28
t UnquotedSymbol 1:0:1 5:0:5 command x70757368
t Numeral 6:0:6 7:0:7 - x31
t ParenClose 7:0:7 8:0:8 - x29
at 11:0:11
t QuotedSymbol 9:0:9 14:0:14 - x612062
at 21:0:21
t String 15:0:15 21:0:21 - x732274
t EndOfFile 21:0:21 21:0:21 - x
at 0:0:0
at 1:0:1
t UnquotedSymbol 0:0:0 1:0:1 - x78
t EndOfFile 1:0:1 1:0:1 - x
at 0:0:0
ok
```

The same bytes `"a\"b" lambda` under two versions: in 2.0 the backslash
escapes the quote and `lambda` is not reserved; in 2.7 the string ends at the
second quote, and the `b` after it is not delimited.

```
lex 2.0 s22615c226222206c616d626461 e
t String 0:0:0 6:0:6 - x612262
at 13:0:13
t UnquotedSymbol 7:0:7 13:0:13 - x6c616d626461
t EndOfFile 13:0:13 13:0:13 - x
at 0:0:0
ok
lex 2.7 s22615c226222206c616d626461 e
err MissingDelimiter 0:0:0 5:0:5
```

## What the protocol leaves out

The tests of the batch contract (a handler that asks for a relex, finishes or
fails in the middle of a batch), of the token cursor, and of recovery after an
error test the Rust interface in process. They stay Rust-only until the Lean
port has the corresponding interface and this protocol is extended for it.

## How the Rust tests select the driver

When the environment variable `BLAZING_SMTLIB_LEAN_DRIVER` holds the path of
the executable, the lexer test helpers send their inputs to it; without the
variable they call the Rust lexer directly. Each test thread starts the driver
once and keeps it for all its requests.

```
cd rust
BLAZING_SMTLIB_LEAN_DRIVER=/path/to/the/driver cargo test
```

The tests that go through the driver are those of `tests/lexer.rs`,
`tests/lexer_slices.rs`, `tests/lexer_symbols.rs` and `tests/lexer_v2_0.rs`
that do not use the Rust lexer's own interface. Everything else in the suite
tests the Rust library whatever the variable says.
