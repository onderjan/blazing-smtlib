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
lex <version> <option> ... <feed> <feed> ...
```

- `<version>` is the SMT-LIB version the lexer starts in: `2.0`, `2.5`, `2.6`
  or `2.7`.
- The options come before the first feed; there may be none. They are
  described below. A request without options is answered as described here.
- A feed is one of:
  - `s<hex>`: these bytes, fed to the lexer as one slice. `s` alone is an
    empty slice.
  - `e`: the end of the input.
- There may be no feeds at all.

The driver creates one lexer for the request and applies the feeds to it in
order. The lexer keeps going after an `e`, as the Rust lexer does: the feeds
after it are a new input, whose locations start again at the origin. Without
options, the consumer behind the lexer takes every token and always
continues: it never sets a version and never finishes or fails, and it does
not take whitespace and comments.

## Response

For each feed, in order: one line per token handed to the consumer while the
feed is applied, then one line for the feed itself. After the last feed, one
closing line.

A location is written as `offset:line:column`, all zero-based, in decimal.

```
t <type> <start> <end> <reserved> x<hex>
```

A token, the end-of-file token included.

- `<type>` is the token type, spelled as the Rust `SmtTokenCategory` variant:
  `ParenOpen`, `ParenClose`, `Numeral`, `Decimal`, `Hexadecimal`, `Binary`,
  `String`, `Keyword`, `UnquotedSymbol`, `QuotedSymbol`, `Whitespace`,
  `Comment`, `EndOfFile`.
- `<start>` and `<end>` are the two ends of the token's span.
- `<reserved>` says what the token is as a reserved word under the version
  it was handed over in (the request's version, unless the consumer has set
  another one): `general` for a general reserved word, `command` for a command
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
`<kind>` is the Rust `SmtLexicalErrorKind` variant: `UnexpectedCharacter`,
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

## Options

```
ws
```

The consumer takes whitespace and comments. They are handed over as tokens
of the types `Whitespace` and `Comment`: a whitespace token is a maximal run
of whitespace characters and carries them; a comment token carries what
follows its semicolon, through the line feed or carriage return that ends it
if there is one.

```
plan=<reply>,<reply>,...
```

The consumer answers the hand-overs in order by the replies, one reply per
hand-over, and takes every token once the replies have run out. A reply is:

- `t`: take every token and continue;
- `l<k>`: take `k` tokens and continue, so that the rest is handed over again;
- `f<k>`: take `k` tokens and finish;
- `x<k>`: take `k` tokens and fail;
- `v<k>:<version>`: take `k` tokens, set the version and continue;
- `w<k>:<version>`: take `k` tokens, set the version and finish.

`k` is at least one; if the hand-over has fewer tokens, all of them are taken.
`plan=` alone is a plan without replies: every token is taken, and the
hand-overs are reported.

```
rules
rules=refuse-end
```

The consumer takes every token and fails by what the tokens are, after
taking the token: on the unquoted symbol `bad` (the error is named `bad`), on
a closing parenthesis that closes nothing (`unmatched`), and on the
end-of-file token inside a parenthesis (`unexpected-end`). It counts the
parentheses it has taken for that; an abandon sets the count back to zero.
The unquoted symbol `to-2.0` makes it set the version to 2.0. With
`rules=refuse-end` it fails on every end-of-file token.

At most one of `plan` and `rules` is given. A consumer with either of them is
called scripted below.

```
recover
```

The lexer recovers from errors, and the driver feeds it the way a caller
does. After an error on a slice, the driver applies the rest of that slice
again, from where the input continues. After an error on the end of the
input that continues, it applies the end of the input again. The response
goes on; an error that does not continue ends the feed, not the response.

## Response lines of the options

```
h <version> <count>
```

A hand-over to a consumer with a plan: the version of its cursor and the
number of its tokens. The `t` lines of all these tokens follow, also of those
the reply does not take. The boundaries of the hand-overs are a part of the
contract: 256 tokens at most, and what the Rust lexer hands over earlier.

For a consumer with rules, the `t` lines are the tokens it has taken, as
without options.

```
fin <location>
```

The consumer finished, and this is where: after the last token it took. The
lexer then discards the rest of the input: the feeds up to the next `e` hand
nothing over, and that `e` hands over no end-of-file token. The `at` line of
the feed follows as usual.

```
ab <location>
rc <location>
```

With `recover`: the consumer was made to abandon its unfinished work, with
the location where the failure took effect, and later told where the skipped
input ends. They stand in order among the `t` lines. Every `ab` is followed by
exactly one `rc` before the next `t` line.

```
err <kind> <start> <end> <continues>
cerr <name>
cerr <name> <continues>
```

`cerr` is an error of the consumer, by its name (`plan` for a reply that
fails). With `recover`, both kinds of error line end with where the input
continues from: a location, or `-` if it does not continue. Without
`recover`, an error ends the response, as described above.

```
v <version>
```

For a scripted consumer, after the `at` line of every feed: the version the
lexer is in (the Rust `version`).

## Examples with options

A plan: leave after one token, then switch to 2.0 after one, then finish
after one. The input is `a b c d `, then `e `, then its end. The switch makes
the lexer lex the rest again under 2.0. After the finish, the second slice
and the end hand nothing over, and the version lasts until the end.

```
lex 2.7 plan=l1,v1:2.0,f1 s6120622063206420 s6520 e
h 2.7 4
t UnquotedSymbol 0:0:0 1:0:1 - x61
t UnquotedSymbol 2:0:2 3:0:3 - x62
t UnquotedSymbol 4:0:4 5:0:5 - x63
t UnquotedSymbol 6:0:6 7:0:7 - x64
h 2.7 3
t UnquotedSymbol 2:0:2 3:0:3 - x62
t UnquotedSymbol 4:0:4 5:0:5 - x63
t UnquotedSymbol 6:0:6 7:0:7 - x64
h 2.0 2
t UnquotedSymbol 4:0:4 5:0:5 - x63
t UnquotedSymbol 6:0:6 7:0:7 - x64
fin 5:0:5
at 8:0:8
v 2.0
at 10:0:10
v 2.0
at 0:0:0
v 2.7
ok
```

Recovery with rules, on `(assert #q (f x)) y #q)` and its end. The first
error is inside a parenthesis, so the skipping ends after the parenthesis
that closes it. The second is in an atom with nothing open, which ends before
the closing parenthesis; that parenthesis is then handed over and refused.

```
lex 2.7 recover rules s2861737365727420237120286620782929207920237129 e
t ParenOpen 0:0:0 1:0:1 - x28
t UnquotedSymbol 1:0:1 7:0:7 command x617373657274
ab 9:0:9
err BaseSelectionExpected 8:0:8 10:0:10 9:0:9
rc 17:0:17
t UnquotedSymbol 18:0:18 19:0:19 - x79
ab 21:0:21
err BaseSelectionExpected 20:0:20 22:0:22 21:0:21
rc 22:0:22
t ParenClose 22:0:22 23:0:23 - x29
ab 23:0:23
cerr unmatched 23:0:23
rc 23:0:23
at 23:0:23
v 2.7
t EndOfFile 23:0:23 23:0:23 - x
at 0:0:0
v 2.7
ok
```

An error at the end of the input, on `(a b` and its end. The end-of-file
token is refused inside the parenthesis; the end is applied again, which
recovers there and hands the token over once more.

```
lex 2.7 recover rules s28612062 e
t ParenOpen 0:0:0 1:0:1 - x28
t UnquotedSymbol 1:0:1 2:0:2 - x61
at 4:0:4
v 2.7
t UnquotedSymbol 3:0:3 4:0:4 - x62
t EndOfFile 4:0:4 4:0:4 - x
ab 4:0:4
cerr unexpected-end 4:0:4
rc 4:0:4
t EndOfFile 4:0:4 4:0:4 - x
at 0:0:0
v 2.7
ok
```

## What the protocol leaves out

The tests of the token cursor, of the panics that answer a broken contract
(a consumer that takes no token, a slice fed after a failed end of the
input, a call after an error of a lexer that stops at its first error), of
the calls that lex a whole input at once and of the reader test the Rust
interface in process. They stay Rust-only.

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
`tests/lexer_slices.rs`, `tests/lexer_symbols.rs`, `tests/lexer_v2_0.rs`,
`tests/lexer_whitespace.rs`, `tests/lexer_batches.rs` and
`tests/lexer_recovery.rs` that do not use the Rust lexer's own interface. Everything else in the suite tests the Rust
library whatever the variable says.

The environment variable `BLAZING_SMTLIB_LEAN_LEXER` chooses the Lean lexer
that the driver answers with: `z`, the library's, when it is unset; `v`, the
naive lexer of `lean/BSmtLib/Proofs/Lexer/VNaive.lean`, which hands every
token over alone; `w`, the Rust lexer ported to Lean
of `lean/BSmtLib/Proofs/Lexer/WRustPort.lean`; or `x1`, the lexer with the
batch kept in its state of `lean/BSmtLib/Proofs/Lexer/X1BatchInCore.lean`. All
but `v` cut their
hand-overs as the library's lexer does: a batch of up to 256 tokens at a time,
except that a token the lexer builds in a buffer of its own is handed over
alone, after the batch before it. These are a token cut by a slice boundary,
every string literal under 2.0, a string literal with a doubled quote or a line
feed, and a quoted symbol with a line feed. Under `v` the tests that send a
plan, whose expectations depend on where the hand-overs are cut, report
themselves as not applicable on the standard error and end; every other test
runs unchanged. Under every other lexer every test runs.

```
BLAZING_SMTLIB_LEAN_DRIVER=/path/to/the/driver BLAZING_SMTLIB_LEAN_LEXER=v cargo test
```

The answers of the Rust lexer come from `rust/tests/lex_backend/driver.rs`,
which the tests call in process and `tools/rust-lex-driver` prints.
