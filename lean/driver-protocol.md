# The driver protocol

The Rust tests are the only set of tests. To run them against the Lean port,
the Lean side provides a driver: an executable that runs the Lean lexer or
parser on request and prints what it produced. The Rust test helpers
(`rust/tests/lex_backend` for the lexer, `rust/tests/parse_backend` for the
parser and the reader) start it, send the input of a test, and compare the
answer with the same expectations they use for the Rust library.

This document is the contract between the two sides. The sections up to
"How the Rust tests select the driver" cover the lexer; the section "The
parser" after them covers the parser and the reader. Nothing here is to be
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
options, the consumer behind the lexer takes every token and continues: it
never sets a version and never finishes or fails, and it does not take
whitespace and comments.

Every consumer breaks at the end-of-file token at the latest, as the library
requires: whatever its options, where a consumer would continue on that token,
it breaks instead. This break is not a finish and no line reports it.

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
`MissingDelimiter`, `UnexpectedTrailingToken`.

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

The consumer finished by its plan, and this is where: after the last token it
took. The break at the end-of-file token that every consumer makes is not
reported. The lexer holds the result back and goes on lexing: the feeds up to
the next `e` hand nothing over, and that `e` hands over no end-of-file token
but returns the held result. So the line stands in the response of that `e`,
before its `at` line, whichever feed the consumer finished in. A request
without that `e` has no `fin` line. A token after the finish, also one the
consumer left in its last hand-over, is an `err UnexpectedTrailingToken`
spanning that token; with `ws`, whitespace and comments are such tokens too.

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
after two. The input is `a b c d `, then two spaces, then its end. The switch
makes the lexer lex the rest again under 2.0. After the finish, the second
slice and the end hand nothing over, the end returns the finish, and the
version lasts until the end. Had the second slice been `e `, its symbol would
have been a trailing token.

```
lex 2.7 plan=l1,v1:2.0,f2 s6120622063206420 s2020 e
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
at 8:0:8
v 2.0
at 10:0:10
v 2.0
fin 7:0:7
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
input, a call after an error of a lexer that stops at its first error) and of
the calls that lex a whole input at once test the Rust interface in process.
They stay Rust-only. The tests of the reader go through the parser requests
described in "The parser".

## How the Rust tests select the driver

When the environment variable `BLAZING_SMTLIB_LEAN_DRIVER` holds the path of
the executable, the lexer test helpers send their inputs to it; without the
variable they call the Rust lexer directly. Each test thread starts the driver
once and keeps it for all its requests.

```
cd rust
BLAZING_SMTLIB_LEAN_DRIVER=/path/to/the/driver cargo test
```

The lexer tests that go through the driver are those of `tests/lexer.rs`,
`tests/lexer_slices.rs`, `tests/lexer_symbols.rs`, `tests/lexer_v2_0.rs`,
`tests/lexer_whitespace.rs`, `tests/lexer_batches.rs` and
`tests/lexer_recovery.rs` that do not use the Rust lexer's own interface. The
parser tests that go through it are described in "The parser". Everything else
in the suite tests the Rust library whatever the variable says.

The environment variable `BLAZING_SMTLIB_LEAN_LEXER` chooses the Lean lexer
that the driver answers with: `z`, the library's, when it is unset; `v`, the
naive lexer of `lean/BSmtLib/Lexer/Internal/VNaive.lean`, which hands every
token over alone; `w`, the Rust lexer ported to Lean
of `lean/BSmtLib/Lexer/Internal/WRustPort.lean`; or `x1`, the lexer with the
batch kept in its state of `lean/BSmtLib/Lexer/Internal/X1BatchInCore.lean`. All
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

## The parser

The parser tests run a parser over an input with a handler of their own, and
check the handler calls, the results and the errors. Their handlers are
written once, in Rust, and keep their state there: the Rust side holds the
handler, and the driver runs the Lean parser with a handler that asks the Rust
side for every call. So a parser request is a conversation: while the driver
answers it, it writes a line for each handler call and reads the answer to
that call from its standard input before it goes on.

All the general rules of "The executable" hold. A parser request runs the
parser of the Lean library through its public interface, as a user would: the
reader (`BSmtLib.Reader`), the parsers (`BSmtLib.Parser`) and the parse
adapter.

### Values

The values the handler makes of what it is told (sorts, terms,
s-expressions, attributes and scopes) stay on the Rust side. The Rust side
answers a call that makes a value with a number that stands for it, and the
driver hands the number back where the parser hands the value over: the Lean
handler's types of values are numbers. Errors of the handler are numbers the
same way. The numbers mean nothing to the driver.

The Rust handlers take some values by reference and some by move, as the Rust
handler interface says. The driver may name a value in several calls only
where every call but at most the last takes it by reference: the scrutinee of
a `match` (its start, the start and end of each case, and the match's end,
which takes it), and the sorts of the signatures of `define-fun`,
`define-fun-rec` and `define-funs-rec`, which are only ever taken by
reference. A value named again after a call took it, or never made, is a
broken contract, on which the Rust side panics.

### Fields

A request or a line is a sequence of fields separated by single spaces.
Besides the fields of the lexer protocol (hexadecimal bytes, locations,
versions):

- `<sym>`: a symbol, `u<hex>` if it was written unquoted and `q<hex>` if it
  was written quoted, with its content without the bars.
- `x<hex>`: bytes, as a keyword's name (without the colon), a numeral's
  digits or a string's content (with a doubled quote taken as one quote)
  carries them.
- `<n>`: a count, in decimal: the number of the items that follow.
- `<id>`: the number of a value or of an error, in decimal.
- `<opt-id>`: `-` for no value, or an `<id>`.
- `<constant>`: `N<hex>` a numeral's digits, `D<hex>` a decimal as written,
  `X<hex>` the digits of a hexadecimal without `#x`, `B<hex>` the digits of a
  binary without `#b`, `S<hex>` a string's content.
- `<ident>`: `<sym> <n> <index>...`: the symbol and its indices, each a
  `<sym>` or `n<hex>` for a numeral's digits.
- `<sow>`: a `<sym>`, or `_` for the wildcard.
- `<pattern>`: `p <sow>` for a pattern of a symbol or the wildcard, or
  `c <sym> <n> <sow>...` for a constructor applied to its arguments.
- `<sig>`: `<sym> <n> (<sym> <id>)... <id>`: a function's name, its
  parameters each with its sort, and its result sort.
- `<constructors>`: `<n> (<sym> <n> (<sym> <id>)...)...`: datatype
  constructors, each with its selectors and their sorts.
- `<quantifier>`: `forall` or `exists`.
- `<result>`: what a parser finished with: `-` for the script parser; for the
  command parser `command`, `exit`, `end` (the end of the input before a
  command) or `set-version <version>`; for the parsers of sorts, terms and
  s-expressions an `<id>`.

### Requests

```
reader <parser> <version>
```

Creates a reader (`Reader.new`, or `Reader.script` for a script) that starts
in the version, over the handler that asks the Rust side. It replaces the
reader of an earlier request, if there is one. `<parser>` is `command`,
`term`, `sort`, `s-expr`, or `script:<versions>;<limit>`: the script parser
under the posture that allows the versions, separated by commas and maybe
none, and the number of declarations, or `-` for no limit. The default
posture is `script:2.5,2.6,2.7;1`. The response is `ready`.

The following requests act on that reader. A request when there is none,
also after a request that ended with an error, which gives no reader back, is
answered with `fail`.

```
slice <hex>
```

`Reader.readSlice`. The response is `ok`.

```
eof
```

`Reader.readEof`. The response is `done <result> <location>`, or `none` if
the parser broke its contract by continuing on the end of the input.

```
all
```

`Reader.readAll` over a buffered reader that asks the Rust side for the
bytes (see "Calls of the buffered reader"). The response is `done <result>`,
or `none` as for `eof`.

```
file <hex>
```

`Reader.readFile` of the path, given as its bytes. The response is
`done <result>` or `none`.

```
discarded
```

`Reader.discardedFrom`. The response is `at <location>`, or `at -` if the
input is not being discarded.

```
version
```

`Reader.version`. The response is `version <version>`.

```
read-smt
read-smt-file <hex>
```

`read-smt` is `readSmt` over a buffered reader that asks the Rust side; the
bytes consumed last are reported from the buffered reader that `readSmt`
gives back. `read-smt-file` is `readSmtFile` of the path. Neither needs a
reader; each has its own handler. The response is `ok`.

```
drive <parser> <version> <count> <feed>...
```

Runs a parser of a category alone, as the Rust category tests do: a lexer of
the version, whose consumer takes the tokens one at a time and hands them to
the parser, again after each time it finished, until it has finished `count`
times; from then on it counts the tokens that are not the end-of-file token,
and breaks at the end-of-file token. The consumer does not tell the handler
the version. The feeds are those of `lex`, applied as there. The response
has a line `result <result>...` for each time the parser finished, in order,
and ends with `ok <count>`, the number of the tokens counted after the last
result. The `result` lines are written as the parser finishes, so a request
that ends with an error may have some before it.

`<parser>` names a parser of a category, written without spaces, and the
fields of its result:

| `<parser>` | the result's fields |
|---|---|
| `sort`, `s-expr`, `term` | `<id>` |
| `closed-attribute` | `<id>` |
| `closed-multiple-attribute` | `<n> <id>...` |
| `symbol` | `<sym>` |
| `keyword`, `string`, `numeral` | `x<hex>`, as in the calls |
| `open-paren`, `close-paren` | `-` |
| `ident` | `<ident>` |
| `qualified-ident` | `<ident> <opt-id>`: the sort it is qualified with |
| `pattern` | `<pattern>` |
| `sorted-var` | `<sym> <id>` |
| `pair(<a>,<b>)` | the fields of `<a>`'s result, then those of `<b>`'s |
| `closed(<a>)`, `paren(<a>)` | the fields of `<a>`'s result |
| `closed-multiple(<a>)`, `paren-multiple(<a>)` | `<n>`, then the fields of each of `<a>`'s results |

The combinators run the parsers they are given: `pair` the first, then the
second; `closed` its parser, then a `)`; `paren` a `(`, its parser, a `)`;
`closed-multiple` its parser until a `)`; `paren-multiple` a `(`, then as
`closed-multiple`. A name the driver does not know is answered with `fail
unsupported parser <name>`.

### Errors

Any request that reads or drives may end with an error instead:

```
error <start> <end> <cause>
```

The span of the error and its cause:

- `lexical <kind>`: a lexer error, of the kind spelled as in `err`.
- `syntax <kind>`: a syntax error, of the kind spelled as the Rust
  `SmtSyntaxErrorKind` variant; `ExpectedToken` is followed by its token
  types, spelled as in `t` and separated by commas, and
  `TooManyVersionDeclarations` by its limit.
- `handler <id>`: the handler's error that the Rust side answered a call with.
- `nonstandard <sym>`: the error of a command named by the symbol, which the
  Lean handler names without asking (`CommandHandler.nonstandardCommand`). The
  Rust side asks its handler then.
- `io <hex>`: an error while reading, with its message as bytes.

### Calls of the handler

```
call <method> <argument>...
```

A call of the handler: the driver waits for its answer, one line, before it
reads or writes anything else. The method is spelled as the Rust method of
`SmtHandler` or `SmtCommandHandler`:

```
call set_version <version>
call handle_sort <ident> <n> <id>...
call handle_term c <constant>
call handle_term i <ident> <opt-id>
call handle_term a <ident> <opt-id> <n> <id>...
call handle_s_expr c <constant>
call handle_s_expr s <sym>
call handle_s_expr r <word>
call handle_s_expr k x<hex>
call handle_s_expr l <n> <id>...
call handle_attribute x<hex> -
call handle_attribute x<hex> c <constant>
call handle_attribute x<hex> s <sym>
call handle_attribute x<hex> l <n> <id>...
call annotate_term <id> <n> <id>...
call start_let <n> (<sym> <id>)...
call end_let <id> <id>
call start_quantifier <quantifier> <n> (<sym> <id>)...
call end_quantifier <quantifier> <id> <id>
call start_lambda <n> (<sym> <id>)...
call end_lambda <id> <id>
call start_match <id>
call start_match_case <id> <pattern>
call end_match_case <id> <id> <id>
call end_match <id> <n> (<pattern> <id>)...
```

The ident of a term is followed by the sort it is qualified with by `as`; an
application ends with its arguments. `r` is a reserved word, by its
spelling. The value of an attribute is none (`-`), a constant, a symbol or a
list of s-expressions. The ends of binders and of cases name the scope first,
then the scrutinee, if any, then the body. Every call but `set_version` and
`start_match` makes a value.

```
call command_assert <id>
call command_check_sat
call command_check_sat_assuming <n> <id>...
call command_declare_const <sym> <id>
call start_declare_datatype <sym> <n> <sym>...
call end_declare_datatype <constructors>
call start_declare_datatypes <n> (<sym> x<hex>)...
call start_datatype_declaration <n> <sym>...
call end_datatype_declaration <constructors>
call end_declare_datatypes
call command_declare_fun <sym> <n> <id>... <id>
call command_declare_sort <sym> x<hex>
call command_declare_sort_parameter <sym>
call command_define_const <sym> <id> <id>
call start_define_fun <sig>
call end_define_fun <id>
call start_define_fun_rec <sig>
call end_define_fun_rec <id>
call start_define_funs_rec <n> <sig>...
call start_recursive_body <sig>
call end_recursive_body <id>
call end_define_funs_rec
call start_define_sort <sym> <n> <sym>...
call end_define_sort <id>
call command_echo x<hex>
call command_exit
call command_get_assertions
call command_get_assignment
call command_get_info x<hex>
call command_get_model
call command_get_option x<hex>
call command_get_proof
call command_get_unsat_assumptions
call command_get_unsat_core
call command_get_value <n> <id>...
call command_pop x<hex>
call command_push x<hex>
call command_reset
call command_reset_assertions
call command_set_info <id>
call command_set_logic <sym>
call command_set_option <id>
```

The sort arities of `declare-datatypes` are numerals. `command_declare_fun`
names the parameter sorts, then the result sort. No command call makes a
value.

The answer is one of:

- `ok <id>`: the call made the value of that number;
- `ok`: the call succeeded, for a call that makes no value;
- `err <id>`: the call failed with the handler's error of that number.

### Calls of the buffered reader

`all` and `read-smt` read through a buffered reader whose bytes are on the
Rust side. Its operations are calls too:

```
call fill
call consume <n>
```

`call fill` asks for the bytes buffered and not consumed yet (`BufRead.fillBuf`);
the answer is `bytes <hex>`, no bytes at the end of the input, or
`ioerr <hex>`, a failure with its message. The bytes consumed
(`BufRead.consume`) are reported with `call consume <n>`, answered by `ok`:
the driver adds them up and reports them before its next `call fill` and
before the line that ends the request, if they are more than zero.

### The lexer under the parser

The parser requests read with the lexer that `BLAZING_SMTLIB_LEAN_LEXER`
chooses. With `z` the driver uses the reader and the functions of the library
as they are. The other lexers have no reader of their own: the driver builds
the lexer over the library's parse adapter and does what the reader does with
it, step for step. Where the hand-overs are cut changes nothing a parser
request reports, with one exception: the naive lexer `v` gives an error of
its consumer (`syntax`, `handler`, `nonstandard`) an empty span at the end of
the token it failed on, where the other lexers give the span of the token.
Under `v` the parser tests that check the span of such an error report
themselves as not applicable on the standard error and end, as the lexer tests
that send a plan do; every other test runs unchanged.

### An example

`(assert (f 1))` read whole by a script, with a handler that makes values
numbered from 0 and fails nothing. `>` marks the lines the Rust side sends,
`<` those of the driver.

```
> reader script:2.5,2.6,2.7;1 2.7
< ready
> slice 28617373657274202866203129290a
< call set_version 2.7
> ok
< call handle_term c N31
> ok 0
< call handle_term a u66 0 - 1 0
> ok 1
< call command_assert 1
> ok
< ok
> eof
< done - 15:1:0
```

### How the Rust tests select the driver for the parser

The parser tests select the driver as the lexer tests do, by
`BLAZING_SMTLIB_LEAN_DRIVER`; the same driver serves both. The tests that go
through it are listed in `rust/tests/parse_backend/mod.rs`.
