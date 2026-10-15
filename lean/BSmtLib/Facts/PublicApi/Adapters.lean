module

public import BSmtLib

@[expose] public section

/-!
# The small definitions of the theorems about the public API

The theorems of `BSmtLib.Facts.PublicApi` are stated with the library's public API, bytes, lists,
and the definitions below, and nothing else: no definition of the specification and none of the
library's internals. Each definition here is a few lines and states its rule in its docstring; a
reader of the theorems reads these and the public API, and nothing more.
-/

namespace BSmtLib.Facts.PublicApi.Adapters

open BSmtLib.Parser
open BSmtLib.Lexer.Error BSmtLib.Traits

/-- Bytes as a list: the form in which the theorems speak of an input. -/
abbrev ByteList := List UInt8

/-! ## Layout -/

/--
`Layout bytes`: the bytes are layout: a run of whitespace bytes (tab, line feed, carriage return,
space) and comments, a comment being `;` and bytes other than a line feed or a carriage return.

This is looser than SMT-LIB's whitespace: it does not require a comment to be followed by a line
break.
-/
inductive Layout : ByteList → Prop
  /-- No layout. -/
  | nil : Layout []
  /-- A whitespace byte, then layout. -/
  | space {c : UInt8} {rest : ByteList} : c = 9 ∨ c = 10 ∨ c = 13 ∨ c = 32 → Layout rest →
      Layout (c :: rest)
  /-- A comment, then layout. -/
  | comment {body rest : ByteList} : (∀ c ∈ body, c ≠ 10 ∧ c ≠ 13) → Layout rest →
      Layout (59 :: body ++ rest)

/--
`Spaced tokens bytes`: the bytes are the tokens in order, with layout before each and after the
last.
-/
inductive Spaced : List ByteList → ByteList → Prop
  /-- Layout alone. -/
  | nil {gap : ByteList} : Layout gap → Spaced [] gap
  /-- Layout, the first token, and the rest spaced. -/
  | cons {gap token rest : ByteList} {tokens : List ByteList} : Layout gap → Spaced tokens rest →
      Spaced (token :: tokens) (gap ++ token ++ rest)

/-! ## Spellings of string literals in 2.0 -/

/-- What the inside of a 2.0 string literal stands for, read from the left: `\"` for `"`, `\\`
for `\`, every other byte for itself. -/
def unescape20 : ByteList → ByteList
  | a :: b :: rest =>
    if a = 92 ∧ (b = 34 ∨ b = 92) then b :: unescape20 rest else a :: unescape20 (b :: rest)
  | bytes => bytes

/--
`SameSpelling written printed`: the two are the same bytes, or both are string literals, `"`
inside `"`, whose insides stand for the same bytes in 2.0.
-/
def SameSpelling (written printed : ByteList) : Prop :=
  written = printed ∨
    ∃ inner inner', written = 34 :: inner ++ [34] ∧ printed = 34 :: inner' ++ [34] ∧
      unescape20 inner = unescape20 inner'

/-- `SameSpellings written printed`: the lists are as long, and each written token has the same
spelling as the printed one at its place. -/
def SameSpellings (written printed : List ByteList) : Prop :=
  written.length = printed.length ∧ ∀ pair ∈ written.zip printed, SameSpelling pair.1 pair.2

/-! ## Feeding a reader -/

/-- The posture that allows every version and any number of version declarations. -/
def allVersions : Token.VersionPosture :=
  (Token.VersionPostureBuilder.new.clearAllowed.addAllowed .v2_0 |>.addAllowed .v2_5
    |>.addAllowed .v2_6 |>.addAllowed .v2_7 |>.setMaxDeclarations none).build

section

variable {H P E R : Type} [Parse P H Id E R] [Handler H Id]

/-- The reader fed the slices in order by `Reader.readSlice`: the reader after the last, or the
first failure. -/
def feed (reader : Reader H P) : List ByteList → Except (Reader.ReadFailure H P) (Reader H P)
  | [] => .ok reader
  | slice :: slices =>
    match (reader.readSlice slice.toByteArray.toByteSlice : Id _) with
    | .ok reader => feed reader slices
    | .error failure => .error failure

/-- The reader fed the slices by `Reader.readSlice` and then the end of the input by
`Reader.readEof`: the result, the reader before the end of the input, and the reader after it;
or the first failure. -/
def readThrough (reader : Reader H P) (slices : List ByteList) :
    Except (Reader.ReadFailure H P) (Option (Span.Located R) × Reader H P × Reader H P) :=
  match feed reader slices with
  | .error failure => .error failure
  | .ok before =>
    match (before.readEof : Id _) with
    | .ok (result, after) => .ok (result, before, after)
    | .error failure => .error failure

/-- The offset up to which the input of `length` bytes was read: where the reader began to
discard it, if it did, else its end. -/
def readUpTo (reader : Reader H P) (length : Nat) : Nat :=
  match reader.discardedFrom with
  | some location => location.offset
  | none => length

end

/-! ## A concrete consumer that collects spans -/

/-- What `Collector` writes down of each token handed to it: its category and the offsets of
its span's start and end. -/
abbrev Entry := Token.TokenCategory × Nat × Nat

/-- The monad of `Collector`: the entries written down so far, in order, kept outside the lexer
so that they survive a failed call. -/
abbrev CollectM := StateM (List Entry)

/-- The consumer that takes every token, whitespace and comments included, one per call, writes
down its entry, continues, and breaks at the end of the input. It never fails. -/
structure Collector where

instance : Token.Consume Collector Unit Empty where
  isConcrete := true

instance {batch : Token.BatchTag} : Token.ConsumeFrom Collector
    (Token.BatchCursor batch) CollectM where
  consume cursor h := do
    let (token, next) := cursor.next h
    let span := cursor.span token
    let category := cursor.category token
    modifyThe (List Entry) (· ++ [(category, span.start.offset, span.end.offset)])
    let flow : ControlFlow Unit := if category == .endOfFile then .break () else .continue
    return (.ok flow, next)

/-- The lexer with the collector fed the slices by `Lexer.lexSlice` and then the end of the
input by `Lexer.lexEof`: the result and the lexer after the end of the input, or the first
error. -/
def collectWith (lexer : Lexer Collector) :
    List ByteList → CollectM (Except (LexError Empty)
        (Option (Span.Located Unit) × Lexer Collector))
  | [] => do
    match ← lexer.lexEof with
    | .ok (result, lexer) => return .ok (result, lexer)
    | .error (error, _) => return .error error
  | slice :: slices => do
    match ← lexer.lexSlice slice.toByteArray.toByteSlice with
    | .ok lexer => collectWith lexer slices
    | .error (error, _) => return .error error

/-- The result of a run, without the lexer it leaves. -/
def resultOf {ε α β : Type} : Except ε (α × β) → Except ε α
  | .ok (result, _) => .ok result
  | .error error => .error error

/-- The library's lexer with the collector, from the version, fed the slices by
`Lexer.lexSlice` and then the end of the input by `Lexer.lexEof`: the result or the first error,
and the entries written down. -/
def collect (version : Token.Version) (slices : List ByteList) :
    Except (LexError Empty) (Option (Span.Located Unit)) × List Entry :=
  (resultOf <$> collectWith (Lexer.new Collector.mk version) slices).run []

/-- `Tiles entries start stop`: the entries' spans follow each other without a gap or an
overlap from `start` to `stop`. -/
def Tiles : List Entry → Nat → Nat → Prop
  | [], start, stop => start = stop
  | (_, first, last) :: entries, start, stop => first = start ∧ Tiles entries last stop

/-- The entries with their offsets moved by `k`. -/
def shift (k : Nat) (entries : List Entry) : List Entry :=
  entries.map fun (category, start, stop) => (category, start + k, stop + k)

end BSmtLib.Facts.PublicApi.Adapters
