namespace BlazingSmtlib

/--
A location in an SMT-LIB stream.

All counts are in bytes (SMT-LIB works on bytes).
While SMT-LIB accepts both CR and LF as a comment separator,
we consider only LF to start a new line for location purposes
as that is compatible with both LF and CRLF conventions.

The offset, line, and column all start at zero.
-/
/- LEAN: the counts are `Nat`, Lean's arbitrary-precision natural numbers, where Rust has
`u64`. In Rust, `u64` stands for "big enough"; `Nat` is exactly that, and small values are
stored unboxed, so it costs little. -/
structure SmtLocation where
  /-- Zero-based byte offset from the start of the stream. -/
  offset : Nat
  /-- Zero-based line number. -/
  line : Nat
  /-- Zero-based column number, measured in bytes. -/
  column : Nat
  /- LEAN: `deriving` is Rust's `#[derive]`: `BEq` is `PartialEq`, `Hashable` is `Hash`,
  `Repr` is `Debug`. `Inhabited` provides a default value, which Lean needs for the
  return type of `panic!` and of functions marked `partial`; values are copied freely in
  Lean, so there is no counterpart of `Clone` and `Copy`. -/
  deriving BEq, Hashable, Repr, Inhabited

namespace SmtLocation

def min (self other : SmtLocation) : SmtLocation :=
  if self.offset ≤ other.offset then self else other

def max (self other : SmtLocation) : SmtLocation :=
  if self.offset ≥ other.offset then self else other

/-- Location directly at the byte stream start. -/
@[inline]
def initial : SmtLocation :=
  { offset := 0, line := 0, column := 0 }

@[inline]
def afterColumn (self : SmtLocation) : SmtLocation :=
  { offset := self.offset + 1, line := self.line, column := self.column + 1 }

@[inline]
def afterByte (self : SmtLocation) (c : UInt8) : SmtLocation :=
  /- LEAN: Lean has no byte literals like `b'\n'`; a character literal is converted with
  `Char.toUInt8`, which keeps the low byte and is exact for ASCII. -/
  if c == '\n'.toUInt8 then
    { offset := self.offset + 1, line := self.line + 1, column := 0 }
  else
    self.afterColumn

end SmtLocation

/-- A value located in an SMT-LIB stream. -/
/- LEAN: the fields are public, as Lean structures expose their fields as accessor
functions (`located.value`, `located.location`); they replace the Rust getters.
`into_value` is the same as `value`, since Lean values are not moved out of. -/
structure SmtLocated (V : Type) where
  /-- The value. -/
  value : V
  /-- The location. -/
  location : SmtLocation
  deriving BEq, Hashable, Repr

/--
Span of an SMT-LIB element.

The span is a half-open range `[start, end)` between locations.
-/
structure SmtSpan where
  /- LEAN: `end` is a keyword in Lean, so the field name is written in guillemets where it
  is declared or bound; `span.end` works as usual. -/
  start : SmtLocation
  «end» : SmtLocation
  deriving BEq, Hashable, Repr, Inhabited

namespace SmtSpan

@[inline]
def newUnchecked (start «end» : SmtLocation) : SmtSpan :=
  { start, «end» }

/--
A span within one line: the line, the offset of its start, and the
offsets of the span on it.
-/
@[inline]
def onLine (line lineStart start «end» : Nat) : SmtSpan :=
  { start := { offset := start, line, column := start - lineStart },
    «end» := { offset := «end», line, column := «end» - lineStart } }

@[inline]
def newEmpty (location : SmtLocation) : SmtSpan :=
  { start := location, «end» := location }

def newZero : SmtSpan :=
  newEmpty SmtLocation.initial

def isEmpty (self : SmtSpan) : Bool :=
  self.start == self.end

def join (self other : SmtSpan) : SmtSpan :=
  { start := self.start.min other.start, «end» := self.end.max other.end }

end SmtSpan

end BlazingSmtlib
