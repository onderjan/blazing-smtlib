module

public section

namespace BSmtLib.Span

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
stored unboxed, so it costs little. The constructor is private, as Rust's fields are, and the
library builds a location with `Location.Internal.new`; the fields are read-only and stand as
Rust's getters. -/
structure Location where
  private mk ::
  /-- Zero-based byte offset. -/
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

namespace Location

@[inline]
def Internal.new (offset line column : Nat) : Location :=
  { offset, line, column }

@[simp]
theorem Internal.offset_new (offset line column : Nat) :
    (Internal.new offset line column).offset = offset :=
  (rfl)

@[simp]
theorem Internal.line_new (offset line column : Nat) :
    (Internal.new offset line column).line = line :=
  (rfl)

@[simp]
theorem Internal.column_new (offset line column : Nat) :
    (Internal.new offset line column).column = column :=
  (rfl)

/-- A location is the one built from its numbers. -/
@[simp]
theorem Internal.new_eta (location : Location) :
    Internal.new location.offset location.line location.column = location :=
  (rfl)

/-- Two locations with the same numbers are equal. -/
theorem Internal.new_inj {offset line column offset' line' column' : Nat} :
    Internal.new offset line column = Internal.new offset' line' column' ↔
      offset = offset' ∧ line = line' ∧ column = column' := by
  constructor
  · intro h
    exact ⟨congrArg Location.offset h, congrArg Location.line h, congrArg Location.column h⟩
  · rintro ⟨rfl, rfl, rfl⟩
    rfl

/-- Locations are equal if their numbers are. -/
@[ext]
theorem ext {a b : Location} (offset : a.offset = b.offset) (line : a.line = b.line)
    (column : a.column = b.column) : a = b := by
  cases a; cases b; cases offset; cases line; cases column; rfl

def min (self other : Location) : Location :=
  if self.offset ≤ other.offset then self else other

def max (self other : Location) : Location :=
  if self.offset ≥ other.offset then self else other

/-- Location directly at the byte stream start. -/
@[expose, inline]
def initial : Location :=
  Internal.new 0 0 0

@[expose, inline]
def afterColumn (self : Location) : Location :=
  Internal.new (self.offset + 1) self.line (self.column + 1)

@[expose, inline]
def afterByte (self : Location) (c : UInt8) : Location :=
  /- LEAN: Lean has no byte literals like `b'\n'`; a character literal is converted with
  `Char.toUInt8`, which keeps the low byte and is exact for ASCII. -/
  if c == '\n'.toUInt8 then
    Internal.new (self.offset + 1) (self.line + 1) 0
  else
    self.afterColumn

end Location

/-- A value located in an SMT-LIB stream. -/
/- LEAN: the constructor is private, as Rust's fields are, and the library builds a located value
with `Located.Internal.new`. The fields are read-only accessor functions (`located.value`,
`located.location`); they replace the Rust getters. `into_value` is the same as `value`, since
Lean values are not moved out of. -/
structure Located (V : Type) where
  private mk ::
  /-- Returns a reference to the value. -/
  value : V
  /-- Returns the location. -/
  location : Location
  deriving BEq, Hashable, Repr

@[inline]
def Located.Internal.new {V : Type} (value : V) (location : Location) : Located V :=
  { value, location }

@[simp]
theorem Located.Internal.value_new {V : Type} (value : V) (location : Location) :
    (Located.Internal.new value location).value = value :=
  (rfl)

@[simp]
theorem Located.Internal.location_new {V : Type} (value : V) (location : Location) :
    (Located.Internal.new value location).location = location :=
  (rfl)

/-- A located value is the one built from its value and location. -/
@[simp]
theorem Located.Internal.new_eta {V : Type} (located : Located V) :
    Located.Internal.new located.value located.location = located :=
  (rfl)

/-- Two located values built from the same value and location are equal. -/
theorem Located.Internal.new_inj {V : Type} {value value' : V} {location location' : Location} :
    Located.Internal.new value location = Located.Internal.new value' location' ↔
      value = value' ∧ location = location' := by
  constructor
  · intro h
    exact ⟨congrArg Located.value h, congrArg Located.location h⟩
  · rintro ⟨rfl, rfl⟩
    rfl

/--
Span of an SMT-LIB element.

The span is a half-open range `[start, end)` between locations.
-/
/- LEAN: Rust's span holds its two locations inline. A Lean structure holds a structure field
as a pointer to a separate object, so a span of two `Location` fields would take three
allocations. The span therefore holds the six numbers itself, and `start` and `end` are
functions that build the locations when asked. -/
structure _root_.BSmtLib.Span where
  private mk ::
  private startOffset : Nat
  private startLine : Nat
  private startColumn : Nat
  private endOffset : Nat
  private endLine : Nat
  private endColumn : Nat
  deriving BEq, Hashable, Inhabited

@[inline]
def start (self : Span) : Location :=
  Location.Internal.new self.startOffset self.startLine self.startColumn

/- LEAN: `end` is a keyword in Lean, so the name is written in guillemets where it is
declared; `span.end` works as usual. -/
@[inline]
def «end» (self : Span) : Location :=
  Location.Internal.new self.endOffset self.endLine self.endColumn

@[inline]
def Internal.newUnchecked (start «end» : Location) : Span :=
  { startOffset := start.offset, startLine := start.line, startColumn := start.column,
    endOffset := «end».offset, endLine := «end».line, endColumn := «end».column }

/--
A span given by the numbers of its two locations.
-/
/- LEAN: not in Rust; it builds a span without building its locations first. -/
@[inline]
def Internal.ofNumbers (startOffset startLine startColumn endOffset endLine endColumn : Nat) :
    Span :=
  { startOffset, startLine, startColumn, endOffset, endLine, endColumn }

/- LEAN: the fields of a span are private to this module, so the modules that build a span with
`Internal.ofNumbers` read its locations back through these. -/
/-- The start of a span given by its numbers. -/
theorem start_ofNumbers (startOffset startLine startColumn endOffset endLine endColumn : Nat) :
    (Internal.ofNumbers startOffset startLine startColumn endOffset endLine endColumn).start =
      Location.Internal.new startOffset startLine startColumn :=
  (rfl)

/-- The end of a span given by its numbers. -/
theorem end_ofNumbers (startOffset startLine startColumn endOffset endLine endColumn : Nat) :
    (Internal.ofNumbers startOffset startLine startColumn endOffset endLine endColumn).end =
      Location.Internal.new endOffset endLine endColumn :=
  (rfl)

/--
A span within one line: the line, the offset of its start, and the
offsets of the span on it.
-/
@[inline]
def Internal.onLine (line lineStart start «end» : Nat) : Span :=
  ofNumbers start line (start - lineStart) «end» line («end» - lineStart)

@[inline]
def Internal.newEmpty (location : Location) : Span :=
  newUnchecked location location

def Internal.newZero : Span :=
  newEmpty Location.initial

def isEmpty (self : Span) : Bool :=
  self.start == self.end

def join (self other : Span) : Span :=
  Internal.newUnchecked (self.start.min other.start) (self.end.max other.end)

/- LEAN: the format is built, not rendered: rendering a format (`Std.Format.pretty`, which `s!`
and `toString` call) holds a `panic`, which a `Repr` instance is not to reach. -/
instance : Repr Span where
  reprPrec span _ :=
    .text "{ start := " ++ repr span.start ++ .text ", end := " ++ repr span.end ++ .text " }"

end BSmtLib.Span
