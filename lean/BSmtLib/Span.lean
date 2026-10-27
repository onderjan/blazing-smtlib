module

public section

/-!
# Locations and spans in a byte stream, used in lexer tokens and errors

A location records an offset in bytes and line/column information, and a span is a half-open
range `[start, end)` between locations. The span can be empty, which is usually the case if an
error occurred at the end of input due to some unclosed item.

The locations and spans are given by the lexer for tokens via `LexerCursor.span`. `Lexer` and
`Reader` produce the result value wrapped in `Located` on success and a spanned error on failure.
Parsers and handlers do not interact with locations and spans.
-/

namespace BSmtLib.Span

/--
Location in a byte stream.

All counts are in bytes. While SMT-LIB accepts both CR and LF as a comment separator, the
line/column location convention here is that only LF starts a new line, for compatibility with
both the LF and the CRLF line endings.

The offset, line, and column all start at zero.

The location is guaranteed to be valid with respect to the offset and line/column: as each
terminated line must contain at least one byte (LF), the offset must be equal to or greater than
the sum of line and column.
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
  `Repr` is `Debug`, `Ord` is `Ord`, which compares the offsets, then the lines, then the
  columns. `Inhabited` provides a default value, which Lean needs for the
  return type of `panic!` and of functions marked `partial`; values are copied freely in
  Lean, so there is no counterpart of `Clone` and `Copy`. -/
  deriving BEq, Hashable, Repr, Inhabited, Ord

/--
Error constructing a location that would be invalid.

See `Location` for the validity condition.
-/
structure InvalidLocationError where
  deriving BEq, Hashable, Repr, Inhabited

@[no_expose] instance : ToString InvalidLocationError := ⟨fun _ => "invalid location"⟩

namespace Location

/- LEAN: Rust's `new_unchecked`, crate-private there; the caller ensures what `new` checks. -/
@[inline]
def Internal.new (offset line column : Nat) : Location :=
  { offset, line, column }

/--
The location at the offset, the line and the column; an error if the line and the column cannot
be at the offset, as every line before and every column on the line take at least one byte.
-/
def new (offset line column : Nat) : Except InvalidLocationError Location :=
  -- each line before ends with a line feed, each column is a byte
  if line + column ≤ offset then .ok (Internal.new offset line column) else .error {}

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

/- LEAN: Rust's `Ord::min` and `Ord::max`, by the derived order: of two locations that compare
equal, `min` gives the first and `max` the second. -/
@[no_expose] instance : Min Location where
  min self other := match compare self other with
    | .gt => other
    | _ => self

@[no_expose] instance : Max Location where
  max self other := match compare self other with
    | .gt => self
    | _ => other

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

/-- Value located in a byte stream. -/
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
Span of an item in a byte stream.

The span is a half-open range `[start, end)` between locations.

The span is guaranteed to be valid with respect to the offsets and line/column of its locations:
the end is not before the start, and the bytes between them hold what separates them. On the same
line, the column advances by exactly the number of bytes. On a later line, each line ended takes at
least one byte (LF), and each column before the end takes one byte.
-/
/- LEAN: Rust's span holds its two locations inline. A Lean structure holds a structure field
as a pointer to a separate object, so a span of two `Location` fields would take three
allocations. The span therefore holds the six numbers itself, and `start` and `end` are
functions that build the locations when asked. The derived `Ord` compares the numbers in their
order, which is Rust's order of the start, then the end. -/
structure _root_.BSmtLib.Span where
  private mk ::
  private startOffset : Nat
  private startLine : Nat
  private startColumn : Nat
  private endOffset : Nat
  private endLine : Nat
  private endColumn : Nat
  deriving BEq, Hashable, Inhabited, Ord

/--
Error constructing a span that would be invalid.

See `Span` for the validity condition.
-/
structure InvalidSpanError where
  deriving BEq, Hashable, Repr, Inhabited

@[no_expose] instance : ToString InvalidSpanError := ⟨fun _ => "invalid span"⟩

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

/-- Whether the end is not before the start and the bytes between them hold what separates them,
by the offsets and by the lines and columns. -/
private def isAllowed (start «end» : Location) : Bool :=
  -- the end offset must not be less than the start offset; the difference is the number of bytes
  -- between them
  start.offset ≤ «end».offset &&
    let difference := «end».offset - start.offset
    match compare «end».line start.line with
    -- the end line must not be less than the start line
    | .lt => false
    -- on the same line, the column advances by exactly the number of bytes
    | .eq => start.column ≤ «end».column && «end».column - start.column == difference
    -- on a later line, each line ended takes at least one byte (LF), and each column of the end
    -- line takes one byte
    | .gt => «end».line - start.line + «end».column ≤ difference

/-- The span from the start to the end; an error if the span would be invalid. -/
def new (start «end» : Location) : Except InvalidSpanError Span :=
  if isAllowed start «end» then .ok (Internal.newUnchecked start «end») else .error {}

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

/- LEAN: the format is built, not rendered: rendering a format (`Std.Format.pretty`, which `s!`
and `toString` call) holds a `panic`, which a `Repr` instance is not to reach. -/
instance : Repr Span where
  reprPrec span _ :=
    .text "{ start := " ++ repr span.start ++ .text ", end := " ++ repr span.end ++ .text " }"

end BSmtLib.Span
