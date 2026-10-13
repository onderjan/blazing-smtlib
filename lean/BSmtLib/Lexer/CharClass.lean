import Std.Data.ByteSlice

namespace BSmtLib.Lexer

/--
Class of a character following the SMT-LIB standard.

In SMT-LIB, the characters are encoded in 8-bit bytes,
with the bytes 0..=127 denoting US-ASCII characters.
The meaning of values 128..=255 is not lexically defined
but all are considered printable non-whitespace characters.

'Non-printable' characters are US-ASCII control characters:
those with byte codes 0..=31 and 127 (DEL).
'Printable' characters have byte codes 32..=126 and 128..=255.

'Whitespace' characters are only TAB (9), LF (10), CR (13), SPACE (32).
'Non-whitespace' characters are all the others.

Specially, 32 (SPACE) is both printable and whitespace.
0..=31 except (9, 10, 13) and 127 (DEL) are neither printable nor whitespace.
-/
inductive CharClass where
  /-- any non-printable character except for TAB, LF, CR, and DEL
  meaning 0..=31 except (9, 10, 13) -/
  | otherNonPrintable
  /-- TAB (9) -/
  | tab
  /-- LF (10) / CR (13) -/
  | lineBreak
  /-- ' ' (32) -/
  | space
  /-- '"' (34) -/
  | doubleQuote
  /-- '#' (35) -/
  | hash
  /-- '(' (40) -/
  | parenOpen
  /-- ')' (41) -/
  | parenClose
  /-- '.' (46), this is also allowed in symbols -/
  | dot
  /-- ':' (58) -/
  | colon
  /-- ';' (59) -/
  | semicolon
  /-- '0'-'9' (48-57) -/
  | digit
  /-- 'A'-'Z' (65-90) or 'a'-'z' (97-122) -/
  | letter
  /-- '\' (92) -/
  | backslash
  /-- '|' (124) -/
  | pipe
  /-- DEL (127) -/
  | del
  /-- not letters or digits or dot but allowed in symbols (all ASCII printable) -/
  | special
  /-- not in any interesting category, code in 33..=126 -/
  | otherAsciiPrintable
  /-- any character greater or equal to 128 -/
  | nonAscii
  deriving BEq, Repr, Inhabited

/- LEAN: Lean has no byte literals like `b'('`; `byte! '('` stands for one. It is a macro, so
that the byte is a constant in the compiled code: converting the character with a function
is not folded by the compiler and costs a call at every use. -/
/-- The byte of an ASCII character literal. -/
macro "byte! " c:char : term =>
  `(($(Lean.Syntax.mkNumLit (toString c.getChar.toNat)) : UInt8))

namespace CharClass

/- LEAN: Lean's `match` cannot match a byte against character patterns and ranges as Rust
does, so the classification is a chain of comparisons in the order of the Rust arms. -/
def classify (c : UInt8) : CharClass :=
  let n := c.toNat
  if (65 ≤ n && n ≤ 90) || (97 ≤ n && n ≤ 122) then
    .letter
  else if 48 ≤ n && n ≤ 57 then
    .digit
  else if n ≥ 128 then
    .nonAscii
  else if c == byte! '\t' then .tab
  else if c == byte! '\r' || c == byte! '\n' then .lineBreak
  else if c == byte! ' ' then .space
  else if c == byte! '#' then .hash
  else if c == byte! '"' then .doubleQuote
  else if c == byte! '(' then .parenOpen
  else if c == byte! ')' then .parenClose
  else if c == byte! '.' then .dot
  else if c == byte! ':' then .colon
  else if c == byte! ';' then .semicolon
  else if c == byte! '\\' then .backslash
  else if c == byte! '|' then .pipe
  else if "~!@$%^&*_-+=<>?/".toList.any (fun s => s.toUInt8 == c) then .special
  else if n == 127 then .del
  -- below 128 and not in any interesting class
  else if n < 32 then .otherNonPrintable
  else .otherAsciiPrintable

@[inline]
def isPrintableOrWhitespace (self : CharClass) : Bool :=
  -- everything except other non-printable and DEL
  !(self == .otherNonPrintable || self == .del)

@[inline]
def isAllowedInSimpleSymbol (self : CharClass) : Bool :=
  -- letters, digits, special, dot
  self == .letter || self == .digit || self == .special || self == .dot

end CharClass

def RUN_STRING_PLAIN : UInt8 := (1 : UInt8) <<< 0
def RUN_DIGIT : UInt8 := (1 : UInt8) <<< 1
def RUN_HEX_DIGIT : UInt8 := (1 : UInt8) <<< 2
def RUN_BINARY_DIGIT : UInt8 := (1 : UInt8) <<< 3
def RUN_NON_LF_WHITESPACE : UInt8 := (1 : UInt8) <<< 4
def RUN_QUOTED_PLAIN : UInt8 := (1 : UInt8) <<< 5
def RUN_SIMPLE_SYMBOL : UInt8 := (1 : UInt8) <<< 6
def RUN_COMMENT_PLAIN : UInt8 := (1 : UInt8) <<< 7

/-- The run flags, one per bit of the byte. -/
private def RUN_FLAG_BITS : Array UInt8 :=
  #[RUN_STRING_PLAIN, RUN_DIGIT, RUN_HEX_DIGIT, RUN_BINARY_DIGIT, RUN_NON_LF_WHITESPACE,
    RUN_QUOTED_PLAIN, RUN_SIMPLE_SYMBOL, RUN_COMMENT_PLAIN]

/- LEAN: `#guard` checks the condition when the module is built, as the Rust `assert!` in a
`const` block does. -/
-- the run flags partition the byte into single bits, each at its own place
#guard (List.range 8).all fun i => RUN_FLAG_BITS[i]? == some ((1 : UInt8) <<< i.toUInt8)
#guard RUN_FLAG_BITS.foldl (· ||| ·) 0 == 0xFF

namespace CharClass

def runFlags (c : UInt8) : UInt8 := Id.run do
  let class_ := classify c
  let mut flags : UInt8 := 0
  if class_.isAllowedInSimpleSymbol then
    flags := flags ||| RUN_SIMPLE_SYMBOL
  if class_ == .digit then
    flags := flags ||| RUN_DIGIT
  -- letter does not separate a-f from the rest
  if class_ == .digit || (byte! 'a' ≤ c && c ≤ byte! 'f') || (byte! 'A' ≤ c && c ≤ byte! 'F') then
    flags := flags ||| RUN_HEX_DIGIT
  if c == byte! '0' || c == byte! '1' then
    flags := flags ||| RUN_BINARY_DIGIT
  if (class_ == .tab || class_ == .space || class_ == .lineBreak) && c != byte! '\n' then
    flags := flags ||| RUN_NON_LF_WHITESPACE
  -- lineBreak covers CR too, and CR is plain inside strings and quoted symbols;
  -- only LF ends the run (it has to be marked before the scan continues)
  let plainText := class_.isPrintableOrWhitespace && c != byte! '\n'
  if plainText && !(class_ == .pipe || class_ == .backslash) then
    flags := flags ||| RUN_QUOTED_PLAIN
  if plainText && class_ != .doubleQuote then
    flags := flags ||| RUN_STRING_PLAIN
  if class_ != .lineBreak then
    flags := flags ||| RUN_COMMENT_PLAIN
  flags

end CharClass

/- LEAN: computed once when the module is loaded, where Rust computes the `static` at
compile time. -/
/-- The run flags of every byte. -/
def RUN_FLAGS : ByteArray :=
  ⟨(Array.range 256).map fun i => CharClass.runFlags i.toUInt8⟩

/-- The table of run flags has an entry for every byte. -/
theorem size_RUN_FLAGS : RUN_FLAGS.size = 256 := by
  simp [RUN_FLAGS, ByteArray.size]

/-- The run flags of the byte. -/
@[inline]
def runFlagsOf (c : UInt8) : UInt8 :=
  RUN_FLAGS[c.toNat]'(size_RUN_FLAGS ▸ c.toNat_lt)

/- LEAN: Rust's lexer reads a `&[u8]` with `usize` indices. Here the lexer reads the slice's
array with `USize` positions in the array, from `start` to `stop`: a `Nat` would be checked
for being small at every operation, and the functions of the standard library's `ByteSlice`
are calls that the compiler does not inline. `stop_le` is the proof that every position
below `stop` is in the array, so the reads need no bounds check; it is established once, where
the lexer receives the slice (see `Input.ofSlice?`). A position never wraps around: the
lexer only adds to a position that is below `stop`, and only one. -/
/-- The input slice of the lexer: the bytes of `bytes` from `start` to `stop`. -/
structure Input where
  /-- The array the slice is in. -/
  bytes : ByteArray
  /-- The position of the first byte of the slice. -/
  start : USize
  /-- The position after the last byte of the slice. -/
  stop : USize
  /-- Every position below `stop` is in the array. -/
  stop_le : stop.toNat ≤ bytes.size

namespace Input

/-
LEAN: that the end of an array is below `USize.size` holds for every array in memory, but
Lean's standard library states no lemma for it, so the lexer checks it, once per slice.
-/
/-- The input over the slice, whose end is below `USize.size`. -/
def ofSlice (slice : ByteSlice) (h : slice.stop < USize.size) : Input :=
  { bytes := slice.byteArray
    start := USize.ofNat slice.start
    stop := USize.ofNatLT slice.stop h
    stop_le := by
      simp only [USize.toNat_ofNatLT]
      exact slice.stop_le_size_byteArray }

/-- The byte at `position`, if it is below the end of the slice. -/
@[inline]
def get? (input : Input) (position : USize) : Option UInt8 :=
  if h : position < input.stop then
    some (input.bytes.uget position (by
      have := USize.lt_iff_toNat_lt.mp h
      have := input.stop_le
      omega))
  else
    none

/-- The byte at `position`, which is below the end of the slice. -/
@[inline]
def get (input : Input) (position : USize) (h : position.toNat < input.stop.toNat) : UInt8 :=
  input.bytes.uget position (by have := input.stop_le; omega)

/-- The byte at a position below the end of the slice is the one `get?` gives. -/
theorem get?_eq_some_get (input : Input) {position : USize}
    (h : position.toNat < input.stop.toNat) : input.get? position = some (input.get position h) := by
  unfold get? get
  simp only [USize.lt_iff_toNat_lt.mpr h, dite_true]

/-- A position within the slice that is not its end is below the end. -/
theorem lt_stop_of_ne {input : Input} {position : USize}
    (hle : position.toNat ≤ input.stop.toNat) (hne : ¬ (position == input.stop) = true) :
    position.toNat < input.stop.toNat := by
  rcases Nat.lt_or_eq_of_le hle with h | h
  · exact h
  · exact absurd (beq_iff_eq.mpr (USize.toNat_inj.mp h)) hne

end Input

/-- Whether the byte ends a run as it carries no flags from the mask. -/
@[inline]
def endsRun (c : UInt8) (mask : UInt8) : Bool :=
  runFlagsOf c &&& mask == 0

/- LEAN: Rust calls `start + run_end(&slice[start..], mask)`; taking `start` here avoids
building a sub-slice. The scan is a recursive function: Lean has no `while` that it can prove
to end, and `termination_by` names the quantity that shrinks with every call, with the proof
after `decreasing_by`. The test is a function argument for the two kinds of runs; the scan
is `@[specialize]`, so that each kind gets its own compiled scan instead of a call through a
closure for every byte. The 4-byte unrolling of the Rust scan is left out. -/

/-!
The scan of the runs. It is public, in `Internal`, only so that the proofs of the lexers can read
it; it is not a part of the library's interface.
-/

namespace Internal

/-- Whether the byte at `position` of `bytes` ends the run. -/
abbrev RunTest := (bytes : ByteArray) → (position : USize) → position.toNat < bytes.size → Bool

/-- The first position from `position` to `stop` of a byte ending the run, `stop` if none. -/
@[specialize]
def runEndIn (test : RunTest) (bytes : ByteArray) (position stop : USize)
    (hstop : stop.toNat ≤ bytes.size) : USize :=
  if h : position < stop then
    if test bytes position (by have := USize.lt_iff_toNat_lt.mp h; omega) then position
    else runEndIn test bytes (position + 1) stop hstop
  else
    position
termination_by stop.toNat - position.toNat
decreasing_by
  have h1 := USize.lt_iff_toNat_lt.mp h
  have h2 := USize.toNat_lt_size stop
  have h3 : USize.size = 2 ^ System.Platform.numBits := USize.size_eq_two_pow
  rw [USize.toNat_add, USize.toNat_one, Nat.mod_eq_of_lt (by omega)]
  omega

end Internal

open Internal

/--
Position of the first byte at `start` or after it carrying no flags from the
mask, the end of the slice if none, or `start` if it is at the end or after it.

In other words, the end of the longest run from `start` where all bytes carry
at least one flag from the mask.
-/
@[inline]
def runEnd (input : Input) (start : USize) (mask : UInt8) : USize :=
  runEndIn (fun bytes position h => endsRun (bytes.uget position h) mask) input.bytes start
    input.stop input.stop_le

/--
Like `runEnd`, but a byte continues the run only if it has all the flags of
the mask.
-/
@[inline]
def runEndAll (input : Input) (start : USize) (mask : UInt8) : USize :=
  runEndIn (fun bytes position h => runFlagsOf (bytes.uget position h) &&& mask != mask)
    input.bytes start input.stop input.stop_le

/- LEAN: the facts below are what the loops of the lexer are shown to end by: a loop goes on
from a position after one it has read a byte at, and so closer to the end of the slice. -/

/-- The position after one below another does not wrap around. -/
theorem toNat_add_one_of_lt {position bound : USize} (h : position.toNat < bound.toNat) :
    (position + 1).toNat = position.toNat + 1 := by
  have := USize.toNat_lt_size bound
  have : USize.size = 2 ^ System.Platform.numBits := USize.size_eq_two_pow
  rw [USize.toNat_add, USize.toNat_one, Nat.mod_eq_of_lt (by omega)]

namespace Input

/-- A position with a byte is below the end of the slice. -/
theorem lt_stop_of_get? {input : Input} {position : USize} {c : UInt8}
    (h : input.get? position = some c) : position.toNat < input.stop.toNat := by
  unfold get? at h
  split at h
  · exact USize.lt_iff_toNat_lt.mp ‹_›
  · cases h

/-- The position after one with a byte is below the end of the slice or at it. -/
theorem toNat_add_one_of_get? {input : Input} {position : USize} {c : UInt8}
    (h : input.get? position = some c) :
    position.toNat < input.stop.toNat ∧ (position + 1).toNat = position.toNat + 1 :=
  ⟨lt_stop_of_get? h, toNat_add_one_of_lt (lt_stop_of_get? h)⟩

end Input

private theorem le_runEndIn (test : RunTest) (bytes : ByteArray) (position stop : USize)
    (hstop : stop.toNat ≤ bytes.size) :
    position.toNat ≤ (runEndIn test bytes position stop hstop).toNat := by
  fun_induction runEndIn test bytes position stop hstop with
  | case1 => exact Nat.le_refl _
  | case2 position h _ ih =>
    rw [toNat_add_one_of_lt (USize.lt_iff_toNat_lt.mp h)] at ih
    omega
  | case3 => exact Nat.le_refl _

private theorem lt_runEndIn (test : RunTest) (bytes : ByteArray) (position stop : USize)
    (hstop : stop.toNat ≤ bytes.size) (h : position < stop)
    (hcontinues : test bytes position (by have := USize.lt_iff_toNat_lt.mp h; omega) = false) :
    position.toNat < (runEndIn test bytes position stop hstop).toNat := by
  rw [runEndIn]
  simp only [h, hcontinues, dite_true, Bool.false_eq_true, ite_false]
  have := le_runEndIn test bytes (position + 1) stop hstop
  rw [toNat_add_one_of_lt (USize.lt_iff_toNat_lt.mp h)] at this
  omega

/-- A run ends at its start or after it. -/
theorem le_runEnd (input : Input) (start : USize) (mask : UInt8) :
    start.toNat ≤ (runEnd input start mask).toNat :=
  le_runEndIn _ _ _ _ _

/-- A run ends at its start or after it. -/
theorem le_runEndAll (input : Input) (start : USize) (mask : UInt8) :
    start.toNat ≤ (runEndAll input start mask).toNat :=
  le_runEndIn _ _ _ _ _

private theorem runEndIn_le (test : RunTest) (bytes : ByteArray) (position stop : USize)
    (hstop : stop.toNat ≤ bytes.size) (h : position.toNat ≤ stop.toNat) :
    (runEndIn test bytes position stop hstop).toNat ≤ stop.toNat := by
  fun_induction runEndIn test bytes position stop hstop with
  | case1 => exact h
  | case2 position hlt _ ih =>
    apply ih
    have := USize.lt_iff_toNat_lt.mp hlt
    rw [toNat_add_one_of_lt this]
    omega
  | case3 => exact h

/-- A run from a position within the slice ends within it. -/
theorem runEnd_le (input : Input) {start : USize} (mask : UInt8)
    (h : start.toNat ≤ input.stop.toNat) : (runEnd input start mask).toNat ≤ input.stop.toNat :=
  runEndIn_le _ _ _ _ _ h

/-- A run from a position within the slice ends within it. -/
theorem runEndAll_le (input : Input) {start : USize} (mask : UInt8)
    (h : start.toNat ≤ input.stop.toNat) :
    (runEndAll input start mask).toNat ≤ input.stop.toNat :=
  runEndIn_le _ _ _ _ _ h

/-- A run ends after its start if the byte at the start does not end it. -/
theorem lt_runEnd {input : Input} {start : USize} {c : UInt8} (mask : UInt8)
    (h : input.get? start = some c) (hc : endsRun c mask = false) :
    start.toNat < (runEnd input start mask).toNat := by
  unfold Input.get? at h
  split at h
  · rename_i hlt
    apply lt_runEndIn _ _ _ _ _ hlt
    simp only [Option.some.injEq] at h
    rw [h]
    exact hc
  · cases h

end BSmtLib.Lexer
