module

public meta import BSmtLib.Token
public meta import BSmtLib.Token.Reserved
public meta import BSmtLib.Lexer.Internal.CharClass
public meta import BSmtLib.Lexer.Internal.Helpers
import all BSmtLib.Token.Reserved
import all BSmtLib.Lexer.Internal.CharClass

@[expose] public section

/-!
# The library's assertions

The checks that the Rust crate makes with `assert!` in `const` blocks: that the tables and flags
of the token categories, the reserved words and the lexer are as the code that reads them
assumes. `#guard` evaluates each when this module is built and fails the build if it is false.
They are here and not beside the tables, so that building the library evaluates nothing.
-/

namespace BSmtLib.Facts.Asserts

open BSmtLib.Lexer

/-! The token categories (`Token.lean`). -/

-- the types are read back from the batch as they were written to it
#guard [Token.TokenCategory.parenOpen, .parenClose, .numeral, .decimal, .hexadecimal, .binary,
    .string, .keyword, .unquotedSymbol, .quotedSymbol, .whitespace, .comment, .endOfFile].all
  fun ty => Token.TokenCategory.Internal.ofUInt8 (Token.TokenCategory.Internal.toUInt8 ty) == ty

/-! The reserved words (`Token/Reserved.lean`). A word that shared a slot would have been
overwritten in the table by a later one. -/

-- the reserved-word hash must be perfect: every word lands in a slot of its own
#guard Token.Reserved.reservedWords.all fun (word, _) =>
  if h : 0 < word.toByteSlice.size then
    Token.Reserved.Internal.reservedTable[
        (Token.Reserved.Internal.reservedSlot word.toByteSlice h).val]?.map (·.1) == some word
  else
    false

/-! The run flags (`Lexer/Internal/Internal.CharClass.lean`). -/

-- the run flags partition the byte into single bits, each at its own place
#guard (List.range 8).all fun i =>
  Internal.CharClass.RUN_FLAG_BITS[i]? == some ((1 : UInt8) <<< i.toUInt8)
#guard Internal.CharClass.RUN_FLAG_BITS.foldl (· ||| ·) 0 == 0xFF

/-! The fast flags (`Lexer/Internal/Internal.Helpers.lean`). -/

-- fast masks partition u8 and are pairwise distinct
#guard (Internal.Helpers.FAST_MASKS.foldl (init := some (0 : UInt8)) fun union mask =>
    union.bind fun union => if union &&& mask == 0 then some (union ||| mask) else none)
  == some 0xFF

-- fast run flags contain exactly the three run flags we need
#guard (Internal.CharClass.RUN_SIMPLE_SYMBOL ||| Internal.CharClass.RUN_NON_LF_WHITESPACE |||
    Internal.CharClass.RUN_QUOTED_PLAIN) &&& Internal.Helpers.FAST_RUN_MASK
    == Internal.Helpers.FAST_RUN_MASK
  && (Internal.CharClass.RUN_STRING_PLAIN ||| Internal.CharClass.RUN_DIGIT |||
      Internal.CharClass.RUN_HEX_DIGIT |||
      Internal.CharClass.RUN_BINARY_DIGIT ||| Internal.CharClass.RUN_COMMENT_PLAIN)
    &&& Internal.Helpers.FAST_RUN_MASK == 0

-- a byte carries the delimiter flag exactly when it is whitespace, a parenthesis, or a semicolon
#guard (List.range 256).all fun i =>
  let c := i.toUInt8
  (Internal.Helpers.fastFlags c &&& Internal.Helpers.FAST_DELIM != 0)
    == (c == byte! ' ' || c == byte! '\t' || c == byte! '\n' || c == byte! '\r'
      || c == byte! '(' || c == byte! ')' || c == byte! ';')

-- a byte is fast exactly when its START class is one the fast path replaces; parentheses
-- are dispatched by byte tests ahead of the table, so they are neither fast nor covered here
#guard (List.range 256).all fun i =>
  let start := Internal.Helpers.startOf i.toUInt8
  (Internal.Helpers.fastFlags i.toUInt8 &&& Internal.Helpers.FAST_ON != 0)
    == (start == .whitespace || start == .pipe || start == .symbol)

end BSmtLib.Facts.Asserts
