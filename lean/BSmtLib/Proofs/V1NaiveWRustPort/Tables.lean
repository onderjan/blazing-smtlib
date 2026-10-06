import BSmtLib.Proofs.V1NaiveWRustPort.Bytes
import BSmtLib.Proofs.Lexer.WRustPort

/-!
# The Rust port's byte tables against the naive lexer's byte classes

The Rust port classifies a byte by its tables (`RUN_FLAGS`, `FAST`, `START`); each class is one
of the naive lexer's byte classes, checked by the kernel for every byte.
-/

namespace BSmtLib.Proofs.Lexer.V1NaiveWRustPort

open V1Naive BSmtLib.Proofs.Simulation
open BSmtLib.Lexer (endsRun RUN_FLAGS RUN_DIGIT RUN_SIMPLE_SYMBOL RUN_HEX_DIGIT RUN_BINARY_DIGIT
  RUN_NON_LF_WHITESPACE RUN_QUOTED_PLAIN RUN_STRING_PLAIN RUN_COMMENT_PLAIN)

/-! ## The byte tables -/

/-- A property of every byte, from its check for every number below 256. -/
theorem byte_table {P : UInt8 → Prop} (h : ∀ n, n < 256 → P n.toUInt8) (c : UInt8) : P c := by
  have := h c.toNat c.toNat_lt
  rwa [show c.toNat.toUInt8 = c by simp] at this

theorem isDelimiter_eq (c : UInt8) : BSmtLib.Lexer.isDelimiter c = V1Naive.isDelimiter c :=
  byte_table (P := fun c => BSmtLib.Lexer.isDelimiter c = V1Naive.isDelimiter c)
    (by decide +kernel) c

theorem endsRun_digit (c : UInt8) : endsRun c RUN_DIGIT = !isDigit c :=
  byte_table (P := fun c => endsRun c RUN_DIGIT = !isDigit c) (by decide +kernel) c

theorem endsRun_symbol (c : UInt8) : endsRun c RUN_SIMPLE_SYMBOL = !isSymbolByte c :=
  byte_table (P := fun c => endsRun c RUN_SIMPLE_SYMBOL = !isSymbolByte c) (by decide +kernel) c

theorem endsRun_hex (c : UInt8) : endsRun c RUN_HEX_DIGIT = !Radix.hexadecimal.allows c :=
  byte_table (P := fun c => endsRun c RUN_HEX_DIGIT = !Radix.hexadecimal.allows c)
    (by decide +kernel) c

theorem endsRun_binary (c : UInt8) : endsRun c RUN_BINARY_DIGIT = !Radix.binary.allows c :=
  byte_table (P := fun c => endsRun c RUN_BINARY_DIGIT = !Radix.binary.allows c)
    (by decide +kernel) c

theorem endsRun_whitespace (c : UInt8) : endsRun c RUN_NON_LF_WHITESPACE = !isWhitespaceRun c :=
  byte_table (P := fun c => endsRun c RUN_NON_LF_WHITESPACE = !isWhitespaceRun c)
    (by decide +kernel) c

theorem endsRun_quoted (c : UInt8) : endsRun c RUN_QUOTED_PLAIN = !isQuotedRun c :=
  byte_table (P := fun c => endsRun c RUN_QUOTED_PLAIN = !isQuotedRun c) (by decide +kernel) c

theorem endsRun_string (c : UInt8) : endsRun c RUN_STRING_PLAIN = !isStringRun c :=
  byte_table (P := fun c => endsRun c RUN_STRING_PLAIN = !isStringRun c) (by decide +kernel) c

theorem endsRun_comment (c : UInt8) : endsRun c RUN_COMMENT_PLAIN = !isCommentRun c :=
  byte_table (P := fun c => endsRun c RUN_COMMENT_PLAIN = !isCommentRun c) (by decide +kernel) c

/-- Whether the byte is a part of a string under version 2.0 that the Rust port's run takes:
any byte of its content but the quote, the backslash, the line feed and the pipe. -/
def isLegacyRun (c : UInt8) : Bool :=
  isLegacyStringRun c && c != byte! '|'

theorem endsRunAll_legacy (c : UInt8) :
    (RUN_FLAGS.get! c.toNat &&& (RUN_STRING_PLAIN ||| RUN_QUOTED_PLAIN) !=
      (RUN_STRING_PLAIN ||| RUN_QUOTED_PLAIN)) = !isLegacyRun c :=
  byte_table (P := fun c => (RUN_FLAGS.get! c.toNat &&& (RUN_STRING_PLAIN ||| RUN_QUOTED_PLAIN) !=
      (RUN_STRING_PLAIN ||| RUN_QUOTED_PLAIN)) = !isLegacyRun c) (by decide +kernel) c

open BSmtLib.Lexer (fastFlags FAST_ON FAST_DELIM FAST_EMIT FAST_PIPE) in
/-- The fast flags of a byte: none for a byte off the fast path, and otherwise those of
whitespace other than a line feed, of the pipe, or of a simple symbol that does not start with a
digit. -/
theorem fastFlags_cases (c : UInt8) :
    (fastFlags c &&& FAST_ON != 0) = false ∨
      (fastFlags c = FAST_ON ||| FAST_DELIM ||| RUN_NON_LF_WHITESPACE ∧ isWhitespaceRun c = true) ∨
      (fastFlags c = FAST_ON ||| FAST_EMIT ||| FAST_PIPE ||| RUN_QUOTED_PLAIN ∧ c = 124) ∨
      (fastFlags c = FAST_ON ||| FAST_EMIT ||| RUN_SIMPLE_SYMBOL ∧ isSymbolByte c = true ∧
        isDigit c = false) :=
  byte_table (P := fun c => (fastFlags c &&& FAST_ON != 0) = false ∨
      (fastFlags c = FAST_ON ||| FAST_DELIM ||| RUN_NON_LF_WHITESPACE ∧ isWhitespaceRun c = true) ∨
      (fastFlags c = FAST_ON ||| FAST_EMIT ||| FAST_PIPE ||| RUN_QUOTED_PLAIN ∧ c = 124) ∨
      (fastFlags c = FAST_ON ||| FAST_EMIT ||| RUN_SIMPLE_SYMBOL ∧ isSymbolByte c = true ∧
        isDigit c = false)) (by decide +kernel) c

open BSmtLib.Lexer (startOf Start) in
theorem startOf_comment {c : UInt8} (h : startOf c = .comment) : c = 59 :=
  byte_table (P := fun c => (startOf c == .comment) = true → c = 59) (by decide +kernel) c
    (by rw [h]; rfl)

open BSmtLib.Lexer (startOf Start) in
theorem startOf_hash {c : UInt8} (h : startOf c = .hash) : c = 35 :=
  byte_table (P := fun c => (startOf c == .hash) = true → c = 35) (by decide +kernel) c
    (by rw [h]; rfl)

open BSmtLib.Lexer (startOf Start) in
theorem startOf_quote {c : UInt8} (h : startOf c = .quote) : c = 34 :=
  byte_table (P := fun c => (startOf c == .quote) = true → c = 34) (by decide +kernel) c
    (by rw [h]; rfl)

open BSmtLib.Lexer (startOf Start) in
theorem startOf_colon {c : UInt8} (h : startOf c = .colon) : c = 58 :=
  byte_table (P := fun c => (startOf c == .colon) = true → c = 58) (by decide +kernel) c
    (by rw [h]; rfl)

open BSmtLib.Lexer (startOf Start) in
theorem startOf_digit {c : UInt8} (h : startOf c = .digit) : isDigit c = true :=
  byte_table (P := fun c => (startOf c == .digit) = true → isDigit c = true) (by decide +kernel) c
    (by rw [h]; rfl)

open BSmtLib.Lexer (fastFlags FAST_ON startOf Start) in
/-- A byte off the fast path, not a parenthesis, that the normal state does not start a token
with: the naive lexer has no token for it either. -/
theorem startOf_other (c : UInt8) :
    (!(startOf c == .other || startOf c == .whitespace || startOf c == .parenOpen ||
        startOf c == .parenClose || startOf c == .symbol || startOf c == .pipe) ||
      (fastFlags c &&& FAST_ON != 0) || c == 40 || c == 41 ||
      (!isWhitespace c && c != 59 && c != 35 && c != 34 && c != 58 && c != 124 && !isDigit c &&
        !isSymbolByte c)) = true :=
  byte_table (P := fun c => (!(startOf c == .other || startOf c == .whitespace ||
        startOf c == .parenOpen || startOf c == .parenClose || startOf c == .symbol ||
        startOf c == .pipe) ||
      (fastFlags c &&& FAST_ON != 0) || c == 40 || c == 41 ||
      (!isWhitespace c && c != 59 && c != 35 && c != 34 && c != 58 && c != 124 && !isDigit c &&
        !isSymbolByte c)) = true) (by decide +kernel) c

end BSmtLib.Proofs.Lexer.V1NaiveWRustPort
