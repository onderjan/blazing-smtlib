import BSmtLib.Facts.Proofs.Lexer.VNaiveWRustPort.Tables.Basic

/-!
# The delimiter table and the fast flags

The Rust port's delimiter table and its fast flags against the naive lexer's byte classes.
-/

namespace BSmtLib.Facts.Proofs.Lexer.VNaiveWRustPort.Tables.Delimiters

open BSmtLib.Lexer.Internal.VNaive
open BSmtLib.Lexer.CharClass (RUN_SIMPLE_SYMBOL RUN_NON_LF_WHITESPACE RUN_QUOTED_PLAIN)
open BSmtLib.Facts.Proofs.Lexer.VNaiveWRustPort.Bytes
open BSmtLib.Facts.Proofs.Lexer.VNaiveWRustPort.Tables.Basic

theorem isDelimiter_eq (c : UInt8) : Lexer.Helpers.isDelimiter c =
    Lexer.Internal.VNaive.isDelimiter c :=
  byte_table (P := fun c => Lexer.Helpers.isDelimiter c = Lexer.Internal.VNaive.isDelimiter c)
    (by decide +kernel) c

open BSmtLib.Lexer.Helpers (fastFlags FAST_ON FAST_DELIM FAST_EMIT FAST_PIPE) in
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

end BSmtLib.Facts.Proofs.Lexer.VNaiveWRustPort.Tables.Delimiters
