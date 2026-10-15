module

public import BSmtLib.Facts.Proofs.Lexer.VNaiveWRustPort.Tables.Basic
import all BSmtLib.Lexer.Internal.Helpers
import all BSmtLib.Lexer.Internal.VNaive

@[expose] public section

/-!
# The start table for comments, keywords and bytes without a token

The bytes that the Rust port's start table lets start a comment or a keyword, and those that
start no token.
-/

namespace BSmtLib.Facts.Proofs.Lexer.VNaiveWRustPort.Tables.Start

open BSmtLib.Lexer.Internal.VNaive
open BSmtLib.Facts.Proofs.Lexer.VNaiveWRustPort.Tables.Basic

open BSmtLib.Lexer.Internal.Helpers (startOf Start) in
theorem startOf_comment {c : UInt8} (h : startOf c = .comment) : c = 59 :=
  byte_table (P := fun c => (startOf c == .comment) = true → c = 59) (by decide +kernel) c
    (by rw [h]; rfl)

open BSmtLib.Lexer.Internal.Helpers (startOf Start) in
theorem startOf_colon {c : UInt8} (h : startOf c = .colon) : c = 58 :=
  byte_table (P := fun c => (startOf c == .colon) = true → c = 58) (by decide +kernel) c
    (by rw [h]; rfl)

open BSmtLib.Lexer.Internal.Helpers (fastFlags FAST_ON startOf Start) in
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

end BSmtLib.Facts.Proofs.Lexer.VNaiveWRustPort.Tables.Start
