module

public import BSmtLib.Facts.Proofs.Lexer.VNaiveWRustPort.Tables.Basic
import all BSmtLib.Lexer.Helpers
import all BSmtLib.Lexer.Internal.VNaive

@[expose] public section

/-!
# The start table for literals

The bytes that the Rust port's start table lets start a numeral, a hexadecimal or binary literal,
or a string literal.
-/

namespace BSmtLib.Facts.Proofs.Lexer.VNaiveWRustPort.Tables.StartLiterals

open BSmtLib.Lexer.Internal.VNaive
open BSmtLib.Facts.Proofs.Lexer.VNaiveWRustPort.Tables.Basic

open BSmtLib.Lexer.Helpers (startOf Start) in
theorem startOf_hash {c : UInt8} (h : startOf c = .hash) : c = 35 :=
  byte_table (P := fun c => (startOf c == .hash) = true → c = 35) (by decide +kernel) c
    (by rw [h]; rfl)

open BSmtLib.Lexer.Helpers (startOf Start) in
theorem startOf_quote {c : UInt8} (h : startOf c = .quote) : c = 34 :=
  byte_table (P := fun c => (startOf c == .quote) = true → c = 34) (by decide +kernel) c
    (by rw [h]; rfl)

open BSmtLib.Lexer.Helpers (startOf Start) in
theorem startOf_digit {c : UInt8} (h : startOf c = .digit) : isDigit c = true :=
  byte_table (P := fun c => (startOf c == .digit) = true → isDigit c = true) (by decide +kernel) c
    (by rw [h]; rfl)

end BSmtLib.Facts.Proofs.Lexer.VNaiveWRustPort.Tables.StartLiterals
