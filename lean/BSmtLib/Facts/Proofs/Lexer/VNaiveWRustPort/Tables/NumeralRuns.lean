module

public import BSmtLib.Facts.Proofs.Lexer.VNaiveWRustPort.Tables.Basic
import all BSmtLib.Lexer.Internal.VNaive
import all Init.Data.Array.Basic

@[expose] public section

/-!
# The run tables of numerals

The Rust port's runs of decimal, hexadecimal and binary digits against the naive lexer's byte
classes.
-/

namespace BSmtLib.Facts.Proofs.Lexer.VNaiveWRustPort.Tables.NumeralRuns

open BSmtLib.Lexer.Internal.VNaive
open BSmtLib.Lexer.Internal.CharClass (endsRun RUN_DIGIT RUN_HEX_DIGIT RUN_BINARY_DIGIT)
open BSmtLib.Facts.Proofs.Lexer.VNaiveWRustPort.Tables.Basic

theorem endsRun_digit (c : UInt8) : endsRun c RUN_DIGIT = !isDigit c :=
  byte_table (P := fun c => endsRun c RUN_DIGIT = !isDigit c) (by decide +kernel) c

theorem endsRun_hex (c : UInt8) : endsRun c RUN_HEX_DIGIT = !Radix.hexadecimal.allows c :=
  byte_table (P := fun c => endsRun c RUN_HEX_DIGIT = !Radix.hexadecimal.allows c)
    (by decide +kernel) c

theorem endsRun_binary (c : UInt8) : endsRun c RUN_BINARY_DIGIT = !Radix.binary.allows c :=
  byte_table (P := fun c => endsRun c RUN_BINARY_DIGIT = !Radix.binary.allows c)
    (by decide +kernel) c

end BSmtLib.Facts.Proofs.Lexer.VNaiveWRustPort.Tables.NumeralRuns
