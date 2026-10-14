module

public import BSmtLib.Facts.Proofs.Lexer.VNaiveWRustPort.Tables.Basic
import all BSmtLib.Lexer.Internal.VNaive
import all Init.Data.Array.Basic

@[expose] public section

/-!
# The run tables of the fast path

The Rust port's runs of whitespace, of a simple symbol and of a quoted symbol against the naive
lexer's byte classes.
-/

namespace BSmtLib.Facts.Proofs.Lexer.VNaiveWRustPort.Tables.FastRuns

open BSmtLib.Lexer.Internal.VNaive
open BSmtLib.Lexer.CharClass (endsRun RUN_SIMPLE_SYMBOL RUN_NON_LF_WHITESPACE RUN_QUOTED_PLAIN)
open BSmtLib.Facts.Proofs.Lexer.VNaiveWRustPort.Bytes
open BSmtLib.Facts.Proofs.Lexer.VNaiveWRustPort.Tables.Basic

theorem endsRun_symbol (c : UInt8) : endsRun c RUN_SIMPLE_SYMBOL = !isSymbolByte c :=
  byte_table (P := fun c => endsRun c RUN_SIMPLE_SYMBOL = !isSymbolByte c) (by decide +kernel) c

theorem endsRun_whitespace (c : UInt8) : endsRun c RUN_NON_LF_WHITESPACE = !isWhitespaceRun c :=
  byte_table (P := fun c => endsRun c RUN_NON_LF_WHITESPACE = !isWhitespaceRun c)
    (by decide +kernel) c

theorem endsRun_quoted (c : UInt8) : endsRun c RUN_QUOTED_PLAIN = !isQuotedRun c :=
  byte_table (P := fun c => endsRun c RUN_QUOTED_PLAIN = !isQuotedRun c) (by decide +kernel) c

end BSmtLib.Facts.Proofs.Lexer.VNaiveWRustPort.Tables.FastRuns
