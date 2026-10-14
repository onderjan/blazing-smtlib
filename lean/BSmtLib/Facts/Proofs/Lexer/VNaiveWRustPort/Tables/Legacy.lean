module

public import BSmtLib.Facts.Proofs.Lexer.VNaiveWRustPort.Tables.Basic
import all BSmtLib.Lexer.Internal.VNaive
import all Init.Data.Array.Basic

@[expose] public section

/-!
# The run table of strings under version 2.0

The Rust port's run of a string under version 2.0 against the naive lexer's byte classes.
-/

namespace BSmtLib.Facts.Proofs.Lexer.VNaiveWRustPort.Tables.Legacy

open BSmtLib.Lexer.CharClass (RUN_STRING_PLAIN RUN_QUOTED_PLAIN)
open BSmtLib.Facts.Proofs.Lexer.VNaiveWRustPort.Bytes
open BSmtLib.Facts.Proofs.Lexer.VNaiveWRustPort.Tables.Basic

/-- Whether the byte is a part of a string under version 2.0 that the Rust port's run takes:
any byte of its content but the quote, the backslash, the line feed and the pipe. -/
def isLegacyRun (c : UInt8) : Bool :=
  isLegacyStringRun c && c != byte! '|'

theorem endsRunAll_legacy (c : UInt8) :
    (Lexer.CharClass.runFlagsOf c &&& (RUN_STRING_PLAIN ||| RUN_QUOTED_PLAIN) !=
      (RUN_STRING_PLAIN ||| RUN_QUOTED_PLAIN)) = !isLegacyRun c :=
  byte_table (P := fun c =>
      (Lexer.CharClass.runFlagsOf c &&& (RUN_STRING_PLAIN ||| RUN_QUOTED_PLAIN) !=
        (RUN_STRING_PLAIN ||| RUN_QUOTED_PLAIN)) = !isLegacyRun c) (by decide +kernel) c

end BSmtLib.Facts.Proofs.Lexer.VNaiveWRustPort.Tables.Legacy
