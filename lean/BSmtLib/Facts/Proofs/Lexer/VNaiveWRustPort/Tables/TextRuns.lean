module

public import BSmtLib.Facts.Proofs.Lexer.VNaiveWRustPort.Tables.Basic
import all BSmtLib.Lexer.Internal.VNaive
import all Init.Data.Array.Basic

@[expose] public section

/-!
# The run tables of strings and comments

The Rust port's runs of a string literal and of a comment against the naive lexer's byte
classes.
-/

namespace BSmtLib.Facts.Proofs.Lexer.VNaiveWRustPort.Tables.TextRuns

open BSmtLib.Lexer.Internal.CharClass (endsRun RUN_STRING_PLAIN RUN_COMMENT_PLAIN)
open BSmtLib.Facts.Proofs.Lexer.VNaiveWRustPort.Bytes
open BSmtLib.Facts.Proofs.Lexer.VNaiveWRustPort.Tables.Basic

theorem endsRun_string (c : UInt8) : endsRun c RUN_STRING_PLAIN = !isStringRun c :=
  byte_table (P := fun c => endsRun c RUN_STRING_PLAIN = !isStringRun c) (by decide +kernel) c

theorem endsRun_comment (c : UInt8) : endsRun c RUN_COMMENT_PLAIN = !isCommentRun c :=
  byte_table (P := fun c => endsRun c RUN_COMMENT_PLAIN = !isCommentRun c) (by decide +kernel) c

end BSmtLib.Facts.Proofs.Lexer.VNaiveWRustPort.Tables.TextRuns
