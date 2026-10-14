import BSmtLib.Facts.Proofs.Lexer.VNaiveWRustPort.Tables.Delimiters
import BSmtLib.Facts.Proofs.Lexer.VNaiveWRustPort.Tables.FastRuns
import BSmtLib.Facts.Proofs.Lexer.VNaiveWRustPort.Tables.NumeralRuns
import BSmtLib.Facts.Proofs.Lexer.VNaiveWRustPort.Tables.TextRuns
import BSmtLib.Facts.Proofs.Lexer.VNaiveWRustPort.Tables.Legacy
import BSmtLib.Facts.Proofs.Lexer.VNaiveWRustPort.Tables.StartLiterals
import BSmtLib.Facts.Proofs.Lexer.VNaiveWRustPort.Tables.Start

/-!
# The Rust port's byte tables against the naive lexer's byte classes

The Rust port classifies a byte by its tables (`RUN_FLAGS`, `FAST`, `START`); each class is one
of the naive lexer's byte classes, checked by the kernel for every byte.
-/
