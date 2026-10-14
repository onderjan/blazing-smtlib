module

public import BSmtLib.Facts.Proofs.Lexer.VNaiveWRustPort.Tables.Delimiters
public import BSmtLib.Facts.Proofs.Lexer.VNaiveWRustPort.Tables.FastRuns
public import BSmtLib.Facts.Proofs.Lexer.VNaiveWRustPort.Tables.NumeralRuns
public import BSmtLib.Facts.Proofs.Lexer.VNaiveWRustPort.Tables.TextRuns
public import BSmtLib.Facts.Proofs.Lexer.VNaiveWRustPort.Tables.Legacy
public import BSmtLib.Facts.Proofs.Lexer.VNaiveWRustPort.Tables.StartLiterals
public import BSmtLib.Facts.Proofs.Lexer.VNaiveWRustPort.Tables.Start

@[expose] public section

/-!
# The Rust port's byte tables against the naive lexer's byte classes

The Rust port classifies a byte by its tables (`RUN_FLAGS`, `FAST`, `START`); each class is one
of the naive lexer's byte classes, checked by the kernel for every byte.
-/
