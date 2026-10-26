module

public import BSmtLib.Facts.PublicApi.Adapters
public import BSmtLib.Lexer.Internal.VNaive
public import BSmtLib.Lexer.Internal.WRustPort
public import BSmtLib.Lexer.Internal.X1BatchInCore

@[expose] public section

/-!
# The lexers of the chain with the collector

The lexers of the chain that leads from the specification formalism (`BSmtLibSpec`) to the library's
lexer, run as the library's lexer is run in `collect`: with the collector, fed the slices and then
the end of the input. The lexers are what the agreement theorem is about; the definitions here only
run them.
-/

namespace BSmtLib.Facts.PublicApi.Adapters.Chain

open BSmtLib.Lexer.Error

/-- Feeds a lexer with the collector, given by its calls, the slices by its call for a slice and
then the end of the input by its call for the end. Gives the result or the first error. -/
def collectBy {L A B : Type}
    (lexSlice : L → ByteSlice → CollectM (Except (LexerError Empty × A) L))
    (lexEof : L → CollectM (Except (LexerError Empty × B) (Option (Span.Located Unit) × L)))
    (lexer : L) : List ByteList → CollectM (Except (LexerError Empty) (Option (Span.Located Unit)))
  | [] => do
    match ← lexEof lexer with
    | .ok (result, _) => return .ok result
    | .error (error, _) => return .error error
  | slice :: slices => do
    match ← lexSlice lexer slice.toByteArray.toByteSlice with
    | .ok lexer => collectBy lexSlice lexEof lexer slices
    | .error (error, _) => return .error error

/-- The naive lexer with the collector, as `collect` runs the library's lexer. -/
def collectV (version : Version) (slices : List ByteList) :
    Except (LexerError Empty) (Option (Span.Located Unit)) × List Entry :=
  (collectBy (fun lexer slice => Lexer.Internal.VNaive.Lexer.lexSlice lexer slice)
    (fun lexer => Lexer.Internal.VNaive.Lexer.lexEof lexer)
    (Lexer.Internal.VNaive.Lexer.new Collector.mk version) slices).run []

/-- The Rust port with the collector, as `collect` runs the library's lexer. -/
def collectW (version : Version) (slices : List ByteList) :
    Except (LexerError Empty) (Option (Span.Located Unit)) × List Entry :=
  (collectBy (fun lexer slice => Lexer.Internal.WRustPort.Lexer.lexSlice lexer slice)
    (fun lexer => Lexer.Internal.WRustPort.Lexer.lexEof lexer)
    (Lexer.Internal.WRustPort.Lexer.new Collector.mk version)
    slices).run []

/-- The lexer with the batch kept in its state with the collector, as `collect` runs the
library's lexer. -/
def collectX1 (version : Version) (slices : List ByteList) :
    Except (LexerError Empty) (Option (Span.Located Unit)) × List Entry :=
  (collectBy (fun lexer slice => Lexer.Internal.X1BatchInCore.Lexer.lexSlice lexer slice)
    (fun lexer => Lexer.Internal.X1BatchInCore.Lexer.lexEof lexer)
    (Lexer.Internal.WRustPort.Lexer.new Collector.mk version)
    slices).run []

/-- A run's result with an error's cause only, and its entries. -/
def causeOnly {α : Type} (run : Except (LexerError Empty) α × List Entry) :
    Except (LexerErrorCause Empty) α × List Entry :=
  match run with
  | (.ok result, entries) => (.ok result, entries)
  | (.error error, entries) => (.error error.cause, entries)

end BSmtLib.Facts.PublicApi.Adapters.Chain
