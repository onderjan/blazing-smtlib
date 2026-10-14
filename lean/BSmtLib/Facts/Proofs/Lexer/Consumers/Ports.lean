module

public import BSmtLib.Facts.Proofs.Lexer.VNaiveWRustPort
public import BSmtLib.Facts.Proofs.Lexer.Consumers.ChainZ
public import BSmtLib.Facts.Proofs.Lexer.Consumers.VNaive
public import BSmtLib.Facts.Proofs.Lexer.Consumers.VFlatten

@[expose] public section

/-!
# The ports with every consumer

The Rust port `WRustPort` (`VNaiveWRustPort.lexing_wRustPort_vNaive`), the lexer with the batch
in its state `X1BatchInCore` (`lexing_wRustPort_x1BatchInCore`) and the library's lexer
(`lexing_cut`, with `lexing_flatten` of the naive lexer, as the library's lexer cuts slices into
chunks) do with every consumer of the spec what the naive lexer does (`Adapters.lexing`), so each
is `BSmtLibSpec.Lexer.CorrectWithConsumers` as the naive lexer is (`correctWithConsumers_vNaive`).
-/

namespace BSmtLib.Facts.Proofs.Lexer.Consumers.Ports

open BSmtLib.Facts.Proofs.Lexer.Consumers.VFlatten (lexing_flatten)
open BSmtLib.Facts.Proofs.Lexer.Consumers.VNaive (correctWithConsumers_vNaive)
open BSmtLib.Facts.Lexer.Adapters

theorem lexing_wRustPort_vNaive : lexing WRustPort.lexOps = lexing VNaive.lexOps :=
  VNaiveWRustPort.Calls.lexing_wRustPort_vNaive

theorem lexing_x1BatchInCore_vNaive : lexing X1BatchInCore.lexOps = lexing VNaive.lexOps := by
  rw [← ChainX1.lexing_wRustPort_x1BatchInCore, lexing_wRustPort_vNaive]

theorem lexing_lexer_vNaive : lexing Lexer.lexOps = lexing VNaive.lexOps := by
  funext consumer version earlier slices ended
  rw [ChainZ.lexing_cut, lexing_x1BatchInCore_vNaive, lexing_flatten,
    lexing_flatten consumer version earlier slices ended, X1BatchInCoreLexer.Chunks.flatten_cutAll,
    List.map_map]
  congr 2
  funext input
  simp only [Function.comp, X1BatchInCoreLexer.Chunks.flatten_cutAll]

theorem correctWithConsumers_wRustPort :
    BSmtLibSpec.Lexer.CorrectWithConsumers (lexing WRustPort.lexOps) := by
  rw [lexing_wRustPort_vNaive]
  exact correctWithConsumers_vNaive

theorem correctWithConsumers_x1BatchInCore :
    BSmtLibSpec.Lexer.CorrectWithConsumers (lexing X1BatchInCore.lexOps) := by
  rw [lexing_x1BatchInCore_vNaive]
  exact correctWithConsumers_vNaive

theorem correctWithConsumers_lexer : BSmtLibSpec.Lexer.CorrectWithConsumers
    (lexing Lexer.lexOps) := by
  rw [lexing_lexer_vNaive]
  exact correctWithConsumers_vNaive

end BSmtLib.Facts.Proofs.Lexer.Consumers.Ports
