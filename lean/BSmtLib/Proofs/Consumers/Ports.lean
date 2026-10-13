import BSmtLib.Proofs.VNaiveWRustPort
import BSmtLib.Proofs.Consumers.ChainX1
import BSmtLib.Proofs.Consumers.ChainZ
import BSmtLib.Proofs.Consumers.VNaive
import BSmtLib.Proofs.Consumers.VFlatten

/-!
# The ports with every consumer

The Rust port `WRustPort` (`VNaiveWRustPort.lexing_wRustPort_vNaive`), the lexer with the batch
in its state `X1BatchInCore` (`lexing_wRustPort_x1BatchInCore`) and the library's lexer
(`lexing_cut`, with `lexing_flatten` of the naive lexer, as the library's lexer cuts slices into
chunks) do with every consumer of the spec what the naive lexer does (`Adapter.lexing`), so each
is `BSmtLibSpec.Lexer.CorrectWithConsumers` as the naive lexer is (`correctWithConsumers_vNaive`).
-/

namespace BSmtLib.Proofs.Adapter

open Lexer.VNaive (lexing_flatten correctWithConsumers_vNaive)

theorem lexing_wRustPort_vNaive : lexing WRustPort.lexOps = lexing VNaive.lexOps :=
  Lexer.VNaiveWRustPort.lexing_wRustPort_vNaive

theorem lexing_x1BatchInCore_vNaive : lexing X1BatchInCore.lexOps = lexing VNaive.lexOps := by
  rw [← WRustPortX1BatchInCore.lexing_wRustPort_x1BatchInCore, lexing_wRustPort_vNaive]

theorem lexing_lexer_vNaive : lexing Lexer.lexOps = lexing VNaive.lexOps := by
  funext consumer version earlier slices ended
  rw [X1BatchInCoreLexer.lexing_cut, lexing_x1BatchInCore_vNaive, lexing_flatten,
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

theorem correctWithConsumers_lexer : BSmtLibSpec.Lexer.CorrectWithConsumers (lexing Lexer.lexOps) := by
  rw [lexing_lexer_vNaive]
  exact correctWithConsumers_vNaive

end BSmtLib.Proofs.Adapter
