import BSmtLib.Proofs.X1BatchInCoreX2Contents.Collector
import BSmtLib.Proofs.X1BatchInCoreX2Contents.Run

/-!
# The two lexers run by the adapter

The adapter feeds a lexer the slices and then the end of the input, with its consumer, which does
not tell twin cursors apart (`collector_contentBlind`). Each call of the lexer with the batch kept
in the lexer's state on the mapped lexer gives the mapped result of the call of the lexer with the
content buffer, and the lexers given back have their content buffers fit, so the two record the
same tokens (`feed_eq`).
-/

namespace BSmtLib.Proofs.X1BatchInCoreX2Contents

open BSmtLib.Proofs.Adapter

theorem feed_eq :
    ∀ (slices : List Spec.Lexicon.Chars) (self : Lexer.X2Contents.Lexer Collector),
      LexerFits self →
      feed Adapter.X1BatchInCore.ops (lexerMap self) slices =
        feed Adapter.X2Contents.ops self slices
  | [], self, hself => by
    obtain ⟨⟨r, hr⟩, h1, h2⟩ := lexEof_sim collector_contentBlind self hself
    have e1 : Adapter.X1BatchInCore.ops.lexEof (lexerMap self) = resultMap afterEofErrorMap r :=
      h2
    have e2 : Adapter.X2Contents.ops.lexEof self = r := h1
    simp only [feed, e1, e2]
    rcases r with ⟨err, a⟩ | ⟨flow, lexer⟩
    · rfl
    · cases flow <;> rfl
  | slice :: slices, self, hself => by
    obtain ⟨⟨r, hr⟩, h1, h2⟩ := lexSlice_sim collector_contentBlind self hself
      slice.toByteArray.toByteSlice
    have e1 : Adapter.X1BatchInCore.ops.lexSlice (lexerMap self) slice.toByteArray.toByteSlice =
        resultMap afterErrorMap r := h2
    have e2 : Adapter.X2Contents.ops.lexSlice self slice.toByteArray.toByteSlice = r := h1
    simp only [feed, e1, e2]
    rcases r with ⟨err, a⟩ | ⟨flow, lexer⟩
    · rfl
    · cases flow with
      | «continue» => exact feed_eq slices lexer hr
      | «break» f => rfl

end BSmtLib.Proofs.X1BatchInCoreX2Contents
