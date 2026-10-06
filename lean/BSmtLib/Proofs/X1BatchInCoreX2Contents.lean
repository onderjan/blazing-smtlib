import BSmtLib.Proofs.X1BatchInCoreX2Contents.Handed

/-!
# The lexer with the batch kept in the lexer's state and the lexer with the content buffer

`Lexer.X1BatchInCore.lexSlice_eq_lexSlice_x2Contents`: in every lawful monad, with or without
recovery, the lexer with the batch kept in the lexer's state `X1BatchInCore` lexes a slice as the
lexer with the content buffer `X2Contents` does, under the map of their states `coreMap`, for
every consumer that does not tell twin cursors apart (`ContentBlind`), from a lexer whose content
buffer fits its array (which every call keeps, `lexSlice_fits`, and the constructors give). So
do the ends of the input (`lexEof_eq_lexEof_x2Contents`,
`pendingLexEof_eq_pendingLexEof_x2Contents`) and the constructors (`new_eq_new_x2Contents`).

`Lexer.X1BatchInCore.handed_eq_handed_x2Contents`: run by the adapter, the two hand over the same
tokens, however the input is cut into slices.

The two lexers are the same code but for the content of the token in progress, which the lexer
with the content buffer keeps in a buffer whose storage is reused, and the content of a token
lexed from the slice, which it takes as positions in the slice's array. A token handed over alone
with its content in the buffer is handed over in a batch whose array of contents is the buffer's
whole array, which can hold bytes past the content, where the lexer with the batch kept in the
lexer's state hands over the bytes of the content alone. A consumer can tell the two batches apart,
through the array of contents of the batch or of the view of a token's content; the theorem holds
for the consumers that do not (`ContentBlind`), among them the adapter's consumer.

The proof, in parts:

- `X1BatchInCoreX2Contents.Content`: the content buffer against the byte array, and the views of
  the slice against positions in its array; the map of states;
- `X1BatchInCoreX2Contents.Cursor`: twin cursors, and the consumers that do not tell them apart;
- `X1BatchInCoreX2Contents.Collector`: the adapter's consumer is one;
- `X1BatchInCoreX2Contents.Framework`: simulation that keeps an invariant through interruptions;
- `X1BatchInCoreX2Contents.Core`, `.HandOver`, `.Finish`, `.Normal`: the helpers;
- `X1BatchInCoreX2Contents.Loop`, `.Steps`: the loop of the normal state and the steps;
- `X1BatchInCoreX2Contents.Slice`, `.Inner`, `.Run`: the loops over a slice, the calls on the
  lexers' states, and the lexers' calls;
- `X1BatchInCoreX2Contents.Handed`: the two lexers run by the adapter.
-/

namespace BSmtLib.Proofs.Lexer

open BSmtLib.Proofs.Adapter BSmtLib.Proofs.X1BatchInCoreX2Contents

section

variable {H : Type} {m : Type → Type} {R E : Type} [Monad m] [LawfulMonad m] [Consume H m R E]

/-- The lexer with the batch kept in the lexer's state lexes a slice as the lexer with the content
buffer does, for every consumer that does not tell twin cursors apart. -/
theorem X1BatchInCore.lexSlice_eq_lexSlice_x2Contents (hblind : ContentBlind H m R E)
    {recovery : Recovery} [LexRecovery recovery H m] (self : X2Contents.Lexer H recovery)
    (hself : LexerFits self) (slice : ByteSlice) :
    X1BatchInCore.Lexer.lexSlice (lexerMap self) slice =
      resultMap afterErrorMap <$> X2Contents.Lexer.lexSlice self slice := by
  obtain ⟨y, h1, h2⟩ := lexSlice_sim hblind self hself slice
  rw [h1, h2, Functor.map_map]

/-- The lexers that the lexer with the content buffer gives back after a slice have their
content buffers fit. -/
theorem X2Contents.lexSlice_fits (hblind : ContentBlind H m R E) {recovery : Recovery}
    [LexRecovery recovery H m] (self : X2Contents.Lexer H recovery) (hself : LexerFits self)
    (slice : ByteSlice) :
    ∃ y : m {r // ResultFits AfterErrorFits r},
      X2Contents.Lexer.lexSlice self slice = Subtype.val <$> y :=
  (lexSlice_sim hblind self hself slice).imp fun _ h => h.1

/-- The lexer with the batch kept in the lexer's state lexes the end of the input as the lexer
with the content buffer does, for every consumer that does not tell twin cursors apart. -/
theorem X1BatchInCore.lexEof_eq_lexEof_x2Contents (hblind : ContentBlind H m R E)
    {recovery : Recovery} [LexRecovery recovery H m] (self : X2Contents.Lexer H recovery)
    (hself : LexerFits self) :
    X1BatchInCore.Lexer.lexEof (lexerMap self) =
      resultMap afterEofErrorMap <$> X2Contents.Lexer.lexEof self := by
  obtain ⟨y, h1, h2⟩ := lexEof_sim hblind self hself
  rw [h1, h2, Functor.map_map]

/-- The lexers that the lexer with the content buffer gives back after the end of the input
have their content buffers fit. -/
theorem X2Contents.lexEof_fits (hblind : ContentBlind H m R E) {recovery : Recovery}
    [LexRecovery recovery H m] (self : X2Contents.Lexer H recovery) (hself : LexerFits self) :
    ∃ y : m {r // ResultFits AfterEofErrorFits r},
      X2Contents.Lexer.lexEof self = Subtype.val <$> y :=
  (lexEof_sim hblind self hself).imp fun _ h => h.1

/-- The lexer with the batch kept in the lexer's state lexes the end of the input again, after
it failed with recovery, as the lexer with the content buffer does. -/
theorem X1BatchInCore.pendingLexEof_eq_pendingLexEof_x2Contents (hblind : ContentBlind H m R E)
    [Recover H m] (self : X2Contents.Lexer H .recovering) (hself : LexerFits self) :
    X1BatchInCore.Lexer.PendingEof.lexEof ⟨lexerMap self⟩ =
      resultMap lexerMap <$> X2Contents.Lexer.PendingEof.lexEof ⟨self⟩ := by
  obtain ⟨y, h1, h2⟩ := pendingLexEof_sim hblind self hself
  rw [h1, h2, Functor.map_map]

end

/-- The two lexers are constructed alike, with a content buffer that fits. -/
theorem X1BatchInCore.new_eq_new_x2Contents {H : Type} (consumer : H) (version : Version) :
    X1BatchInCore.Lexer.new consumer version =
      lexerMap (X2Contents.Lexer.new consumer version) ∧
      LexerFits (X2Contents.Lexer.new consumer version) :=
  ⟨rfl, fits_new consumer version⟩

/-- The two recovering lexers are constructed alike, with a content buffer that fits. -/
theorem X1BatchInCore.newRecovering_eq_newRecovering_x2Contents {H : Type} {m : Type → Type}
    [Recover H m] (consumer : H) (version : Version) :
    X1BatchInCore.Lexer.newRecovering (m := m) consumer version =
      lexerMap (X2Contents.Lexer.newRecovering (m := m) consumer version) ∧
      LexerFits (X2Contents.Lexer.newRecovering (m := m) consumer version) :=
  ⟨rfl, fits_newRecovering consumer version⟩

/-- The lexer with the batch kept in the lexer's state and the lexer with the content buffer, run
by the adapter, hand over the same tokens. -/
theorem X1BatchInCore.handed_eq_handed_x2Contents :
    handed Adapter.X1BatchInCore.ops = handed Adapter.X2Contents.ops := by
  funext version slices
  exact feed_eq slices _ (fits_new _ _)

end BSmtLib.Proofs.Lexer
