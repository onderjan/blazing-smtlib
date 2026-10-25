module

public import BSmtLib.Facts.Proofs.Reader.Handler.Final
public import BSmtLib.Facts.PublicApi.Adapters
import all BSmtLib.Lexer
import all BSmtLib.Reader
import all BSmtLib.Facts.PublicApi.Adapters

@[expose] public section

/-!
# The script reader with any handler that never fails, on a file

The reader's calls are its lexer's public calls with the parse adapter (`readSlice_ofLexer`,
`readEof_ofLexer`), so where those do not fail the reader reads through as they do, and ends with
the lexer they leave (`readThrough_of_hFeed`). On a file, the script reader with a handler whose
calls never fail therefore reads to the end with a result, and its handler holds what the script
parser's driver over items standing for what a parser receives for the script leaves it with
(`reader_reads_file`).
-/

namespace BSmtLib.Facts.Proofs.Reader.Handler.Reader

open BSmtLibSpec BSmtLibSpec.Grammar
open BSmtLibSpec.Parser.Properties
open BSmtLib.Handler
open BSmtLib.Parser.Script (ScriptParser)
open BSmtLib.Parser.Adapter (ParseAdapter)
open BSmtLib.Facts.Lexer.Adapters (toVersion)
open BSmtLib.Facts.Parser.Adapters.Bridge BSmtLib.Facts.Parser.Adapters.Bridge.Rejection
open BSmtLib.Facts.Parser.Adapters.Run BSmtLib.Facts.Parser.Adapters.Run.Rejection
open BSmtLib.Facts.Proofs.Reader.Handler.Loop BSmtLib.Facts.Proofs.Reader.Handler.Run
open BSmtLib.Facts.Proofs.Parser.Blank.Basic
open BSmtLib.Facts.PublicApi.Adapters (feed readThrough allVersions)

variable {H : Type} [CommandHandler H Id]

theorem readSlice_ofLexer (lexer : HLexer H) (slice : ByteSlice) {lexer' : HLexer H}
    (h : (Lexer.lexSlice lexer slice : Id _) = .ok lexer') :
    ((BSmtLib.Reader.Internal.ofLexer lexer : BSmtLib.Reader H (ScriptParser H)).readSlice slice :
        Id _) = .ok (BSmtLib.Reader.Internal.ofLexer lexer') := by
  revert h
  simp only [BSmtLib.Reader.readSlice, BSmtLib.Reader.Internal.ofLexer, Lexer.lexSlice]
  generalize (Lexer.Internal.run lexer (Lexer.Internal.lexSliceStep
    (H := ParseAdapter H (ScriptParser H)) (m := Id)
    (Lexer.Recovery.LexerRecovery.abandon Lexer.Recovery.FailFast)
    (Lexer.Recovery.LexerRecovery.recover Lexer.Recovery.FailFast) slice) : Id _) = r
  rcases r with ⟨e | held, l⟩
  · intro h; cases h
  · intro h; cases h; rfl

theorem readEof_ofLexer (lexer : HLexer H) {result : Option (Span.Located Unit)}
    {lexer' : HLexer H} (h : (Lexer.lexEof lexer : Id _) = .ok (result, lexer')) :
    ((BSmtLib.Reader.Internal.ofLexer lexer : BSmtLib.Reader H (ScriptParser H)).readEof :
        Id _) = .ok (result, BSmtLib.Reader.Internal.ofLexer lexer') := by
  revert h
  simp only [BSmtLib.Reader.readEof, BSmtLib.Reader.Internal.ofLexer, Lexer.lexEof]
  generalize (Lexer.Internal.run lexer (Lexer.Internal.lexEofStep
    (H := ParseAdapter H (ScriptParser H)) (m := Id) (R := Unit)
    (E := BSmtLib.Parser.ParseError (Handler.Error H))
    (Lexer.Recovery.LexerRecovery.abandon Lexer.Recovery.FailFast)
    (Lexer.Recovery.LexerRecovery.recover Lexer.Recovery.FailFast)) : Id _) = r
  rcases r with ⟨e | flow, l⟩
  · intro h; cases h
  · intro h; cases h; rfl

/-- Where the lexer's public calls with the parse adapter do not fail, the reader reads through
as they do, and ends with the lexer they leave. -/
theorem readThrough_of_hFeed : ∀ (slices : List Regex.Chars) (lexer : HLexer H)
    {result : Option (Span.Located Unit)} {lexer' : HLexer H},
    hFeed lexer slices = .ok (result, lexer') →
    ∃ before, readThrough (BSmtLib.Reader.Internal.ofLexer lexer) slices =
      .ok (result, before, BSmtLib.Reader.Internal.ofLexer lexer')
  | [], lexer, result, lexer', h => by
    simp only [hFeed] at h
    revert h
    cases he : (Lexer.lexEof lexer : Id _) with
    | error e => intro h; cases h
    | ok r =>
      intro h
      cases h
      refine ⟨BSmtLib.Reader.Internal.ofLexer lexer, ?_⟩
      simp only [readThrough, feed]
      rw [readEof_ofLexer lexer he]
  | slice :: slices, lexer, result, lexer', h => by
    simp only [hFeed] at h
    revert h
    cases he : (Lexer.lexSlice lexer slice.toByteArray.toByteSlice : Id _) with
    | error e => intro h; cases h
    | ok l =>
      intro h
      obtain ⟨before, hb⟩ := readThrough_of_hFeed slices l h
      refine ⟨before, ?_⟩
      have hs := readSlice_ofLexer lexer slice.toByteArray.toByteSlice he
      unfold readThrough at hb ⊢
      simp only [feed, hs]
      exact hb

/-- The posture that allows every version, by its two names. -/
theorem allVersions_eq : allVersions = unrestrictedPosture := rfl

/-- The script reader with a handler whose calls never fail, from the handler, allowing every
version, fed a file of commands read from the version in any slices and then the end of the
input: it reads to the end with a result, and its handler holds what the script parser's driver
over items standing for what a parser receives for the script leaves it with, the driver having
finished the script. -/
theorem reader_reads_file [NoFails H] (version : Lexicon.Version) (slices : List Regex.Chars)
    (init : H) {commands : List Tree.Command} (hfile : File version slices.flatten commands) :
    ∃ result before after,
      readThrough (BSmtLib.Reader.script init allVersions (toVersion version)) slices =
        .ok (some result, before, after) ∧
      ∃ items : List LibItem, items.map (rcv ∘ Subtype.val) = received commands ∧
        ∃ r, hRun version init items = (.ok (.inr r), after.handler) := by
  obtain ⟨result, lexer, hfeed, items, hst, r, hr⟩ :=
    Final.adapter_feed_file version slices init hfile
  obtain ⟨before, hb⟩ := readThrough_of_hFeed slices _ hfeed
  exact ⟨result, before, _, hb, items, hst, r, hr⟩

end BSmtLib.Facts.Proofs.Reader.Handler.Reader
