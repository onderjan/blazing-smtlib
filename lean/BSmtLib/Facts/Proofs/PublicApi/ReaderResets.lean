module

public import BSmtLib.Facts.Proofs.PublicApi.ReaderAfter
public import BSmtLib.Facts.Proofs.PublicApi.Reprinting
public import BSmtLib.Facts.Proofs.Parser.Canon.Through
import all BSmtLib.Lexer
import all BSmtLib.Lexer.Internal.WRustPort
import all BSmtLib.Reader
import all BSmtLib.Parser.Adapter
import all BSmtLib.Parser

@[expose] public section

/-!
# The script reader after an input it read to the end, and a new one

The script reader over the recording handler, allowing every version, after an input it read to
the end, and a new script reader over its handler, read the next input alike: the same error, or
the same result, handler and discarding (`resets_recording`). Their lexers are related, through
the lexers with the canonical adapter (`Parser.Canon.Through.lexThrough_link`), by one Rust port's
lexer (`Parser.Canon.Through.lexThrough_zRel`): the reader after the input has the fields of a
new one but for its storage, a reset parser and a handler not told the version
(`ReaderAfter.after_state`).
-/

namespace BSmtLib.Facts.Proofs.PublicApi.ReaderResets

open BSmtLib.Lexer BSmtLib.Lexer.Error
open BSmtLib.Parser BSmtLib.Parser.Adapter BSmtLib.Parser.Script
open BSmtLib.Facts.PublicApi.Adapters
open BSmtLib.Facts.Reader.Adapters (RecReader RecAdapter PLexer)
open BSmtLib.Facts.Proofs.Parser.Canon
open BSmtLib.Facts.Proofs.Lexer
open BSmtLib.Facts.Proofs.Parser.Canon.Through (lexFeed lexThrough eofResultT LinkRel ThroughLink
  ThroughRel lexThrough_link lexThrough_zRel)

/-- A read of the reader over a lexer, and the lexer fed alike: the same error, or the same
result with the reader's lexers before and after the end of the input. -/
def ReadLex :
    Except (Reader.ReadFailure (List BSmtLibSpec.Parser.Properties.Event)
        (ScriptParser (List BSmtLibSpec.Parser.Properties.Event)))
      (Option (Span.Located Unit) × RecReader × RecReader) →
    Except (LexError (ParseError Unit)) (Option (Span.Located Unit) × PLexer × PLexer) →
      Prop
  | .error f, .error e => f.error = Reader.ReadError.ofLex e
  | .ok (r, b, a), .ok (r', b', a') =>
    r = r' ∧ b = Reader.Internal.ofLexer b' ∧ a = Reader.Internal.ofLexer a'
  | _, _ => False

theorem readThrough_lex : ∀ (slices : List ByteList) (l : PLexer),
    ReadLex (readThrough (Reader.Internal.ofLexer l : RecReader) slices)
      (lexThrough (R := Unit) (E := ParseError Unit) l slices)
  | [], l => by
    unfold readThrough lexThrough
    rw [feed]
    simp only [lexFeed, Reader.readEof, BSmtLib.Lexer.lexEof]
    rw [show (Reader.Internal.ofLexer l : RecReader).lexer = l from rfl]
    generalize Internal.run l (Internal.lexEofStep (R := Unit) (E := ParseError Unit)
      (Recovery.LexRecovery.abandon Recovery.FailFast)
      (Recovery.LexRecovery.recover Recovery.FailFast)) = Q
    obtain ⟨r, l'⟩ := Q
    cases r with
    | ok flow =>
      rw [BSmtLib.Facts.Proofs.Reader.Param.Adapter.id_bind_eq]
      dsimp only
      cases flow <;> refine ⟨?_, rfl, rfl⟩ <;> cases hh : Internal.held l' <;>
        (simp only [Internal.held] at hh; simp only [hh]; rfl)
    | error e => exact (rfl : Reader.ReadError.ofLex e = _)
  | slice :: slices, l => by
    rw [Reader.Lexes.Through.readThrough_cons]
    unfold lexThrough
    simp only [lexFeed, Reader.readSlice, BSmtLib.Lexer.lexSlice]
    rw [show (Reader.Internal.ofLexer l : RecReader).lexer = l from rfl]
    generalize Internal.run l (Internal.lexSliceStep (R := Unit) (E := ParseError Unit)
      (Recovery.LexRecovery.abandon Recovery.FailFast)
      (Recovery.LexRecovery.recover Recovery.FailFast) slice.toByteArray.toByteSlice) = Q
    obtain ⟨r, l'⟩ := Q
    cases r with
    | ok held =>
      have := readThrough_lex slices (Internal.withHeld l' (held.or (Internal.held l')))
      unfold lexThrough at this
      exact this
    | error e => exact (rfl : Reader.ReadError.ofLex e = _)

/-- Two reads that show the same outside the handler's state: the same error, or the same result,
handler and discarding. -/
def SameRead {H P E R : Type} [Parse P H Id E R] [Traits.Handler H Id] :
    Except (Reader.ReadFailure H P) (Option (Span.Located R) × Reader H P × Reader H P) →
    Except (Reader.ReadFailure H P) (Option (Span.Located R) × Reader H P × Reader H P) → Prop
  | .error f, .error g => f.error = g.error
  | .ok (r, b, a), .ok (r', b', a') =>
    r = r' ∧ a.handler = a'.handler ∧ b.discardedFrom = b'.discardedFrom
  | _, _ => False

open Canonical Link Chain Adapter in
/-- The lexer with the canonical adapter whose state is the parse adapter's, canonicalised. -/
def canonLexer (l : PLexer) : BSmtLib.Lexer CanonAdapter :=
  Internal.ofParts ⟨canonA (Internal.handler l)⟩ (Internal.core l) (Internal.held l)

open Canonical Adapter in
theorem linkRel_canonLexer (l : PLexer) : LinkRel l (canonLexer l) :=
  ⟨rfl, rfl, rfl⟩

theorem toVersion_fromVersion (version : Token.Version) :
    BSmtLib.Facts.Lexer.Adapters.toVersion (BSmtLib.Facts.Lexer.Adapters.fromVersion version) =
      version := by
  cases version <;> rfl

theorem parseState_eq (s t : ParseState (List BSmtLibSpec.Parser.Properties.Event)) : s = t := by
  cases s; cases t; rfl

open Canonical Adapter Chain in
/-- The script reader over the recording handler, allowing every version, after an input it read
to the end, and a new script reader over its handler, read the next input alike. -/
theorem resets_recording (version : Token.Version) (first next : List ByteList)
    {result : Option (Span.Located Unit)} {before after : RecReader}
    (h : readThrough (Reader.script ([] : List BSmtLibSpec.Parser.Properties.Event) allVersions
      version) first = .ok (result, before, after)) :
    SameRead (readThrough after next)
      (readThrough (Reader.script after.handler allVersions version) next) := by
  rw [Reprinting.reader_eq] at h
  obtain ⟨hpar, hset, ⟨c₀, hc₀, hiv, hrec⟩, hheld⟩ :=
    ReaderAfter.after_state (BSmtLib.Facts.Lexer.Adapters.fromVersion version) first h
  rw [toVersion_fromVersion] at hiv
  obtain ⟨La⟩ := after
  generalize hA : (ParseAdapter.new (Internal.handler La).handler
    (ScriptParser.new (H := List BSmtLibSpec.Parser.Properties.Event) allVersions) :
      RecAdapter) = A
  have hLf : (Reader.script (Internal.handler La).handler allVersions version : RecReader) =
      Reader.Internal.ofLexer (BSmtLib.Lexer.new A version) := by rw [← hA]; rfl
  -- the adapter after the input, canonicalised, is a new one's
  have hcanon : canonA (Internal.handler La) = canonA A := by
    rw [← hA]
    change (Internal.handler La).parser = _ at hpar
    change (Internal.handler La).versionSet = false at hset
    generalize Internal.handler La = H0 at hpar hset ⊢
    obtain ⟨h0, p0, v0, s0⟩ := H0
    dsimp only at hpar hset
    subst hpar hset
    rw [parseState_eq s0 .new]
    rfl
  have hZ : ZRelG (canonLexer La) (BSmtLib.Lexer.new (⟨canonA A⟩ : CanonAdapter) version) := by
    refine ⟨⟨⟨canonA A⟩, X1BatchInCoreLexer.Core.coreMap 0 (Internal.core La), Internal.held La⟩,
      Lexer.Internal.WRustPort.Lexer.new ⟨canonA A⟩ version,
      Lexer.Internal.WRustPort.Lexer.new ⟨canonA A⟩ version,
      ⟨?_, X1BatchInCoreLexer.Outer.rel_coreMap 0 _, rfl⟩, ⟨rfl, ⟨?_, rfl⟩, ?_⟩,
      WRustPortX1BatchInCore.Handed.new_rel _ _, X1BatchInCoreLexer.Handed.lexerRel_new _ _⟩
    · show (⟨canonA A⟩ : CanonAdapter) = ⟨canonA (Internal.handler La)⟩
      rw [hcanon]
    · change Internal.core (Reader.Internal.lexer ⟨La⟩) = _ at hc₀
      show WRustPortX1BatchInCore.Core.CoreRel _
        (X1BatchInCoreLexer.Core.coreMap 0 (Internal.core La))
      rw [show Internal.core La = Resets.resetOf c₀ from hc₀]
      exact Resets.coreRel_reset version c₀ hiv hrec
    · exact hheld.symm
  have hLf' : LinkRel (BSmtLib.Lexer.new A version)
      (BSmtLib.Lexer.new (⟨canonA A⟩ : CanonAdapter) version) := ⟨rfl, rfl, rfl⟩
  show SameRead (readThrough (Reader.Internal.ofLexer La : RecReader) next)
    (readThrough (Reader.script (Internal.handler La).handler allVersions version) next)
  rw [hLf]
  have R1 := readThrough_lex next La
  have R2 := readThrough_lex next (BSmtLib.Lexer.new A version)
  have T1 := lexThrough_link next (linkRel_canonLexer La)
  have T2 := lexThrough_zRel canonAdapter_consumesAlike next hZ
  have T3 := lexThrough_link next hLf'
  generalize readThrough (Reader.Internal.ofLexer La : RecReader) next = X1 at R1 ⊢
  generalize readThrough (Reader.Internal.ofLexer (BSmtLib.Lexer.new A version) : RecReader)
    next = X2 at R2 ⊢
  generalize lexThrough (R := Unit) (E := ParseError Unit) La next = Y1 at R1 T1
  generalize lexThrough (R := Unit) (E := ParseError Unit) (BSmtLib.Lexer.new A version)
    next = Y2 at R2 T3
  generalize lexThrough (R := Unit) (E := ParseError Unit) (canonLexer La) next = Z1
    at T1 T2
  generalize lexThrough (R := Unit) (E := ParseError Unit)
    (BSmtLib.Lexer.new (⟨canonA A⟩ : CanonAdapter) version) next = Z2 at T2 T3
  rcases X1 with f1 | ⟨r1, b1, a1⟩ <;> rcases Y1 with e1 | ⟨s1, c1, d1⟩ <;>
    simp only [ReadLex] at R1 <;>
    rcases Z1 with z1 | ⟨t1, u1, v1⟩ <;> simp only [ThroughLink] at T1 <;>
    rcases Z2 with z2 | ⟨t2, u2, v2⟩ <;> simp only [ThroughRel] at T2 <;>
    rcases Y2 with e2 | ⟨s2, c2, d2⟩ <;> simp only [ThroughLink] at T3 <;>
    rcases X2 with f2 | ⟨r2, b2, a2⟩ <;> simp only [ReadLex] at R2 <;> simp only [SameRead]
  · rw [R1, R2, T1, T2, T3]
  · obtain ⟨rfl, rfl, rfl⟩ := R1
    obtain ⟨rfl, rfl, rfl⟩ := R2
    obtain ⟨rfl, hb1, ha1⟩ := T1
    obtain ⟨rfl, hbz, haz⟩ := T2
    obtain ⟨rfl, hb2, ha2⟩ := T3
    refine ⟨rfl, ?_, ?_⟩
    · have e := (ha1.2.2.trans (congrArg CanonAdapter.adapter haz.handler)).trans ha2.2.2.symm
      show (Internal.handler d1).handler = (Internal.handler d2).handler
      have e2 : (canonA (Internal.handler d1)).handler = (canonA (Internal.handler d2)).handler :=
        congrArg ParseAdapter.handler e
      exact e2
    · show (Internal.core c1).discardedFrom = (Internal.core c2).discardedFrom
      rw [hb1.1, hb2.1]
      exact hbz.discardedFrom

section

-- the handlers are the one given, not the recording handler's instances
attribute [-instance] BSmtLib.Facts.Parser.Adapters.Handler.recordingLibraryTerms
  BSmtLib.Facts.Parser.Adapters.Handler.recordingLibrary

/-- `reading_resets` of a library handler with the recording handler's state, outside the
printer. -/
def ResetsWith (I : Traits.CommandHandler (List BSmtLibSpec.Parser.Properties.Event) Id) :
    Prop :=
  letI := I
  ∀ (version : Token.Version) (first next : List ByteList) (result : Option (Span.Located Unit))
    (before after : Reader (List BSmtLibSpec.Parser.Properties.Event)
      (ScriptParser (List BSmtLibSpec.Parser.Properties.Event) (m := Id)) (m := Id)),
    readThrough (Reader.script ([] : List BSmtLibSpec.Parser.Properties.Event) allVersions
        version) first = .ok (result, before, after) →
      SameRead (readThrough after next)
        (readThrough (Reader.script after.handler allVersions version) next)

end

theorem recording_ResetsWith :
    ResetsWith BSmtLib.Facts.Parser.Adapters.Handler.recordingLibrary :=
  fun version first next _ _ _ h => resets_recording version first next h

open Reprinting BSmtLib.Facts.PublicApi.Adapters.Content in
/-- The recorder, after an input it read to the end, reads the next input as a new script reader
over its handler does. -/
theorem recorder_resets :
    ∀ version first next result before after,
      readThrough (recorder.reader version) first = .ok (result, before, after) →
        recorder.observe (readThrough after next) =
          recorder.observe
            (readThrough (Reader.script after.handler allVersions version) next) := by
  have hw : ResetsWith (@ContentHandler.instCommandHandler
      (List BSmtLibSpec.Parser.Properties.Event)
      Recorder.recorderContent) := Recorder.instCommandHandler_eq ▸ recording_ResetsWith
  intro version first next result before after h
  have hs : SameRead (readThrough after next)
      (readThrough (Reader.script after.handler allVersions version) next) :=
    hw version first next result before after h
  unfold BSmtLib.Facts.PublicApi.Adapters.Reprinter.observe
  revert hs
  generalize readThrough after next = X
  generalize readThrough (Reader.script after.handler allVersions version) next = Y
  intro hs
  rcases X with f | ⟨r, b, a⟩ <;> rcases Y with g | ⟨r', b', a'⟩ <;> simp only [SameRead] at hs
  · dsimp only
    rw [hs]
  · obtain ⟨rfl, ha, hb⟩ := hs
    dsimp only
    rw [ha, hb]

end BSmtLib.Facts.Proofs.PublicApi.ReaderResets
