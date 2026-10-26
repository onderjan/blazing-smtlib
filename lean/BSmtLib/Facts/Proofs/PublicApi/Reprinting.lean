module

public import BSmtLib.Facts.PublicApi.Adapters.Reprinter
public import BSmtLib.Facts.Proofs.PublicApi.Recorder
public import BSmtLib.Facts.Proofs.PublicApi.Discard
public import BSmtLib.Facts.Proofs.PublicApi.Files
public import BSmtLib.Facts.Reader
public import BSmtLib.Facts.Proofs.Reader.Declared
public import BSmtLibSpec.Facts.Proofs.Reader.Switches
import all BSmtLib.Lexer
import all BSmtLib.Parser.Adapter
import all BSmtLib.Reader

@[expose] public section

/-!
# Reprinting

The witness of `Facts.reprinting`: the recording handler, which writes down every call it is told,
and the printer that reads the file's commands back from the calls and writes their tokens. The
calls determine the commands (`BSmtLibSpec.Facts.Reader.callsDetermineCommands`); the reader tells
the handler the calls of a file's commands and finishes only on files
(`Facts.Reader.reader_reads_files`, `Facts.Reader.reader_finishes_only_on_files`); and a file is its
commands' tokens with layout between them (`Files.spaced_of_reading`).
-/

namespace BSmtLib.Facts.Proofs.PublicApi.Reprinting

open BSmtLibSpec BSmtLibSpec.Grammar BSmtLibSpec.Parser BSmtLibSpec.Parser.Properties
open BSmtLibSpec.Facts.Proofs.Grammar.RoundTrip
open BSmtLib.Facts.Reader.Adapters (RecReader readerOf readerRun libraryReader)
open BSmtLib.Facts.Lexer.Adapters (toVersion fromVersion toLocation)
open BSmtLib.Facts.Proofs.PublicApi.Discard BSmtLib.Facts.Proofs.PublicApi.Files
open BSmtLib.Facts.Proofs.PublicApi.Recorder BSmtLib.Facts.PublicApi.Adapters
open BSmtLib.Facts.PublicApi.Adapters.Content BSmtLibSpec.Facts.Proofs.Reader.Switches
open BSmtLib.Facts.PublicApi.Adapters.Reprinter (from25 only20)
open BSmtLib.Facts.Parser.Adapters.Handler (recordingLibrary recordingLibraryTerms)
open BSmtLib.Facts.Proofs.Reader.Param.Posture (Looser)
open BSmtLibSpec.Facts.Proofs.Lexicon.RoundTrip.Tokens (Concrete)
open BSmtLib.Facts.Proofs.Reader.Looser (readThrough_looser)
open BSmtLib.Facts.Proofs.Reader.Declared (Allowed keeps_allowed)
open BSmtLib.Parser.Adapter (ParseAdapter)
open BSmtLib.Parser.Script (ScriptParser)

/-- The tokens of the file whose calls the log holds, newest first, if there is one. -/
noncomputable def printLog (log : List Event) : List ByteList :=
  open Classical in
  if h : ∃ p : Lexicon.Version × List Tree.Command,
      (∃ input, File p.1 input p.2) ∧ BSmtLibSpec.Reader.calls p.1 p.2 = log.reverse then
    tokensOf (Classical.choose h).1 (Classical.choose h).2
  else []

/-- The printer reads back the file whose calls the log holds. -/
theorem printLog_eq {version : Lexicon.Version} {input : Regex.Chars} {commands : List Tree.Command}
    (hfile : File version input commands) {log : List Event}
    (hlog : log.reverse = BSmtLibSpec.Reader.calls version commands) :
    printLog log = tokensOf version commands := by
  have hex : ∃ p : Lexicon.Version × List Tree.Command,
      (∃ input, File p.1 input p.2) ∧ BSmtLibSpec.Reader.calls p.1 p.2 = log.reverse :=
    ⟨(version, commands), ⟨input, hfile⟩, hlog.symm⟩
  unfold printLog
  split
  · rename_i hex'
    obtain ⟨⟨input', hfile'⟩, hcalls⟩ := Classical.choose_spec hex'
    obtain ⟨hv, hc⟩ := Facts.Reader.callsDetermineCommands _ _ _ _ _ _ hfile' hfile
      (hcalls.trans hlog)
    rw [hv, hc]
  · contradiction

/-- A read through slices reads the first slice, then the rest. -/
theorem readThrough_cons {H P E R : Type} [Parser.Parse P H Id E R] [Handler H Id]
    (reader : Reader H P) (slice : ByteList) (slices : List ByteList) :
    readThrough reader (slice :: slices) =
      match (reader.readSlice slice.toByteArray.toByteSlice : Id _) with
      | .ok reader => readThrough reader slices
      | .error failure => .error failure := by
  unfold readThrough
  rw [feed]
  cases (reader.readSlice slice.toByteArray.toByteSlice : Id _) <;> rfl

/-- A read through to the end of the input is the reader's run of the end-to-end proofs. -/
theorem readerRun_of_readThrough :
    ∀ (reader : RecReader) (slices : List ByteList) {result before after},
      readThrough reader slices = .ok (some result, before, after) →
        readerRun reader slices true = (after.handler.reverse, true)
  | reader, [], result, before, after, h => by
    simp only [readThrough, feed] at h
    simp only [readerRun]
    split at h
    · rename_i result' after' heof
      simp only [Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      rw [heof]
      rfl
    · simp at h
  | reader, slice :: slices, result, before, after, h => by
    rw [readThrough_cons] at h
    simp only [readerRun]
    cases hs : (reader.readSlice (List.toByteArray slice).toByteSlice : Id _) with
    | ok reader' =>
      rw [hs] at h
      exact readerRun_of_readThrough reader' slices h
    | error e => rw [hs] at h; cases h

/-- Where the reader of a file began to discard: after `exit`, where the unread rest begins; else
nowhere, so up to the end. -/
theorem readUpTo_of_reading {version : Lexicon.Version} {slices : List ByteList}
    {commands : List Tree.Command} {segments : List (Lexicon.Version × Concrete)}
    {final : ByteList} (hreading : FileReadingFrom version 0 slices.flatten commands segments final)
    {result : Option (Span.Located Unit)} {before after : RecReader}
    (h : readThrough (readerOf version) slices = .ok (result, before, after)) :
    (commands.getLast? = some .exit →
        readUpTo before slices.flatten.length = slices.flatten.length - final.length) ∧
      (commands.getLast? ≠ some .exit →
        readUpTo before slices.flatten.length = slices.flatten.length) := by
  have hd := reader_discardedFrom version slices (feed_of_readThrough h)
  obtain ⟨hex, hnoex⟩ := open_session_discard _ Facts.Lexer.correctWithConsumers version slices
    hreading
  refine ⟨fun he => ?_, fun he => ?_⟩
  · have := hex he
    rw [← hd, Option.map_map] at this
    unfold readUpTo
    cases hb : before.discardedFrom with
    | none => rw [hb] at this; cases this
    | some l =>
      rw [hb] at this
      simpa [toLocation] using this
  · have := hnoex he
    rw [← hd] at this
    unfold readUpTo
    cases hb : before.discardedFrom with
    | none => rfl
    | some l => rw [hb] at this; cases this

/-- The reader of the recording handler with the initial version, allowing every version, is the
reader of the end-to-end proofs. -/
theorem reader_eq (version : Version) :
    Reader.script ([] : List Event) allVersions version = readerOf (fromVersion version) := by
  cases version <;> rfl

/-- Every version `only20` allows, `allVersions` allows, and neither limits the declarations. -/
theorem only20_looser : Looser only20 allVersions :=
  ⟨by simp [only20, allVersions], fun v h => by
    rw [Array.contains_iff_mem] at h ⊢
    simp [only20, allVersions] at h ⊢
    exact .inl h⟩

/-- A reader allowing only 2.0, from 2.0, that reads an input to the end reads it as the reader
allowing every version: to the same handler, with the same discarding. -/
theorem only20_as_all {slices : List ByteList} {result : Span.Located Unit}
    {before after : RecReader}
    (h : readThrough (Reader.script ([] : List Event) only20 .v2_0) slices =
      .ok (some result, before, after)) :
    ∃ before' after' : RecReader,
      readThrough (Reader.script ([] : List Event) allVersions .v2_0) slices =
        .ok (some result, before', after') ∧
      after'.handler = after.handler ∧ before'.discardedFrom = before.discardedFrom := by
  have hI₀ : Allowed only20 (Reader.Param.Watch.new
      (ParseAdapter.new ([] : List Event) (ScriptParser.new (H := List Event) only20))
      .v2_0) :=
    ⟨by
      show only20.allowed.contains .v2_0 = true
      rw [Array.contains_iff_mem]; simp [only20], fun _ h => by cases h⟩
  obtain ⟨before', after', h', hhandler, hdisc, -⟩ :=
    readThrough_looser only20_looser (keeps_allowed only20) .v2_0 hI₀ h
  exact ⟨before', after', h', hhandler, hdisc⟩

/-- Every version `from25` allows, `allVersions` allows, and neither limits the declarations. -/
theorem from25_looser : Looser from25 allVersions :=
  ⟨by simp [from25, allVersions], fun v h => by
    rw [Array.contains_iff_mem] at h ⊢
    simp [from25, allVersions] at h ⊢
    rcases h with rfl | rfl | rfl <;> simp⟩

/-- A reader allowing the versions from 2.5 on, from one of them, that reads an input to the end
reads it as the reader allowing every version: to the same handler, with the same discarding;
and on a file, no command declares 2.0. -/
theorem from25_as_all {version : Version} (hv : version ≠ .v2_0) {slices : List ByteList}
    {result : Span.Located Unit} {before after : RecReader}
    (h : readThrough (Reader.script ([] : List Event) from25 version) slices =
      .ok (some result, before, after)) :
    ∃ before' after' : RecReader,
      readThrough (Reader.script ([] : List Event) allVersions version) slices =
        .ok (some result, before', after') ∧
      after'.handler = after.handler ∧ before'.discardedFrom = before.discardedFrom ∧
      ∀ commands, File (fromVersion version) slices.flatten commands →
        ∀ command ∈ commands, command.declaredVersion ≠ some .v2_0 := by
  have hI₀ : Allowed from25 (Reader.Param.Watch.new
      (ParseAdapter.new ([] : List Event) (ScriptParser.new (H := List Event) from25))
      version) :=
    ⟨by
      show from25.allowed.contains version = true
      rw [Array.contains_iff_mem]; cases version <;> simp_all [from25], fun _ h => by cases h⟩
  obtain ⟨before', after', h', hhandler, hdisc, w, ⟨-, hw⟩, hwi⟩ :=
    readThrough_looser from25_looser (keeps_allowed from25) version hI₀ h
  refine ⟨before', after', h', hhandler, hdisc, fun commands hfile command hmem hd => ?_⟩
  have h'' : readThrough (Reader.script ([] : List Event) allVersions version) slices =
      .ok (some result, before', after') := h'
  rw [reader_eq] at h''
  have hcalls := Reader.reader_reads_files _ _ _ hfile
  change readerRun (readerOf _) slices true = _ at hcalls
  rw [readerRun_of_readThrough _ slices h''] at hcalls
  have hmemc := handlerSwitch_mem_calls hfile hmem hd
  rw [← (Prod.mk.inj hcalls).1, hhandler, List.mem_reverse] at hmemc
  have hhw : after.handler = w.inner.handler := by rw [hwi]; rfl
  rw [hhw] at hmemc
  exact absurd (hw.2 .v2_0 hmemc) (by rw [Array.contains_iff_mem]; simp [from25])

/-- What the recording handler reprints of an input read to the end. -/
theorem recording_reprints (version : Version) (slices : List ByteList)
    {result : Span.Located Unit} {before after : RecReader}
    (h : readThrough (Reader.script ([] : List Event) allVersions version) slices =
      .ok (some result, before, after)) :
    ∃ commands, File (fromVersion version) slices.flatten commands ∧
      ∃ written, Spaced written (slices.flatten.take (readUpTo before slices.flatten.length)) ∧
        SameSpellings written (printLog after.handler) ∧
        (fromVersion version ≠ .v2_0 →
          (∀ command ∈ commands, command.declaredVersion ≠ some .v2_0) →
          written = printLog after.handler) := by
  rw [reader_eq] at h
  have hrun := readerRun_of_readThrough _ slices h
  obtain ⟨commands, hfile⟩ := Reader.reader_finishes_only_on_files (fromVersion version) slices
    (by show (readerRun (readerOf _) slices true).2 = true; rw [hrun])
  have hcalls := Reader.reader_reads_files _ _ _ hfile
  change readerRun (readerOf _) slices true = _ at hcalls
  rw [hrun] at hcalls
  have hprint : printLog after.handler = tokensOf (fromVersion version) commands :=
    printLog_eq hfile (Prod.mk.inj hcalls).1
  rw [hprint]
  obtain ⟨segments, final, hreading⟩ := exists_fileReading hfile
  obtain ⟨pre, written, hpre, hsame, hspaced, hlast, hexact⟩ := spaced_of_reading hreading
  refine ⟨commands, hfile, written, ?_, hsame, hexact⟩
  have hupto := readUpTo_of_reading hreading h
  by_cases hexit : commands.getLast? = some .exit
  · have e : readUpTo before slices.flatten.length = slices.flatten.length - final.length :=
      hupto.1 hexit
    rw [e, hpre]
    have : (pre ++ final).take ((pre ++ final).length - final.length) = pre := by
      simp
    rw [this]
    simpa using hspaced [] (.layout .nil)
  · have e : readUpTo before slices.flatten.length = slices.flatten.length := hupto.2 hexit
    rw [e, hpre, List.take_length]
    exact hspaced final (hlast.resolve_left hexit)

section

-- the handlers are the one given, not the recording handler's instances
attribute [-instance] recordingLibraryTerms recordingLibrary

/-- `Reprints20` of a library handler with the recording handler's state. -/
def Reprints20With (I : Handler.CommandHandler (List Event) Id) : Prop :=
  letI := I
  ∀ (slices : List ByteList) (result : Span.Located Unit)
    (before after : Reader (List Event) (ScriptParser (List Event) (m := Id)) (m := Id)),
    readThrough (Reader.script ([] : List Event) only20 .v2_0) slices =
        .ok (some result, before, after) →
      ∃ written, Spaced written (slices.flatten.take (readUpTo before slices.flatten.length)) ∧
        SameSpellings written (printLog after.handler)

/-- `ReprintsExactly25Plus` of a library handler with the recording handler's state. -/
def ReprintsExactly25PlusWith (I : Handler.CommandHandler (List Event) Id) : Prop :=
  letI := I
  ∀ (version : Version) (slices : List ByteList) (result : Span.Located Unit)
    (before after : Reader (List Event) (ScriptParser (List Event) (m := Id)) (m := Id)),
    version ≠ .v2_0 →
    readThrough (Reader.script ([] : List Event) from25 version) slices =
        .ok (some result, before, after) →
      Spaced (printLog after.handler) (slices.flatten.take (readUpTo before slices.flatten.length))

end

theorem recording_Reprints20With : Reprints20With recordingLibrary := by
  intro slices result before after h
  obtain ⟨before', after', h', hhandler, hdiscard⟩ := only20_as_all h
  obtain ⟨-, -, written, h₁, h₂, -⟩ := recording_reprints .v2_0 slices h'
  have hupto : readUpTo before' slices.flatten.length = readUpTo before slices.flatten.length := by
    simp only [readUpTo, Reader.discardedFrom] at hdiscard ⊢
    rw [hdiscard]
  rw [← hupto, ← hhandler]
  exact ⟨written, h₁, h₂⟩

theorem recording_ReprintsExactly25PlusWith : ReprintsExactly25PlusWith recordingLibrary := by
  intro version slices result before after hv h
  obtain ⟨before', after', h', hhandler, hdiscard, hdecl⟩ := from25_as_all hv h
  obtain ⟨commands, hfile, written, h₁, -, h₃⟩ := recording_reprints version slices h'
  have hupto : readUpTo before' slices.flatten.length = readUpTo before slices.flatten.length := by
    simp only [readUpTo, Reader.discardedFrom] at hdiscard ⊢
    rw [hdiscard]
  rw [← hupto, ← hhandler, ← h₃ (by cases version <;> simp_all [fromVersion])
    (hdecl commands hfile)]
  exact h₁

/-- The recording handler, told contents only, with the printer of the file its calls are
for. -/
noncomputable def recorder : Reprinter where
  H := List Event
  inst := recorderContent
  handler := []
  print := printLog

/-- The recorder reprints. -/
theorem recorder_Reprints20 : recorder.Reprints20 :=
  (instCommandHandler_eq ▸ recording_Reprints20With :
    Reprints20With (@ContentHandler.instCommandHandler (List Event) recorderContent))

/-- The recorder reprints exactly from 2.5 on. -/
theorem recorder_ReprintsExactly25Plus : recorder.ReprintsExactly25Plus :=
  (instCommandHandler_eq ▸ recording_ReprintsExactly25PlusWith :
    ReprintsExactly25PlusWith (@ContentHandler.instCommandHandler (List Event) recorderContent))

end BSmtLib.Facts.Proofs.PublicApi.Reprinting
