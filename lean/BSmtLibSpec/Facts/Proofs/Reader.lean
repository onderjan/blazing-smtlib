module

public import BSmtLibSpec.Facts.Proofs.Reader.Finishes

@[expose] public section

/-!
# Readers

The calls for the commands of a file determine the file's initial version and commands: the commands
of a file make a script (`script_of_file`), the first call is the switch to the file's initial
version, and the calls of a script's recording rebuild the script
(`Parser.recover_record`).

That a reader which lexes then parses (`BSmtLibSpec.Reader.LexesThenParses`) reads files and
finishes only on files is `lexesThenParses_reads`. On a file, the lexer hands over the tokens of the
file's commands, each read in the version in force, and the parser takes what a parser receives
for the script (`files_runs`). If the reader finishes, the parser has taken what a parser takes
for a script, as it would otherwise have rejected a token (`finishes_script`), and the tokens it
took are those of a file with that script (`finishes_file`).

Not trusted: this is a check of the specification formalism (`BSmtLibSpec`).
-/

namespace BSmtLibSpec.Facts.Proofs.Reader

open BSmtLibSpec.Lexicon BSmtLibSpec.Grammar
open BSmtLibSpec.Parser.Properties
open BSmtLibSpec.Regex (Chars)
open BSmtLibSpec.Reader

/-- The commands of a file make a script. -/
theorem script_of_file {version : Version} {offset : Nat} {input : Chars}
    {commands : List Tree.Command} (h : File.From version offset input commands) :
    Script version commands := by
  induction h with
  | done => exact .done
  | command _ hic hm _ ih => exact .command hic.1 hm ih
  | stop _ hic hm => exact .stop hic.1 hm

/-- The calls for the commands of two files are equal only if the files are read from the same
version and have the same commands. -/
theorem calls_determine {version version' : Version} {input input' : Chars}
    {commands commands' : List Tree.Command} (h : File version input commands)
    (h' : File version' input' commands')
    (hc : calls version commands = calls version' commands') :
    version = version' ∧ commands = commands' := by
  have hs := script_of_file h
  have hs' := script_of_file h'
  obtain ⟨r, hr⟩ := Parser.Bridge.record_head hs
  obtain ⟨r', hr'⟩ := Parser.Bridge.record_head hs'
  have hv : version = version' := by
    have hc' := hc
    simp only [calls, hr, hr', List.filter_cons, Event.isCall, ↓reduceIte, List.cons.injEq,
      Event.handlerSwitch.injEq] at hc'
    exact hc'.1
  subst hv
  refine ⟨rfl, ?_⟩
  have h₁ := Parser.Calls.recover_record hs
  have h₂ := Parser.Calls.recover_record hs'
  simp only [calls] at hc
  rw [hc, h₂] at h₁
  exact (Option.some.inj h₁).symm

/-- An empty file: the handler is told the version and nothing else. -/
example : calls .v2_7 [] = [.handlerSwitch .v2_7] := rfl

/-- Events before more arrivals than they have are all of them. -/
theorem eventsBefore_of_le : ∀ (count : Nat) (events : List Event),
    (events.filterMap Event.arrived).length ≤ count → eventsBefore count events = events
  | _, [], _ => rfl
  | 0, .arrive _ :: _, h => by simp [Event.arrived] at h
  | count + 1, .arrive received :: rest, h => by
    simp only [List.filterMap_cons, Event.arrived, List.length_cons] at h
    simp only [eventsBefore, eventsBefore_of_le count rest (by omega)]
  | 0, .process _ :: rest, h => by
    simp only [List.filterMap_cons, Event.arrived] at h
    simp only [eventsBefore, eventsBefore_of_le 0 rest h]
  | count + 1, .process _ :: rest, h => by
    simp only [List.filterMap_cons, Event.arrived] at h
    simp only [eventsBefore, eventsBefore_of_le (count + 1) rest h]
  | 0, .call _ _ :: rest, h => by
    simp only [List.filterMap_cons, Event.arrived] at h
    simp only [eventsBefore, eventsBefore_of_le 0 rest h]
  | count + 1, .call _ _ :: rest, h => by
    simp only [List.filterMap_cons, Event.arrived] at h
    simp only [eventsBefore, eventsBefore_of_le (count + 1) rest h]
  | 0, .handlerSwitch _ :: rest, h => by
    simp only [List.filterMap_cons, Event.arrived] at h
    simp only [eventsBefore, eventsBefore_of_le 0 rest h]
  | count + 1, .handlerSwitch _ :: rest, h => by
    simp only [List.filterMap_cons, Event.arrived] at h
    simp only [eventsBefore, eventsBefore_of_le (count + 1) rest h]
  | 0, .producerSwitch _ :: rest, h => by
    simp only [List.filterMap_cons, Event.arrived] at h
    simp only [eventsBefore, eventsBefore_of_le 0 rest h]
  | count + 1, .producerSwitch _ :: rest, h => by
    simp only [List.filterMap_cons, Event.arrived] at h
    simp only [eventsBefore, eventsBefore_of_le (count + 1) rest h]
  | 0, .producerDiscard :: rest, h => by
    simp only [List.filterMap_cons, Event.arrived] at h
    simp only [eventsBefore, eventsBefore_of_le 0 rest h]
  | count + 1, .producerDiscard :: rest, h => by
    simp only [List.filterMap_cons, Event.arrived] at h
    simp only [eventsBefore, eventsBefore_of_le (count + 1) rest h]

/-- A reader that lexes then parses, fed an input, does with its lexer and parser what the lexer
does with the parser from the start of the input. -/
theorem lexes_runs {lexing : Lexer.Lexing} {parser : RecordingParser}
    {item : Lexer.Handed → parser.Item}
    (hL : Lexer.CorrectWithConsumers lexing) (version : Version) (slices : List Chars) :
    Lexer.Runs lexing.fed (Reader.consumer parser item version) version slices.flatten true version
      ((Lexer.segment lexing.fed version slices.flatten true 0).handed.drop
          ([] : List Token).length)
      (Lexer.segment lexing.fed version slices.flatten true 0).failed []
      (lexing (Reader.consumer parser item version) version [] slices true) := by
  have := hL.2.1 (Reader.consumer parser item version) version slices true
    (Consumer.consumer_breaksAtEnd version)
  simpa [Lexer.readyFrom, Lexer.withLayout, Reader.consumer] using this

/-- A reader that lexes then parses reads files and finishes only on files. -/
theorem lexesThenParses_reads (reader : RecordingReader) (h : LexesThenParses reader) :
    ReadsFiles reader ∧ FinishesOnlyOnFiles reader := by
  obtain ⟨lexing, parser, item, hL, hF, hR, hI, hread⟩ := h
  refine ⟨fun version slices commands hfile => ?_, fun version slices hfin => ?_⟩
  · have hscript := script_of_file hfile
    have hS := Finishes.script_takes hscript
    obtain ⟨more, location, hruns, hstood⟩ := Files.files_runs hF hI hL.1
        (input := slices.flatten) hS
      hfile [] 0 []
      (by simp) (by simp) (by simp) (Nat.zero_le _) (Nat.le_refl 0)
      (by simpa using Files.tokenization_nil version) (Or.inl ⟨rfl, rfl⟩)
    have hsession := Lexer.Consumers.runs_unique (lexes_runs hL version slices) hruns
    rw [hread, hsession]
    simp only [List.nil_append] at hstood ⊢
    have hne : more ≠ [] := by
      intro e
      rw [e] at hstood
      exact Files.received_ne_nil commands (by simpa [Consumer.stood] using hstood.symm)
    have hlen : more.length = (received commands).length := by
      simpa [Consumer.stood] using congrArg List.length hstood
    rw [Consumer.parse_of_takes hF hI hS (by rw [hstood, hlen, List.take_length]) (by omega)]
    simp only [hne, ite_false, hlen, Lexer.Outcome.isFinished]
    rw [eventsBefore_of_le _ _ (by rw [(Parser.Calls.record_items hscript).1]; exact Nat.le_refl _)]
    rfl
  · rw [hread] at hfin
    simp only at hfin
    have h₀ := lexes_runs (item := item) hL version slices
    obtain ⟨commands, hscript, hstood⟩ := Finishes.finishes_script hF hR hI hL.1 h₀
      ⟨[], [.endOfInput], .finished, .done, rfl, by simp⟩ rfl
      (by simpa using Finishes.segment_ofVersion hL.1 version slices.flatten 0) (Or.inl rfl) hfin
    obtain ⟨tokens, hread₀, hfed₀⟩ := Lexing.fed_readout hL.1 version (slices.flatten.drop 0)
    have hfile := Finishes.finishes_file hF hI hL.1
        (Finishes.script_takes hscript) hstood hscript [] 0 0 [] tokens
      (lexes_runs hL version slices) (by simp) (by simp) (Nat.le_refl 0) (Nat.zero_le _)
      (by simpa using Files.tokenization_nil version) (Or.inl ⟨rfl, rfl⟩) hread₀ hfed₀ (by simp)
    exact ⟨commands, by simpa [File] using hfile⟩

end BSmtLibSpec.Facts.Proofs.Reader
