import BSmtLibSpec.Facts.Proofs.Lexicon.Compose
import BSmtLibSpec.Facts.Proofs.Grammar.OneToOne

/-!
# Every file has at most one reading

A command is written with tokens that end with its `)`, so the characters of a command, read
in a version, end with a `)` at their end. Two readings of a file start with the same
characters, so by `Lexicon.tokenizationFrom_close_prefix` the tokens of the shorter first
command start those of the longer one; a command is read back from its tokens whatever follows
them (`readCommand_tokens`), so both are the same command, with the same characters
(`segment_eq`). The command determines the mode after it, so the rest of the file is read in
the same version, or not at all, in both readings (`fileFrom_unique`).

Not trusted: everything here is proved.
-/

namespace BSmtLibSpec.Facts.Proofs.Grammar.Files

open BSmtLibSpec.Lexicon BSmtLibSpec.Grammar
open BSmtLibSpec.Grammar.Syntax
open BSmtLibSpec.Regex (Chars)
open BSmtLibSpec.Facts.Proofs.Lexicon.Compose
open BSmtLibSpec.Facts.Proofs.Grammar.OneToOne

/-- The tokens of a command end with `)`. -/
theorem command_getLast (command : Tree.Command) :
    command.tokens.getLast? = some .parenClose := by
  have h : ∃ inner, command.tokens = paren inner := by
    cases command <;> exact ⟨_, rfl⟩
  obtain ⟨inner, h⟩ := h
  rw [h, paren, List.getLast?_append]
  simp

/-- The characters of a command, read in a version, end with a `)` at their end. -/
theorem endsWithClose_of_command {version : Version} {offset : Nat} {segment : Chars}
    {tokens : List Token} {command : Tree.Command}
    (h : Tokenization.Exactly version offset segment tokens)
    (hc : IsCommand version (tokens.map (SyntaxToken.ofToken version)) command) :
    EndsWithClose tokens (offset + segment.length) := by
  obtain ⟨-, last, hlast, hend⟩ := h
  refine ⟨last, hlast, ?_, hend⟩
  have h₁ := command_getLast command
  rw [hc.2, List.getLast?_map, hlast] at h₁
  simp only [Option.map_some, Option.some.injEq] at h₁
  revert h₁
  unfold SyntaxToken.ofToken
  cases last.category <;> simp

/-- A command read from characters that start the characters of another command is that
command, from the same characters. -/
theorem segment_prefix {version : Version} {offset : Nat} {segment more : Chars}
    {tokens tokens' : List Token} {command command' : Tree.Command}
    (h : Tokenization.Exactly version offset segment tokens)
    (hc : IsCommand version (tokens.map (SyntaxToken.ofToken version)) command)
    (h' : Tokenization.Exactly version offset (segment ++ more) tokens')
    (hc' : IsCommand version (tokens'.map (SyntaxToken.ofToken version)) command') :
    more = [] ∧ command = command' := by
  obtain ⟨others, rfl, -⟩ :=
    tokenizationFrom_close_prefix h.1 (endsWithClose_of_command h hc) h'.1
  have hr := readCommand_tokens version command (others.map (SyntaxToken.ofToken version))
    hc.1 (n := sizeOf command + sizeOf command' + 1) (by omega)
  have hr' := readCommand_tokens version command' [] hc'.1
    (n := sizeOf command + sizeOf command' + 1) (by omega)
  rw [hc'.2, List.map_append, ← hc.2, List.append_nil, hr] at hr'
  obtain ⟨rfl, hnil⟩ := Prod.mk.inj (Option.some.inj hr')
  rw [List.map_eq_nil_iff] at hnil
  subst hnil
  obtain ⟨last, hlast, -, hend⟩ := endsWithClose_of_command h hc
  obtain ⟨-, last', hlast', hend'⟩ := h'
  rw [List.append_nil, hlast] at hlast'
  obtain rfl := Option.some.inj hlast'
  simp only [List.length_append] at hend'
  exact ⟨List.eq_nil_of_length_eq_zero (by omega), rfl⟩

/-- Two commands that one input starts with, each read in the version, are the same command,
from the same characters. -/
theorem segment_eq {version : Version} {offset : Nat} {segment segment' rest rest' : Chars}
    {tokens tokens' : List Token} {command command' : Tree.Command}
    (h : Tokenization.Exactly version offset segment tokens)
    (hc : IsCommand version (tokens.map (SyntaxToken.ofToken version)) command)
    (h' : Tokenization.Exactly version offset segment' tokens')
    (hc' : IsCommand version (tokens'.map (SyntaxToken.ofToken version)) command')
    (heq : segment ++ rest = segment' ++ rest') :
    segment = segment' ∧ rest = rest' ∧ command = command' := by
  rcases List.append_eq_append_iff.mp heq with ⟨more, rfl, rfl⟩ | ⟨more, rfl, rfl⟩
  · obtain ⟨rfl, rfl⟩ := segment_prefix h hc h' hc'
    simp
  · obtain ⟨rfl, rfl⟩ := segment_prefix h' hc' h hc
    simp

/-- A file that is only whitespace has no command. -/
theorem not_command_of_done {version : Version} {offset : Nat} {segment rest : Chars}
    {tokens : List Token} {command : Tree.Command}
    (h : Tokenization.Exactly version offset segment tokens)
    (hc : IsCommand version (tokens.map (SyntaxToken.ofToken version)) command)
    (hdone : Tokenization.From version offset (segment ++ rest) []) : False := by
  obtain ⟨others, heq, -⟩ :=
    tokenizationFrom_close_prefix h.1 (endsWithClose_of_command h hc) hdone
  obtain ⟨last, hlast, -⟩ := endsWithClose_of_command h hc
  rw [List.nil_eq, List.append_eq_nil_iff] at heq
  rw [heq.1] at hlast
  simp at hlast

/-- What `File.From` holds of an input, taken apart. -/
theorem fileFrom_inv {version : Version} {offset : Nat} {input : Chars}
    {commands : List Tree.Command} (h : File.From version offset input commands) :
    (commands = [] ∧ Tokenization.From version offset input []) ∨
    (∃ segment rest tokens command others next, input = segment ++ rest ∧
      Tokenization.Exactly version offset segment tokens ∧
      IsCommand version (tokens.map (SyntaxToken.ofToken version)) command ∧
      command.modeAfter version = some (.read next) ∧
      File.From next (offset + segment.length) rest others ∧ commands = command :: others) ∨
    (∃ segment rest tokens command, input = segment ++ rest ∧
      Tokenization.Exactly version offset segment tokens ∧
      IsCommand version (tokens.map (SyntaxToken.ofToken version)) command ∧
      command.modeAfter version = some .unparsed ∧ commands = [command]) := by
  cases h with
  | done h => exact .inl ⟨rfl, h⟩
  | command h₁ h₂ h₃ h₄ => exact .inr (.inl ⟨_, _, _, _, _, _, rfl, h₁, h₂, h₃, h₄, rfl⟩)
  | stop h₁ h₂ h₃ => exact .inr (.inr ⟨_, _, _, _, rfl, h₁, h₂, h₃, rfl⟩)

/-- A file read from a version at an offset has at most one reading. -/
theorem fileFrom_unique {version : Version} {offset : Nat} {input : Chars}
    {commands commands' : List Tree.Command} (h : File.From version offset input commands)
    (h' : File.From version offset input commands') : commands = commands' := by
  induction h generalizing commands' with
  | done hdone =>
    rcases fileFrom_inv h' with ⟨rfl, -⟩ | ⟨_, _, _, _, _, _, rfl, h₁, h₂, -⟩ |
      ⟨_, _, _, _, rfl, h₁, h₂, -⟩
    · rfl
    · exact (not_command_of_done h₁ h₂ hdone).elim
    · exact (not_command_of_done h₁ h₂ hdone).elim
  | command h₁ h₂ h₃ _ ih =>
    rcases fileFrom_inv h' with ⟨-, hdone⟩ | ⟨_, _, _, _, _, _, heq, h₁', h₂', h₃', h₄', rfl⟩ |
      ⟨_, _, _, _, heq, h₁', h₂', h₃', rfl⟩
    · exact (not_command_of_done h₁ h₂ hdone).elim
    · obtain ⟨rfl, rfl, rfl⟩ := segment_eq h₁ h₂ h₁' h₂' heq
      rw [h₃] at h₃'
      cases h₃'
      rw [ih h₄']
    · obtain ⟨rfl, rfl, rfl⟩ := segment_eq h₁ h₂ h₁' h₂' heq
      rw [h₃] at h₃'
      cases h₃'
  | stop h₁ h₂ h₃ =>
    rcases fileFrom_inv h' with ⟨-, hdone⟩ | ⟨_, _, _, _, _, _, heq, h₁', h₂', h₃', -, rfl⟩ |
      ⟨_, _, _, _, heq, h₁', h₂', -, rfl⟩
    · exact (not_command_of_done h₁ h₂ hdone).elim
    · obtain ⟨rfl, rfl, rfl⟩ := segment_eq h₁ h₂ h₁' h₂' heq
      rw [h₃] at h₃'
      cases h₃'
    · obtain ⟨-, -, rfl⟩ := segment_eq h₁ h₂ h₁' h₂' heq
      rfl

end BSmtLibSpec.Facts.Proofs.Grammar.Files
