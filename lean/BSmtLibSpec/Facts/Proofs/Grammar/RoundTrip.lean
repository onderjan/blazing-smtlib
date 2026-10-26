module

public import BSmtLibSpec.Facts.Proofs.Lexicon.RoundTrip.Rewrite
public import BSmtLibSpec.Facts.Proofs.Grammar.Files

@[expose] public section

/-!
# Reproducing a file

A file is reproduced from its concrete reading, the whitespace and comments between its tokens,
and its parse: each command is written as its tokens, each token as the syntax token it stands
for, in the version in force, with the gaps of the reading between them; then what follows the
last command, its whitespace or the unparsed rest after `exit`, as it is (`reproduce`).

The reproduction is the input but for the spelling of 2.0 string literals that stand for the same
content (`reproduce_similar`); it is the input when no 2.0 string literal has a lone backslash
(`reproduce_eq`); and a reproduced input is a file with the same commands, which reproduces as
itself (`reproduce_reading`).

Not trusted: everything here is proved.
-/

namespace BSmtLibSpec.Facts.Proofs.Grammar.RoundTrip

open BSmtLibSpec.Lexicon BSmtLibSpec.Grammar
open BSmtLibSpec.Grammar.Syntax
open BSmtLibSpec.Regex (Chars)
open BSmtLibSpec.Facts.Proofs.Grammar.Files BSmtLibSpec.Facts.Proofs.Lexicon.RoundTrip.Lexical
open BSmtLibSpec.Facts.Proofs.Lexicon.RoundTrip.Rewrite
open BSmtLibSpec.Facts.Proofs.Lexicon.RoundTrip.Tokens BSmtLibSpec.Facts.Proofs.Lexicon.Unique

/-- The version in force after the command, read in the version. -/
def nextVersion (version : Version) (command : Tree.Command) : Version :=
  match command.modeAfter version with
  | some (.read next) => next
  | _ => version

/-- A command written as its tokens in the version, with the gaps before them and after the last. -/
def writeSegment (version : Version) (gaps : List Gap) (final : Gap) (command : Tree.Command) :
    Chars :=
  ((gaps.zip (command.tokens.map fun token => (lexForm version token).2)).flatMap
    fun piece => piece.1 ++ piece.2) ++ final

/-- A file reproduced from the gaps of its concrete reading, command by command, what follows its
last command, and its commands, with the initial version. -/
def reproduce : Version → List Tree.Command → List Concrete → Chars → Chars
  | version, command :: commands, segment :: segments, final =>
    writeSegment version (segment.pieces.map Prod.fst) segment.final command ++
      reproduce (nextVersion version command) commands segments final
  | _, _, _, final => final

/--
`FileReadingFrom version offset input commands segments final`: with the initial version
`version` and the starting offset `offset`, the input is read as the commands, each read from
the characters whose concrete reading, with the version it is read in, is the next of
`segments`, and `final` follows the last command: whitespace and comments, or the unparsed rest
after `exit`.
-/
inductive FileReadingFrom : Version → Nat → Chars → List Tree.Command →
    List (Version × Concrete) → Chars → Prop
  | done : Tokenization.From version offset input [] →
      FileReadingFrom version offset input [] [] input
  | command : Tokenization.Exactly version offset segment tokens →
      IsCommand version (tokens.map (SyntaxToken.ofToken version)) command →
      command.modeAfter version = some (.read next) →
      FileReadingFrom next (offset + segment.length) rest commands segments final →
      FileReadingFrom version offset (segment ++ rest) (command :: commands)
        ((version, readConcreteFrom offset segment tokens) :: segments) final
  | stop : Tokenization.Exactly version offset segment tokens →
      IsCommand version (tokens.map (SyntaxToken.ofToken version)) command →
      command.modeAfter version = some .unparsed →
      FileReadingFrom version offset (segment ++ rest) [command]
        [(version, readConcreteFrom offset segment tokens)] rest

theorem exists_fileReading {version : Version} {offset : Nat} {input : Chars}
    {commands : List Tree.Command} (h : File.From version offset input commands) :
    ∃ segments final, FileReadingFrom version offset input commands segments final := by
  induction h with
  | done h => exact ⟨[], _, .done h⟩
  | command h₁ h₂ h₃ _ ih =>
    obtain ⟨segments, final, hr⟩ := ih
    exact ⟨_, final, .command h₁ h₂ h₃ hr⟩
  | stop h₁ h₂ h₃ => exact ⟨_, _, .stop h₁ h₂ h₃⟩

theorem FileReadingFrom.file {version : Version} {offset : Nat} {input : Chars}
    {commands : List Tree.Command} {segments : List (Version × Concrete)} {final : Chars}
    (h : FileReadingFrom version offset input commands segments final) :
    File.From version offset input commands := by
  induction h with
  | done h => exact .done h
  | command h₁ h₂ h₃ _ ih => exact .command h₁ h₂ h₃ ih
  | stop h₁ h₂ h₃ => exact .stop h₁ h₂ h₃

theorem nextVersion_read {version next : Version} {command : Tree.Command}
    (h : command.modeAfter version = some (.read next)) : nextVersion version command = next := by
  simp [nextVersion, h]

/-- A command written with the gaps of a reading of its tokens is that reading rewritten. -/
theorem writeSegment_eq (version : Version) {command : Tree.Command} :
    ∀ (offset : Nat) (pieces : List (Gap × Token)) (final : Gap),
      command.tokens = pieces.map (SyntaxToken.ofToken version ∘ Prod.snd) →
      writeSegment version (pieces.map Prod.fst) final command =
        printConcrete ⟨rewritePieces version offset pieces, final⟩ := by
  intro offset pieces final h
  simp only [writeSegment, h]
  clear h
  induction pieces generalizing offset with
  | nil => simp [rewritePieces, printConcrete]
  | cons piece pieces ih =>
    obtain ⟨gap, token⟩ := piece
    rw [rewritePieces, printConcrete_cons]
    simp only [List.map_cons, List.zip_cons_cons, List.flatMap_cons, Function.comp,
      List.append_assoc]
    rw [ih (offset + gap.length + (rewriteForm version token).2.length)]
    simp [rewriteForm, printConcrete]

/-- The tokens of a command, as the pieces of the concrete reading of its characters. -/
theorem command_tokens_pieces {version : Version} {offset : Nat} {segment : Chars}
    {tokens : List Token} {command : Tree.Command}
    (hc : IsCommand version (tokens.map (SyntaxToken.ofToken version)) command) :
    command.tokens = (readConcreteFrom offset segment tokens).pieces.map
      (SyntaxToken.ofToken version ∘ Prod.snd) := by
  have ht := readConcreteFrom_tokens offset segment tokens
  simp only [Concrete.tokens] at ht
  rw [hc.2, ← List.map_map, ht]

/-- The tokens of the concrete reading of a tokenisation are lexical tokens. -/
theorem pieces_regex {version : Version} {offset : Nat} {input : Chars} {tokens : List Token}
    (h : Tokenization.From version offset input tokens) :
    ∀ piece ∈ (readConcreteFrom offset input tokens).pieces,
      categoryRegex version piece.2.category piece.2.text := by
  intro piece hp
  have ht := readConcreteFrom_tokens offset input tokens
  simp only [Concrete.tokens] at ht
  exact tokenizationFrom_regex h piece.2 (ht ▸ List.mem_map_of_mem hp)

/-- A file is reproduced but for the spelling of 2.0 string literals with the same content. -/
theorem reproduce_similar {version : Version} {offset : Nat} {input : Chars}
    {commands : List Tree.Command} {segments : List (Version × Concrete)} {final : Chars}
    (h : FileReadingFrom version offset input commands segments final) :
    SameButStrings20 (reproduce version commands (segments.map Prod.snd) final) input := by
  induction h with
  | done => exact SameButStrings20.refl _
  | @command version offset segment tokens command next rest commands segments final
      h₁ h₂ h₃ _ ih =>
    simp only [List.map_cons, reproduce, nextVersion_read h₃]
    rw [writeSegment_eq version offset _ _ (command_tokens_pieces h₂)]
    have hs := printConcrete_rewritePieces_similar version offset
      (readConcreteFrom offset segment tokens).pieces
      (readConcreteFrom offset segment tokens).final (pieces_regex h₁.1)
    rw [show printConcrete ⟨(readConcreteFrom offset segment tokens).pieces,
        (readConcreteFrom offset segment tokens).final⟩ = segment from
      printConcrete_readConcreteFrom h₁.1] at hs
    exact hs.append ih
  | @stop version offset segment tokens command rest h₁ h₂ h₃ =>
    simp only [List.map_cons, List.map_nil, reproduce]
    rw [writeSegment_eq version offset _ _ (command_tokens_pieces h₂)]
    have hs := printConcrete_rewritePieces_similar version offset
      (readConcreteFrom offset segment tokens).pieces
      (readConcreteFrom offset segment tokens).final (pieces_regex h₁.1)
    rw [show printConcrete ⟨(readConcreteFrom offset segment tokens).pieces,
        (readConcreteFrom offset segment tokens).final⟩ = segment from
      printConcrete_readConcreteFrom h₁.1] at hs
    exact hs.append (SameButStrings20.refl rest)

/-- With no 2.0 string literal that has a lone backslash, the tokens of a reading are written
back as themselves. -/
theorem pieces_exact {version : Version} {offset : Nat} {input : Chars} {tokens : List Token}
    (h : Tokenization.From version offset input tokens)
    (hl : NoLoneBackslash version (readConcreteFrom offset input tokens).tokens) :
    ∀ piece ∈ (readConcreteFrom offset input tokens).pieces,
      (rewriteForm version piece.2).2 = piece.2.text := by
  intro piece hp
  have hone : NoLoneBackslash version [piece.2] := by
    intro hv t ht hcat
    simp only [List.mem_singleton] at ht
    subst ht
    exact hl hv _ (List.mem_map_of_mem hp) hcat
  have := lexForm_ofToken (pieces_regex h piece hp) hone
  simp only [rewriteForm, this, form]

/-- The rewritten reading of an input with no 2.0 string literal that has a lone backslash is
the input. -/
theorem rewrite_segment_eq {version : Version} {offset : Nat} {segment : Chars}
    {tokens : List Token} (h : Tokenization.From version offset segment tokens)
    (hl : NoLoneBackslash version (readConcreteFrom offset segment tokens).tokens) :
    printConcrete ⟨rewritePieces version offset (readConcreteFrom offset segment tokens).pieces,
      (readConcreteFrom offset segment tokens).final⟩ = segment := by
  rw [printConcrete_rewritePieces_eq version offset _ _ (pieces_exact h hl)]
  exact printConcrete_readConcreteFrom h

/-- With no 2.0 string literal that has a lone backslash, a file is reproduced exactly. -/
theorem reproduce_eq {version : Version} {offset : Nat} {input : Chars}
    {commands : List Tree.Command} {segments : List (Version × Concrete)} {final : Chars}
    (h : FileReadingFrom version offset input commands segments final)
    (hl : ∀ segment ∈ segments, NoLoneBackslash segment.1 segment.2.tokens) :
    reproduce version commands (segments.map Prod.snd) final = input := by
  induction h with
  | done => rfl
  | @command version offset segment tokens command next rest commands segments final
      h₁ h₂ h₃ _ ih =>
    simp only [List.map_cons, reproduce, nextVersion_read h₃]
    rw [writeSegment_eq version offset _ _ (command_tokens_pieces h₂),
      ih fun s hs => hl s (List.mem_cons_of_mem _ hs)]
    rw [rewrite_segment_eq h₁.1 (hl _ List.mem_cons_self)]
  | @stop version offset segment tokens command rest h₁ h₂ h₃ =>
    simp only [List.map_cons, List.map_nil, reproduce]
    rw [writeSegment_eq version offset _ _ (command_tokens_pieces h₂),
      rewrite_segment_eq h₁.1 (hl _ List.mem_cons_self)]

/-! ## Reproducing a reproduction -/

theorem printConcrete_rewritePieces_offset (version : Version) :
    ∀ (offset offset' : Nat) (pieces : List (Gap × Token)) (final : Gap),
      printConcrete ⟨rewritePieces version offset pieces, final⟩ =
        printConcrete ⟨rewritePieces version offset' pieces, final⟩
  | _, _, [], _ => rfl
  | offset, offset', (gap, token) :: pieces, final => by
    rw [rewritePieces, rewritePieces, printConcrete_cons, printConcrete_cons,
      printConcrete_rewritePieces_offset version _
        (offset' + gap.length + (rewriteForm version token).2.length) pieces final]

/-- Reading the rewritten pieces back gives them back. -/
theorem readConcreteFrom_rewritePieces (version : Version) :
    ∀ (offset : Nat) (pieces : List (Gap × Token)) (final : Gap),
      readConcreteFrom offset (printConcrete ⟨rewritePieces version offset pieces, final⟩)
        ((rewritePieces version offset pieces).map Prod.snd) =
        ⟨rewritePieces version offset pieces, final⟩
  | _, [], final => by simp [rewritePieces, readConcreteFrom, printConcrete]
  | offset, (gap, token) :: pieces, final => by
    rw [rewritePieces, printConcrete_cons, List.map_cons]
    rw [readConcreteFrom_token]
    rw [readConcreteFrom_rewritePieces version _ pieces final]

theorem tokenizationFrom_offset_nil {version : Version} {offset offset' : Nat} {input : Chars}
    (h : Tokenization.From version offset input []) : Tokenization.From version offset' input [] :=
    by
  cases h with
  | done hw => exact .done hw

/-- The characters of a command rewritten are read as the same command, ending with its last
token. -/
theorem segment_rewrite {version : Version} {offset : Nat} {segment : Chars}
    {tokens : List Token} {command : Tree.Command}
    (h₁ : Tokenization.Exactly version offset segment tokens)
    (h₂ : IsCommand version (tokens.map (SyntaxToken.ofToken version)) command) (out : Nat) :
    Tokenization.Exactly version out
      (printConcrete ⟨rewritePieces version out (readConcreteFrom offset segment tokens).pieces,
        (readConcreteFrom offset segment tokens).final⟩)
      ((rewritePieces version out (readConcreteFrom offset segment tokens).pieces).map
        Prod.snd) ∧
    IsCommand version (((rewritePieces version out
      (readConcreteFrom offset segment tokens).pieces).map Prod.snd).map
        (SyntaxToken.ofToken version)) command := by
  have hfinal := readConcreteFrom_final_nil h₁.1 h₁.2
  have hne : (readConcreteFrom offset segment tokens).pieces ≠ [] := by
    intro he
    have ht := readConcreteFrom_tokens offset segment tokens
    simp only [Concrete.tokens, he, List.map_nil] at ht
    obtain ⟨_, hl, -⟩ := h₁.2
    rw [← ht] at hl
    simp at hl
  refine ⟨⟨rewrite_tokenization h₁.1 out, ?_⟩, ⟨h₂.1, ?_⟩⟩
  · rw [hfinal]
    exact rewritePieces_end version out _ hne
  · rw [List.map_map, rewritePieces_ofToken, ← command_tokens_pieces h₂]

/-- A reproduced file is a file with the same commands, which reproduces as itself. -/
theorem reproduce_reading {version : Version} {offset : Nat} {input : Chars}
    {commands : List Tree.Command} {segments : List (Version × Concrete)} {final : Chars}
    (h : FileReadingFrom version offset input commands segments final) (out : Nat) :
    ∃ segments', FileReadingFrom version out
        (reproduce version commands (segments.map Prod.snd) final) commands segments' final ∧
      reproduce version commands (segments'.map Prod.snd) final =
        reproduce version commands (segments.map Prod.snd) final := by
  induction h generalizing out with
  | done h => exact ⟨[], .done (tokenizationFrom_offset_nil h), rfl⟩
  | @command version offset segment tokens command next rest commands segments final
      h₁ h₂ h₃ _ ih =>
    obtain ⟨ht, hc⟩ := segment_rewrite h₁ h₂ out
    have hw := writeSegment_eq (command := command) version offset _
      (readConcreteFrom offset segment tokens).final
      (command_tokens_pieces (offset := offset) (segment := segment) h₂)
    rw [printConcrete_rewritePieces_offset version offset out] at hw
    obtain ⟨segments', hr, he⟩ := ih (out + (printConcrete ⟨rewritePieces version out
      (readConcreteFrom offset segment tokens).pieces,
      (readConcreteFrom offset segment tokens).final⟩).length)
    refine ⟨(version, ⟨rewritePieces version out (readConcreteFrom offset segment tokens).pieces,
      (readConcreteFrom offset segment tokens).final⟩) :: segments', ?_, ?_⟩
    · have := FileReadingFrom.command ht hc h₃ hr
      rw [readConcreteFrom_rewritePieces] at this
      simpa only [List.map_cons, reproduce, nextVersion_read h₃, hw] using this
    · simp only [List.map_cons, reproduce, nextVersion_read h₃, he, hw]
      rw [writeSegment_eq (command := command) version out _ _
        (by rw [rewritePieces_ofToken]
            exact command_tokens_pieces (offset := offset) (segment := segment) h₂),
        rewritePieces_rewritePieces]
  | @stop version offset segment tokens command rest h₁ h₂ h₃ =>
    obtain ⟨ht, hc⟩ := segment_rewrite h₁ h₂ out
    have hw := writeSegment_eq (command := command) version offset _
      (readConcreteFrom offset segment tokens).final
      (command_tokens_pieces (offset := offset) (segment := segment) h₂)
    rw [printConcrete_rewritePieces_offset version offset out] at hw
    refine ⟨[(version, ⟨rewritePieces version out (readConcreteFrom offset segment tokens).pieces,
      (readConcreteFrom offset segment tokens).final⟩)], ?_, ?_⟩
    · have := FileReadingFrom.stop (rest := rest) ht hc h₃
      rw [readConcreteFrom_rewritePieces] at this
      simpa only [List.map_cons, List.map_nil, reproduce, hw] using this
    · simp only [List.map_cons, List.map_nil, reproduce, hw]
      rw [writeSegment_eq (command := command) version out _ _
        (by rw [rewritePieces_ofToken]
            exact command_tokens_pieces (offset := offset) (segment := segment) h₂),
        rewritePieces_rewritePieces]

/-- What `FileReadingFrom` holds of an input, taken apart. -/
theorem fileReadingFrom_inv {version : Version} {offset : Nat} {input : Chars}
    {commands : List Tree.Command} {segments : List (Version × Concrete)} {final : Chars}
    (h : FileReadingFrom version offset input commands segments final) :
    (commands = [] ∧ segments = [] ∧ final = input ∧ Tokenization.From version offset input []) ∨
    (∃ segment rest tokens command commands' segments' next, input = segment ++ rest ∧
      Tokenization.Exactly version offset segment tokens ∧
      IsCommand version (tokens.map (SyntaxToken.ofToken version)) command ∧
      command.modeAfter version = some (.read next) ∧
      FileReadingFrom next (offset + segment.length) rest commands' segments' final ∧
      commands = command :: commands' ∧
      segments = (version, readConcreteFrom offset segment tokens) :: segments') ∨
    (∃ segment tokens command, input = segment ++ final ∧
      Tokenization.Exactly version offset segment tokens ∧
      IsCommand version (tokens.map (SyntaxToken.ofToken version)) command ∧
      command.modeAfter version = some .unparsed ∧ commands = [command] ∧
      segments = [(version, readConcreteFrom offset segment tokens)]) := by
  cases h with
  | done h => exact .inl ⟨rfl, rfl, rfl, h⟩
  | command h₁ h₂ h₃ h₄ => exact .inr (.inl ⟨_, _, _, _, _, _, _, rfl, h₁, h₂, h₃, h₄, rfl, rfl⟩)
  | stop h₁ h₂ h₃ => exact .inr (.inr ⟨_, _, _, rfl, h₁, h₂, h₃, rfl, rfl⟩)

/-- A file has at most one reading. -/
theorem fileReadingFrom_unique {version : Version} {offset : Nat} {input : Chars}
    {commands commands' : List Tree.Command} {segments segments' : List (Version × Concrete)}
    {final final' : Chars}
    (h : FileReadingFrom version offset input commands segments final)
    (h' : FileReadingFrom version offset input commands' segments' final') :
    segments = segments' ∧ final = final' := by
  induction h generalizing commands' segments' final' with
  | done hdone =>
    rcases fileReadingFrom_inv h' with ⟨-, rfl, rfl, -⟩ |
      ⟨_, _, _, _, _, _, _, rfl, h₁, h₂, -⟩ | ⟨_, _, _, rfl, h₁, h₂, -⟩
    · exact ⟨rfl, rfl⟩
    · exact (not_command_of_done h₁ h₂ hdone).elim
    · exact (not_command_of_done h₁ h₂ hdone).elim
  | command h₁ h₂ h₃ _ ih =>
    rcases fileReadingFrom_inv h' with ⟨-, -, -, hdone⟩ |
      ⟨_, _, _, _, _, _, _, heq, h₁', h₂', h₃', h₄', -, rfl⟩ |
      ⟨_, _, _, heq, h₁', h₂', h₃', -, rfl⟩
    · exact (not_command_of_done h₁ h₂ hdone).elim
    · obtain ⟨rfl, rfl, rfl⟩ := segment_eq h₁ h₂ h₁' h₂' heq
      obtain rfl := tokenizationFrom_unique h₁.1 h₁'.1
      rw [h₃] at h₃'
      cases h₃'
      obtain ⟨rfl, rfl⟩ := ih h₄'
      exact ⟨rfl, rfl⟩
    · obtain ⟨rfl, rfl, rfl⟩ := segment_eq h₁ h₂ h₁' h₂' heq
      rw [h₃] at h₃'
      cases h₃'
  | stop h₁ h₂ h₃ =>
    rcases fileReadingFrom_inv h' with ⟨-, -, -, hdone⟩ |
      ⟨_, _, _, _, _, _, _, heq, h₁', h₂', h₃', -, -, rfl⟩ |
      ⟨_, _, _, heq, h₁', h₂', -, -, rfl⟩
    · exact (not_command_of_done h₁ h₂ hdone).elim
    · obtain ⟨rfl, rfl, rfl⟩ := segment_eq h₁ h₂ h₁' h₂' heq
      rw [h₃] at h₃'
      cases h₃'
    · obtain ⟨rfl, rfl, rfl⟩ := segment_eq h₁ h₂ h₁' h₂' heq
      obtain rfl := tokenizationFrom_unique h₁.1 h₁'.1
      exact ⟨rfl, rfl⟩

end BSmtLibSpec.Facts.Proofs.Grammar.RoundTrip
