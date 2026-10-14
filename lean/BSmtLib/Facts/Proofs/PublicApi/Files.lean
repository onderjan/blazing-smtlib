module

public import BSmtLib.Facts.PublicApi.Adapters
public import BSmtLibSpec.Facts

@[expose] public section

/-!
# Files as tokens with layout between them

A file of the specification is its commands' tokens, each as the version in force writes it,
with layout between them: up to the end of its last command, and then either whitespace or the
unread rest after `exit` (`spaced_of_reading`). The tokens are written as in the input but for
the spelling of 2.0 string literals, and exactly on an input without a backslash.

Facts of the specification, in the terms of the theorems of `Facts.PublicApi`.
-/

namespace BSmtLib.Facts.Proofs.PublicApi.Files

open BSmtLibSpec BSmtLibSpec.Lexicon BSmtLibSpec.Grammar
open BSmtLibSpec.Grammar.Syntax BSmtLibSpec.Grammar.File
open BSmtLibSpec.Regex (Chars chars)
open BSmtLibSpec.Facts.Proofs.Grammar.RoundTrip
open BSmtLib.Facts.PublicApi.Adapters BSmtLibSpec.Facts.Proofs.Lexicon.RoundTrip.Lexical
open BSmtLibSpec.Facts.Proofs.Lexicon.RoundTrip.Rewrite
open BSmtLibSpec.Facts.Proofs.Lexicon.RoundTrip.Tokens BSmtLibSpec.Facts.Proofs.Lexicon.Unique

/-! ## Layout -/

/-- Layout followed by layout is layout. -/
theorem layout_append {a b : ByteList} (ha : Layout a) (hb : Layout b) :
    Layout (a ++ b) := by
  induction ha with
  | nil => exact hb
  | space hc _ ih => exact .space hc ih
  | comment hbody _ ih => simpa [List.append_assoc] using Layout.comment hbody ih

/-- A comment's body: no line break. -/
private theorem body_of_star {body : Chars}
    (h : Regex.star (Regex.minus Regex.anyChar lineBreak) body) :
    ∀ c ∈ body, c ≠ 10 ∧ c ≠ 13 := by
  obtain ⟨parts, rfl, hparts⟩ := h
  intro c hc
  obtain ⟨p, hp, hcp⟩ := List.mem_flatten.mp hc
  obtain ⟨hany, hnot⟩ := hparts p hp
  simp only [Regex.anyChar, Regex.range] at hany
  obtain ⟨d, rfl, -⟩ := hany
  simp only [List.mem_singleton] at hcp
  subst hcp
  refine ⟨fun h10 => hnot (Or.inl ⟨c, by simp, by simp [h10]⟩),
    fun h13 => hnot (Or.inr ⟨c, by simp, by simp [h13]⟩)⟩

/-- A white space character or a comment is layout. -/
private theorem layout_of_part {p : Chars} (h : Regex.alt whiteSpaceChar comment p) : Layout p := by
  rcases h with ⟨r, hr, hp⟩ | ⟨semi, rest, rfl, hsemi, body, lb, rfl, hbody, hlb⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;>
      · obtain ⟨c, rfl, h1, h2⟩ := hp
        refine .space ?_ .nil
        have : c.toNat = _ := Nat.le_antisymm h2 h1
        first
          | exact Or.inl (UInt8.toNat_inj.mp this)
          | exact Or.inr (Or.inl (UInt8.toNat_inj.mp this))
          | exact Or.inr (Or.inr (Or.inl (UInt8.toNat_inj.mp this)))
          | exact Or.inr (Or.inr (Or.inr (UInt8.toNat_inj.mp this)))
  · have hs : semi = [59] := hsemi
    subst hs
    have hl : Layout lb := by
      rcases hlb with ⟨c, rfl, h1, h2⟩ | ⟨c, rfl, h1, h2⟩
      · exact .space (Or.inr (Or.inl (UInt8.toNat_inj.mp (Nat.le_antisymm h2 h1)))) .nil
      · exact .space (Or.inr (Or.inr (Or.inl (UInt8.toNat_inj.mp (Nat.le_antisymm h2 h1))))) .nil
    have := Layout.comment (body_of_star hbody) hl
    simpa using this

/-- Whitespace is layout. -/
theorem layout_of_whitespace {w : Chars} (h : whitespace w) : Layout w := by
  obtain ⟨parts, rfl, hparts⟩ := h
  induction parts with
  | nil => exact .nil
  | cons p ps ih =>
    rw [List.flatten_cons]
    exact layout_append (layout_of_part (hparts p (by simp)))
        (ih fun q hq => hparts q (by simp [hq]))

/-- Whitespace at the end of the input is layout. -/
theorem layout_of_whitespaceAtEnd {w : Chars} (h : whitespaceAtEnd w) : Layout w := by
  obtain ⟨a, b, rfl, ha, hb⟩ := h
  refine layout_append (layout_of_whitespace ha) ?_
  rcases hb with hb | ⟨semi, body, rfl, hsemi, hbody⟩
  · have : b = [] := hb
    subst this
    exact .nil
  · have hs : semi = [59] := hsemi
    subst hs
    simpa using Layout.comment (body_of_star hbody) .nil

/-! ## The spelling of a token -/

/-- The unescaping of `Facts.PublicApi` is the specification's. -/
theorem unescape20_eq : ∀ bytes : ByteList, PublicApi.Adapters.unescape20 bytes =
    Lexicon.unescape20 bytes
  | a :: b :: rest => by
    rw [PublicApi.Adapters.unescape20, Lexicon.unescape20]
    split
    · rw [unescape20_eq rest]
    · rw [unescape20_eq (b :: rest)]
  | [] => by simp [PublicApi.Adapters.unescape20, Lexicon.unescape20]
  | [_] => by simp [PublicApi.Adapters.unescape20, Lexicon.unescape20]

/-- A token of the version is spelled as the version writes what it stands for. -/
theorem sameSpelling_token {version : Lexicon.Version} {token : Lexicon.Token}
    (h : categoryRegex version token.category token.text) :
    SameSpelling token.text (lexForm version (Grammar.SyntaxToken.ofToken version token)).2 := by
  rcases rewriteForm_similar h with he | ⟨ha, hb, hu⟩
  · exact .inl (by simpa [rewriteForm] using he.symm)
  · right
    obtain ⟨x, hx, -⟩ := string20_inv ha
    obtain ⟨y, hy, -⟩ := string20_inv hb
    refine ⟨y, x, by simpa using hy, by simpa [rewriteForm] using hx, ?_⟩
    rw [unescape20_eq, unescape20_eq]
    rw [hx, hy] at hu
    simpa using hu.symm

/-- A token of a version other than 2.0 is written as itself. -/
theorem lexForm_token_exact {version : Lexicon.Version} {token : Lexicon.Token}
    (h : categoryRegex version token.category token.text) (hv : version ≠ .v2_0) :
    (lexForm version (Grammar.SyntaxToken.ofToken version token)).2 = token.text := by
  rw [lexForm_ofToken h fun hv' => absurd hv' hv]
  rfl

/-! ## The tokens of commands -/

/-- The tokens of the commands, read from the version, each command's tokens as the version in
force writes them. -/
def tokensOf : Lexicon.Version → List Tree.Command → List ByteList
  | _, [] => []
  | version, command :: commands =>
    command.tokens.map (fun token => (lexForm version token).2) ++
      tokensOf (nextVersion version command) commands

/-- A command after which the input is not read is `exit`. -/
theorem exit_of_unparsed {version : Lexicon.Version} {command : Tree.Command}
    (h : command.modeAfter version = some .unparsed) : command = .exit := by
  cases command with
  | exit => rfl
  | setInfo info =>
    obtain ⟨keyword, value⟩ := info
    simp only [Tree.Command.modeAfter] at h
    split at h <;> (try split at h) <;> simp_all [Option.map_eq_some_iff]
  | _ => simp [Tree.Command.modeAfter] at h

/-- The pieces of a concrete reading are spaced: their gaps are layout, so the reading followed
by spaced tokens is spaced. -/
theorem spaced_pieces {version : Lexicon.Version} {offset : Nat} {segment : Chars}
    {tokens : List Lexicon.Token}
    (h : Tokenization.From version offset segment tokens)
    {written : List ByteList} {rest : ByteList} (hrest : Spaced written rest) :
    Spaced (((readConcreteFrom offset segment tokens).pieces.map (·.2.text)) ++ written)
      (printConcrete ⟨(readConcreteFrom offset segment tokens).pieces, []⟩ ++ rest) := by
  have hgaps := (readConcreteFrom_gaps h).1
  generalize (readConcreteFrom offset segment tokens).pieces = pieces at hgaps
  induction pieces with
  | nil => simpa [printConcrete] using hrest
  | cons piece pieces ih =>
    obtain ⟨gap, token⟩ := piece
    rw [printConcrete_cons, List.map_cons, List.cons_append, List.append_assoc]
    exact .cons (layout_of_whitespace (hgaps _ List.mem_cons_self))
      (ih fun p hp => hgaps p (List.mem_cons_of_mem _ hp))

/-- Same spellings, appended, are same spellings. -/
theorem SameSpellings.append {a b c d : List ByteList} (h₁ : SameSpellings a c)
    (h₂ : SameSpellings b d) : SameSpellings (a ++ b) (c ++ d) := by
  refine ⟨by simp [h₁.1, h₂.1], fun pair hp => ?_⟩
  rw [List.zip_append h₁.1] at hp
  rcases List.mem_append.mp hp with hp | hp
  · exact h₁.2 pair hp
  · exact h₂.2 pair hp

/-- Two lists made from one by two maps with the same spelling at each element have the same
spellings. -/
theorem sameSpellings_map {α : Type} (f g : α → ByteList) :
    ∀ (l : List α), (∀ x ∈ l, SameSpelling (f x) (g x)) → SameSpellings (l.map f) (l.map g)
  | [], _ => ⟨rfl, by simp⟩
  | x :: l, h => by
    have := sameSpellings_map f g l fun y hy => h y (List.mem_cons_of_mem _ hy)
    refine ⟨by simp, fun pair hp => ?_⟩
    simp only [List.map_cons, List.zip_cons_cons, List.mem_cons] at hp
    rcases hp with rfl | hp
    · exact h x List.mem_cons_self
    · exact this.2 pair hp

/-- What a command's characters give: they are the gaps and the tokens of their concrete
reading, the tokens spelled as the version writes the command's tokens, and exactly so without a
backslash. -/
theorem segment_facts {version : Lexicon.Version} {offset : Nat} {segment : Chars}
    {tokens : List Lexicon.Token} {command : Tree.Command}
    (h₁ : Tokenization.Exactly version offset segment tokens)
    (h₂ : IsCommand version (tokens.map (Grammar.SyntaxToken.ofToken version)) command) :
    segment = printConcrete ⟨(readConcreteFrom offset segment tokens).pieces, []⟩ ∧
      SameSpellings ((readConcreteFrom offset segment tokens).pieces.map (·.2.text))
        (command.tokens.map fun token => (lexForm version token).2) ∧
      (version ≠ .v2_0 →
        command.tokens.map (fun token => (lexForm version token).2) =
          (readConcreteFrom offset segment tokens).pieces.map (·.2.text)) := by
  have hseg : segment = printConcrete ⟨(readConcreteFrom offset segment tokens).pieces, []⟩ := by
    have hp : printConcrete ⟨(readConcreteFrom offset segment tokens).pieces,
        (readConcreteFrom offset segment tokens).final⟩ = segment :=
      printConcrete_readConcreteFrom h₁.1
    rw [readConcreteFrom_final_nil h₁.1 h₁.2] at hp
    exact hp.symm
  rw [command_tokens_pieces (offset := offset) (segment := segment) h₂, List.map_map]
  refine ⟨hseg, sameSpellings_map _ _ _ fun p hp =>
    sameSpelling_token (pieces_regex h₁.1 p hp), fun hv => ?_⟩
  exact List.map_congr_left fun p hp => lexForm_token_exact (pieces_regex h₁.1 p hp) hv

/-- The version a command leaves in force is the one it was read in, or the one it declares. -/
theorem next_of_read {version next : Lexicon.Version} {command : Tree.Command}
    (h : command.modeAfter version = some (.read next)) :
    next = version ∨ command.declaredVersion = some next := by
  cases command with
  | setInfo info =>
    obtain ⟨keyword, value⟩ := info
    simp only [Tree.Command.modeAfter, Tree.Command.declaredVersion] at h ⊢
    split at h
    · split at h
      · rename_i decimal _
        right
        simp only [Option.map_eq_some_iff, Mode.read.injEq] at h
        obtain ⟨v, hv, rfl⟩ := h
        simp_all
      · simp at h
    · left
      simp only [Option.some.injEq, Mode.read.injEq] at h
      exact h.symm
  | exit => simp [Tree.Command.modeAfter] at h
  | _ =>
    left
    simp only [Tree.Command.modeAfter, Option.some.injEq, Mode.read.injEq] at h
    exact h.symm

/-- What a reading of a file gives: the input is the part up to its last command's end and what
follows; the part up to the end is the commands' tokens, each spelled as the version in force
writes it or, for a 2.0 string literal, spelled otherwise with the same meaning, and exactly
where no part is read in 2.0, with layout between them; and what follows is layout unless the
last command is `exit`. -/
theorem spaced_of_reading {version : Lexicon.Version} {offset : Nat} {input : Chars}
    {commands : List Tree.Command} {segments : List (Lexicon.Version × Concrete)} {final : Chars}
    (h : FileReadingFrom version offset input commands segments final) :
    ∃ pre written, input = pre ++ final ∧ SameSpellings written (tokensOf version commands) ∧
      (∀ tail, Layout tail → Spaced written (pre ++ tail)) ∧
      (commands.getLast? = some .exit ∨ Layout final) ∧
      (version ≠ .v2_0 → (∀ command ∈ commands, command.declaredVersion ≠ some .v2_0) →
        written = tokensOf version commands) := by
  induction h with
  | done hw =>
    refine ⟨[], [], by simp, ⟨rfl, by simp⟩, fun tail ht => by simpa using Spaced.nil ht,
      .inr (layout_of_whitespaceAtEnd ?_), fun _ _ => rfl⟩
    cases hw with
    | done hw => exact hw
  | @command version offset segment tokens command next rest commands segments final
      h₁ h₂ h₃ _ ih =>
    obtain ⟨pre, written, hpre, hsame, hspaced, hlast, hexact⟩ := ih
    obtain ⟨hseg, htexts, htok⟩ := segment_facts h₁ h₂
    refine ⟨segment ++ pre,
      (readConcreteFrom offset segment tokens).pieces.map (·.2.text) ++ written,
      by rw [hpre, List.append_assoc], ?_, fun tail ht => ?_,
      ?_, fun hv hdecl => ?_⟩
    · rw [tokensOf, nextVersion_read h₃]
      exact SameSpellings.append htexts hsame
    · have := spaced_pieces h₁.1 (hspaced tail ht)
      rwa [← hseg, ← List.append_assoc] at this
    · rcases hlast with hl | hl
      · left
        cases commands with
        | nil => simp at hl
        | cons c cs => simpa [List.getLast?_cons_cons] using hl
      · exact .inr hl
    · have hnext : next ≠ .v2_0 := by
        rcases next_of_read h₃ with rfl | hd
        · exact hv
        · intro hn
          exact hdecl command List.mem_cons_self (hn ▸ hd)
      rw [tokensOf, nextVersion_read h₃,
        hexact hnext fun c hc => hdecl c (List.mem_cons_of_mem _ hc), htok hv]
  | @stop version offset segment tokens command rest h₁ h₂ h₃ =>
    obtain ⟨hseg, htexts, htok⟩ := segment_facts h₁ h₂
    refine ⟨segment, (readConcreteFrom offset segment tokens).pieces.map (·.2.text) ++ [], rfl, ?_,
      fun tail ht => ?_, .inl ?_, fun hv _ => ?_⟩
    · rw [tokensOf, tokensOf]
      exact SameSpellings.append htexts ⟨rfl, by simp⟩
    · have := spaced_pieces h₁.1 (Spaced.nil ht)
      rwa [← hseg] at this
    · simp [exit_of_unparsed h₃]
    · rw [tokensOf, tokensOf, htok hv]

end BSmtLib.Facts.Proofs.PublicApi.Files
