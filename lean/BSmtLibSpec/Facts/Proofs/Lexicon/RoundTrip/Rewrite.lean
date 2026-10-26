module

public import BSmtLibSpec.Facts.Proofs.Lexicon.RoundTrip.Lexical

@[expose] public section

/-!
# Writing the tokens of a concrete reading back

A concrete reading keeps the gaps of an input and its tokens. Rewriting it (`rewrite`) keeps the
gaps and writes each token as the syntax token it stands for (`lexForm`), so that only what a
token stands for decides how it is written. The rewritten input:
- has a tokenisation that stands for the same syntax tokens (`rewrite_tokenization`,
  `rewritePieces_ofToken`);
- stays as it is when rewritten again (`rewritePieces_rewritePieces`);
- is the input but for 2.0 string literals written differently with the same content
  (`printConcrete_rewritePieces_similar`), and exactly the input when every token is written
  back as itself (`printConcrete_rewritePieces_eq`).

Not trusted: everything here is proved.
-/

namespace BSmtLibSpec.Facts.Proofs.Lexicon.RoundTrip.Rewrite

open BSmtLibSpec.Lexicon BSmtLibSpec.Grammar
open BSmtLibSpec.Regex (Chars chars)
open BSmtLibSpec.Facts.Proofs.Lexicon.RoundTrip.Lexical
open BSmtLibSpec.Facts.Proofs.Lexicon.RoundTrip.Tokens BSmtLibSpec.Facts.Proofs.Lexicon.Unique

/-- The category and characters the token is written back as: those of what it stands for. -/
def rewriteForm (version : Version) (token : Token) : Category × Chars :=
  lexForm version (SyntaxToken.ofToken version token)

/-- The pieces of a concrete reading whose first character is at `offset`, each token written
back, at the offset where it then stands. -/
def rewritePieces (version : Version) : Nat → List (Gap × Token) → List (Gap × Token)
  | _, [] => []
  | offset, (gap, token) :: pieces =>
    (gap, ⟨(rewriteForm version token).1, offset + gap.length, (rewriteForm version token).2⟩) ::
      rewritePieces version (offset + gap.length + (rewriteForm version token).2.length) pieces

/-- A concrete reading whose first character is at `offset`, its tokens written back. -/
def rewrite (version : Version) (offset : Nat) (concrete : Concrete) : Concrete :=
  ⟨rewritePieces version offset concrete.pieces, concrete.final⟩

/-! ## The first character -/

/-- A token is written back starting with the character it starts with. -/
theorem rewriteForm_head {version : Version} {token : Token}
    (h : categoryRegex version token.category token.text) :
    (rewriteForm version token).2.head? = token.text.head? := by
  obtain ⟨category, offset, text⟩ := token
  cases category with
  | string =>
    by_cases hv : version = .v2_0
    · subst hv
      obtain ⟨b, rfl, -⟩ := string20_inv (by simpa [categoryRegex] using h)
      simp [rewriteForm, lexForm, SyntaxToken.ofToken]
    · obtain ⟨b, rfl, -⟩ := string_inv (by simpa [categoryRegex, hv] using h)
      simp [rewriteForm, lexForm, SyntaxToken.ofToken]
  | quotedSymbol =>
    obtain ⟨b, rfl, -⟩ := quotedSymbol_inv h
    simp [rewriteForm, lexForm, SyntaxToken.ofToken, symbolForm]
  | hexadecimal =>
    obtain ⟨t, rfl, -⟩ := hexadecimal_inv h
    simp [rewriteForm, lexForm, SyntaxToken.ofToken, chars_hex]
  | binary =>
    obtain ⟨t, rfl, -⟩ := binary_inv h
    simp [rewriteForm, lexForm, SyntaxToken.ofToken, chars_bin]
  | keyword =>
    obtain ⟨t, rfl, -⟩ := keyword_inv h
    simp [rewriteForm, lexForm, SyntaxToken.ofToken]
  | parenOpen =>
    have h' : text = chars "(" := h
    simp [rewriteForm, lexForm, SyntaxToken.ofToken, h']
  | parenClose =>
    have h' : text = chars ")" := h
    simp [rewriteForm, lexForm, SyntaxToken.ofToken, h']
  | simpleSymbol => simp [rewriteForm, lexForm, SyntaxToken.ofToken, symbolForm, Token.content]
  | numeral => rfl
  | decimal => rfl
  | reserved => rfl

/-- Delimitation looks only at the first character after a token. -/
theorem delimited_of_head {category : Category} {rest rest' : Chars}
    (h : Tokenization.Delimited category rest) (he : rest'.head? = rest.head?) :
    Tokenization.Delimited category rest' := by
  rcases h with h | h | rfl | ⟨c, more, rfl, hc⟩
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · cases rest' with
    | nil => exact Or.inr (Or.inr (Or.inl rfl))
    | cons => simp at he
  · cases rest' with
    | nil => simp at he
    | cons c' more' =>
      simp only [List.head?_cons, Option.some.injEq] at he
      subst he
      exact Or.inr (Or.inr (Or.inr ⟨c', more', rfl, hc⟩))

/-! ## The rewritten input -/

theorem readConcreteFrom_token {offset : Nat} {w s rest : Chars} {category : Category}
    {tokens : List Token} :
    readConcreteFrom offset (w ++ s ++ rest) (⟨category, offset + w.length, s⟩ :: tokens) =
      ⟨(w, ⟨category, offset + w.length, s⟩) ::
        (readConcreteFrom (offset + w.length + s.length) rest tokens).pieces,
        (readConcreteFrom (offset + w.length + s.length) rest tokens).final⟩ := by
  have hbefore : offset + w.length - offset = w.length := by omega
  have hdrop : (w ++ s ++ rest).drop (w.length + s.length) = rest := by
    rw [List.append_assoc, ← List.drop_drop, List.drop_left, List.drop_left]
  have htake : (w ++ s ++ rest).take w.length = w := by
    rw [List.append_assoc, List.take_left]
  simp only [readConcreteFrom, hbefore, hdrop, htake, Nat.add_assoc]

/-- The rewritten input starts with the character the input starts with. -/
theorem rewrite_head {version : Version} {offset : Nat} {input : Chars} {tokens : List Token}
    (h : Tokenization.From version offset input tokens) (out : Nat) :
    (printConcrete (rewrite version out (readConcreteFrom offset input tokens))).head? =
      input.head? := by
  cases h with
  | done => simp [readConcreteFrom, rewrite, rewritePieces, printConcrete]
  | @token w category s rest _ _ _ hs _ _ =>
    rw [readConcreteFrom_token]
    simp only [rewrite, rewritePieces, printConcrete_cons]
    obtain ⟨c, t, rfl, -, -⟩ := token_shape hs
    have hh := rewriteForm_head (version := version) (token := ⟨category, offset + w.length,
      c :: t⟩) hs
    cases w with
    | cons => simp
    | nil =>
      obtain ⟨c', t', he⟩ : ∃ c' t', (rewriteForm version ⟨category, offset, c :: t⟩).2 =
          c' :: t' := by
        cases hr : (rewriteForm version ⟨category, offset, c :: t⟩).2 with
        | nil => simp [hr] at hh
        | cons c' t' => exact ⟨c', t', rfl⟩
      simp only [List.length_nil, Nat.add_zero] at hh ⊢
      rw [he] at hh ⊢
      simp_all

/-- The rewritten input has a tokenisation: the tokens written back, where they then stand. -/
theorem rewrite_tokenization {version : Version} {offset : Nat} {input : Chars}
    {tokens : List Token} (h : Tokenization.From version offset input tokens) (out : Nat) :
    Tokenization.From version out
      (printConcrete (rewrite version out (readConcreteFrom offset input tokens)))
      (rewrite version out (readConcreteFrom offset input tokens)).tokens := by
  induction h generalizing out with
  | done hw =>
    simpa [readConcreteFrom, rewrite, rewritePieces, printConcrete, Concrete.tokens] using
      Tokenization.From.done hw
  | @token w category s rest offset tokens hw hs hd hrest ih =>
    rw [readConcreteFrom_token]
    simp only [rewrite, rewritePieces, printConcrete_cons, Concrete.tokens, List.map_cons]
    have ih' := ih (out + w.length +
      (rewriteForm version ⟨category, offset + w.length, s⟩).2.length)
    simp only [rewrite, Concrete.tokens] at ih'
    refine Tokenization.From.token hw (lexForm_regex hs) ?_ ih'
    have hhead := rewrite_head hrest
      (out + w.length + (rewriteForm version ⟨category, offset + w.length, s⟩).2.length)
    simp only [rewrite] at hhead
    rcases hd with hc | hc | hr | hr
    · subst hc
      exact Or.inl (by simp [rewriteForm, lexForm, SyntaxToken.ofToken])
    · subst hc
      exact Or.inr (Or.inl (by simp [rewriteForm, lexForm, SyntaxToken.ofToken]))
    · exact delimited_of_head (Or.inr (Or.inr (Or.inl hr))) hhead
    · exact delimited_of_head (Or.inr (Or.inr (Or.inr hr))) hhead

/-! ## What the rewriting keeps -/

theorem rewritePieces_gaps (version : Version) :
    ∀ (offset : Nat) (pieces : List (Gap × Token)),
      (rewritePieces version offset pieces).map Prod.fst = pieces.map Prod.fst
  | _, [] => rfl
  | offset, (gap, token) :: pieces => by
    simp [rewritePieces, rewritePieces_gaps version _ pieces]

/-- A syntax token written as a token, at any offset, stands for itself. -/
theorem ofToken_lexForm (version : Version) (token : SyntaxToken) (offset : Nat) :
    SyntaxToken.ofToken version ⟨(lexForm version token).1, offset, (lexForm version token).2⟩ =
      token := by
  have := ofToken_offset version (lexToken version token) offset
  rw [ofToken_lexToken] at this
  exact this

/-- Written back, a token stands for what it stood for. -/
theorem rewritePieces_ofToken (version : Version) :
    ∀ (offset : Nat) (pieces : List (Gap × Token)),
      (rewritePieces version offset pieces).map (SyntaxToken.ofToken version ∘ Prod.snd) =
        pieces.map (SyntaxToken.ofToken version ∘ Prod.snd)
  | _, [] => rfl
  | offset, (gap, token) :: pieces => by
    simp only [rewritePieces, List.map_cons, Function.comp, rewriteForm, ofToken_lexForm]
    exact congrArg _ (rewritePieces_ofToken version _ pieces)

/-- Written back twice, the tokens are as written back once. -/
theorem rewritePieces_rewritePieces (version : Version) :
    ∀ (offset offset' : Nat) (pieces : List (Gap × Token)),
      rewritePieces version offset (rewritePieces version offset' pieces) =
        rewritePieces version offset pieces
  | _, _, [] => rfl
  | offset, offset', (gap, token) :: pieces => by
    have h : rewriteForm version ⟨(rewriteForm version token).1, offset' + gap.length,
        (rewriteForm version token).2⟩ = rewriteForm version token := by
      simp only [rewriteForm, ofToken_lexForm]
    simp only [rewritePieces, h, rewritePieces_rewritePieces version _ _ pieces]

/-- When every token is written back as itself, the rewriting writes the input back. -/
theorem printConcrete_rewritePieces_eq (version : Version) :
    ∀ (offset : Nat) (pieces : List (Gap × Token)) (final : Gap),
      (∀ piece ∈ pieces, (rewriteForm version piece.2).2 = piece.2.text) →
      printConcrete ⟨rewritePieces version offset pieces, final⟩ = printConcrete ⟨pieces, final⟩
  | _, [], _, _ => rfl
  | offset, (gap, token) :: pieces, final, h => by
    have h0 := h (gap, token) (by simp)
    rw [rewritePieces, printConcrete_cons, printConcrete_cons]
    dsimp only at h0 ⊢
    rw [h0, printConcrete_rewritePieces_eq version _ pieces final
      (fun piece hp => h piece (by simp [hp]))]

/-! ## Written differently, standing for the same -/

/-- Two 2.0 string literals that stand for the same content. -/
def StringSpelling20 (a b : Chars) : Prop :=
  string20 a ∧ string20 b ∧ unescape20 ((a.drop 1).dropLast) = unescape20 ((b.drop 1).dropLast)

/-- Two inputs are equal but for the spelling of 2.0 string literals that stand for the same
content: they are made of the same parts, but for parts that are 2.0 string literals standing for
the same content. -/
def SameButStrings20 (a b : Chars) : Prop :=
  ∃ parts : List (Chars × Chars), a = (parts.map Prod.fst).flatten ∧
    b = (parts.map Prod.snd).flatten ∧
      ∀ part ∈ parts, part.1 = part.2 ∨ StringSpelling20 part.1 part.2

theorem SameButStrings20.refl (a : Chars) : SameButStrings20 a a :=
  ⟨[(a, a)], by simp, by simp, by simp⟩

theorem SameButStrings20.append {a b c d : Chars} (h₁ : SameButStrings20 a b)
    (h₂ : SameButStrings20 c d) : SameButStrings20 (a ++ c) (b ++ d) := by
  obtain ⟨p₁, rfl, rfl, h₁⟩ := h₁
  obtain ⟨p₂, rfl, rfl, h₂⟩ := h₂
  refine ⟨p₁ ++ p₂, by simp, by simp, fun part hp => ?_⟩
  rcases List.mem_append.mp hp with hp | hp
  · exact h₁ part hp
  · exact h₂ part hp

theorem SameButStrings20.of_part {a b : Chars} (h : a = b ∨ StringSpelling20 a b) :
    SameButStrings20 a b :=
  ⟨[(a, b)], by simp, by simp, by simpa using h⟩

/-- A token is written back as itself, or, a 2.0 string literal, as one standing for the same
content. -/
theorem rewriteForm_similar {version : Version} {token : Token}
    (h : categoryRegex version token.category token.text) :
    (rewriteForm version token).2 = token.text ∨
      StringSpelling20 (rewriteForm version token).2 token.text := by
  by_cases hs : version = .v2_0 ∧ token.category = .string
  · obtain ⟨rfl, hc⟩ := hs
    obtain ⟨category, offset, text⟩ := token
    simp only at hc
    subst hc
    have h' : string20 text := by simpa [categoryRegex] using h
    have hr := lexForm_regex (version := .v2_0) (token := ⟨.string, offset, text⟩) h
    right
    refine ⟨by simpa [categoryRegex, SyntaxToken.ofToken, lexForm, rewriteForm] using hr, h', ?_⟩
    simp [rewriteForm, SyntaxToken.ofToken, lexForm, Token.content, unescape20_escape]
  · left
    have hl : NoLoneBackslash version [token] := by
      intro hv t ht hcat
      simp only [List.mem_singleton] at ht
      subst ht
      exact absurd ⟨hv, hcat⟩ hs
    have := lexForm_ofToken h hl
    simp only [rewriteForm, this, form]

/-- The rewritten reading is the reading but for the spelling of 2.0 string literals. -/
theorem printConcrete_rewritePieces_similar (version : Version) :
    ∀ (offset : Nat) (pieces : List (Gap × Token)) (final : Gap),
      (∀ piece ∈ pieces, categoryRegex version piece.2.category piece.2.text) →
      SameButStrings20 (printConcrete ⟨rewritePieces version offset pieces, final⟩)
        (printConcrete ⟨pieces, final⟩)
  | _, [], final, _ => SameButStrings20.refl _
  | offset, (gap, token) :: pieces, final, h => by
    rw [rewritePieces, printConcrete_cons, printConcrete_cons]
    exact ((SameButStrings20.refl gap).append (SameButStrings20.of_part
      (rewriteForm_similar (h (gap, token) (by simp))))).append
      (printConcrete_rewritePieces_similar version _ pieces final
        (fun piece hp => h piece (by simp [hp])))

/-! ## Inputs that end with their last token -/

/-- The concrete reading of an input that ends with its last token has nothing after it. -/
theorem readConcreteFrom_final_nil {version : Version} {offset : Nat} {input : Chars}
    {tokens : List Token} (h : Tokenization.From version offset input tokens)
    (hend : ∃ last, tokens.getLast? = some last ∧
      last.offset + last.text.length = offset + input.length) :
    (readConcreteFrom offset input tokens).final = [] := by
  induction h with
  | done => obtain ⟨_, h, -⟩ := hend; simp at h
  | @token w category s rest offset tokens hw hs hd hrest ih =>
    rw [readConcreteFrom_token]
    obtain ⟨last, hlast, hendl⟩ := hend
    cases tokens with
    | nil =>
      simp only [List.getLast?_singleton, Option.some.injEq] at hlast
      subst hlast
      simp only [List.length_append] at hendl
      have hr : rest = [] := List.eq_nil_of_length_eq_zero (by omega)
      subst hr
      simp [readConcreteFrom]
    | cons t ts =>
      refine ih ⟨last, by simpa [List.getLast?_cons_cons] using hlast, ?_⟩
      simp only [List.length_append] at hendl
      omega

/-- The last token written back ends where the rewritten pieces end. -/
theorem rewritePieces_end (version : Version) :
    ∀ (offset : Nat) (pieces : List (Gap × Token)), pieces ≠ [] →
      ∃ last, ((rewritePieces version offset pieces).map Prod.snd).getLast? = some last ∧
        last.offset + last.text.length =
          offset + (printConcrete ⟨rewritePieces version offset pieces, []⟩).length
  | _, [], h => absurd rfl h
  | offset, [(gap, token)], _ => by
    simp [rewritePieces, printConcrete, Nat.add_assoc]
  | offset, (gap, token) :: p :: pieces, _ => by
    obtain ⟨last, hlast, hend⟩ := rewritePieces_end version
      (offset + gap.length + (rewriteForm version token).2.length) (p :: pieces) (by simp)
    refine ⟨last, ?_, ?_⟩
    · rw [rewritePieces, List.map_cons, List.getLast?_cons]
      simp only [hlast]
      cases hp : rewritePieces version (offset + gap.length + (rewriteForm version token).2.length)
        (p :: pieces) with
      | nil => simp [rewritePieces] at hp
      | cons => rfl
    · rw [rewritePieces, printConcrete_cons, hend]
      simp [Nat.add_assoc]

end BSmtLibSpec.Facts.Proofs.Lexicon.RoundTrip.Rewrite
