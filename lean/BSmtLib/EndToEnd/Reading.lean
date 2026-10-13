import BSmtLib.EndToEnd.Outcome

/-!
# Reading the characters of the commands a correct lexer handed over

The converse of `Feed`: where a correct lexer, read from an offset in a version, hands over tokens
that stand for the tokens of commands, the characters from that offset start with those commands,
each the whitespace before it and its tokens, as a file reads them (`Spec.Grammar.FileFrom`).

A tokenisation is split after each command's `)` (`tokenizationFrom_split_close`), which needs no
delimiter, so the characters before it are a tokenisation of their own that ends with the `)`
(`TokenizationExactly`).
-/

namespace BSmtLib.EndToEnd

open BSmtLib.Spec BSmtLib.Spec.Lexicon BSmtLib.Spec.Grammar BSmtLib.Spec.Lexer
open BSmtLib.ParserProofs.Rejection (rcv)
open BSmtLib.Spec.Parser.Traversal (Received)

/-! ## Splitting a tokenisation after a `)` -/

theorem ofToken_moveBy (version : Lexicon.Version) (k : Nat) (token : Lexicon.Token) :
    SyntaxToken.ofToken version (token.moveBy k) = SyntaxToken.ofToken version token := by
  obtain ⟨c, o, t⟩ := token
  cases c <;> rfl

theorem category_of_parenClose {version : Lexicon.Version} {token : Lexicon.Token}
    (h : SyntaxToken.ofToken version token = .parenClose) : token.category = .parenClose := by
  obtain ⟨c, o, t⟩ := token
  cases c <;> first | rfl | simp [SyntaxToken.ofToken] at h

/-- A tokenisation whose tokens start with tokens that end with a `)` is split after it: the
characters up to the `)` are tokenised by those tokens, ending with it, and the rest by the
rest. -/
theorem tokenizationFrom_split_close {version : Lexicon.Version} :
    ∀ {A : List Lexicon.Token} {o : Nat} {S : Chars} {B : List Lexicon.Token}
      {last : Lexicon.Token}, TokenizationFrom version o S (A ++ B) → A.getLast? = some last →
      last.category = .parenClose →
      ∃ S₁ S₂, S = S₁ ++ S₂ ∧ TokenizationExactly version o S₁ A ∧
        TokenizationFrom version (o + S₁.length) S₂ B
  | [], _, _, _, _, _, hlast, _ => by simp at hlast
  | a :: A, o, S, B, last, h, hlast, hcat => by
    rcases SpecChecks.Lexicon.tokenizationFrom_inv h with ⟨he, -⟩ |
      ⟨w, category, s, rest, ts, rfl, hw, hs, hd, hrest, he⟩
    · simp at he
    · simp only [List.cons_append, List.cons.injEq] at he
      obtain ⟨rfl, rfl⟩ := he
      cases A with
      | nil =>
        simp only [List.getLast?_singleton, Option.some.injEq] at hlast
        subst hlast
        refine ⟨w ++ s, rest, by simp, ⟨?_, _, rfl, by simp; omega⟩, ?_⟩
        · have := TokenizationFrom.token (version := version) (offset := o) (rest := [])
            (tokens := []) hw hs (Or.inr (Or.inl hcat))
            (.done ⟨[], [], rfl, SpecChecks.Lexicon.whitespace_nil, Or.inl rfl⟩)
          simpa using this
        · simpa [Nat.add_assoc] using hrest
      | cons a' A' =>
        have hlast' : (a' :: A').getLast? = some last := by
          simpa [List.getLast?_cons_cons] using hlast
        obtain ⟨S₁, S₂, rfl, ⟨hte, l, hl, hend⟩, hS₂⟩ :=
          tokenizationFrom_split_close (A := a' :: A') hrest hlast' hcat
        have hne : S₁ ≠ [] := SpecChecks.Lexicon.tokenizationFrom_ne_nil hte (by simp)
        have hd' : Delimited category S₁ := by
          have := SpecChecks.Lexer.delimited_take S₁.length hd
          simpa using this
        refine ⟨w ++ s ++ S₁, S₂, by simp, ⟨.token hw hs hd' hte, l, ?_, ?_⟩, ?_⟩
        · rw [List.getLast?_cons_cons]; exact hl
        · simp only [List.length_append] at hend ⊢; omega
        · simpa [Nat.add_assoc] using hS₂

/-! ## The characters of commands -/

/-- Commands of the version that keep it, whose tokens a tokenisation starts with: the
characters start with them, as a file reads them. -/
theorem file_of_tokens {version : Lexicon.Version} :
    ∀ (commands : List Tree.Command) {o : Nat} {S : Chars} {A more : List Lexicon.Token},
      TokenizationFrom version o S (A ++ more) →
      A.map (SyntaxToken.ofToken version) = commands.flatMap Tree.Command.tokens →
      (∀ c ∈ commands, c.Valid version ∧ c.modeAfter version = some (.read version)) →
      ∃ S₁ S₂, S = S₁ ++ S₂ ∧ TokenizationFrom version (o + S₁.length) S₂ more ∧
        (∀ t ∈ A, t.offset + t.text.length ≤ o + S₁.length) ∧
        ∀ rest cs, FileFrom version (o + S₁.length) rest cs →
          FileFrom version o (S₁ ++ rest) (commands ++ cs)
  | [], o, S, A, more, h, hmap, _ => by
    have hA : A = [] := by simpa using hmap
    subst hA
    exact ⟨[], S, rfl, by simpa using h, by simp, fun rest cs hf => by simpa using hf⟩
  | c :: commands, o, S, A, more, h, hmap, hvalid => by
    rw [List.flatMap_cons] at hmap
    obtain ⟨A₁, A₂, rfl, h₁, h₂⟩ := List.map_eq_append_iff.mp hmap
    have hne : A₁ ≠ [] := by
      rintro rfl
      have := tokens_length_pos c
      rw [← h₁] at this
      simp at this
    obtain ⟨last, hlast⟩ := Option.isSome_iff_exists.mp (List.getLast?_isSome.mpr hne)
    have hcat : last.category = .parenClose := by
      have hc := command_tokens_last c
      rw [← h₁, List.getLast?_map, hlast] at hc
      simp only [Option.map_some, Option.some.injEq] at hc
      exact category_of_parenClose hc
    rw [List.append_assoc] at h
    obtain ⟨Sa, Sb, rfl, hte, hb⟩ := tokenizationFrom_split_close h hlast hcat
    obtain ⟨Sc, Sd, rfl, hd, hwithin, hcont⟩ := file_of_tokens commands hb h₂
      (fun c' hc' => hvalid c' (by simp [hc']))
    refine ⟨Sa ++ Sc, Sd, by simp, by simpa [Nat.add_assoc] using hd, ?_, ?_⟩
    · intro t ht
      rcases List.mem_append.mp ht with ht | ht
      · have := tokenizationFrom_within hte.1 t ht
        simp only [List.length_append]; omega
      · have := hwithin t ht
        simp only [List.length_append]; omega
    · intro rest cs hf
      have hf' := hcont rest cs (by simpa [Nat.add_assoc] using hf)
      have := FileFrom.command hte ⟨(hvalid c (by simp)).1, h₁.symm⟩ (hvalid c (by simp)).2 hf'
      simpa using this

/-! ## What a correct lexer hands over from an offset -/

variable {feed : Lexicon.Version → List Lexicon.Chars → Bool → Fed}

theorem handed_type_ne (version : Lexicon.Version) (input : Chars) (token : Lexicon.Token) :
    (token.handed version input).type ≠ .endOfFile := by
  obtain ⟨c, o, t⟩ := token
  cases c <;> simp [Lexicon.Token.handed, Category.type]

/-- What a correct lexer hands over from an offset within the input, read on its own after the
end of the input, in a version: tokens that start a tokenisation of an input that starts with a
start of the characters from the offset, each within that start, located in the whole input; and
the end-of-file token after them where those characters have a tokenisation, which the tokens
are. -/
theorem segment_structure (hc : Correct feed) (version : Lexicon.Version) {input : Chars}
    {offset : Nat} (hoff : offset ≤ input.length) :
    ∃ L E s ext all, (segment feed version input true offset).handed =
        L.map (fun token => (token.moveBy offset).handed version input) ++ E ∧
      s <+: input.drop offset ∧ Tokenization version (s ++ ext) all ∧ L <+: all ∧
      (∀ t ∈ L, t.offset + t.text.length ≤ s.length) ∧
      (E = [] ∨ (E = [endOfFile input] ∧ s = input.drop offset ∧ ext = [] ∧ all = L)) := by
  have hf : [input.drop offset].flatten = input.drop offset := by simp
  have hB : (input.take offset).length = offset := by simp; omega
  have hinput : input.take offset ++ input.drop offset = input := List.take_append_drop _ _
  have hafter : ∀ (s : Chars) (token : Lexicon.Token), s <+: input.drop offset →
      token.offset + token.text.length ≤ s.length →
      (token.handed version (input.drop offset)).after (input.take offset) =
        (token.moveBy offset).handed version input := by
    intro s token hs hin
    rw [handed_after (input.take offset) (input.drop offset) (input.drop offset) token
      (List.prefix_refl _) (by have := hs.length_le; omega), hB, hinput]
  by_cases hcomp : Complete version [input.drop offset].flatten true
  · obtain ⟨t, ht, e⟩ := SpecChecks.Lexer.handsOverAll_of_correct hc hcomp
    rw [hf] at ht e
    refine ⟨t, [endOfFile input], input.drop offset, [], t, ?_, List.prefix_refl _,
      by simpa using ht, List.prefix_refl _, ?_, Or.inr ⟨rfl, rfl, rfl, rfl⟩⟩
    · simp only [segment, e, List.map_append, List.map_map, List.map_cons, List.map_nil]
      congr 1
      · refine List.map_congr_left fun token htoken => ?_
        exact hafter _ token (List.prefix_refl _)
          (by have := tokenizationFrom_within ht token htoken; omega)
      · rw [endOfFile_after, hinput]
    · intro token htoken
      have := tokenizationFrom_within ht token htoken
      omega
  · obtain ⟨s, hs⟩ := SpecChecks.Lexer.exists_longestViableStart version
      [input.drop offset].flatten
    obtain ⟨t, hmax, e⟩ := SpecChecks.Lexer.handsOverMaximal_of_correct hc hcomp s hs
    rw [hf] at e hs
    have hv := hs.2.1
    obtain ⟨ext, all, hall⟩ := hv
    have hwithin := SpecChecks.Lexer.handoverReady_within hs.2.1 hmax.1
    refine ⟨t, [], s, ext, all, ?_, hs.1, hall,
      SpecChecks.Lexicon.determined_prefix hmax.1.1 hall, hwithin, Or.inl rfl⟩
    simp only [segment, e, List.map_map, List.append_nil]
    refine List.map_congr_left fun token htoken => ?_
    exact hafter s token hs.1 (hwithin token htoken)

/-- A handed token of a tokenisation, moved, stands for its syntax token. -/
theorem rcv_itemOf_moved {version : Lexicon.Version} (input : Chars) (offset : Nat)
    {token : Lexicon.Token} (hcat : categoryRegex version token.category token.text) :
    rcv (itemOf ((token.moveBy offset).handed version input)) =
      .token (SyntaxToken.ofToken version token) := by
  rw [rcv_itemOf_handed input (token := token.moveBy offset) hcat, ofToken_moveBy]

theorem map_token_injective : ∀ {xs ys : List Grammar.SyntaxToken},
    xs.map Received.token = ys.map Received.token → xs = ys
  | [], [], _ => rfl
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h
  | x :: xs, y :: ys, h => by
    simp only [List.map_cons, List.cons.injEq, Received.token.injEq] at h
    rw [h.1, map_token_injective h.2]

/-- Handed tokens without the end-of-file token at the start of what a correct lexer hands over
from an offset, standing for the tokens of commands of the version, the last of which may change
the mode: the characters from the offset start with those commands, up to the end of the last
handed token, as a file reads them. -/
theorem reading_split (hc : Correct feed) {version : Lexicon.Version} {input : Chars}
    {offset : Nat} (hoff : offset ≤ input.length) {Y : List Handed}
    (hY : Y <+: (segment feed version input true offset).handed)
    (htypes : ∀ h ∈ Y, h.type ≠ .endOfFile)
    {commands : List Tree.Command} {last : Tree.Command}
    (hitems : Y.map (rcv ∘ itemOf) =
      ((commands ++ [last]).flatMap Tree.Command.tokens).map .token)
    (hvalid : ∀ c ∈ commands, c.Valid version ∧ c.modeAfter version = some (.read version))
    (hlast : last.Valid version) :
    ∃ S₁ D₂, input.drop offset = S₁ ++ D₂ ∧
      Y.getLast?.map (·.«end».offset) = some (offset + S₁.length) ∧
      (∀ next cs, last.modeAfter version = some (.read next) →
        FileFrom next (offset + S₁.length) D₂ cs →
        FileFrom version offset (input.drop offset) (commands ++ last :: cs)) ∧
      (last.modeAfter version = some .unparsed →
        FileFrom version offset (input.drop offset) (commands ++ [last])) := by
  obtain ⟨L, E, s, ext, all, hseg, hs, hall, hLall, hwithin, hE⟩ :=
    segment_structure hc version hoff (feed := feed)
  rw [hseg] at hY
  -- `Y` is handed tokens of `L`
  have hYL : Y = (L.take Y.length).map fun token => (token.moveBy offset).handed version input := by
    by_cases hle : Y.length ≤ L.length
    · have := List.prefix_iff_eq_take.mp hY
      rw [this, List.take_append_of_le_length (by simpa using hle), List.map_take]
      simp
    · exfalso
      rcases hE with rfl | ⟨rfl, -⟩
      · have := hY.length_le
        simp at this
        omega
      · obtain ⟨Z, hZ⟩ := hY
        have hlt : L.length < Y.length := by omega
        have hget : Y[L.length]? = some (endOfFile input) := by
          have h1 := congrArg (·[L.length]?) hZ
          rw [List.getElem?_append_left hlt] at h1
          rw [h1, List.getElem?_append_right (by simp)]
          simp
        exact htypes _ (List.mem_of_getElem? hget) rfl
  obtain ⟨n, hn⟩ : ∃ n, Y.length = n := ⟨_, rfl⟩
  rw [hn] at hYL
  have hcats : ∀ t ∈ all, categoryRegex version t.category t.text := fun t ht =>
    (SpecChecks.Lexer.tokenizationFrom_mem hall t ht).1
  have hmapL : (L.take n).map (SyntaxToken.ofToken version) =
      (commands ++ [last]).flatMap Tree.Command.tokens := by
    apply map_token_injective
    rw [← hitems, hYL, List.map_map, List.map_map]
    refine List.map_congr_left fun token htoken => ?_
    simp only [Function.comp_apply]
    exact (rcv_itemOf_moved input offset (hcats token
      (hLall.subset (List.take_subset _ _ htoken)))).symm
  -- the moved tokens tokenise the characters from the offset
  obtain ⟨more, hmore⟩ := (List.take_prefix n L).trans hLall
  have hmoved := SpecChecks.Lexicon.tokenizationFrom_moveBy hall offset
  rw [Nat.zero_add, ← hmore, List.map_append] at hmoved
  obtain ⟨A, hA⟩ : ∃ A, A = (L.take n).map (Lexicon.Token.moveBy offset) := ⟨_, rfl⟩
  rw [← hA] at hmoved
  have hAmap : A.map (SyntaxToken.ofToken version) =
      commands.flatMap Tree.Command.tokens ++ last.tokens := by
    rw [hA, List.map_map]
    rw [show (SyntaxToken.ofToken version ∘ Lexicon.Token.moveBy offset) =
      SyntaxToken.ofToken version from funext (ofToken_moveBy version offset), hmapL]
    simp
  obtain ⟨A₁, A₂, hA12, h₁, h₂⟩ := List.map_eq_append_iff.mp hAmap
  rw [hA12, List.append_assoc] at hmoved
  obtain ⟨Sa, Sb, hSab, hb, hwa, hconta⟩ := file_of_tokens commands hmoved h₁ hvalid
  have hne : A₂ ≠ [] := by
    rintro rfl
    have := tokens_length_pos last
    rw [← h₂] at this
    simp at this
  obtain ⟨lt, hlt⟩ := Option.isSome_iff_exists.mp (List.getLast?_isSome.mpr hne)
  have hcat : lt.category = .parenClose := by
    have hc' := command_tokens_last last
    rw [← h₂, List.getLast?_map, hlt] at hc'
    simp only [Option.map_some, Option.some.injEq] at hc'
    exact category_of_parenClose hc'
  obtain ⟨Sl, S₃, hSl3, hte, -⟩ := tokenizationFrom_split_close hb hlt hcat
  -- the end of the last token
  have hlastA : A.getLast? = some lt := by
    rw [hA12, List.getLast?_append, hlt]
    rfl
  obtain ⟨-, lt', hlt', hend⟩ := id hte
  rw [hlt] at hlt'
  cases hlt'
  have hlen : (Sa ++ Sl).length ≤ s.length := by
    have hmem : lt ∈ A := List.mem_of_getLast? hlastA
    rw [hA] at hmem
    obtain ⟨t₀, ht₀, rfl⟩ := List.mem_map.mp hmem
    have := hwithin t₀ (List.take_subset _ _ ht₀)
    simp only [Lexicon.Token.moveBy, List.length_append] at hend this ⊢
    omega
  have hSs : s ++ ext = Sa ++ Sl ++ S₃ := by rw [hSab, hSl3, List.append_assoc]
  have hpre : Sa ++ Sl <+: input.drop offset := by
    have : Sa ++ Sl <+: s := by
      have h' := congrArg (List.take (Sa ++ Sl).length) hSs
      rw [List.take_append_of_le_length hlen, List.take_left'] at h'
      · rw [← h']
        exact List.take_prefix _ _
      · rfl
    exact this.trans hs
  obtain ⟨D₂, hD₂⟩ := hpre
  refine ⟨Sa ++ Sl, D₂, by rw [← hD₂], ?_, ?_, ?_⟩
  · -- the last handed token ends where the characters of the commands end
    have hYlast : Y.getLast? = some (lt.handed version input) := by
      rw [hYL, List.getLast?_map]
      have : (L.take n).getLast?.map (Lexicon.Token.moveBy offset) = some lt := by
        rw [← List.getLast?_map, ← hA]
        exact hlastA
      obtain ⟨t₀, ht₀, rfl⟩ := Option.map_eq_some_iff.mp this
      rw [ht₀]
      rfl
    rw [hYlast]
    simp only [Option.map_some, Lexicon.Token.handed, locate, Option.some.injEq]
    simp only [List.length_append] at hend ⊢
    omega
  · intro next cs hm hf
    have hcmd := FileFrom.command (rest := D₂) (commands := cs) hte ⟨hlast, h₂.symm⟩ hm
      (by simpa [Nat.add_assoc] using hf)
    have := hconta (Sl ++ D₂) (last :: cs) hcmd
    rw [← hD₂]
    simpa using this
  · intro hm
    have hcmd := FileFrom.stop (rest := D₂) hte ⟨hlast, h₂.symm⟩ hm
    have := hconta (Sl ++ D₂) [last] hcmd
    rw [← hD₂]
    simpa using this

/-- What a correct lexer hands over from an offset within the input, read on its own after the
end of the input, where the end-of-file token follows handed tokens standing for the tokens of
commands of the version that keep it: the characters from the offset are those commands, as a
file reads them. -/
theorem reading_end (hc : Correct feed) {version : Lexicon.Version} {input : Chars}
    {offset : Nat} (hoff : offset ≤ input.length) {current ready : List Handed} {token : Handed}
    (hseg : (segment feed version input true offset).handed = current ++ token :: ready)
    (htype : token.type = .endOfFile)
    {commands : List Tree.Command}
    (hitems : current.map (rcv ∘ itemOf) = (commands.flatMap Tree.Command.tokens).map .token)
    (hvalid : ∀ c ∈ commands, c.Valid version ∧ c.modeAfter version = some (.read version)) :
    FileFrom version offset (input.drop offset) commands := by
  obtain ⟨L, E, s, ext, all, hseg', hs, hall, hLall, hwithin, hE⟩ :=
    segment_structure hc version hoff (feed := feed)
  rw [hseg'] at hseg
  have hnot : ∀ h ∈ L.map (fun t => (t.moveBy offset).handed version input),
      h.type ≠ .endOfFile := by
    intro h hh
    obtain ⟨t, -, rfl⟩ := List.mem_map.mp hh
    exact handed_type_ne _ _ _
  -- the end-of-file token is the one after the tokens
  have hcurL : current = L.map (fun t => (t.moveBy offset).handed version input) ∧ E ≠ [] := by
    rcases List.append_eq_append_iff.mp hseg with ⟨a', hcur', hE'⟩ | ⟨c', hL', htail⟩
    · rcases hE with rfl | ⟨rfl, -⟩
      · simp at hE'
      · cases a' with
        | nil => simp at hcur'; exact ⟨hcur', by simp⟩
        | cons a as =>
          simp only [List.cons_append, List.cons.injEq] at hE'
          obtain ⟨rfl, he⟩ := hE'
          simp at he
    · cases c' with
      | nil => simp at hL' htail; exact ⟨hL'.symm, by rw [← htail]; simp⟩
      | cons c cs =>
        simp only [List.cons_append, List.cons.injEq] at htail
        obtain ⟨rfl, -⟩ := htail
        exact absurd htype (hnot token (by rw [hL']; simp))
  obtain ⟨hcurL, hEne⟩ := hcurL
  rcases hE with rfl | ⟨rfl, rfl, rfl, hallL⟩
  · exact absurd rfl hEne
  rw [hallL] at hall
  have hcats : ∀ t ∈ L, categoryRegex version t.category t.text := fun t ht =>
    (SpecChecks.Lexer.tokenizationFrom_mem hall t ht).1
  have hmapL : (L.map (Lexicon.Token.moveBy offset)).map (SyntaxToken.ofToken version) =
      commands.flatMap Tree.Command.tokens := by
    apply map_token_injective
    rw [← hitems, hcurL, List.map_map, List.map_map, List.map_map]
    refine List.map_congr_left fun t ht => ?_
    simp only [Function.comp_apply, ofToken_moveBy]
    exact (rcv_itemOf_moved input offset (hcats t ht)).symm
  have hmoved := SpecChecks.Lexicon.tokenizationFrom_moveBy hall offset
  rw [Nat.zero_add, List.append_nil, ← List.append_nil (L.map _)] at hmoved
  obtain ⟨S₁, S₂, hS, hS₂, -, hcont⟩ := file_of_tokens commands hmoved hmapL hvalid
  have := hcont S₂ [] (.done hS₂)
  rw [hS]
  simpa using this

end BSmtLib.EndToEnd
