module

public import BSmtLibSpec.Facts.Proofs.Reader.Files

@[expose] public section

/-!
# The commands a lexer has handed over

The converse of `command_block`: tokens that a correct lexer has handed over after a block, and
that stand for the tokens of a command, are the tokens of characters that follow the block and
that are the command, read in the version (`command_of_handed`). A start of a tokenisation that
ends with a `)` is the tokenisation of the characters up to that `)` (`tokenizationFrom_split`).

Not trusted: everything here is proved.
-/

namespace BSmtLibSpec.Facts.Proofs.Reader.Commands

open BSmtLibSpec.Lexicon BSmtLibSpec.Lexer BSmtLibSpec.Grammar
open BSmtLibSpec.Grammar.Syntax
open BSmtLibSpec.Regex (Chars)
open BSmtLibSpec.Parser
open BSmtLibSpec.Parser.Properties
open BSmtLibSpec.Facts.Proofs.Lexer.StreamingFacts BSmtLibSpec.Facts.Proofs.Grammar.Files
open BSmtLibSpec.Facts.Proofs.Lexicon.Compose BSmtLibSpec.Facts.Proofs.Lexicon.Lemmas
open BSmtLibSpec.Facts.Proofs.Lexicon.Unique BSmtLibSpec.Facts.Proofs.Reader.Consumer
open BSmtLibSpec.Facts.Proofs.Reader.Files BSmtLibSpec.Facts.Proofs.Reader.Lexing

/-- The end of the input after nothing. -/
theorem whitespaceAtEnd_nil : whitespaceAtEnd [] := ⟨[], [], by simp, whitespace_nil, Or.inl rfl⟩

/-- The tokens of a tokenisation up to a `)` are the tokenisation of the characters up to the end
of that `)`, and the tokens after it that of the characters after it. -/
theorem tokenizationFrom_split {version : Version} :
    ∀ {offset : Nat} {input : Chars} {first : List Token} {rest : List Token} {stop : Nat},
      Tokenization.From version offset input (first ++ rest) → EndsWithClose first stop →
      offset ≤ stop ∧ stop ≤ offset + input.length ∧
        Tokenization.From version offset (input.take (stop - offset)) first ∧
        Tokenization.From version stop (input.drop (stop - offset)) rest := by
  intro offset input first
  induction first generalizing offset input with
  | nil => intro rest stop _ hc; obtain ⟨_, h, -⟩ := hc; simp at h
  | cons token first ih =>
    intro rest stop h hc
    rcases tokenizationFrom_inv h with ⟨he, -⟩ | ⟨w, category, s, more, ts, rfl, hw, hs, hd, hmore,
        he⟩
    · simp at he
    · simp only [List.cons_append, List.cons.injEq] at he
      obtain ⟨rfl, rfl⟩ := he
      cases first with
      | nil =>
        obtain ⟨last, hlast, hcat, hend⟩ := hc
        simp only [List.getLast?_singleton, Option.some.injEq] at hlast
        subst hlast
        simp only at hcat hend
        subst hcat
        simp only [List.nil_append] at hmore
        have e₁ : (w ++ s ++ more).take (stop - offset) = w ++ s := by
          rw [List.take_left' (by simp; omega)]
        have e₂ : (w ++ s ++ more).drop (stop - offset) = more := by
          rw [List.drop_left' (by simp; omega)]
        refine ⟨by omega, by simp; omega, ?_, ?_⟩
        · rw [e₁]
          simpa using Tokenization.From.token (rest := []) hw hs (Or.inr (Or.inl rfl))
            (.done whitespaceAtEnd_nil)
        · rw [e₂, ← hend]; simpa [Nat.add_assoc] using hmore
      | cons token' first =>
        have hc' : EndsWithClose (token' :: first) stop := by
          obtain ⟨last, hlast, hcat, hend⟩ := hc
          exact ⟨last, by simpa [List.getLast?_cons_cons] using hlast, hcat, hend⟩
        obtain ⟨h₁, h₂, h₃, h₄⟩ := ih hmore hc'
        have e₁ : (w ++ s ++ more).take (stop - offset) =
            w ++ s ++ more.take (stop - (offset + w.length + s.length)) := by
          rw [take_append_ge (by simp; omega)]
          congr 2
          simp only [List.length_append]
          omega
        have e₂ : (w ++ s ++ more).drop (stop - offset) =
            more.drop (stop - (offset + w.length + s.length)) := by
          rw [List.drop_append, List.drop_eq_nil_of_le (by simp; omega), List.nil_append]
          congr 1
          simp only [List.length_append]
          omega
        refine ⟨by omega, by simp; omega, ?_, ?_⟩
        · rw [e₁]
          exact .token hw hs (delimited_take _ hd) h₃
        · rw [e₂]; exact h₄

/-- The tokens of a readout are lexical tokens. -/
theorem readout_regex {version : Version} {input : Chars} {tokens : List Token}
    (h : Readout version input tokens) :
    ∀ token ∈ tokens, categoryRegex version token.category token.text := by
  obtain ⟨other, all, _, hall, hp, -, -⟩ := h
  intro token ht
  obtain ⟨more, rfl⟩ := hp
  exact (tokenizationFrom_mem hall token (by simp [ht])).1

theorem map_token_inj : ∀ {a b : List SyntaxToken},
    a.map Traversal.Received.token = b.map Traversal.Received.token → a = b
  | [], [], _ => rfl
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h
  | x :: a, y :: b, h => by
    simp only [List.map_cons, List.cons.injEq, Traversal.Received.token.injEq] at h
    rw [h.1, map_token_inj h.2]

/-- A token stands for `)` only if it is one. -/
theorem category_of_ofToken {version : Version} {token : Token}
    (h : SyntaxToken.ofToken version token = .parenClose) : token.category = .parenClose := by
  obtain ⟨category, offset, text⟩ := token
  cases category <;> simp_all [SyntaxToken.ofToken]

/-! ## Going back through a run -/

section

variable {feed : Version → List Chars → Bool → Fed} {consumer : Consumer} {start : Version}
  {input : Chars} {ended : Bool} {version : Version} {failed : Bool}
  {session : Session consumer.Result consumer.Error}

/-- The tokens a consumer has taken start those it takes in the end. -/
theorem runs_prefix {feed : Version → List Chars → Bool → Fed} {consumer : Consumer}
    {start : Version} {input : Chars} {ended : Bool} {version : Version} {ready : List Handed}
    {failed : Bool} {taken : List Handed} {session : Session consumer.Result consumer.Error}
    (h : Runs feed consumer start input ended version ready failed taken session) :
    taken <+: session.taken := by
  induction h with
  | continues _ _ _ _ ih => exact (List.prefix_append _ _).trans ih
  | _ => simp only [settle]; split <;> simp

/-- With no token ready, the consumer takes nothing more. -/
theorem runs_nil {taken : List Handed}
    (h : Runs feed consumer start input ended version [] failed taken session) :
    session.taken = taken := by
  cases h <;> simp only [settle] <;> split <;> rfl

/-- The consumer takes the token ready next, if it takes any. -/
theorem runs_head {token : Handed} {ready taken : List Handed}
    (h : Runs feed consumer start input ended version (token :: ready) failed taken session) :
    taken ++ [token] <+: session.taken := by
  cases h with
  | continues _ _ _ h' => exact runs_prefix h'
  | _ => simp only [settle]; split <;> simp

/-- A consumer that continues at the token ready next, asking for no discarding, goes on after
it. -/
theorem runs_continue_inv {token : Handed} {ready taken : List Handed}
    (h : Runs feed consumer start input ended version (token :: ready) failed taken session)
    (htype : token.type ≠ .endOfFile) (hans : consumer.answer (taken ++ [token]) = .continue)
    (hdisc : consumer.discards (taken ++ [token]) = false) :
    Runs feed consumer start input ended
      ((consumer.switchTo (taken ++ [token])).getD version)
      (following feed consumer.concrete input ended token.«end».offset
        (consumer.switchTo (taken ++ [token])) ready failed).handed
      (following feed consumer.concrete input ended token.«end».offset
        (consumer.switchTo (taken ++ [token])) ready failed).failed
      (taken ++ [token]) session := by
  cases h with
  | continues _ _ _ h' => exact h'
  | fails h' => rw [hans] at h'; cases h'
  | ends h' => exact absurd h' htype
  | breaks _ h' => rw [hans] at h'; cases h'
  | discardsHeld _ h' => rw [hans] at h'; cases h'
  | discardsEnds _ h' => rw [hans] at h'; cases h'
  | discardsWaiting _ _ h' => rw [hdisc] at h'; cases h'
  | discardsToEnd _ _ h' => rw [hdisc] at h'; cases h'
  | discardsFailsAtEnd _ _ h' => rw [hdisc] at h'; cases h'

/-- A consumer that continues on the tokens it takes, asking for nothing, takes the tokens ready
as they come. -/
theorem runs_walk : ∀ (count : Nat) (taken ready rest : List Handed),
    Runs feed consumer start input ended version ready failed taken session →
    session.taken = taken ++ rest →
    (∀ i, 1 ≤ i → i ≤ count →
      consumer.answer (taken ++ rest.take i) = .continue ∧
        consumer.discards (taken ++ rest.take i) = false ∧
        consumer.switchTo (taken ++ rest.take i) = none) →
    (∀ token ∈ rest.take count, token.type ≠ .endOfFile) →
    count ≤ rest.length →
    ready.take count = rest.take count ∧
      Runs feed consumer start input ended version (ready.drop count) failed
        (taken ++ rest.take count) session
  | 0, taken, ready, rest, h, _, _, _, _ => by simpa using h
  | count + 1, taken, ready, rest, h, hs, hsteps, htype, hlen => by
    cases ready with
    | nil =>
      have h0 := congrArg List.length (runs_nil h)
      rw [hs] at h0
      simp only [List.length_append] at h0
      omega
    | cons token ready =>
      obtain ⟨more, hmore⟩ := runs_head h
      rw [hs, List.append_assoc] at hmore
      have hrest : rest = token :: more := by simpa using hmore.symm
      subst hrest
      obtain ⟨hans, hdisc, hsw⟩ := hsteps 1 (Nat.le_refl 1) (by omega)
      simp only [List.take_succ_cons, List.take_zero] at hans hdisc hsw
      have h' := runs_continue_inv h (htype token (by simp)) hans hdisc
      rw [hsw] at h'
      simp only [Option.getD_none, following] at h'
      obtain ⟨h₁, h₂⟩ := runs_walk count (taken ++ [token]) ready more h'
        (by rw [hs]; simp)
        (fun i h₁ h₂ => by simpa using hsteps (i + 1) (by omega) (by omega))
        (fun t ht => htype t (by
          simp only [List.take_succ_cons, List.mem_cons]; exact Or.inr ht))
        (by simp at hlen; omega)
      refine ⟨by simp [h₁], ?_⟩
      simpa using h₂

/-- A consumer that continues on the tokens of a command but the last, asking for nothing,
takes the command's tokens as they are ready, and the last one is ready after the others. -/
theorem runs_command {count : Nat} {taken ready rest : List Handed} (hc : 1 ≤ count)
    (hlen : count ≤ rest.length)
    (h : Runs feed consumer start input ended version ready failed taken session)
    (hs : session.taken = taken ++ rest)
    (hsteps : ∀ i, 1 ≤ i → i < count →
      consumer.answer (taken ++ rest.take i) = .continue ∧
        consumer.discards (taken ++ rest.take i) = false ∧
        consumer.switchTo (taken ++ rest.take i) = none)
    (htype : ∀ token ∈ rest.take count, token.type ≠ .endOfFile) :
    ready.take count = rest.take count ∧ ∃ last more, ready.drop (count - 1) = last :: more ∧
      rest.take count = rest.take (count - 1) ++ [last] ∧
      Runs feed consumer start input ended version (last :: more) failed
        (taken ++ rest.take (count - 1)) session := by
  obtain ⟨h₁, h₂⟩ := runs_walk (count - 1) taken ready rest h hs
    (fun i hi₁ hi₂ => hsteps i hi₁ (by omega))
    (fun t ht => htype t (List.take_subset_take_left _ (by omega) ht)) (by omega)
  cases hd : ready.drop (count - 1) with
  | nil =>
    rw [hd] at h₂
    have h0 := congrArg List.length (runs_nil h₂)
    rw [hs] at h0
    simp only [List.length_append, List.length_take] at h0
    omega
  | cons last more =>
    rw [hd] at h₂
    obtain ⟨more', hmore⟩ := runs_head h₂
    rw [hs, List.append_assoc, List.append_assoc] at hmore
    have hrest : rest = rest.take (count - 1) ++ last :: more' := by
      simpa using hmore.symm
    have htk : rest.take count = rest.take (count - 1) ++ [last] := by
      have hP : (rest.take (count - 1)).length = count - 1 := by
        rw [List.length_take]; omega
      have e : rest.take count = (rest.take (count - 1) ++ last :: more').take count := by
        conv => lhs; rw [hrest]
      generalize rest.take (count - 1) = first at e hP ⊢
      rw [e, List.take_append, List.take_of_length_le (by omega), hP,
        show count - (count - 1) = 1 by omega]
      simp
    refine ⟨?_, last, more, rfl, htk, h₂⟩
    rw [show count = (count - 1) + 1 by omega, List.take_add, h₁, hd,
      show count - 1 + 1 = count by omega, htk]
    simp

end

variable {lexing : Lexing} {parser : RecordingParser} {item : Handed → parser.Item}

/-- What the tokens handed over from a readout stand for. -/
theorem stood_blockHanded (hI : StandsFor parser item) {version : Version} {input : Chars}
    {offset : Nat} {tokens : List Token} (hread : Readout version (input.drop offset) tokens)
    {rel : List Token} (hrel : ∀ token ∈ rel, token ∈ tokens) :
    stood parser item (blockHanded version input offset rel) =
      rel.map fun token => .token (SyntaxToken.ofToken version token) := by
  simp only [stood, blockHanded, List.map_map]
  refine List.map_congr_left fun token ht => ?_
  have hreg := readout_regex hread token (hrel token ht)
  exact hI _ _ version (received_after (input.take offset) _ ▸
    (received_handed hreg (input.drop offset)).1) (received_handed hreg (input.drop offset)).2

/-- The end of the file stands for the end of the input. -/
theorem stands_endOfFile (hI : StandsFor parser item) {handed : Handed}
    (h : handed.type = .endOfFile) : parser.stands (item handed) = .endOfInput :=
  hI _ _ .v2_7 (by simp [Handed.received, h]) trivial

/--
Tokens that a correct lexer has handed over after a block, reading from `offset` on, and that
stand for the tokens of a valid command, are the tokens of characters that follow the
block and are the command; the block grows by them.
-/
theorem command_of_handed (hI : StandsFor parser item) {version : Version} {input : Chars}
    {offset stop : Nat} {block tokens : List Token} {command : Tree.Command}
    {handed : List Handed}
    (hread : Readout version (input.drop offset) tokens)
    (hfed : (lexing.fed version [input.drop offset] true).handed =
        tokens.map (·.handed version (input.drop offset)) ∨
      (Tokenization version (input.drop offset) tokens ∧
        (lexing.fed version [input.drop offset] true).handed =
          tokens.map (·.handed version (input.drop offset)) ++ [endOfFile (input.drop offset)]))
    (hblockEq : block = tokens.take block.length) (hos : offset ≤ stop)
    (hle : stop ≤ input.length)
    (hclosed : stop = offset ∧ block = [] ∨ EndsWithClose block (stop - offset))
    (htoks : ((BSmtLibSpec.Lexer.segment lexing.fed version input true offset).handed.drop
      block.length).take command.tokens.length = handed)
    (hstood : stood parser item handed = command.tokens.map .token)
    (hv : command.Valid version) :
    ∃ segment rel, input.drop stop = segment ++ input.drop (stop + segment.length) ∧
      Tokenization.Exactly version stop segment (rel.map (Token.moveBy offset)) ∧
      IsCommand version ((rel.map (Token.moveBy offset)).map (SyntaxToken.ofToken version))
        command ∧
      handed = blockHanded version input offset rel ∧
      tokens.take (block.length + rel.length) = block ++ rel ∧
      Tokenization version ((input.drop offset).take (stop + segment.length - offset))
        (block ++ rel) ∧
      EndsWithClose (block ++ rel) (stop + segment.length - offset) ∧
      handed.getLast?.map (·.«end».offset) = some (stop + segment.length) ∧
      stop + segment.length ≤ input.length := by
  have hk : handed.length = command.tokens.length := by
    simpa [stood] using congrArg List.length hstood
  have hk₁ : 1 ≤ command.tokens.length :=
    List.length_pos_iff.mpr (tokens_ne_nil command)
  have hseg : (BSmtLibSpec.Lexer.segment lexing.fed version input true offset).handed =
      blockHanded version input offset tokens ∨
      (Tokenization version (input.drop offset) tokens ∧
        (BSmtLibSpec.Lexer.segment lexing.fed version input true offset).handed =
          blockHanded version input offset tokens ++
            [(endOfFile (input.drop offset)).after (input.take offset)]) := by
    rcases hfed with h | ⟨ht, h⟩
    · left; simp [BSmtLibSpec.Lexer.segment, h, blockHanded, Function.comp_def]
    · right; exact ⟨ht, by simp [BSmtLibSpec.Lexer.segment, h, blockHanded, Function.comp_def]⟩
  -- the command's tokens are tokens of the readout
  have hfit : block.length + command.tokens.length ≤ tokens.length := by
    refine Nat.le_of_not_lt fun hlt => ?_
    have hbl : (blockHanded version input offset tokens).length = tokens.length := by
      simp [blockHanded]
    rcases hseg with h | ⟨-, h⟩
    · rw [h] at htoks
      have := congrArg List.length htoks
      simp [hbl] at this
      omega
    · rw [h] at htoks
      by_cases hm : block.length ≤ tokens.length
      · rw [List.drop_append_of_le_length (by omega), List.take_of_length_le (by simp; omega)]
          at htoks
        have hmem : (endOfFile (input.drop offset)).after (input.take offset) ∈ handed := by
          rw [← htoks]; simp
        have hst := stands_endOfFile hI (handed := (endOfFile (input.drop offset)).after
          (input.take offset)) rfl
        have : Traversal.Received.endOfInput ∈ stood parser item handed := by
          rw [← hst]; exact List.mem_map_of_mem hmem
        rw [hstood] at this
        simp at this
      · have := congrArg List.length htoks
        simp at this
        omega
  let rel := (tokens.drop block.length).take command.tokens.length
  have hrelLen : rel.length = command.tokens.length := by simp [rel]; omega
  have hrelMem : ∀ token ∈ rel, token ∈ tokens :=
    fun token ht => List.mem_of_mem_drop (List.mem_of_mem_take ht)
  have hhanded : handed = blockHanded version input offset rel := by
    rw [← htoks]
    have hwithin : ((blockHanded version input offset tokens).drop block.length).take
        command.tokens.length = blockHanded version input offset rel := by
      simp [blockHanded, rel, List.map_drop, List.map_take]
    rcases hseg with h | ⟨-, h⟩
    · rw [h, hwithin]
    · rw [h, List.drop_append_of_le_length (by simp [blockHanded]; omega),
        List.take_append_of_le_length (by simp [blockHanded]; omega), hwithin]
  have hrelTokens : rel.map (SyntaxToken.ofToken version) = command.tokens := by
    apply map_token_inj
    rw [← hstood, hhanded, stood_blockHanded hI hread hrelMem, List.map_map]
    rfl
  have htake : tokens.take (block.length + rel.length) = block ++ rel := by
    rw [List.take_add, ← hblockEq, hrelLen]
  -- the last token is the command's `)`
  have hrelNe : rel ≠ [] := List.ne_nil_of_length_pos (by omega)
  have hlastRel := List.getLast?_eq_some_getLast hrelNe
  generalize rel.getLast hrelNe = last at hlastRel
  have hlastClose : last.category = .parenClose := by
    apply category_of_ofToken (version := version)
    have h₁ := command_getLast command
    rw [← hrelTokens, List.getLast?_map, hlastRel] at h₁
    simpa using h₁
  let stop' := last.offset + last.text.length
  have hcloseAll : EndsWithClose (block ++ rel) stop' :=
    endsWithClose_append ⟨last, hlastRel, hlastClose, rfl⟩
  -- the block with the command is the tokenisation of the characters up to the `)`
  obtain ⟨other, all, n, hall, hp, hagree, hwithin⟩ := hread
  have hp' : block ++ rel <+: all := by
    rw [← htake]; exact (List.take_prefix _ _).trans hp
  obtain ⟨restAll, hrestAll⟩ := hp'
  rw [← hrestAll] at hall
  obtain ⟨-, hstopOther, hcut, -⟩ := tokenizationFrom_split hall hcloseAll
  have hlastMem : last ∈ tokens := hrelMem last (List.mem_of_getLast? hlastRel)
  have hn : stop' ≤ n := hwithin last hlastMem
  have hZ : (input.drop offset).take stop' = other.take stop' := by
    have := congrArg (List.take stop') hagree
    simpa [List.take_take, Nat.min_eq_left hn] using this
  have hcut' : Tokenization version ((input.drop offset).take stop') (block ++ rel) := by
    rw [hZ]; exact hcut
  have hstopLen : stop' ≤ (input.drop offset).length := by
    have := congrArg List.length hZ
    simp only [List.length_take] at this
    omega
  -- the command's characters, after the block
  have hcmd : stop - offset ≤ stop' ∧ Tokenization.From version (stop - offset)
      (((input.drop offset).take stop').drop (stop - offset)) rel := by
    rcases hclosed with ⟨he, hb⟩ | hc
    · subst hb
      refine ⟨by omega, ?_⟩
      rw [show stop - offset = 0 by omega, List.drop_zero]
      simpa [Tokenization] using hcut'
    · obtain ⟨-, h₂, -, h₄⟩ := tokenizationFrom_split hcut' hc
      refine ⟨?_, h₄⟩
      simp only [List.length_take] at h₂
      omega
  obtain ⟨hstopLe, hcmdTok⟩ := hcmd
  let segment := ((input.drop offset).take stop').drop (stop - offset)
  have hsegLen : segment.length = stop' - (stop - offset) := by
    have := hstopLen
    simp only [segment, List.length_drop, List.length_take] at this ⊢
    omega
  have hend : stop + segment.length = offset + stop' := by
    rw [hsegLen]; omega
  refine ⟨segment, rel, ?_, ⟨?_, ?_⟩, ⟨hv, ?_⟩, hhanded, htake, ?_, ?_, ?_, ?_⟩
  · rw [hend]
    have e₁ : input.drop stop = (input.drop offset).drop (stop - offset) := by
      rw [List.drop_drop]; congr 1; omega
    have e₂ : input.drop (offset + stop') = (input.drop offset).drop stop' := by
      rw [List.drop_drop]
    rw [e₁, e₂]
    conv => lhs; rw [← List.take_append_drop stop' (input.drop offset)]
    rw [List.drop_append_of_le_length (by simp; omega)]
  · have := tokenizationFrom_moveBy hcmdTok offset
    rwa [show stop - offset + offset = stop by omega] at this
  · refine ⟨last.moveBy offset, by simp [List.getLast?_map, hlastRel], ?_⟩
    simp only [Token.moveBy]
    omega
  · rw [List.map_map]
    rw [← hrelTokens]
    exact List.map_congr_left fun token _ => ofToken_moveBy version offset token
  · rw [show stop + segment.length - offset = stop' by omega]; exact hcut'
  · rw [show stop + segment.length - offset = stop' by omega]; exact hcloseAll
  · rw [hhanded]
    simp only [blockHanded, List.getLast?_map, hlastRel, Option.map_some, end_offset_after,
      end_offset_handed, List.length_take]
    congr 1
    omega
  · have := hstopLen
    simp only [List.length_drop] at this
    omega

end BSmtLibSpec.Facts.Proofs.Reader.Commands
