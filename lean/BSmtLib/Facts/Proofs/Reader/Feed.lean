import BSmtLibSpec.Facts.Proofs.Lexer.Consumers
import BSmtLibSpec.Facts.Proofs.Lexer.StreamingFacts
import BSmtLibSpec.Facts.Proofs.Lexicon.Compose
import BSmtLibSpec.Facts.Proofs.Parser.Rebuild

/-!
# What a correct lexer hands over for the commands of a file

A file is read in readings: from where a version is in force, its commands up to the first
version declaration or `exit`, or up to the end of the input (`Group`). What a lexer that is
`BSmtLibSpec.Lexer.Correct` hands over, read from the start of a reading in its version
(`BSmtLibSpec.Lexer.segment`), starts with the tokens of the reading's commands, and if the reading
runs to the end of the input, is those tokens and the end of the input (`segment_group`). A command
ends with a `)`, which needs no delimiter, so its tokens are handed over whole, whatever follows.
-/

namespace BSmtLib.Facts.Proofs.Reader.Feed

open BSmtLibSpec BSmtLibSpec.Lexicon BSmtLibSpec.Grammar BSmtLibSpec.Lexer
open BSmtLibSpec.Grammar.Syntax
open BSmtLibSpec.Regex (Chars)
open BSmtLibSpec.Facts.Proofs.Lexer.Consumers (locate_after)
open BSmtLibSpec.Facts.Proofs.Lexer.StreamingFacts
    (handed_prefix_of_correct handed_prefix_end_of_correct handsOverAll_of_correct
    handsOverMaximal_of_correct exists_longestViableStart viable_of_tokenization locate_append)
open BSmtLibSpec.Facts.Proofs.Lexer.Streaming (handoverMaximal_unique)
open BSmtLibSpec.Facts.Proofs.Lexicon.Compose (close_handoverMaximal tokenizationFrom_close_append
    tokenizationFrom_moveBy_inv)
open BSmtLibSpec.Facts.Proofs.Lexicon.Unique (tokenizationFrom_unique)

variable {feed : Lexicon.Version → List Chars → Bool → Fed}

/-! ## A correct lexer does not tell how its input is cut -/

/-- A correct lexer hands over what the input joined gives, however it is cut. -/
theorem handed_flatten (h : Correct feed) (version : Lexicon.Version) (slices : List Chars)
    (ended : Bool) :
    (feed version slices ended).handed = (feed version [slices.flatten] ended).handed := by
  have hf : [slices.flatten].flatten = slices.flatten := by simp
  by_cases hc : Complete version slices.flatten ended
  · obtain ⟨t₁, h₁, e₁⟩ := handsOverAll_of_correct h hc
    obtain ⟨t₂, h₂, e₂⟩ := handsOverAll_of_correct h (slices := [slices.flatten]) (by rwa [hf])
    rw [hf] at h₂ e₂
    have hc' := hc.1
    subst hc'
    rw [e₁, e₂, tokenizationFrom_unique h₁ h₂]
  · obtain ⟨s, hs⟩ := exists_longestViableStart version slices.flatten
    obtain ⟨t₁, h₁, e₁⟩ := handsOverMaximal_of_correct h hc s hs
    obtain ⟨t₂, h₂, e₂⟩ := handsOverMaximal_of_correct h (slices := [slices.flatten])
      (by rwa [hf]) s (by rwa [hf])
    rw [hf] at e₂
    rw [e₁, e₂, handoverMaximal_unique hs.2.1 h₁ h₂]

/-! ## Characters whose tokenisation ends with a `)` -/

/-- Before the end of the input, a correct lexer fed characters whose tokenisation ends with a
`)` at their end has handed over that tokenisation. -/
theorem handed_close (h : Correct feed) {version : Lexicon.Version} {start : Chars}
    {tokens : List Lexicon.Token} (ht : Tokenization version start tokens)
    (hclose : EndsWithClose tokens start.length) :
    (feed version [start] false).handed = tokens.map (·.handed version start) := by
  have hs : LongestViableStart version start start :=
    ⟨List.prefix_refl start, viable_of_tokenization ht, fun _ hp _ => hp.length_le⟩
  obtain ⟨t, hmax, e⟩ := handsOverMaximal_of_correct h
    (Facts.Proofs.Lexer.StreamingFacts.not_complete_false version [start].flatten) start
    (by simpa using hs)
  have hu := handoverMaximal_unique (viable_of_tokenization ht)
    (show HandoverMaximal version start t by simpa using hmax) (close_handoverMaximal ht hclose)
  rw [e, hu]
  simp

/-- At the end of the input, a correct lexer fed characters followed by more has handed over what
it had handed over on the characters before the end. -/
theorem handed_close_prefix (h : Correct feed) (version : Lexicon.Version) (start more : Chars) :
    (feed version [start] false).handed <+: (feed version [start ++ more] true).handed := by
  have h₁ := handed_prefix_of_correct h version [start] [more]
  have h₂ := handed_prefix_end_of_correct h version ([start] ++ [more])
  rw [handed_flatten h version ([start] ++ [more]) true] at h₂
  simpa using h₁.trans h₂

/-! ## Locating what is read on its own -/

theorem handed_after {version : Lexicon.Version} (before rest start : Chars)
    (token : Lexicon.Token) (hstart : start <+: rest)
    (hin : token.offset + token.text.length ≤ start.length) :
    (token.handed version start).after before =
      (token.moveBy before.length).handed version (before ++ rest) := by
  obtain ⟨more, rfl⟩ := hstart
  have h₁ : locate (start ++ more) token.offset = locate start token.offset :=
    locate_append (by omega)
  have h₂ : locate (start ++ more) (token.offset + token.text.length) =
      locate start (token.offset + token.text.length) := locate_append (by omega)
  have e₁ : locate (before ++ (start ++ more)) (token.offset + before.length) =
      (locate start token.offset).after before := by
    rw [show token.offset + before.length = before.length + token.offset by omega, locate_after,
      h₁]
  have e₂ : locate (before ++ (start ++ more)) (token.offset + before.length + token.text.length)
      = (locate start (token.offset + token.text.length)).after before := by
    rw [show token.offset + before.length + token.text.length =
      before.length + (token.offset + token.text.length) by omega, locate_after, h₂]
  obtain ⟨category, offset, text⟩ := token
  simp only [Lexicon.Token.handed, Handed.after, Lexicon.Token.moveBy] at e₁ e₂ ⊢
  rw [e₁, e₂]
  rfl

theorem endOfFile_after (before rest : Chars) :
    (endOfFile rest).after before = endOfFile (before ++ rest) := by
  simp only [endOfFile, Handed.after, List.length_append]
  rw [locate_after]

/-! ## The readings of a file -/

/--
`Group version offset chars commands tokens eof`: from the offset, read in the version, the
characters start with the commands of one reading, whose tokens are `tokens`: commands that keep
the version, up to and including the first version declaration or `exit`; or up to the end of the
input if none comes (`eof`), where only whitespace follows.
-/
inductive Group (version : Lexicon.Version) :
    Nat → Chars → List Tree.Command → List Lexicon.Token → Bool → Prop
  /-- The end of the input, after whitespace. -/
  | done : Tokenization.From version offset rest [] → Group version offset rest [] [] true
  /-- `exit`: the reading stops. -/
  | stop : Tokenization.Exactly version offset part tokens →
      IsCommand version (tokens.map (SyntaxToken.ofToken version)) command →
      command.modeAfter version = some .unparsed →
      Group version offset (part ++ rest) [command] tokens false
  /-- A version declaration: the next reading starts after it, in its version. -/
  | switch : Tokenization.Exactly version offset part tokens →
      IsCommand version (tokens.map (SyntaxToken.ofToken version)) command →
      command.modeAfter version = some (.read next) → command.declaredVersion = some next →
      File.From next (offset + part.length) rest commands →
      Group version offset (part ++ rest) (command :: commands) tokens false
  /-- A command that keeps the version: the reading goes on after it. -/
  | keep : Tokenization.Exactly version offset part tokens →
      IsCommand version (tokens.map (SyntaxToken.ofToken version)) command →
      command.modeAfter version = some (.read version) → command.declaredVersion = none →
      Group version (offset + part.length) rest commands others eof →
      Group version offset (part ++ rest) (command :: commands) (tokens ++ others) eof

/-- A file starts with a reading. -/
theorem group_of_file {version : Lexicon.Version} {offset : Nat} {chars : Chars}
    {commands : List Tree.Command} (h : File.From version offset chars commands) :
    ∃ tokens eof, Group version offset chars commands tokens eof := by
  induction h with
  | done ht => exact ⟨[], true, .done ht⟩
  | command hte hic hm hrest ih =>
    rcases Facts.Proofs.Parser.Rebuild.modeAfter_read hm with ⟨hd, rfl⟩ | hd
    · obtain ⟨others, eof, hg⟩ := ih
      exact ⟨_, eof, .keep hte hic hm hd hg⟩
    · exact ⟨_, false, .switch hte hic hm hd hrest⟩
  | stop hte hic hm => exact ⟨_, false, .stop hte hic hm⟩

theorem paren_getLast (tokens : List SyntaxToken) : (paren tokens).getLast? = some .parenClose := by
  simp [paren, List.getLast?_cons, List.getLast?_append]

theorem command_tokens_last (command : Tree.Command) :
    command.tokens.getLast? = some .parenClose := by
  cases command <;> simp only [Tree.Command.tokens, commandTokens] <;> exact paren_getLast _

/-- The tokens of a command end with its `)`. -/
theorem close_of_command {version : Lexicon.Version} {offset : Nat} {segment : Chars}
    {tokens : List Lexicon.Token} {command : Tree.Command}
    (hte : Tokenization.Exactly version offset segment tokens)
    (hic : IsCommand version (tokens.map (SyntaxToken.ofToken version)) command) :
    EndsWithClose tokens (offset + segment.length) := by
  obtain ⟨-, last, hlast, hend⟩ := hte
  refine ⟨last, hlast, ?_, hend⟩
  have h := command_tokens_last command
  rw [hic.2, List.getLast?_map, hlast] at h
  simp only [Option.map_some, Option.some.injEq] at h
  obtain ⟨category, offset, text⟩ := last
  cases category <;> simp_all [SyntaxToken.ofToken]

theorem endsWithClose_append {tokens others : List Lexicon.Token} {stop : Nat}
    (h : EndsWithClose others stop) : EndsWithClose (tokens ++ others) stop := by
  obtain ⟨last, hlast, hc, he⟩ := h
  refine ⟨last, ?_, hc, he⟩
  rw [List.getLast?_append, hlast]
  rfl

/-- The tokens of a reading: a tokenisation of all the rest if the reading runs to the end of the
input, and otherwise of a start of the rest, ending with a `)` at its end. -/
theorem group_tokens {version : Lexicon.Version} {offset : Nat} {chars : Chars}
    {commands : List Tree.Command} {tokens : List Lexicon.Token} {eof : Bool}
    (h : Group version offset chars commands tokens eof) :
    (eof = true → Tokenization.From version offset chars tokens) ∧
      (eof = false → ∃ start more, chars = start ++ more ∧
        Tokenization.From version offset start tokens ∧
        EndsWithClose tokens (offset + start.length)) := by
  induction h with
  | done ht => exact ⟨fun _ => ht, fun h => by cases h⟩
  | stop hte hic hm =>
    exact ⟨fun h => (by cases h), fun _ => ⟨_, _, rfl, hte.1, close_of_command hte hic⟩⟩
  | switch hte hic hm hd hrest =>
    exact ⟨fun h => (by cases h), fun _ => ⟨_, _, rfl, hte.1, close_of_command hte hic⟩⟩
  | keep hte hic hm hd hg ih =>
    have hc := close_of_command hte hic
    refine ⟨fun he => tokenizationFrom_close_append hte.1 hc (ih.1 he), fun he => ?_⟩
    obtain ⟨start, more, rfl, ht, hc'⟩ := ih.2 he
    refine ⟨_ ++ start, more, by simp, tokenizationFrom_close_append hte.1 hc ht, ?_⟩
    rw [List.length_append, ← Nat.add_assoc]
    exact endsWithClose_append hc'

/-- The tokens of a tokenisation end within its characters. -/
theorem tokenizationFrom_within {version : Lexicon.Version} {offset : Nat} {chars : Chars}
    {tokens : List Lexicon.Token} (h : Tokenization.From version offset chars tokens) :
    ∀ token ∈ tokens, token.offset + token.text.length ≤ offset + chars.length := by
  induction h with
  | done => simp
  | @token w category s rest offset tokens hw hs hd hrest ih =>
    intro token htoken
    rcases List.mem_cons.mp htoken with rfl | htoken
    · simp; omega
    · have := ih token htoken
      simp only [List.length_append] at this ⊢
      omega

theorem endsWithClose_moveBy {tokens : List Lexicon.Token} {k stop : Nat}
    (h : EndsWithClose (tokens.map (Lexicon.Token.moveBy k)) (k + stop)) :
    EndsWithClose tokens stop := by
  obtain ⟨last, hlast, hc, he⟩ := h
  rw [List.getLast?_map, Option.map_eq_some_iff] at hlast
  obtain ⟨last₀, hlast₀, rfl⟩ := hlast
  refine ⟨last₀, hlast₀, hc, ?_⟩
  simp only [Lexicon.Token.moveBy] at he
  omega

/-- A correct lexer read from the start of a reading, in its version, hands over the reading's
tokens first; if the reading runs to the end of the input, it hands over those tokens and the end
of the input. -/
theorem segment_group (h : Correct feed) {version : Lexicon.Version} {input : Chars}
    {offset : Nat} {commands : List Tree.Command} {tokens : List Lexicon.Token} {eof : Bool}
    (hg : Group version offset (input.drop offset) commands tokens eof)
    (hoff : offset ≤ input.length) :
    ∃ tail, (segment feed version input true offset).handed =
        tokens.map (·.handed version input) ++ tail ∧
      (eof = true → tail = [endOfFile input]) := by
  have hbefore : (input.take offset).length = offset := by simp; omega
  have hinput : input = input.take offset ++ input.drop offset := (List.take_append_drop _ _).symm
  obtain ⟨hfull, hpart⟩ := group_tokens hg
  cases eof with
  | true =>
    have ht : Tokenization.From version (0 + offset) (input.drop offset) tokens := by
      simpa using hfull rfl
    obtain ⟨t₀, rfl, ht₀⟩ := tokenizationFrom_moveBy_inv ht
    have hc : Complete version [input.drop offset].flatten true :=
      ⟨rfl, t₀, by simpa [Tokenization] using ht₀⟩
    obtain ⟨t, ht', e⟩ := handsOverAll_of_correct h hc
    simp only [List.flatten_cons, List.flatten_nil, List.append_nil] at ht' e
    rw [tokenizationFrom_unique ht' ht₀] at e
    refine ⟨[endOfFile input], ?_, fun _ => rfl⟩
    simp only [segment, e, List.map_append, List.map_map, List.map_cons, List.map_nil]
    congr 1
    · refine List.map_congr_left fun token htoken => ?_
      simp only [Function.comp_apply]
      have := handed_after (version := version) (input.take offset) (input.drop offset)
        (input.drop offset) token (List.prefix_refl _)
        (by have := tokenizationFrom_within ht₀ token htoken; omega)
      rw [this, hbefore, ← hinput]
    · rw [endOfFile_after, ← hinput]
  | false =>
    obtain ⟨start, more, hsplit, ht, hc⟩ := hpart rfl
    have ht' : Tokenization.From version (0 + offset) start tokens := by simpa using ht
    obtain ⟨t₀, rfl, ht₀⟩ := tokenizationFrom_moveBy_inv ht'
    have hc₀ : EndsWithClose t₀ start.length := endsWithClose_moveBy (by simpa using hc)
    have hpre := handed_close_prefix h version start more
    rw [handed_close h ht₀ hc₀, ← hsplit] at hpre
    obtain ⟨tail₀, htail⟩ := hpre
    refine ⟨tail₀.map (Handed.after (input.take offset)), ?_, fun he => by cases he⟩
    simp only [segment, ← htail, List.map_append, List.map_map]
    congr 1
    refine List.map_congr_left fun token htoken => ?_
    simp only [Function.comp_apply]
    have := handed_after (version := version) (input.take offset) (input.drop offset) start token
      ⟨more, hsplit.symm⟩ (by have := tokenizationFrom_within ht₀ token htoken; omega)
    rw [this, hbefore, ← hinput]

end BSmtLib.Facts.Proofs.Reader.Feed
