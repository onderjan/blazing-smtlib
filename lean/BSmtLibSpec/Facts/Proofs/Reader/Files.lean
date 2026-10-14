import BSmtLibSpec.Facts.Proofs.Reader.Consumer
import BSmtLibSpec.Facts.Proofs.Grammar.Files

/-!
# A lexer with a parser reads a file

A correct lexer with a parser that follows the traversal as its consumer, fed a file, hands over
the tokens of the file's commands, each command read in the version in force, and the parser
takes them, switches the version after each version declaration and has the rest discarded after
`exit`, and finishes at the end of the input (`files_runs`).

The lexer reads the input after a switch of the version on its own (`BSmtLibSpec.Lexer.segment`);
until the next switch, the commands it reads are a block whose characters end with a `)`, so the
lexer has handed their tokens over whatever follows (`command_block`).

Not trusted: everything here is proved.
-/

namespace BSmtLibSpec.Facts.Proofs.Reader.Files

open BSmtLibSpec.Lexicon BSmtLibSpec.Lexer BSmtLibSpec.Grammar
open BSmtLibSpec.Grammar.Syntax BSmtLibSpec.Grammar.File
open BSmtLibSpec.Regex (Chars chars)
open BSmtLibSpec.Parser.Properties
open BSmtLibSpec.Facts.Proofs.Lexer.StreamingFacts BSmtLibSpec.Facts.Proofs.Grammar.Files
open BSmtLibSpec.Facts.Proofs.Lexicon.Compose BSmtLibSpec.Facts.Proofs.Lexicon.Lemmas
open BSmtLibSpec.Facts.Proofs.Reader.Consumer BSmtLibSpec.Facts.Proofs.Reader.Lexing
open BSmtLibSpec.Facts.Proofs.Reader.Requests

/-! ## Runs of a consumer that continues -/

/-- A consumer that continues on each of the tokens, asking for nothing, goes on after them as
the lexer with the tokens taken. -/
theorem runs_continues {feed : Version → List Chars → Bool → Fed} {consumer : Consumer}
    {start : Version} {input : Chars} {ended : Bool} {version : Version} {failed : Bool}
    {session : Session consumer.Result consumer.Error} :
    ∀ (tokens taken ready : List Handed),
      (∀ i, 1 ≤ i → i ≤ tokens.length →
        consumer.answer (taken ++ tokens.take i) = .continue ∧
          consumer.discards (taken ++ tokens.take i) = false ∧
          consumer.switchTo (taken ++ tokens.take i) = none) →
      (∀ token ∈ tokens, token.type ≠ .endOfFile) →
      Runs feed consumer start input ended version ready failed (taken ++ tokens) session →
      Runs feed consumer start input ended version (tokens ++ ready) failed taken session
  | [], taken, ready, _, _, h => by simpa using h
  | token :: tokens, taken, ready, hstep, htype, h => by
    obtain ⟨hc, hd, hs⟩ := hstep 1 (Nat.le_refl 1) (by simp)
    simp only [List.take_succ_cons, List.take_zero] at hc hd hs
    refine Runs.continues (htype token (by simp)) hc hd ?_
    rw [hs]
    simp only [Option.getD_none, following]
    refine runs_continues tokens (taken ++ [token]) ready (fun i h₁ h₂ => ?_)
      (fun t ht => htype t (by simp [ht])) (by simpa using h)
    have := hstep (i + 1) (by omega) (by simp; omega)
    simpa using this

/-! ## Commands and the mode after them -/

/-- A command after which the input is read in a version declares that version, or keeps the
version in force, and is not `exit`. -/
theorem read_next {version next : Version} {command : Tree.Command}
    (h : command.modeAfter version = some (.read next)) :
    next = command.declaredVersion.getD version ∧ exitFlag command = false := by
  cases command with
  | exit => simp [Tree.Command.modeAfter] at h
  | setInfo info =>
    obtain ⟨keyword, value⟩ := info
    simp only [Tree.Command.modeAfter] at h
    by_cases hk : keyword = chars "smt-lib-version"
    · simp only [hk, ite_true] at h
      rcases value with _ | ((_ | decimal | _ | _ | _) | _ | _)
      all_goals try (cases hv : versionOfNumber decimal)
      all_goals simp_all [Tree.Command.declaredVersion, exitFlag]
    · simp only [hk, ite_false, Option.some.injEq, Mode.read.injEq] at h
      subst h
      rcases value with _ | ((_ | decimal | _ | _ | _) | _ | _) <;>
        simp [Tree.Command.declaredVersion, hk, exitFlag]
  | _ =>
    simp only [Tree.Command.modeAfter, Option.some.injEq, Mode.read.injEq] at h
    subst h
    simp [Tree.Command.declaredVersion, exitFlag]

/-- The tokens of a command are not empty. -/
theorem tokens_ne_nil (command : Tree.Command) : command.tokens ≠ [] := by
  obtain ⟨inner, h⟩ := Parser.Simulation.command_tokens_open command
  simp [h]

/-- What a parser receives is never empty. -/
theorem received_ne_nil (commands : List Tree.Command) : received commands ≠ [] := by
  cases commands with
  | nil => simp [received]
  | cons first rest =>
    cases first <;> simp [received, tokens_ne_nil]

/-! ## Blocks of commands -/

/-- The tokens, read from the offset of the input on, as handed over from the whole input. -/
def blockHanded (version : Version) (input : Chars) (offset : Nat) (tokens : List Token) :
    List Handed :=
  tokens.map fun token => (token.handed version (input.drop offset)).after (input.take offset)

theorem blockHanded_append (version : Version) (input : Chars) (offset : Nat)
    (tokens tokens' : List Token) :
    blockHanded version input offset (tokens ++ tokens') =
      blockHanded version input offset tokens ++ blockHanded version input offset tokens' := by
  simp [blockHanded]

/-- A tokenisation with no tokens is one from any offset. -/
theorem tokenizationFrom_nil_offset {version : Version} {offset offset' : Nat} {input : Chars}
    (h : Tokenization.From version offset input []) : Tokenization.From version offset' input [] :=
    by
  cases h with
  | done hw => exact .done hw

theorem endsWithClose_moveBy {tokens : List Token} {stop k : Nat}
    (h : EndsWithClose (tokens.map (Token.moveBy k)) (stop + k)) : EndsWithClose tokens stop := by
  obtain ⟨last, hlast, hcat, hend⟩ := h
  rw [List.getLast?_map] at hlast
  cases hl : tokens.getLast? with
  | none => simp [hl] at hlast
  | some t =>
    simp only [hl, Option.map_some, Option.some.injEq] at hlast
    subst hlast
    refine ⟨t, hl, hcat, ?_⟩
    simp only [Token.moveBy] at hend
    omega

theorem endsWithClose_append {tokens tokens' : List Token} {stop : Nat}
    (h : EndsWithClose tokens' stop) : EndsWithClose (tokens ++ tokens') stop := by
  obtain ⟨last, hlast, hcat, hend⟩ := h
  refine ⟨last, ?_, hcat, hend⟩
  rw [List.getLast?_append, hlast]
  rfl

variable {lexing : Lexing} {parser : RecordingParser} {item : Handed → parser.Item}

/--
The next command of a block: a correct lexer reading from the offset `offset` in the version,
having handed over the tokens of the block up to `stop`, hands over the command's tokens next,
which stand for the command's tokens and end where the command does; the block grows by the
command.
-/
theorem command_block (hL : Correct lexing.fed) (hI : StandsFor parser item)
    {version : Version} {input : Chars} {offset stop : Nat} {block : List Token}
    {segment rest : Chars} {tokens : List Token} {command : Tree.Command}
    (hdrop : input.drop stop = segment ++ rest) (hos : offset ≤ stop)
    (hblock : Tokenization version ((input.drop offset).take (stop - offset)) block)
    (hclosed : stop = offset ∧ block = [] ∨ EndsWithClose block (stop - offset))
    (htok : Tokenization.Exactly version stop segment tokens)
    (hic : IsCommand version (tokens.map (SyntaxToken.ofToken version)) command) :
    ∃ rel more, (BSmtLibSpec.Lexer.segment lexing.fed version input true offset).handed =
        blockHanded version input offset (block ++ rel) ++ more ∧
      stood parser item (blockHanded version input offset rel) =
        command.tokens.map .token ∧
      (∀ handed ∈ blockHanded version input offset rel, handed.type ≠ .endOfFile) ∧
      (blockHanded version input offset rel).getLast?.map (·.«end».offset) =
        some (stop + segment.length) ∧
      Tokenization version ((input.drop offset).take (stop + segment.length - offset))
        (block ++ rel) ∧
      EndsWithClose (block ++ rel) (stop + segment.length - offset) := by
  have hstop : stop ≤ input.length := by
    refine Nat.le_of_not_lt fun hc => ?_
    have : input.drop stop = [] := List.drop_eq_nil_of_le (by omega)
    rw [this] at hdrop
    have hne := tokenizationFrom_ne_nil htok.1 (by
      obtain ⟨last, hlast, -⟩ := htok.2
      intro e; simp [e] at hlast)
    exact hne (List.append_eq_nil_iff.mp hdrop.symm).1
  -- the command's tokens, read from the offset
  have hst : stop = (stop - offset) + offset := by omega
  have htok₁ : Tokenization.From version ((stop - offset) + offset) segment tokens := by
    rw [← hst]; exact htok.1
  obtain ⟨rel, hrel, htrel⟩ := tokenizationFrom_moveBy_inv htok₁
  have hclose := endsWithClose_of_command htok hic
  have hcloseRel : EndsWithClose rel (stop - offset + segment.length) := by
    rw [hrel] at hclose
    exact endsWithClose_moveBy (k := offset) (by
      rw [show stop - offset + segment.length + offset = stop + segment.length by omega]
      exact hclose)
  let A := (input.drop offset).take (stop - offset)
  have hA : A.length = stop - offset := by simp [A]; omega
  have hsplit : input.drop offset = A ++ segment ++ rest := by
    rw [List.append_assoc, ← hdrop]
    simp only [A]
    rw [show input.drop stop = (input.drop offset).drop (stop - offset) by
      rw [List.drop_drop]; congr 1; omega]
    exact (List.take_append_drop _ _).symm
  have hoi : offset ≤ input.length := by omega
  have hall : Tokenization version (A ++ segment) (block ++ rel) := by
    rcases hclosed with ⟨he, hb⟩ | hc
    · subst hb
      have hA0 : A = [] := by simp [A, he]
      rw [hA0]
      simpa [Tokenization, he] using htrel
    · refine tokenizationFrom_close_append hblock (by rw [Nat.zero_add, hA]; exact hc) ?_
      rw [Nat.zero_add, hA]; exact htrel
  have hallClose : EndsWithClose (block ++ rel) (A ++ segment).length := by
    rw [List.length_append, hA]
    exact endsWithClose_append (tokens := block) hcloseRel
  obtain ⟨more, hmore⟩ := handed_close_prefix hL hall hallClose rest
  refine ⟨rel, more.map (Handed.after (input.take offset)), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [BSmtLibSpec.Lexer.segment, hsplit]
    rw [hmore]
    simp [blockHanded, hsplit, Function.comp_def]
  · simp only [stood, blockHanded, List.map_map, hic.2, hrel]
    refine List.map_congr_left fun token htoken => ?_
    have hreg := (tokenizationFrom_mem hall token (by simp [htoken])).1
    simp only [Function.comp]
    rw [ofToken_moveBy]
    exact hI _ _ version (received_after (input.take offset) _ ▸
        (received_handed hreg (input.drop offset)).1)
      (received_handed hreg []).2
  · intro handed hh
    simp only [blockHanded, List.mem_map] at hh
    obtain ⟨token, -, rfl⟩ := hh
    rw [type_after]
    simp only [Token.handed]
    cases token.category <;> simp [Category.type]
  · obtain ⟨last, hlast, -, hend⟩ := hcloseRel
    simp only [blockHanded, List.getLast?_map, hlast, Option.map_some, end_offset_after,
      end_offset_handed, List.length_take]
    congr 1
    omega
  · have : (input.drop offset).take (stop + segment.length - offset) = A ++ segment := by
      rw [hsplit]
      exact List.take_left' (by simp [hA]; omega)
    rw [this]; exact hall
  · rw [show stop + segment.length - offset = (A ++ segment).length by simp [hA]; omega]
    exact hallClose

/-- A correct lexer fed the whole input from the offset on, which has the tokenisation, has
handed over its tokens and the end of the file, and has not failed. -/
theorem segment_complete (hL : Correct lexing.fed) {version : Version} {input : Chars}
    {offset : Nat} {tokens : List Token} (ht : Tokenization version (input.drop offset) tokens) :
    BSmtLibSpec.Lexer.segment lexing.fed version input true offset =
      ⟨blockHanded version input offset tokens ++
        [(endOfFile (input.drop offset)).after (input.take offset)], false⟩ := by
  simp [BSmtLibSpec.Lexer.segment, fed_complete hL ht, blockHanded, Function.comp_def]

/-- The empty input has no tokens. -/
theorem tokenization_nil (version : Version) : Tokenization version [] [] :=
  .done ⟨[], [], by simp, whitespace_nil, Or.inl rfl⟩

/-- Taking the first list and a start of the second of three. -/
theorem take_mid {α : Type} (a b c : List α) {n : Nat} (h : n ≤ b.length) :
    (a ++ b ++ c).take (a.length + n) = a ++ b.take n := by
  rw [List.append_assoc, List.take_append, List.take_of_length_le (by omega),
    Nat.add_sub_cancel_left, List.take_append, Nat.sub_eq_zero_of_le h]
  simp

variable (hF : FollowsTheTraversal parser) (hI : StandsFor parser item)
include hF hI

/-- On the tokens of a command of a script, a parser that follows the traversal continues, and
asks for the switch and the discarding that the traversal asks for after the command's `)`. -/
theorem command_steps {start : Version} {all : List Tree.Command} {command : Tree.Command}
    {commands : List Tree.Command} (hS : Takes start all (received all) .finished)
    {taken tokens : List Handed}
    (hrec : received all = stood parser item taken ++ command.tokens.map .token ++
      received commands)
    (hreq : ∀ i, 1 ≤ i → requestsAt all (taken.length + i) = requestsAt (command :: commands) i)
    (hstood : stood parser item tokens = command.tokens.map .token)
    (htype : ∀ handed ∈ tokens, handed.type ≠ .endOfFile) :
    ∀ i, 1 ≤ i → i ≤ tokens.length →
      (Reader.consumer parser item start).answer (taken ++ tokens.take i) = .continue ∧
      (Reader.consumer parser item start).switchTo (taken ++ tokens.take i) =
        (requestsAt (command :: commands) i).1 ∧
      (Reader.consumer parser item start).discards (taken ++ tokens.take i) =
        (requestsAt (command :: commands) i).2 := by
  intro i h₁ h₂
  have hl : tokens.length = command.tokens.length := by
    simpa [stood] using congrArg List.length hstood
  have hlen : (taken ++ tokens.take i).length = taken.length + i := by
    simp; omega
  have hst : (stood parser item taken).length = taken.length := by simp [stood]
  have hs : stood parser item (taken ++ tokens.take i) =
      (received all).take (taken ++ tokens.take i).length := by
    have ht : stood parser item (tokens.take i) = (command.tokens.map .token).take i := by
      rw [← hstood]; simp [stood, List.map_take]
    rw [stood_append, ht, hlen, hrec, ← hst, take_mid _ _ _ (by simp; omega)]
  have hlt : (taken ++ tokens.take i).length < (received all).length := by
    have := List.length_pos_iff.mpr (received_ne_nil commands)
    rw [hlen, hrec]
    simp only [List.length_append, List.length_map, hst]
    omega
  have hend : (taken ++ tokens.take i).getLast?.map (·.type) ≠ some .endOfFile := by
    have hne : tokens.take i ≠ [] :=
      List.ne_nil_of_length_pos (by rw [List.length_take]; omega)
    have ht := List.getLast?_eq_some_getLast hne
    generalize (tokens.take i).getLast hne = t at ht
    rw [List.getLast?_append, ht]
    simp only [Option.some_or, Option.map_some, ne_eq, Option.some.injEq]
    exact htype t (List.mem_of_mem_take (List.mem_of_getLast? ht))
  refine ⟨answer_of_takes hF hI hS hs hlt hend, ?_, ?_⟩
  · rw [switchTo_of_takes hF hI hS hs (by omega) (by omega), hlen, hreq i h₁]
  · rw [discards_of_takes hF hI hS hs (by omega) (by omega), hlen, hreq i h₁]

omit hF hI in
/-- A consumer that continues on the tokens but the last, asking for nothing, goes on as the lexer
at the last token. -/
theorem runs_through {feed : Version → List Chars → Bool → Fed} {consumer : Consumer}
    {start : Version} {input : Chars} {ended : Bool} {version : Version} {failed : Bool}
    {session : Session consumer.Result consumer.Error} {taken init ready : List Handed}
    {last : Handed}
    (hsteps : ∀ i, 1 ≤ i → i ≤ init.length →
      consumer.answer (taken ++ (init ++ [last]).take i) = .continue ∧
        consumer.discards (taken ++ (init ++ [last]).take i) = false ∧
        consumer.switchTo (taken ++ (init ++ [last]).take i) = none)
    (htype : ∀ token ∈ init, token.type ≠ .endOfFile)
    (hlast : Runs feed consumer start input ended version (last :: ready) failed (taken ++ init)
      session) :
    Runs feed consumer start input ended version (init ++ last :: ready) failed taken session :=
  runs_continues init taken (last :: ready) (fun i h₁ h₂ => by
    have := hsteps i h₁ h₂
    rwa [List.take_append_of_le_length h₂] at this) htype hlast

omit hF hI in
/-- The input from the offset on is the block's characters and the rest. -/
theorem drop_split {input rest : Chars} {offset stop : Nat} (hdrop : input.drop stop = rest)
    (hos : offset ≤ stop) :
    input.drop offset = (input.drop offset).take (stop - offset) ++ rest := by
  rw [← hdrop, show input.drop stop = (input.drop offset).drop (stop - offset) by
    rw [List.drop_drop]; congr 1; omega]
  exact (List.take_append_drop _ _).symm

/--
A correct lexer with a parser that follows the traversal as its consumer, fed a file from a point
between two commands on: the parser has taken the tokens of the commands before, the lexer reads
from `offset` on in the version in force, and the commands from there to `stop` are a block of
tokens. Then the lexer hands over the tokens of the rest of the file, and the run finishes with
the parser having taken what a parser takes for the whole script.
-/
theorem files_runs (hL : Correct lexing.fed) {start : Version} {input : Chars}
    {all : List Tree.Command} (hS : Takes start all (received all) .finished) :
    ∀ {version stop rest commands}, File.From version stop rest commands →
    ∀ (taken : List Handed) (offset : Nat) (block : List Token),
      received all = stood parser item taken ++ received commands →
      (∀ i, 1 ≤ i → requestsAt all (taken.length + i) = requestsAt commands i) →
      input.drop stop = rest → stop ≤ input.length → offset ≤ stop →
      Tokenization version ((input.drop offset).take (stop - offset)) block →
      (stop = offset ∧ block = [] ∨ EndsWithClose block (stop - offset)) →
      ∃ more location, Runs lexing.fed (Reader.consumer parser item start) start input true version
        ((BSmtLibSpec.Lexer.segment lexing.fed version input true offset).handed.drop block.length)
        (BSmtLibSpec.Lexer.segment lexing.fed version input true offset).failed taken
        ⟨taken ++ more, .finished () location, start, none⟩ ∧
        stood parser item (taken ++ more) = received all := by
  intro version stop rest commands h
  induction h with
  | @done version stop rest htz =>
    intro taken offset block hrec _ hdrop hle hos hblock hclosed
    have hA : ((input.drop offset).take (stop - offset)).length = stop - offset := by
      simp; omega
    have hsplit := drop_split hdrop hos
    have hall : Tokenization version (input.drop offset) block := by
      rcases hclosed with ⟨he, hb⟩ | hc
      · subst hb
        rw [hsplit, show stop - offset = 0 by omega]
        simpa [Tokenization] using tokenizationFrom_nil_offset (offset' := 0) htz
      · rw [hsplit]
        have := tokenizationFrom_close_append hblock (by rw [Nat.zero_add, hA]; exact hc)
          (by rw [Nat.zero_add, hA]; exact tokenizationFrom_nil_offset htz)
        rwa [List.append_nil] at this
    rw [segment_complete hL hall]
    have hd : (blockHanded version input offset block ++
        [(endOfFile (input.drop offset)).after (input.take offset)]).drop block.length =
        [(endOfFile (input.drop offset)).after (input.take offset)] := by
      simp [blockHanded]
    rw [hd]
    have hstood : stood parser item
        (taken ++ [(endOfFile (input.drop offset)).after (input.take offset)]) =
        received all := by
      rw [stood_append, hrec]
      simp only [received, stood, List.map_cons, List.map_nil]
      rw [hI ((endOfFile (input.drop offset)).after (input.take offset)) .endOfInput start rfl
        trivial]
    exact ⟨_, _, Runs.ends rfl (answer_of_script hF hI hS hstood), hstood⟩
  | @command version stop segment tokens command next rest commands htok hic hm _ ih =>
    intro taken offset block hrec hreq hdrop hle hos hblock hclosed
    obtain ⟨rel, more, hseg, hstood, htype, hlast, hnew, hnewClose⟩ :=
      command_block hL hI hdrop hos hblock hclosed htok hic
    obtain ⟨hnext, hexit⟩ := read_next hm
    have hne : command ≠ .exit := by rintro rfl; simp [exitFlag] at hexit
    have hrec' : received all = stood parser item taken ++ command.tokens.map .token ++
        received commands := by
      rw [hrec, Parser.Simulation.received_cons hne, List.append_assoc]
    have steps := command_steps hF hI hS hrec' hreq hstood htype
    rw [blockHanded_append, List.append_assoc] at hseg
    have hrl : (blockHanded version input offset rel).length = rel.length := by simp [blockHanded]
    generalize blockHanded version input offset rel = toks at *
    have hl : toks.length = command.tokens.length := by
      simpa [stood] using congrArg List.length hstood
    have hdrop₁ : (BSmtLibSpec.Lexer.segment lexing.fed version input true offset).handed.drop
        block.length = toks ++ more := by
      rw [hseg, List.drop_left' (by simp [blockHanded])]
    have hdrop₂ : (BSmtLibSpec.Lexer.segment lexing.fed version input true offset).handed.drop
        (block ++ rel).length = more := by
      rw [hseg, ← List.append_assoc, List.drop_left' (by simp [blockHanded, hrl])]
    -- what holds after the command
    have hrec'' : received all = stood parser item (taken ++ toks) ++ received commands := by
      rw [stood_append, hstood, hrec']
    have hreq'' : ∀ i, 1 ≤ i →
        requestsAt all ((taken ++ toks).length + i) = requestsAt commands i := by
      intro i hi
      rw [List.length_append, hl, Nat.add_assoc, hreq _ (by omega)]
      have h₁ : ¬ (command.tokens.length + i < command.tokens.length) := by omega
      have h₂ : ¬ (command.tokens.length + i = command.tokens.length) := by omega
      simp only [requestsAt, h₁, h₂, ite_false, Nat.add_sub_cancel_left]
    have hlen : (input.drop stop).length = segment.length + rest.length := by
      rw [hdrop]; simp
    have hdrop' : input.drop (stop + segment.length) = rest := by
      rw [← List.drop_drop, hdrop]; simp
    have hle' : stop + segment.length ≤ input.length := by
      simp at hlen; omega
    -- the last token, the command's `)`
    have hne' : toks ≠ [] := by
      intro e; rw [e] at hl; exact tokens_ne_nil command (List.eq_nil_of_length_eq_zero hl.symm)
    obtain ⟨init, last, rfl⟩ : ∃ init last, toks = init ++ [last] :=
      ⟨_, _, (List.dropLast_concat_getLast hne').symm⟩
    have hlastEnd : last.«end».offset = stop + segment.length := by
      simpa using hlast
    have hinit : ∀ i, 1 ≤ i → i ≤ init.length →
        (Reader.consumer parser item start).answer (taken ++ (init ++ [last]).take i) = .continue ∧
        (Reader.consumer parser item start).discards (taken ++ (init ++ [last]).take i) = false ∧
        (Reader.consumer parser item start).switchTo (taken ++ (init ++ [last]).take i) = none := by
      intro i h₁ h₂
      obtain ⟨ha, hs, hd⟩ := steps i h₁ (by simp; omega)
      have hlt : i < command.tokens.length := by simp at hl; omega
      simp only [requestsAt, hlt, ite_true] at hs hd
      exact ⟨ha, hd, hs⟩
    obtain ⟨ha, hs, hd⟩ := steps (init ++ [last]).length (by simp) (Nat.le_refl _)
    rw [List.take_length] at ha hs hd
    simp only [requestsAt, hl, Nat.lt_irrefl, ite_false, ite_true, hexit] at hs hd
    have htypeLast : last.type ≠ .endOfFile := htype last (by simp)
    have htypeInit : ∀ token ∈ init, token.type ≠ .endOfFile :=
      fun token ht => htype token (by simp [ht])
    rw [hdrop₁, List.append_assoc, List.singleton_append]
    cases hdecl : command.declaredVersion with
    | none =>
      simp only [hdecl, Option.getD_none] at hnext hs
      subst hnext
      obtain ⟨more', location, hruns, hst⟩ := ih (taken ++ (init ++ [last])) offset (block ++ rel)
        hrec'' hreq'' hdrop' hle' (by omega) hnew (Or.inr hnewClose)
      rw [hdrop₂] at hruns
      refine ⟨init ++ [last] ++ more', location, ?_, by rwa [← List.append_assoc]⟩
      refine runs_through hinit htypeInit (Runs.continues htypeLast ?_
          (by rw [List.append_assoc]; exact hd) ?_)
      · simpa using ha
      · rw [List.append_assoc, hs]
        simpa [following, List.append_assoc] using hruns
    | some declared =>
      simp only [hdecl, Option.getD_some] at hnext hs
      subst hnext
      obtain ⟨more', location, hruns, hst⟩ := ih (taken ++ (init ++ [last]))
        (stop + segment.length) [] hrec'' hreq'' hdrop' hle' (Nat.le_refl _)
        (by simpa using tokenization_nil _) (Or.inl ⟨rfl, rfl⟩)
      refine ⟨init ++ [last] ++ more', location, ?_, by rwa [← List.append_assoc]⟩
      refine runs_through hinit htypeInit (Runs.continues htypeLast ?_
          (by rw [List.append_assoc]; exact hd) ?_)
      · simpa using ha
      · rw [List.append_assoc, hs]
        simpa [following, readyFrom, withLayout, hlastEnd, List.append_assoc, Reader.consumer]
            using hruns
  | @stop version stop segment tokens command rest htok hic hm =>
    intro taken offset block hrec hreq hdrop hle hos hblock hclosed
    obtain rfl := Parser.Simulation.modeAfter_unparsed hm
    obtain ⟨rel, more, hseg, hstood, htype, -, -, -⟩ :=
      command_block hL hI hdrop hos hblock hclosed htok hic
    have hrec' : received all = stood parser item taken ++ Tree.Command.exit.tokens.map .token ++
        received [] := by
      rw [hrec]; simp [received]
    have steps := command_steps hF hI hS hrec' hreq hstood htype
    rw [blockHanded_append, List.append_assoc] at hseg
    generalize blockHanded version input offset rel = toks at *
    have hl : toks.length = Tree.Command.exit.tokens.length := by
      simpa [stood] using congrArg List.length hstood
    have hdrop₁ : (BSmtLibSpec.Lexer.segment lexing.fed version input true offset).handed.drop
        block.length = toks ++ more := by
      rw [hseg, List.drop_left' (by simp [blockHanded])]
    have hne' : toks ≠ [] := by
      intro e; rw [e] at hl; exact tokens_ne_nil .exit (List.eq_nil_of_length_eq_zero hl.symm)
    obtain ⟨init, last, rfl⟩ : ∃ init last, toks = init ++ [last] :=
      ⟨_, _, (List.dropLast_concat_getLast hne').symm⟩
    have hinit : ∀ i, 1 ≤ i → i ≤ init.length →
        (Reader.consumer parser item start).answer (taken ++ (init ++ [last]).take i) = .continue ∧
        (Reader.consumer parser item start).discards (taken ++ (init ++ [last]).take i) = false ∧
        (Reader.consumer parser item start).switchTo (taken ++ (init ++ [last]).take i) = none := by
      intro i h₁ h₂
      obtain ⟨ha, hs, hd⟩ := steps i h₁ (by simp; omega)
      have hlt : i < Tree.Command.exit.tokens.length := by simp at hl; omega
      simp only [requestsAt, hlt, ite_true] at hs hd
      exact ⟨ha, hd, hs⟩
    obtain ⟨ha, -, hd⟩ := steps (init ++ [last]).length (by simp) (Nat.le_refl _)
    rw [List.take_length] at ha hd
    simp only [requestsAt, hl, Nat.lt_irrefl, ite_false, ite_true, exitFlag] at hd
    have htypeLast : last.type ≠ .endOfFile := htype last (by simp)
    have htypeInit : ∀ token ∈ init, token.type ≠ .endOfFile :=
      fun token ht => htype token (by simp [ht])
    have hstoodAll : stood parser item (taken ++ init ++ [last, endOfFileAt last.«end»]) =
        received all := by
      rw [hrec']
      simp only [stood, List.map_append, List.map_cons, List.map_nil, received]
      have h₁ : List.map (fun handed => parser.stands (item handed)) (init ++ [last]) =
          Tree.Command.exit.tokens.map .token := hstood
      rw [hI (endOfFileAt last.«end») .endOfInput start rfl trivial, ← h₁]
      simp
    rw [hdrop₁, List.append_assoc, List.singleton_append]
    refine ⟨init ++ [last, endOfFileAt last.«end»], last.«end», ?_, by
      rw [← List.append_assoc]; exact hstoodAll⟩
    refine runs_through hinit htypeInit ?_
    have := Runs.discardsToEnd (feed := lexing.fed) (start := start) (input := input)
      (version := version) (ready := more)
      (failed := (BSmtLibSpec.Lexer.segment lexing.fed version input true offset).failed)
      htypeLast (by simpa using ha) (by simpa using hd) rfl
      (answer_of_script hF hI hS hstoodAll)
    simpa [settle, Outcome.isFinished, List.append_assoc] using this

end BSmtLibSpec.Facts.Proofs.Reader.Files
