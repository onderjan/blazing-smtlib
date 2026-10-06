import BSmtLib.SpecChecks.RoundTrip.Lexical
import BSmtLib.SpecChecks.RoundTrip.Trees
import BSmtLib.Spec.Parser

/-!
# Printing scripts

The abstract printer of a script: each command's syntax tokens written as lexical tokens in the
version in force at the command, laid out canonically, and followed by `commandSeparator`. A
version declaration switches the version for itself and the commands after it, as in
`ScriptParse`.

`ScriptLexing` is `ScriptParseFrom` that also records the tokens of each command and the version
they are read in; `scriptParse_iff` shows that it adds nothing else.

Not trusted: everything here is proved.
-/

namespace BSmtLib.SpecChecks.Grammar

open BSmtLib.Spec BSmtLib.Spec.Lexicon BSmtLib.Spec.Grammar BSmtLib.Spec.Parser
open BSmtLib.SpecChecks.Lexicon

/-! ## The printer -/

/-- What the abstract printer writes after each command: a line feed. -/
def commandSeparator : Chars := [10]

/-- The lexical tokens of a command, written in the version. -/
def lexCommand (version : Version) (command : Tree.Command) : List Token :=
  (printCommand command).map (lexToken version)

/-- The characters of a command, written in the version and laid out canonically. -/
def printCommandText (version : Version) (command : Tree.Command) : Chars :=
  layout (lexCommand version command)

/-- The version in force after the command, when the version is in force before it. -/
def versionAfter (version : Version) (command : Tree.Command) : Version :=
  (declaredVersion command).getD version

/-- The characters of a script that starts in the version: each command in the version in force
at it, followed by `commandSeparator`. -/
def printScript : Version → List Tree.Command → Chars
  | _, [] => []
  | version, command :: commands =>
    printCommandText (versionAfter version command) command ++ commandSeparator ++
      printScript (versionAfter version command) commands

/-! ## Scripts with their tokens -/

/-- `ScriptLexing version offset input commands segments`: as `ScriptParseFrom`, and the segments
are the tokens of each command with the version they are read in. -/
inductive ScriptLexing : Version → Nat → Chars → List Tree.Command →
    List (Version × List Token) → Prop
  | done : TokenizationFrom version offset input [] → ScriptLexing version offset input [] []

  | command : TokenizationExactly commandVersion offset segment tokens →
      Grammar.Command commandVersion (tokens.map (SyntaxToken.ofToken commandVersion)) command →
      (commandVersion = version ∨ command.DeclaresVersion) → command ≠ .exit →
      ScriptLexing commandVersion (offset + segment.length) rest commands segments →
      ScriptLexing version offset (segment ++ rest) (command :: commands)
        ((commandVersion, tokens) :: segments)

  | exit : TokenizationExactly version offset segment tokens →
      Grammar.Command version (tokens.map (SyntaxToken.ofToken version)) .exit →
      ScriptLexing version offset (segment ++ rest) [.exit] [(version, tokens)]

theorem scriptParseFrom_iff {version : Version} {offset : Nat} {input : Chars}
    {commands : List Tree.Command} :
    ScriptParseFrom version offset input commands ↔
      ∃ segments, ScriptLexing version offset input commands segments := by
  constructor
  · intro h
    induction h with
    | done h => exact ⟨_, .done h⟩
    | command hseg hc hv hne _ ih =>
      obtain ⟨segments, ih⟩ := ih
      exact ⟨_, .command hseg hc hv hne ih⟩
    | exit hseg hc => exact ⟨_, .exit hseg hc⟩
  · rintro ⟨segments, h⟩
    induction h with
    | done h => exact .done h
    | command hseg hc hv hne _ ih => exact .command hseg hc hv hne ih
    | exit hseg hc => exact .exit hseg hc

/-- The canonical layout of the tokens of the commands, each followed by `commandSeparator`. -/
def layoutScript (segments : List (Version × List Token)) : Chars :=
  segments.flatMap fun segment => layout segment.2 ++ commandSeparator

/-- No string literal among the tokens of the commands has a backslash that does not start
`\\` or `\"` in 2.0. -/
def NoLoneBackslashIn (segments : List (Version × List Token)) : Prop :=
  ∀ segment ∈ segments, NoLoneBackslash segment.1 segment.2

/-! ## The version in force -/

theorem versionOfNumber_number (version : Version) :
    versionOfNumber (versionNumber version) = some version := by
  cases version <;> rfl

theorem declaresVersion_of {command : Tree.Command} {version : Version}
    (h : declaredVersion command = some version) : command.DeclaresVersion := by
  unfold declaredVersion at h
  split at h
  · split at h
    · rename_i hk
      exact ⟨_, by rw [hk]⟩
    · simp at h
  · simp at h

/-- The version after a command of a parse is the version the command is read in. -/
theorem versionAfter_eq {version commandVersion : Version} {tokens : List SyntaxToken}
    {command : Tree.Command} (h : Grammar.Command commandVersion tokens command)
    (hv : commandVersion = version ∨ command.DeclaresVersion) :
    versionAfter version command = commandVersion := by
  by_cases hd : command.DeclaresVersion
  · obtain ⟨value, rfl⟩ := hd
    generalize hc : Tree.Command.setInfo ⟨chars "smt-lib-version", value⟩ = command at h
    cases h with
    | setInfo _ hkeyword =>
      simp only [Tree.Command.setInfo.injEq] at hc
      exact absurd (by rw [← hc]) hkeyword
    | declareVersion =>
      simp only [Tree.Command.setInfo.injEq, Tree.Attribute.mk.injEq, true_and] at hc
      subst hc
      simp [versionAfter, declaredVersion, versionOfNumber_number]
    | _ => simp at hc
  · have hnone : declaredVersion command = none := by
      cases hc : declaredVersion command with
      | none => rfl
      | some _ => exact absurd (declaresVersion_of hc) hd
    rw [versionAfter, hnone]
    rcases hv with hv | hv
    · exact hv.symm
    · exact absurd hv hd

/-! ## Commands -/

theorem placeFrom_ofToken (version : Version) (previous : Option Category) (offset : Nat)
    (tokens : List Token) :
    (placeFrom previous offset tokens).map (SyntaxToken.ofToken version) =
      tokens.map (SyntaxToken.ofToken version) := by
  induction tokens generalizing previous offset with
  | nil => rfl
  | cons token tokens ih => simp [placeFrom, ih, ofToken_offset]

/-- The last placed token ends where the layout ends. -/
theorem placeFrom_last (previous : Option Category) (offset : Nat) {tokens : List Token}
    (hne : tokens ≠ []) :
    ∃ last, (placeFrom previous offset tokens).getLast? = some last ∧
      last.offset + last.text.length =
        offset + (printConcrete ⟨canonicalFrom previous tokens, []⟩).length := by
  induction tokens generalizing previous offset with
  | nil => exact absurd rfl hne
  | cons token tokens ih =>
    cases tokens with
    | nil =>
      refine ⟨⟨token.category, offset + (separator previous token.category).length, token.text⟩,
        by simp [placeFrom], ?_⟩
      simp [canonicalFrom, printConcrete]
      omega
    | cons next more =>
      obtain ⟨last, hlast, hend⟩ := ih (some token.category)
        (offset + (separator previous token.category).length + token.text.length) (by simp)
      refine ⟨last, ?_, ?_⟩
      · simp only [placeFrom] at hlast ⊢
        rw [List.getLast?_cons_cons]
        exact hlast
      · rw [hend]
        simp only [canonicalFrom, printConcrete_cons, List.length_append]
        simp only [canonicalFrom] at *
        omega

theorem whitespace_lineFeed : whitespace commandSeparator :=
  star_each fun c hc => by
    simp only [commandSeparator, List.mem_singleton] at hc
    subst hc
    exact Or.inl (whiteSpaceChar_one.mpr (by decide))

/-- A command read from tokens of an input is written as tokens that are tokens of the version. -/
theorem lexCommand_regex {version : Version} {offset : Nat} {input : Chars}
    {tokens : List Token} {command : Tree.Command}
    (hseg : TokenizationFrom version offset input tokens)
    (hc : Grammar.Command version (tokens.map (SyntaxToken.ofToken version)) command) :
    ∀ token ∈ lexCommand version command,
      categoryRegex version token.category token.text := by
  intro token htoken
  rw [lexCommand, ← command_tokens hc, List.map_map] at htoken
  obtain ⟨t, ht, rfl⟩ := List.mem_map.mp htoken
  exact lexForm_regex (tokenizationFrom_regex hseg t ht)

/-- Print-read for a command: whitespace followed by the written command is read, in the version
the command was read in, as tokens that the command is read from. -/
theorem printCommandText_read {version : Version} {offset : Nat} {input : Chars}
    {tokens : List Token} {command : Tree.Command}
    (hseg : TokenizationFrom version offset input tokens) (hne : tokens ≠ [])
    (hc : Grammar.Command version (tokens.map (SyntaxToken.ofToken version)) command)
    (offset' : Nat) {w : Chars} (hw : whitespace w) :
    TokenizationExactly version offset' (w ++ printCommandText version command)
        (placeFrom none (offset' + w.length) (lexCommand version command)) ∧
      Grammar.Command version
        ((placeFrom none (offset' + w.length) (lexCommand version command)).map
          (SyntaxToken.ofToken version)) command := by
  have hvalid := lexCommand_regex hseg hc
  have hlexne : lexCommand version command ≠ [] := by
    rw [lexCommand, ← command_tokens hc]
    simpa using hne
  refine ⟨⟨canonicalFrom_tokenization hvalid none offset' hw, ?_⟩, ?_⟩
  · obtain ⟨last, hlast, hend⟩ := placeFrom_last none (offset' + w.length) hlexne
    refine ⟨last, hlast, ?_⟩
    rw [hend, printCommandText, layout, List.length_append]
    omega
  · rw [placeFrom_ofToken, lexCommand, List.map_map]
    have hid : (SyntaxToken.ofToken version ∘ lexToken version) = id :=
      funext (ofToken_lexToken version)
    rw [hid, List.map_id, ← command_tokens hc]
    exact hc

/-! ## Print-read -/

theorem ne_nil_of_exactly {version : Version} {offset : Nat} {segment : Chars}
    {tokens : List Token} (h : TokenizationExactly version offset segment tokens) :
    tokens ≠ [] := by
  obtain ⟨last, hlast, -⟩ := h.2
  intro e
  rw [e] at hlast
  simp at hlast

theorem printScript_read {version : Version} {offset : Nat} {input : Chars}
    {commands : List Tree.Command} (h : ScriptParseFrom version offset input commands) :
    ∀ (offset' : Nat) {w : Chars}, whitespace w →
      ScriptParseFrom version offset' (w ++ printScript version commands) commands := by
  induction h with
  | done _ =>
    intro offset' w hw
    simpa [printScript] using ScriptParseFrom.done (offset := offset')
      (TokenizationFrom.done (whitespaceAtEnd_of hw))
  | command hseg hc hv hne _ ih =>
    intro offset' w hw
    have htne := ne_nil_of_exactly hseg
    obtain ⟨hT, hC⟩ := printCommandText_read hseg.1 htne hc offset' hw
    have := ScriptParseFrom.command hT hC hv hne (ih _ whitespace_lineFeed)
    simpa [printScript, versionAfter_eq hc hv, List.append_assoc] using this
  | exit hseg hc =>
    intro offset' w hw
    have htne := ne_nil_of_exactly hseg
    obtain ⟨hT, hC⟩ := printCommandText_read hseg.1 htne hc offset' hw
    have := ScriptParseFrom.exit (rest := commandSeparator) hT hC
    simpa [printScript, versionAfter, declaredVersion, List.append_assoc]
      using this

/-! ## Read-print -/

theorem layout_ofToken {version : Version} {offset : Nat} {input : Chars}
    {tokens : List Token} (hseg : TokenizationFrom version offset input tokens)
    (hl : NoLoneBackslash version tokens) :
    layout ((tokens.map (SyntaxToken.ofToken version)).map (lexToken version)) = layout tokens := by
  apply layout_eq
  rw [List.map_map, List.map_map]
  apply List.map_congr_left
  intro t ht
  have hl' : NoLoneBackslash version [t] := fun hv u hu hcat =>
    hl hv u (by simp at hu; exact hu ▸ ht) hcat
  simp only [Function.comp, form, lexToken]
  rw [lexForm_ofToken (tokenizationFrom_regex hseg t ht) hl']
  rfl

theorem printScript_layout {version : Version} {offset : Nat} {input : Chars}
    {commands : List Tree.Command} {segments : List (Version × List Token)}
    (h : ScriptLexing version offset input commands segments) (hl : NoLoneBackslashIn segments) :
    printScript version commands = layoutScript segments := by
  induction h with
  | done _ => rfl
  | command hseg hc hv _ _ ih =>
    have hl₁ := hl _ (List.mem_cons_self ..)
    have ih := ih fun s hs => hl s (List.mem_cons_of_mem _ hs)
    simp only [printScript, versionAfter_eq hc hv, ih, layoutScript, List.flatMap_cons,
      printCommandText, lexCommand, ← command_tokens hc, layout_ofToken hseg.1 hl₁]
  | exit hseg hc =>
    have hl₁ := hl _ (List.mem_cons_self ..)
    simp only [printScript, versionAfter, declaredVersion, Option.getD_none,
      layoutScript, List.flatMap_cons, List.flatMap_nil, printCommandText, lexCommand,
      ← command_tokens hc, layout_ofToken hseg.1 hl₁]

/-! ## Idempotence of a command -/

theorem printCommandText_idempotent {version : Version} {input : Chars}
    {tokens tokens' : List Token} {command command' : Tree.Command}
    (hseg : Tokenization version input tokens)
    (hc : Grammar.Command version (tokens.map (SyntaxToken.ofToken version)) command)
    (hseg' : Tokenization version (printCommandText version command) tokens')
    (hc' : Grammar.Command version (tokens'.map (SyntaxToken.ofToken version)) command') :
    printCommandText version command' = printCommandText version command := by
  have hT := layout_tokenization (lexCommand_regex hseg hc)
  have e : tokens' = place (lexCommand version command) :=
    tokenizationFrom_unique hseg' hT
  have hp : printCommand command' = printCommand command := by
    rw [← command_tokens hc', e, place, placeFrom_ofToken, lexCommand, List.map_map]
    have hid : (SyntaxToken.ofToken version ∘ lexToken version) = id :=
      funext (ofToken_lexToken version)
    rw [hid, List.map_id]
  rw [printCommandText, printCommandText, lexCommand, lexCommand, hp]

end BSmtLib.SpecChecks.Grammar
