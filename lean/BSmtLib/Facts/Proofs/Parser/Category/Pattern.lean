module

public import BSmtLib.Facts.Proofs.Parser.Category.Ident
public import BSmtLib.Facts.Proofs.Parser.Category.StepsPattern
import all BSmtLib.Parser
import all BSmtLib.Parser.Category.Pattern
import all BSmtLib.Token.Reserved

@[expose] public section

/-!
# The pattern parser on a cursor

The pattern parser steps as `PatternState.step`, whose lemma against the traversal is the term
proofs' (`Category.StepsPattern.pattern_runs`).
-/

namespace BSmtLib.Facts.Proofs.Parser.Category.Pattern

open BSmtLibSpec.Grammar
open BSmtLib.Token (Produce)
open BSmtLib.Parser (Parse ParseState SyntaxErrorKind)
open BSmtLib.Parser.Internal (PM)
open BSmtLib.Parser.Category.Pattern
open BSmtLib.Parser.Category.Pattern.Internal
open BSmtLib.Facts.Parser.Adapters.Bridge
open BSmtLib.Facts.Parser.Adapters.Cursor (Takes Reads noPoints)
open BSmtLib.Facts.Parser.Adapters.Outcome (Finishes Rejects)
open BSmtLib.Facts.Proofs.Parser.Category.Cursor (Simulates Moves)
open BSmtLib.Facts.Proofs.Parser.Category.Ident
open BSmtLib.Facts.Proofs.Parser.Category.Steps BSmtLib.Facts.Proofs.Parser.Category.CursorS
open BSmtLib.Facts.Proofs.Parser.Drive

section

variable {H : Type} {m : Type → Type} [Monad m] [LawfulMonad m] [Traits.Handler H m]

private theorem pattern_sim (version : Token.Version) :
    Simulates version (PatternParser.mk (H := H))
      (mapSteps Nodes.Pattern.intoOwned (PatternState.step (H := H) version))
      PatternParser.new := by
  refine ⟨fun _ _ => rfl, fun state token => ?_, fun _ => rfl, fun _ _ => rfl⟩
  show (do
      match ← state.step version token with
      | .more state => return Parser.Internal.Flow.more (PatternParser.mk state)
      | .done result => return .done result.intoOwned) = _
  rw [mapSteps, Functor.map_map, map_eq_pure_bind]
  refine bind_congr fun step => ?_
  cases step <;> rfl

omit [LawfulMonad m] in
private theorem pattern_hparse {Z : Type} [Produce Z] (p : PatternParser H) (s : ParseState H)
    (c : Z) : Parse.parse (m := m) p s c = Parser.Internal.parseByToken p s c := rfl

/-- The pattern parser from its start on the tokens of a valid pattern: it finishes with the
owned pattern of a view that is the pattern through the bridge, making no call. -/
theorem pattern_parses {version : Token.Version} (pattern : Tree.Pattern)
    (hvalid : pattern.Valid (Bridge.version version)) {tokens : List Parser.Internal.Input}
    (hs : Stands tokens pattern.tokens) :
    ∃ result : Nodes.Pattern, Bridge.pattern result = pattern ∧
      Finishes version (PatternParser.new (H := H)) tokens
        (pure result.intoOwned : PM H Nodes.PatternBuf) PatternParser.new := by
  obtain ⟨result, hresult, hruns⟩ :=
    BSmtLib.Facts.Proofs.Parser.Category.StepsPattern.pattern_runs (H := H)
      (points := noPoints) hvalid hs
  have := parses_of_runsS_map (state := PatternState.start) (program := pure result)
    (@pattern_hparse H m _ _) (pattern_sim version)
    ((RunsS.map_program (f := fun _ => result) hruns).congr (by simp [ticks_noPoints]) rfl)
  rw [map_pure] at this
  exact ⟨result, hresult, this⟩

private theorem pattern_rejects {version : Token.Version} {state last : PatternState}
    {tokens : List Parser.Internal.Input} {token : Parser.Internal.Input} {kind : SyntaxErrorKind}
    (hmoves : Moves (PatternState.step (H := H) version) state tokens last)
    (hfail : PatternState.step (H := H) version last token = throw (.syntax kind)) :
    Rejects version (PatternParser.mk (H := H) state) (tokens ++ [token]) (pure () : PM H Unit)
      kind :=
  rejects_of_movesS_map (@pattern_hparse H m _ _) (pattern_sim version) hmoves hfail

/-- The pattern parser on a first token that is neither `(` nor a symbol, nor the wildcard `_`
from 2.7 on; the error names the wildcard from 2.7 on. -/
theorem pattern_rejects_first {version : Token.Version} {token : Parser.Internal.Input}
    (hopen : token ≠ .parenOpen) (hsymbol : ∀ symbol, token ≠ .symbol symbol)
    (hwildcard : version ≥ .v2_7 → token ≠ .reserved (.general .underscore)) :
    Rejects version (PatternParser.new (H := H)) [token] (pure () : PM H Unit)
      (if version ≥ .v2_7 then .expectedSymbolUnderscoreOrParenOpen
        else .expectedSymbolOrParenOpen) := by
  have hnone : PatternState.symbolOrWildcard? version token = none := by
    cases token with
    | symbol s => exact absurd rfl (hsymbol s)
    | reserved word =>
      simp only [PatternState.symbolOrWildcard?, PatternState.wildcardAllowed]
      by_cases hv : version ≥ .v2_7
      · have hw := hwildcard hv
        have : (Parser.Internal.Input.reserved word).isWord .underscore = false := by
          cases word with
          | general w => cases w <;> first | exact absurd rfl hw | rfl
          | _ => rfl
        simp [this]
      · simp [hv]
    | _ => simp [PatternState.symbolOrWildcard?, Parser.Internal.Input.isWord]
  refine pattern_rejects (tokens := []) (.nil _) ?_
  cases token <;> first | exact absurd rfl hopen |
    simp_all [PatternState.step, PatternState.wildcardAllowed, Parser.Internal.syntaxError, apply_ite]

/-- The pattern parser on `(` and a token that is not a symbol. -/
theorem pattern_rejects_constructor {version : Token.Version} {token : Parser.Internal.Input}
    (htoken : ∀ symbol, token ≠ .symbol symbol) :
    Rejects version (PatternParser.new (H := H)) [.parenOpen, token] (pure () : PM H Unit)
      .expectedSymbol :=
  pattern_rejects (tokens := [.parenOpen])
    (.cons (middle := .opened) (by simp [PatternState.step]) (.nil _)) (by
      cases token <;> first | exact absurd rfl (htoken _) |
        simp [PatternState.step, Parser.Internal.syntaxError])

/-- The pattern parser on `(`, a constructor and `)`, a constructor pattern without
arguments. -/
theorem pattern_rejects_empty {version : Token.Version} (constructor : Plain.Symbol) :
    Rejects version (PatternParser.new (H := H)) [.parenOpen, .symbol constructor, .parenClose]
      (pure () : PM H Unit) .emptyPatternArguments :=
  pattern_rejects (tokens := [.parenOpen, .symbol constructor])
    (.cons (middle := .opened) (by simp [PatternState.step])
      (.cons (middle := .arguments constructor #[]) (by simp [PatternState.step]) (.nil _)))
    (by simp [PatternState.step, Parser.Internal.syntaxError])


/-- A token that is an argument of a constructor pattern in the version: a symbol, or the
wildcard `_` from 2.7 on. -/
def IsArgument (version : Token.Version) (token : Parser.Internal.Input) : Prop :=
  (∃ symbol, token = .symbol symbol) ∨
    (version ≥ .v2_7 ∧ token = .reserved (.general .underscore))

omit [LawfulMonad m] in
private theorem arguments_move {version : Token.Version} (constructor : Plain.Symbol) :
    (arguments : List Parser.Internal.Input) →
    (∀ argument ∈ arguments, IsArgument version argument) → (found : Array Nodes.SimplePattern) →
    ∃ found', Moves (PatternState.step (H := H) version) (.arguments constructor found) arguments
      (.arguments constructor found')
  | [], _, found => ⟨found, .nil _⟩
  | argument :: arguments, harguments, found => by
    rcases harguments argument (List.mem_cons_self ..) with ⟨name, rfl⟩ | ⟨hversion, rfl⟩
    · obtain ⟨found', hmoves⟩ := arguments_move constructor arguments
        (fun a ha => harguments a (List.mem_cons_of_mem _ ha)) (found.push (.symbol name))
      exact ⟨found', .cons (by simp [PatternState.step, PatternState.symbolOrWildcard?]) hmoves⟩
    · obtain ⟨found', hmoves⟩ := arguments_move constructor arguments
        (fun a ha => harguments a (List.mem_cons_of_mem _ ha)) (found.push .wildcard)
      refine ⟨found', .cons ?_ hmoves⟩
      have hw : (Parser.Internal.Input.reserved (.general .underscore)).isWord .underscore =
        true := rfl
      simp [PatternState.step, PatternState.symbolOrWildcard?, PatternState.wildcardAllowed,
        hversion, hw]

/-- The pattern parser on `(`, a constructor, arguments of the version and a token that is
neither an argument of the version nor `)`; the error names the wildcard from 2.7 on. -/
theorem pattern_rejects_argument {version : Token.Version} (constructor : Plain.Symbol)
    {arguments : List Parser.Internal.Input}
    (harguments : ∀ argument ∈ arguments, IsArgument version argument)
    {token : Parser.Internal.Input} (htoken : ¬ IsArgument version token)
    (hclose : token ≠ .parenClose) :
    Rejects version (PatternParser.new (H := H))
      ([.parenOpen, .symbol constructor] ++ arguments ++ [token]) (pure () : PM H Unit)
      (if version ≥ .v2_7 then .expectedSymbolOrUnderscore else .expectedSymbol) := by
  obtain ⟨found, hmoves⟩ :=
    arguments_move (H := H) (version := version) constructor arguments harguments #[]
  refine pattern_rejects (.cons (middle := .opened) (by simp [PatternState.step])
    (.cons (middle := .arguments constructor #[]) (by simp [PatternState.step]) hmoves)) ?_
  simp only [IsArgument, not_or, not_and, not_exists] at htoken
  have hnone : PatternState.symbolOrWildcard? version token = none := by
    cases token with
    | symbol s => exact absurd rfl (htoken.1 s)
    | reserved word =>
      simp only [PatternState.symbolOrWildcard?, PatternState.wildcardAllowed]
      by_cases hv : version ≥ .v2_7
      · have hw := htoken.2 hv
        have : (Parser.Internal.Input.reserved word).isWord .underscore = false := by
          cases word with
          | general w => cases w <;> first | exact absurd rfl hw | rfl
          | _ => rfl
        simp [this]
      · simp [hv]
    | _ => simp [PatternState.symbolOrWildcard?, Parser.Internal.Input.isWord]
  cases token <;> first | exact absurd rfl hclose |
    simp_all [PatternState.step, PatternState.wildcardAllowed, Parser.Internal.syntaxError, apply_ite]

end

end BSmtLib.Facts.Proofs.Parser.Category.Pattern
