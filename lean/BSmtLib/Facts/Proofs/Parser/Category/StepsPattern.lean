module

public import BSmtLib.Facts.Proofs.Parser.Category.CursorS
public import BSmtLib.Facts.Proofs.Parser.TermParts
import all BSmtLib.Parser
import all BSmtLib.Parser.Category.Pattern
import all BSmtLib.Token.Reserved

@[expose] public section

/-!
# The pattern parser's steps, keeping where they stop

The lemmas of the patterns in `Facts.Proofs.Parser.TermParts`, for `RunsS`.
-/

namespace BSmtLib.Facts.Proofs.Parser.Category.StepsPattern

open BSmtLibSpec.Grammar
open BSmtLib.Parser.Internal (PM)
open BSmtLib.Parser.Category.Pattern.Internal (PatternState)
open BSmtLib.Facts.Parser.Adapters.Bridge BSmtLib.Facts.Parser.Adapters.Run
open BSmtLib.Facts.Proofs.Parser.Drive BSmtLib.Facts.Proofs.Parser.Lemmas
open BSmtLib.Facts.Proofs.Parser.Reserved
open BSmtLib.Facts.Proofs.Parser.Tokens BSmtLib.Facts.Proofs.Parser.Tokens.Stands
open BSmtLib.Facts.Proofs.Parser.Category.Steps
open BSmtLib.Facts.Proofs.Parser.TermParts (symbolOrWildcard_runs)

open BSmtLibSpec.Parser
open BSmtLibSpec.Parser.Traversal

section

variable {H : Type} {m : Type → Type} [Monad m] [LawfulMonad m] [Traits.Handler H m]
variable {points : Points (StateT H m)} {version : Token.Version}


/-- The arguments of a constructor pattern, appended to those found so far. -/
theorem patternArguments_runs : (arguments : List Tree.SymbolOrWildcard) →
    (∀ argument ∈ arguments, argument.Valid (Bridge.version version)) →
    ∀ {tokens : List Parser.Internal.Input},
        Stands tokens (arguments.map Tree.SymbolOrWildcard.token) →
    ∀ (constructor : Plain.Symbol) (found : Array Nodes.SimplePattern),
    ∃ parsed : Array Nodes.SimplePattern,
      parsed.toList.map Bridge.symbolOrWildcard = arguments ∧
      RunsS points (PatternState.step (H := H) version) (.arguments constructor found) tokens
        (ticks points tokens) fun _ => pure (.more (.arguments constructor (found ++ parsed)))
  | [], _, _, hs, constructor, found => by
    have := Stands.eq_nil hs
    subst this
    exact ⟨#[], rfl, (RunsS.nil () (by simp)).congr (by simp) rfl⟩
  | first :: rest, hvalid, _, hs, constructor, found => by
    obtain ⟨token, tokens, rfl, htoken, hrest⟩ := Stands.split_cons hs
    obtain ⟨parsed, hparsed, hfirst, hne⟩ := symbolOrWildcard_runs
      (hvalid first (List.mem_cons_self ..)) htoken
    obtain ⟨others, hothers, hruns⟩ := patternArguments_runs rest
      (fun a ha => hvalid a (List.mem_cons_of_mem _ ha)) hrest constructor (found.push parsed)
    refine ⟨#[parsed] ++ others, by simp [hothers, hfirst], ?_⟩
    rw [show token :: tokens = [token] ++ tokens by rfl]
    refine (RunsS.append (middle := fun _ => .arguments constructor (found.push parsed))
      (RunsS.token_more (by
        cases token <;> simp_all [PatternState.step])) fun _ => hruns).congr ?_ ?_
    · simp
    · funext
      simp

/-- From its start, the pattern parser reads a pattern and ends with it. -/
theorem pattern_runs {pattern : Tree.Pattern} (hvalid : pattern.Valid (Bridge.version version))
    {tokens : List Parser.Internal.Input} (hs : Stands tokens pattern.tokens) :
    ∃ parsed : Nodes.Pattern, Bridge.pattern parsed = pattern ∧
      RunsS points (PatternState.step (H := H) version) .start tokens (ticks points tokens)
        fun _ => pure (.done parsed) := by
  cases pattern with
  | single item =>
    obtain ⟨token, rfl, htoken⟩ := Stands.split_single hs
    obtain ⟨parsed, hparsed, hitem, hne⟩ := symbolOrWildcard_runs hvalid htoken
    refine ⟨.simple parsed, by simp [Bridge.pattern, hitem], ?_⟩
    refine (RunsS.token (program := pure ()) ?_).congr (by simp) rfl
    cases token <;> simp_all [PatternState.step, PatternState.symbolOrWildcard?,
        Parser.Internal.Input.isWord]
  | constructor name arguments =>
    obtain ⟨inner, rfl, hinner⟩ := Stands.split_paren hs
    obtain ⟨symbolToken, argumentTokens, rfl, hsymbol, hargumentTokens⟩ :=
      Stands.split_cons hinner
    obtain ⟨symbol, rfl, rfl⟩ := Parser.Internal.Input.received_symbol hsymbol
    obtain ⟨parsed, hmap, hruns⟩ := patternArguments_runs (H := H) (points := points) arguments
      hvalid.2 hargumentTokens symbol #[]
    have hparsed : parsed.isEmpty = false := by
      cases parsed using Array.recOn with
      | mk list => cases list <;> simp_all [Tree.Pattern.Valid]
    have hpos : 0 < (#[] ++ parsed).size :=
      Nodes.PatternApplication.Internal.size_pos (by simp [hparsed])
    refine ⟨.application ⟨symbol, #[] ++ parsed, hpos⟩, by simp [Bridge.pattern, hmap], ?_⟩
    have hclose : RunsS points (PatternState.step (H := H) version)
        (.arguments symbol (#[] ++ parsed)) [.parenClose] (do tick points .parenClose; pure ())
        fun _ => pure (.done (.application ⟨symbol, #[] ++ parsed, hpos⟩)) :=
      RunsS.token (by simp [PatternState.step, hparsed])
    rw [show Parser.Internal.Input.parenOpen ::
        (Parser.Internal.Input.symbol symbol :: argumentTokens ++ [.parenClose]) =
      [.parenOpen] ++ ([.symbol symbol] ++ (argumentTokens ++ [.parenClose])) by simp]
    refine (RunsS.append (middle := fun _ => PatternState.opened)
      (RunsS.token_more (by simp [PatternState.step])) fun _ =>
        RunsS.append (middle := fun _ => PatternState.arguments symbol #[])
          (RunsS.token_more (by simp [PatternState.step])) fun _ =>
            RunsS.append hruns fun _ => hclose).congr ?_ rfl
    simp [ticks_append]

end

end BSmtLib.Facts.Proofs.Parser.Category.StepsPattern
