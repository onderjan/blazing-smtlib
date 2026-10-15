module

public import BSmtLib.Facts.Proofs.Parser.Reserved
import all BSmtLib.Parser.Category.SExpr

@[expose] public section

/-!
# The s-expression parser against the traversal

The s-expression parser keeps a stack of open lists, the items of each so far. Its lemma is
stated for every stack: from the stack, the parser reads the tokens of an s-expression with the
traversal's effects, and the s-expression goes where the parser puts a complete one
(`sExprComplete`): it is the result on the empty stack, the next item of the innermost list
otherwise. The items of a list are read from the stack with that list on top, and leave it
with the items appended. The two lemmas go by recursion over the tree.

This is the template of the stack parsers (sorts, terms): a lemma for every stack, whose
continuation is the parser's own "a value is complete" step, and one for the items of a level
on top of the stack.
-/

namespace BSmtLib.Facts.Proofs.Parser.SExpr

open BSmtLibSpec.Grammar
open BSmtLib.Parser (PM)
open BSmtLib.Parser.Category.SExpr (SExprState sExprStep sExprComplete)
open BSmtLibSpec.Parser
open BSmtLibSpec.Parser.Traversal
open BSmtLibSpec.Facts.Proofs.Parser.Equations (sExpr_constant sExpr_symbol sExpr_reserved
    sExpr_keyword sExpr_list)
open BSmtLib.Facts.Parser.Adapters.Bridge BSmtLib.Facts.Parser.Adapters.Run
open BSmtLib.Facts.Proofs.Parser.Drive BSmtLib.Facts.Proofs.Parser.Lemmas
open BSmtLib.Facts.Proofs.Parser.Tokens

section

variable {version : Token.Version}

theorem versionAtLeast_v2_5 (h : versionAtLeast (Bridge.version version) .v2_5) :
    version ≥ .v2_5 := by
  cases version <;> simp_all [versionAtLeast, Bridge.version, BSmtLibSpec.Lexicon.Version.upTo] <;>
    decide

theorem versionAtLeast_v2_6 (h : versionAtLeast (Bridge.version version) .v2_6) :
    version ≥ .v2_6 := by
  cases version <;> simp_all [versionAtLeast, Bridge.version, BSmtLibSpec.Lexicon.Version.upTo] <;>
    decide

theorem versionAtLeast_v2_7 (h : versionAtLeast (Bridge.version version) .v2_7) :
    version ≥ .v2_7 := by
  cases version <;> simp_all [versionAtLeast, Bridge.version, BSmtLibSpec.Lexicon.Version.upTo] <;>
    decide

end

section

variable {H : Type} {m : Type → Type} [Monad m] [LawfulMonad m] [Traits.Handler H m]
variable {points : Points (StateT H m)}
variable {h : Traversal.Handler (StateT H m) (Traits.Handler.Error H) (valuesOf H)}
variable {version : Token.Version}

/-- An atom of an s-expression: the parser handles it at its token, then completes it. -/
theorem sExprStep_atom (levels : SExprState (Traits.Handler.SExpr H))
    (token : Parser.Internal.Input)
    (node : Nodes.SExprNode (Traits.Handler.SExpr H))
    (hstep : sExprStep version levels token =
      Parser.call (Traits.Handler.handleSExpr node) >>= fun r => pure (sExprComplete levels r)) :
    Runs points (sExprStep version) levels [token]
      (do tick points token; Parser.call (Traits.Handler.handleSExpr node))
      fun r => pure (sExprComplete levels r) :=
  Runs.token hstep


mutual

/--
From any stack, the parser reads the tokens of an s-expression with the traversal's effects,
then completes the s-expression on that stack.
-/
theorem sExpr_runs (hA : TermAgrees h) : (item : Tree.SExpr) → item.Valid (Bridge.version version) →
    ∀ {tokens : List Parser.Internal.Input}, Stands tokens item.tokens →
    ∀ levels : SExprState (Traits.Handler.SExpr H),
    Runs points (sExprStep version) levels tokens
      (adaptRun (Traversal.sExpr points h item))
      fun r => pure (sExprComplete levels r)
  | .constant constant, _, _, hs, levels => by
    obtain ⟨constant', rfl, rfl⟩ := Stands.constant hs
    refine (sExprStep_atom levels _ (.constant constant') (by simp [sExprStep])).congr ?_ rfl
    simp [sExpr_constant, adaptRun_take (token := .constant constant')
      (by rfl), hA.handleSExpr, Bridge.sExprNode]
  | .symbol name, _, _, hs, levels => by
    obtain ⟨token, rfl, htoken⟩ := Stands.split_single hs
    obtain ⟨symbol, rfl, rfl⟩ := Parser.Internal.Input.received_symbol htoken
    refine (sExprStep_atom levels _ (.symbol symbol) (by simp [sExprStep])).congr ?_ rfl
    simp [sExpr_symbol, adaptRun_take htoken,
      hA.handleSExpr, Bridge.sExprNode]
  | .reserved word, hversion, _, hs, levels => by
    obtain ⟨token, rfl, htoken⟩ := Stands.split_single hs
    obtain ⟨reserved, rfl, rfl⟩ := Parser.Internal.Input.received_reserved htoken
    refine (sExprStep_atom levels _ (.reserved reserved)
      (by simp [sExprStep, versionAtLeast_v2_6 hversion.1])).congr ?_ rfl
    simp [sExpr_reserved, adaptRun_take htoken,
      hA.handleSExpr, Bridge.sExprNode]
  | .keyword name, _, _, hs, levels => by
    obtain ⟨token, rfl, htoken⟩ := Stands.split_single hs
    obtain ⟨keyword, rfl, rfl⟩ := Parser.Internal.Input.received_keyword htoken
    refine (sExprStep_atom levels _ (.keyword keyword) (by simp [sExprStep])).congr ?_ rfl
    simp [sExpr_keyword, adaptRun_take htoken,
      hA.handleSExpr, Bridge.sExprNode]
  | .list items, hvalid, _, hs, levels => by
    obtain ⟨inner, rfl, hinner⟩ := Stands.split_paren hs
    have hopen : Runs points (sExprStep version) levels [.parenOpen]
        (do tick points .parenOpen; pure ()) fun _ => pure (.more (#[] :: levels)) :=
      Runs.token (by simp [sExprStep])
    have hclose : ∀ items : Array (Traits.Handler.SExpr H),
        Runs points (sExprStep version) (items :: levels) [.parenClose]
          (do tick points .parenClose; Parser.call (Traits.Handler.handleSExpr (.list items)))
          fun r => pure (sExprComplete levels r) :=
      fun items => Runs.token (by simp [sExprStep])
    refine (Runs.append hopen fun _ =>
      Runs.append (sExprs_runs hA items hvalid hinner #[] levels) fun items =>
        hclose _).congr ?_ rfl
    simp [sExpr_list,
      adaptRun_take (token := .parenOpen) rfl, adaptRun_take (token := .parenClose) rfl,
      hA.handleSExpr, Bridge.sExprNode]

/--
From a stack whose innermost list has the items so far, the parser reads the tokens of
s-expressions with the traversal's effects, and appends them to that list.
-/
theorem sExprs_runs (hA : TermAgrees h) : (items : List Tree.SExpr) →
    Tree.SExpr.ValidAll (Bridge.version version) items →
    ∀ {tokens : List Parser.Internal.Input}, Stands tokens (Tree.SExpr.tokensAll items) →
    ∀ (found : Array (Traits.Handler.SExpr H)) (levels : SExprState (Traits.Handler.SExpr H)),
    Runs points (sExprStep version) (found :: levels) tokens
      (adaptRun (Traversal.sExprs points h items))
      fun handled => pure (.more ((found ++ handled.toArray) :: levels))
  | [], _, _, hs, found, levels => by
    have := Stands.eq_nil hs
    subst this
    exact (Runs.nil [] (by simp)).congr (by simp [Traversal.sExprs]) rfl
  | first :: rest, hvalid, _, hs, found, levels => by
    obtain ⟨tokens₁, tokens₂, rfl, hs₁, hs₂⟩ := Stands.split hs
    have htail : ∀ r, Runs points (sExprStep version) (found.push r :: levels) tokens₂
        ((r :: ·) <$> adaptRun (Traversal.sExprs points h rest))
        fun handled => pure (.more ((found ++ handled.toArray) :: levels)) := fun r =>
      Runs.map_program ((sExprs_runs hA rest hvalid.2 hs₂ (found.push r) levels).congr rfl
        (by funext handled; simp))
    refine (Runs.append (middle := fun r => found.push r :: levels)
      (sExpr_runs hA first hvalid.1 hs₁ _) htail).congr ?_ rfl
    simp [Traversal.sExprs]

end

end

end BSmtLib.Facts.Proofs.Parser.SExpr
