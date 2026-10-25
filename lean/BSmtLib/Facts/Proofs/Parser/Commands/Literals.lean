module

public import BSmtLib.Facts.Proofs.Parser.Commands.Terms
import all BSmtLib.Parser.Category.Term
import all BSmtLib.Parser.Command.Internal.Standard

@[expose] public section

/-!
# Propositional literals against the traversal

In 2.5 and 2.6, `check-sat-assuming` takes propositional literals, ⟨symbol⟩ |
`(` `not` ⟨symbol⟩ `)`. The literal parser checks each token against the shape of a literal and
hands it to the term parser, which handles the literal as the term it is written as. The tokens
of a literal are few and fixed, so the lemma follows the term parser token by token.
-/

namespace BSmtLib.Facts.Proofs.Parser.Commands.Literals

open BSmtLibSpec.Grammar
open BSmtLib.Parser.Command.Internal.Standard (Payload FinalCall payloadStep finalCall LiteralState
    LiteralShape literalStep)
open BSmtLib.Parser.Command (CommandOutcome)
open BSmtLib.Parser.Category.Combinator.Internal (ListState)
open BSmtLib.Parser.Category.Term.Internal (termStep TermState TermLevel)
open BSmtLib.Facts.Parser.Adapters.Bridge BSmtLib.Facts.Parser.Adapters.Run
open BSmtLib.Facts.Proofs.Parser.Commands.Bytes BSmtLib.Facts.Proofs.Parser.Commands.Elements
open BSmtLib.Facts.Proofs.Parser.Commands.Frame BSmtLib.Facts.Proofs.Parser.Commands.Simple
open BSmtLib.Facts.Proofs.Parser.Drive BSmtLib.Facts.Proofs.Parser.Lemmas
open BSmtLib.Facts.Proofs.Parser.Tokens

open BSmtLibSpec.Parser
open BSmtLibSpec.Parser.Traversal
open BSmtLibSpec.Facts.Proofs.Parser (Program.callUnit)
open BSmtLibSpec.Facts.Proofs.Parser.Equations (term_identifier term_application)

section

variable {H : Type} {m : Type → Type} [Monad m] [LawfulMonad m] [Traits.Handler H m]
variable {points : Points (StateT H m)} {version : Token.Version}
variable {h : Traversal.Handler (StateT H m) (Traits.Handler.Error H) (valuesOf H)}

theorem asTerm_valid (literal : Tree.PropLiteral) (v : BSmtLibSpec.Lexicon.Version) :
    literal.asTerm.Valid v := by
  cases literal with
  | positive symbol =>
    simp [Tree.PropLiteral.asTerm, Tree.Term.Valid, Tree.QualIdentifier.Valid,
      Tree.Identifier.Valid]
  | negative negation symbol =>
    simp [Tree.PropLiteral.asTerm, Tree.Term.Valid, Tree.QualIdentifier.Valid,
      Tree.Identifier.Valid, Tree.Term.ValidAll]

theorem terms_map_asTerm (literals : List Tree.PropLiteral) :
    Traversal.terms points h (literals.map Tree.PropLiteral.asTerm) =
      literals.mapM fun literal => Traversal.term points h literal.asTerm := by
  induction literals with
  | nil => rfl
  | cons literal literals ih => simp [Traversal.terms, ih]

/-- The literal parser reads a literal, as the term it is written as. -/
theorem literal_element (hA : TermAgrees h) :
    ElementRuns points (literalStep version) LiteralState.init Tree.PropLiteral.tokens
      Tree.PropLiteral.Valid
      (fun literal => adaptRun (Traversal.term points h literal.asTerm)) id := by
  intro literal hvalid tokens hs
  cases literal with
  | positive name =>
    obtain ⟨token, rfl, htoken⟩ := Stands.split_single hs
    obtain ⟨symbol, rfl, rfl⟩ := Parser.Internal.Input.received_symbol htoken
    refine ⟨⟨_, [], rfl, by simp⟩, do
        tick points (.symbol symbol)
        Parser.Internal.call (Traits.Handler.handleTerm (.qualifiedIdent ⟨symbol, #[]⟩ none)), ?_,
      Runs.token (by simp [literalStep, LiteralState.init, TermState.init, termStep,
        Parser.Category.Term.Internal.termComplete])⟩
    simp [Tree.PropLiteral.asTerm, term_identifier, qualIdentifier, takeAll,
      Tree.Identifier.tokens, adaptRun_take htoken, hA.handleTerm, Bridge.termNode,
      Bridge.identifier]
  | negative negation name =>
    obtain ⟨inner, rfl, hinner⟩ := Stands.split_paren hs
    obtain ⟨negationToken, rest, rfl, hnegationToken, hrest⟩ := Stands.split_cons hinner
    obtain ⟨nameToken, rfl, hnameToken⟩ := Stands.split_single hrest
    obtain ⟨notSymbol, rfl, rfl⟩ := Parser.Internal.Input.received_symbol hnegationToken
    obtain ⟨symbol, rfl, rfl⟩ := Parser.Internal.Input.received_symbol hnameToken
    have hnot := Symbol.isNot_of_name hvalid
    let function : Nodes.Ident := ⟨notSymbol, #[]⟩
    refine ⟨⟨_, _, rfl, by simp⟩, do
        tick points .parenOpen
        tick points (.symbol notSymbol)
        tick points (.symbol symbol)
        let t ← Parser.Internal.call
          (Traits.Handler.handleTerm (.qualifiedIdent ⟨symbol, #[]⟩ none))
        tick points .parenClose
        Parser.Internal.call
          (Traits.Handler.handleTerm (.application function none (.new #[t])
            (Multiple.len_pos_new (by simp)))), ?_, ?_⟩
    · simp [Tree.PropLiteral.asTerm, term_application, term_identifier, qualIdentifier, takeAll,
        Traversal.terms, Tree.Identifier.tokens, adaptRun_take hnameToken,
        adaptRun_take hnegationToken, adaptRun_take (token := .parenOpen) rfl,
        adaptRun_take (token := .parenClose) rfl, hA.handleTerm, Bridge.termNode,
        Bridge.identifier, function]
    rw [show Parser.Internal.Input.parenOpen :: ([.symbol notSymbol,
        .symbol symbol] ++ [.parenClose]) =
      [.parenOpen] ++ ([.symbol notSymbol] ++ ([.symbol symbol] ++ [.parenClose])) by rfl]
    refine (Runs.append (middle := fun _ =>
        (⟨.negation, ⟨.opened, []⟩⟩ : Parser.Command.Internal.Standard.LiteralStateOf H))
      (Runs.token_more (by simp [literalStep, LiteralState.init, TermState.init, termStep]))
      fun _ => Runs.append (middle := fun _ =>
        (⟨.negated, ⟨.start, [TermLevel.application function none #[]]⟩⟩ :
          Parser.Command.Internal.Standard.LiteralStateOf H))
      (Runs.token_more (by simp [literalStep, hnot, termStep,
          Parser.Category.Term.Internal.termOpened,
          function]))
      fun _ => Runs.append (middle := fun t =>
        (⟨.close, ⟨.start, [TermLevel.application function none #[t]]⟩⟩ :
          Parser.Command.Internal.Standard.LiteralStateOf H))
      (Runs.token (program := Parser.Internal.call (Traits.Handler.handleTerm
        (.qualifiedIdent ⟨symbol, #[]⟩ none)))
        (by simp [literalStep, termStep, Parser.Category.Term.Internal.termComplete]))
      fun t => Runs.token (program := Parser.Internal.call (Traits.Handler.handleTerm
        (.application function none (.new #[t]) (Multiple.len_pos_new (by simp)))))
        (by simp [literalStep, termStep, Parser.Category.Term.Internal.termComplete])).congr ?_ rfl
    simp

end

section

variable {H : Type} {m : Type → Type} [Monad m] [LawfulMonad m] [Traits.CommandHandler H m]
variable {points : Points (StateT H m)} {version : Token.Version}
variable {h : Traversal.Handler (StateT H m) (Traits.Handler.Error H) (valuesOf H)}

theorem checkSatAssumingLiterals_payload (hA : Agrees h) (literals : List Tree.PropLiteral)
    (hversion : ¬ versionAtLeast (Bridge.version version) .v2_7)
    (hvalid : ∀ literal ∈ literals, literal.Valid) {payload : List Parser.Internal.Input}
    (hs : Stands payload (paren (literals.flatMap Tree.PropLiteral.tokens))) :
    PayloadRuns points version (Payload.init .checkSatAssuming version)
      (payload ++ [.parenClose])
      (adaptRun (do
        take points .parenOpen
        let handled ← Traversal.terms points h (literals.map Tree.PropLiteral.asTerm)
        takeAll points [.parenClose, .parenClose]
        Program.callUnit h (.commandCheckSatAssuming handled)))
      fun _ => pure (.done .command) := by
  have hinit : (Payload.init .checkSatAssuming version : Parser.Command.Internal.Standard.PayloadOf
      H) =
      .checkSatAssumingLiterals (ListState.paren LiteralState.init) := by
    have : ¬ version ≥ .v2_7 := fun hge => hversion (versionAtLeast_v2_7_of_ge hge)
    simp [Payload.init, this]
  rw [hinit]
  obtain ⟨inner, rfl, hinner⟩ := Stands.split_paren hs
  obtain ⟨program, hprogram, -, hlistRuns⟩ := parenList_runs (maximum := none)
    (literal_element (points := points) (version := version) hA.toTermAgrees) literals hvalid
    hinner (by simp)
  have hlistPayload := (Runs.embedA (outer := payloadStep version)
      (outerArrival := Parser.Command.Internal.Standard.payloadArrive)
    Payload.checkSatAssumingLiterals
    (fun assumptions => pure (.more (.closing (.checkSatAssuming assumptions))))
    (by payload_step) hlistRuns).congr rfl
    (next' := fun l => pure (.more (.closing (.checkSatAssuming (l : List _).toArray))))
    (by funext; simp [Parser.Internal.Step.wrap])
  refine (Runs.append (middle := fun l => .closing (.checkSatAssuming (l : List _).toArray))
    hlistPayload fun l => closing_runs (h := h)
      (request := .commandCheckSatAssuming l) (.checkSatAssuming l.toArray)
      (by simp [finalCall, hA.commandCheckSatAssuming]) rfl).congr ?_ rfl
  simp only [List.map_id_fun, id_map] at hprogram
  simp [takeAll, terms_map_asTerm, adaptRun_mapM, ← hprogram,
    adaptRun_take (token := .parenOpen) rfl, adaptRun_take (token := .parenClose) rfl]

end

end BSmtLib.Facts.Proofs.Parser.Commands.Literals
