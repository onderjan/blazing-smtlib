module

public import BSmtLib.Facts.Proofs.Parser.Category.SortedVar
import all BSmtLib.Parser
import all BSmtLib.Parser.Category.Token
import all BSmtLib.Parser.Category.Ident
import all BSmtLib.Parser.Category.Sort
import all BSmtLib.Parser.Category.QualifiedIdent
import all BSmtLib.Token.Reserved

@[expose] public section

/-!
# The qualified identifier parser on a cursor

The qualified identifier parser runs the identifier parser and the sort parser inside its
states; their lemmas are taken over by `RunsS.embed`. The parser's own step turns the identifier
and the sort into a `Nodes.QualifiedIdent`, taken over by `RunsS.embed` with no wrapping.
-/

namespace BSmtLib.Facts.Proofs.Parser.Category.QualifiedIdent

open BSmtLibSpec.Grammar
open BSmtLibSpec.Parser
open BSmtLibSpec.Parser.Traversal
open BSmtLib.Token (Produce)
open BSmtLib.Parser (Parse ParseState SyntaxErrorKind)
open BSmtLib.Parser.Internal (PM)
open BSmtLib.Parser.Category.QualifiedIdent BSmtLib.Parser.Category.Ident
open BSmtLib.Parser.Category.QualifiedIdent.Internal
open BSmtLib.Parser.Category.Ident.Internal
open BSmtLib.Parser.Category.QualifiedIdent.Internal
open BSmtLib.Parser.Category.Ident.Internal
open BSmtLib.Parser.Category.Sort
open BSmtLib.Parser.Category.Sort.Internal
open BSmtLib.Facts.Parser.Adapters.Bridge BSmtLib.Facts.Parser.Adapters.Run
open BSmtLib.Facts.Parser.Adapters.Cursor (Takes Reads noPoints)
open BSmtLib.Facts.Parser.Adapters.Outcome (Finishes Rejects)
open BSmtLib.Facts.Proofs.Parser.Category.Cursor (Simulates Moves tick_noPoints flowOf)
open BSmtLib.Facts.Proofs.Parser.Category.Ident
open BSmtLib.Facts.Proofs.Parser.Category.Steps BSmtLib.Facts.Proofs.Parser.Category.CursorS
open BSmtLib.Facts.Proofs.Parser.Drive BSmtLib.Facts.Proofs.Parser.Tokens
open BSmtLib.Facts.Proofs.Parser.Tokens.Stands BSmtLib.Facts.Proofs.Parser.Reserved

section

variable {m : Type → Type} [Monad m] [LawfulMonad m] {ε : Type} {values : Values}

@[simp]
theorem take_noPoints (token : SyntaxToken) :
    take (noPoints : Points m) token = (pure () : Run m ε Unit) := by
  simp [take, receive, noPoints, ExceptT.lift_pure]

@[simp]
theorem takeAll_noPoints (tokens : List SyntaxToken) :
    takeAll (noPoints : Points m) tokens = (pure () : Run m ε Unit) := by
  induction tokens with
  | nil => rfl
  | cons token tokens ih =>
    simp only [takeAll] at ih ⊢
    simpa using ih

end

section

variable {H : Type} {m : Type → Type} [Monad m] [LawfulMonad m] [Traits.Handler H m]

/-- The steps of the qualified identifier parser, its result a `Nodes.QualifiedIdent`. -/
def qualStep (version : Token.Version) (state : QualIdentState (Traits.Handler.«Sort» H))
    (token : Parser.Internal.Input) :
    PM H (Parser.Internal.Step (QualIdentState (Traits.Handler.«Sort» H))
      (Nodes.QualifiedIdent (Traits.Handler.«Sort» H))) := do
  match ← qualIdentStep version state token with
  | .more state => return .more state
  | .done (identifier, sort) =>
    return .done ({ ident := identifier, sort } : Nodes.QualifiedIdent _)

/-- The owned value of what `qualStep` gives. -/
abbrev ownQualified (qualified : Nodes.QualifiedIdent (Traits.Handler.«Sort» H)) :
    Nodes.QualifiedIdentBuf (Traits.Handler.«Sort» H) :=
  { ident := qualified.ident.intoOwned, sort := qualified.sort }

private theorem qualifiedIdent_sim (version : Token.Version) :
    Simulates version (QualifiedIdentParser.mk (H := H)) (mapSteps ownQualified (qualStep version))
      QualifiedIdentParser.new := by
  refine ⟨fun _ _ => rfl, fun state token => ?_, fun _ => rfl, fun _ _ => rfl⟩
  show (do
      match ← qualIdentStep version state token with
      | .more state => return Parser.Internal.Flow.more (QualifiedIdentParser.mk state)
      | .done (identifier, sort) =>
        return .done ({ ident := identifier.intoOwned, sort } : Nodes.QualifiedIdentBuf _))
    = _
  simp only [mapSteps, qualStep, map_bind]
  refine bind_congr fun step => ?_
  rcases step with state | ⟨identifier, sort⟩ <;> simp [flowOf, mapDone]

/-- A run of `qualIdentStep` that ends the parser is one of `qualStep`, its result made a
qualified identifier. -/
theorem runs_qualStep {version : Token.Version} {state : QualIdentState (Traits.Handler.«Sort» H)}
    {tokens : List Parser.Internal.Input} {α : Type} {program : PM H α}
    {result : α → Nodes.Ident × Option (Traits.Handler.«Sort» H)}
    (h : RunsS noPoints (qualIdentStep version) state tokens program
      fun a => pure (.done (result a))) :
    RunsS noPoints (qualStep version) state tokens program
      fun a => pure (.done { ident := (result a).1, sort := (result a).2 }) :=
  (RunsS.embed (outer := qualStep version) id
    (fun (identifier, sort) => pure (.done { ident := identifier, sort }))
    (fun state token => by
      simp only [qualStep]
      congr 1
      funext step
      rcases step with state | ⟨identifier, sort⟩ <;> rfl) h).congr rfl (by
        funext a
        simp [Parser.Internal.Step.wrap])

theorem qualIdentifier_plain {h : Traversal.Handler (StateT H m) (Traits.Handler.Error H)
    (valuesOf H)} (identifier : Tree.Identifier) :
    adaptRun (Traversal.qualIdentifier noPoints h (.plain identifier)) =
      pure (identifier, none) := by
  simp [Traversal.qualIdentifier]

theorem qualIdentifier_as {h : Traversal.Handler (StateT H m) (Traits.Handler.Error H)
    (valuesOf H)} (identifier : Tree.Identifier) (sort : Tree.«Sort») :
    adaptRun (Traversal.qualIdentifier noPoints h (.as identifier sort)) =
      (fun handled => (identifier, some handled)) <$> adaptRun (Traversal.sort noPoints h sort) := by
  simp [Traversal.qualIdentifier, bind_pure_comp]

/-- From its start, the qualified identifier parser's steps read the tokens of a valid
identifier, unqualified, with no call, and end with it, through the bridge. -/
theorem qualifiedIdent_runs_plain {version : Token.Version} (identifier : Tree.Identifier)
    (hvalid : identifier.Valid (Bridge.version version)) {tokens : List Parser.Internal.Input}
    (hs : Stands tokens identifier.tokens) :
    ∃ result : Nodes.Ident,
      (RunsS noPoints (qualIdentStep (H := H) version) .start tokens
        (pure (identifier, (none : Option (Traits.Handler.«Sort» H))))
        fun r => pure (.done (result, r.2))) ∧
      Bridge.identifier result = identifier := by
  match identifier with
  | ⟨name, []⟩ =>
    obtain ⟨token, rfl, htoken⟩ := Stands.split_single hs
    obtain ⟨symbol, rfl, rfl⟩ := Parser.Internal.Input.received_symbol htoken
    refine ⟨⟨symbol, #[]⟩, ?_, by simp [Bridge.identifier]⟩
    exact (RunsS.token (next := fun result => pure (.done (⟨symbol, #[]⟩, result.2)))
      (program := pure ((⟨Bridge.symbol symbol, []⟩ : Tree.Identifier),
        (none : Option (Traits.Handler.«Sort» H))))
      (by simp [qualIdentStep])).congr (by simp) rfl
  | ⟨name, index :: indices⟩ =>
    obtain ⟨symbolToken, rest, rfl, hsymbol, hrest⟩ :=
      BSmtLib.Facts.Proofs.Parser.«Sort».Stands.indexed (List.cons_ne_nil _ _) hs
    obtain ⟨head, hhead, hruns⟩ :=
      BSmtLib.Facts.Proofs.Parser.Category.StepsSort.indexed_runs (H := H)
      (points := noPoints) (version := version) hvalid (List.cons_ne_nil _ _) hsymbol hrest
    refine ⟨head, ?_, hhead⟩
    have hembed := (RunsS.embed (outer := qualIdentStep (H := H) version)
      (fun state => QualIdentState.indexed state)
      (fun identifier => pure (.done (identifier, none)))
      (fun state token => by
        simp only [qualIdentStep]
        congr 1
        funext step
        cases step <;> rfl) hruns).congr rfl (next' := fun _ => pure (.done (head, none))) (by
          funext
          simp [Parser.Internal.Step.wrap])
    have hmapped := RunsS.map_program
      (f := fun _ => ((⟨name, index :: indices⟩ : Tree.Identifier),
        (none : Option (Traits.Handler.«Sort» H))))
      (next := fun result => pure (.done (head, result.2))) hembed
    rw [show Parser.Internal.Input.parenOpen :: Parser.Internal.Input.reserved
        (.general .underscore) :: symbolToken :: (rest ++ [.parenClose]) =
      [.parenOpen] ++ ([.reserved (.general .underscore)] ++
        (symbolToken :: (rest ++ [.parenClose]))) by rfl]
    refine (RunsS.append (middle := fun _ => QualIdentState.opened)
      (RunsS.token_more (by simp [qualIdentStep])) fun _ =>
        RunsS.append (middle := fun _ => QualIdentState.indexed IdentState.afterUnderscore)
          (RunsS.token_more (by simp [qualIdentStep])) fun _ => hmapped).congr ?_ rfl
    simp [ticks_noPoints]

/-- From its start, the qualified identifier parser's steps read the tokens of a valid qualified
identifier with the traversal's calls for its sort, and end with its identifier, through the
bridge, and the handled sort. -/
theorem qualifiedIdent_runs {version : Token.Version}
    {h : Traversal.Handler (StateT H m) (Traits.Handler.Error H) (valuesOf H)}
    (hA : TermAgrees h) (qualified : Tree.QualIdentifier)
    (hvalid : qualified.Valid (Bridge.version version)) {tokens : List Parser.Internal.Input}
    (hs : Stands tokens qualified.tokens) :
    ∃ identifier : Nodes.Ident,
      (RunsS noPoints (qualIdentStep version) .start tokens
        (adaptRun (Traversal.qualIdentifier noPoints h qualified))
        fun result => pure (.done (identifier, result.2))) ∧
      Bridge.identifier identifier = (match qualified with
        | .plain identifier => identifier
        | .as identifier _ => identifier) := by
  match qualified with
  | .plain ⟨name, []⟩ =>
    obtain ⟨token, rfl, htoken⟩ := Stands.split_single hs
    obtain ⟨symbol, rfl, rfl⟩ := Parser.Internal.Input.received_symbol htoken
    refine ⟨⟨symbol, #[]⟩, ?_, by simp [Bridge.identifier]⟩
    rw [qualIdentifier_plain]
    exact (RunsS.token (next := fun result => pure (.done (⟨symbol, #[]⟩, result.2)))
      (program := pure ((⟨Bridge.symbol symbol, []⟩ : Tree.Identifier),
        (none : Option (Traits.Handler.«Sort» H))))
      (by simp [qualIdentStep])).congr (by simp) rfl
  | .plain ⟨name, index :: indices⟩ =>
    obtain ⟨symbolToken, rest, rfl, hsymbol, hrest⟩ :=
      BSmtLib.Facts.Proofs.Parser.«Sort».Stands.indexed (List.cons_ne_nil _ _) hs
    obtain ⟨head, hhead, hruns⟩ :=
      BSmtLib.Facts.Proofs.Parser.Category.StepsSort.indexed_runs (H := H)
      (points := noPoints) (version := version) hvalid (List.cons_ne_nil _ _) hsymbol hrest
    refine ⟨head, ?_, hhead⟩
    have hembed := (RunsS.embed (outer := qualIdentStep (H := H) version)
      (fun state => QualIdentState.indexed state)
      (fun identifier => pure (.done (identifier, none)))
      (fun state token => by
        simp only [qualIdentStep]
        congr 1
        funext step
        cases step <;> rfl) hruns).congr rfl (next' := fun _ => pure (.done (head, none))) (by
          funext
          simp [Parser.Internal.Step.wrap])
    have hmapped := RunsS.map_program
      (f := fun _ => ((⟨name, index :: indices⟩ : Tree.Identifier),
        (none : Option (Traits.Handler.«Sort» H))))
      (next := fun result => pure (.done (head, result.2))) hembed
    rw [show Parser.Internal.Input.parenOpen :: Parser.Internal.Input.reserved
        (.general .underscore) :: symbolToken :: (rest ++ [.parenClose]) =
      [.parenOpen] ++ ([.reserved (.general .underscore)] ++
        (symbolToken :: (rest ++ [.parenClose]))) by rfl, qualIdentifier_plain]
    refine (RunsS.append (middle := fun _ => QualIdentState.opened)
      (RunsS.token_more (by simp [qualIdentStep])) fun _ =>
        RunsS.append (middle := fun _ => QualIdentState.indexed IdentState.afterUnderscore)
          (RunsS.token_more (by simp [qualIdentStep])) fun _ => hmapped).congr ?_ rfl
    simp [ticks_noPoints]
  | .as identifier sort =>
    obtain ⟨inner, rfl, hinner⟩ := Stands.split_paren hs
    obtain ⟨asToken, rest, rfl, has, hrest⟩ := Stands.split_cons hinner
    obtain rfl : asToken = _ := Parser.Internal.Input.received_word (word := .general .as) has
    obtain ⟨identTokens, sortTokens, rfl, hident, hsort⟩ := Stands.split hrest
    obtain ⟨head, hhead, hidentRuns⟩ := ident_runs (H := H) identifier hvalid.1 hident
    refine ⟨head, ?_, hhead⟩
    have hidentEmbed := RunsS.embed (outer := qualIdentStep (H := H) version)
      (fun state => QualIdentState.qualifiedIdent state)
      (fun identifier => pure (.more (.sort identifier .init)))
      (fun state token => by
        simp only [qualIdentStep]
        congr 1
        funext step
        cases step <;> rfl) hidentRuns
    have hsortEmbed := RunsS.embed (outer := qualIdentStep (H := H) version)
      (fun state => QualIdentState.sort head state)
      (fun sort => pure (.more (.close head sort)))
      (fun state token => by
        simp only [qualIdentStep]
        congr 1
        funext step
        cases step <;> rfl)
      (BSmtLib.Facts.Proofs.Parser.Category.StepsSort.sort_runs (points := noPoints) hA sort
        hvalid.2 hsort [])
    have hclose : ∀ handled : Traits.Handler.«Sort» H,
        RunsS noPoints (qualIdentStep version) (.close head handled) [.parenClose]
          (do tick noPoints .parenClose; pure (identifier, some handled))
          fun result => pure (.done (head, result.2)) :=
      fun handled => RunsS.token (by
        simp [qualIdentStep, Parser.Category.Token.Internal.expectClose])
    rw [show Parser.Internal.Input.parenOpen :: (Parser.Internal.Input.reserved (.general .as) ::
        (identTokens ++ sortTokens) ++ [.parenClose]) =
      [.parenOpen] ++ ([.reserved (.general .as)] ++
        (identTokens ++ (sortTokens ++ [.parenClose]))) by simp, qualIdentifier_as]
    refine (RunsS.append (middle := fun _ => QualIdentState.opened)
      (RunsS.token_more (by simp [qualIdentStep])) fun _ =>
        RunsS.append (middle := fun _ => QualIdentState.qualifiedIdent IdentState.start)
          (RunsS.token_more (by
            have hnu : (Parser.Internal.Input.reserved (.general .as)).isWord .underscore =
              false := rfl
            simp [qualIdentStep, hnu, Parser.Internal.Input.isWord_general])) fun _ =>
            RunsS.append (middle := fun _ => QualIdentState.sort head .init)
              (hidentEmbed.congr rfl (by funext; simp [Parser.Internal.Step.wrap])) fun _ =>
                RunsS.append (middle := fun handled => QualIdentState.close head handled)
                  (hsortEmbed.congr rfl (by
                    funext
                    simp [BSmtLib.Facts.Proofs.Parser.«Sort».sortPush,
                      Parser.Internal.Step.wrap]))
                  hclose).congr ?_ rfl
    simp only [tick_noPoints, pure_bind]
    rw [bind_pure_comp]

omit [LawfulMonad m] in
private theorem qualifiedIdent_hparse {Z : Type} [Produce Z] (p : QualifiedIdentParser H)
    (s : ParseState H) (c : Z) :
    Parse.parse (m := m) p s c = Parser.Internal.parseByToken p s c := rfl

/-- The qualified identifier parser from its start on the tokens of a valid qualified
identifier: it finishes with its identifier, through the bridge, and the handled sort if it is
qualified by `as`, making the traversal's calls for that sort. -/
theorem qualifiedIdent_parses {version : Token.Version}
    {h : Traversal.Handler (StateT H m) (Traits.Handler.Error H) (valuesOf H)}
    (hA : TermAgrees h) (qualified : Tree.QualIdentifier)
    (hvalid : qualified.Valid (Bridge.version version)) {tokens : List Parser.Internal.Input}
    (hs : Stands tokens qualified.tokens) :
    ∃ identifier : Nodes.Ident,
      Bridge.identifier identifier = (match qualified with
        | .plain identifier => identifier
        | .as identifier _ => identifier) ∧
      Finishes version (QualifiedIdentParser.new (H := H)) tokens
        ((fun result => ({ ident := identifier.intoOwned, sort := result.2 } :
            Nodes.QualifiedIdentBuf _)) <$>
          adaptRun (Traversal.qualIdentifier noPoints h qualified))
        QualifiedIdentParser.new := by
  obtain ⟨identifier, hruns, hidentifier⟩ := qualifiedIdent_runs hA qualified hvalid hs
  refine ⟨identifier, hidentifier, ?_⟩
  have := parses_of_runsS_map (state := QualIdentState.start) (@qualifiedIdent_hparse H m _ _)
    (qualifiedIdent_sim version)
    (RunsS.map_program (f := fun r : Tree.Identifier × Option (Traits.Handler.«Sort» H) =>
      ({ ident := identifier, sort := r.2 } : Nodes.QualifiedIdent _))
      (runs_qualStep (result := fun r : Tree.Identifier × Option (Traits.Handler.«Sort» H) =>
        (identifier, r.2)) hruns))
  rw [Functor.map_map] at this
  exact this

/-- The qualified identifier parser on the tokens of a valid identifier, unqualified: it
finishes with the identifier, through the bridge, and no sort, making no call. -/
theorem qualifiedIdent_parses_plain {version : Token.Version} (identifier : Tree.Identifier)
    (hvalid : identifier.Valid (Bridge.version version)) {tokens : List Parser.Internal.Input}
    (hs : Stands tokens identifier.tokens) :
    ∃ result : Nodes.Ident, Bridge.identifier result = identifier ∧
      Finishes version (QualifiedIdentParser.new (H := H)) tokens
        (pure { ident := result.intoOwned, sort := none } :
          PM H (Nodes.QualifiedIdentBuf (Traits.Handler.«Sort» H)))
        QualifiedIdentParser.new := by
  obtain ⟨result, hruns, hresult⟩ := qualifiedIdent_runs_plain (H := H) identifier hvalid hs
  refine ⟨result, hresult, ?_⟩
  have hparses := parses_of_runsS_map (state := QualIdentState.start)
    (@qualifiedIdent_hparse H m _ _) (qualifiedIdent_sim version)
    (RunsS.map_program (f := fun r : Tree.Identifier × Option (Traits.Handler.«Sort» H) =>
      ({ ident := result, sort := r.2 } : Nodes.QualifiedIdent _))
      (runs_qualStep (result := fun r : Tree.Identifier × Option (Traits.Handler.«Sort» H) =>
        (result, r.2)) hruns))
  simp only [map_pure] at hparses
  exact hparses

/-- The qualified identifier parser on the tokens of a valid identifier qualified by `as` with a
valid sort: it finishes with the identifier, through the bridge, and the handled sort, making the
traversal's calls for the sort. -/
theorem qualifiedIdent_parses_as {version : Token.Version}
    {h : Traversal.Handler (StateT H m) (Traits.Handler.Error H) (valuesOf H)}
    (hA : TermAgrees h) (identifier : Tree.Identifier) (sort : Tree.«Sort»)
    (hvalid : (Tree.QualIdentifier.as identifier sort).Valid (Bridge.version version))
    {tokens : List Parser.Internal.Input}
    (hs : Stands tokens (Tree.QualIdentifier.as identifier sort).tokens) :
    ∃ result : Nodes.Ident, Bridge.identifier result = identifier ∧
      Finishes version (QualifiedIdentParser.new (H := H)) tokens
        ((fun handled => ({ ident := result.intoOwned, sort := some handled } :
            Nodes.QualifiedIdentBuf _)) <$>
          adaptRun (Traversal.sort noPoints h sort))
        QualifiedIdentParser.new := by
  obtain ⟨result, hresult, hparses⟩ := qualifiedIdent_parses hA (.as identifier sort) hvalid hs
  refine ⟨result, hresult, ?_⟩
  rw [qualIdentifier_as, Functor.map_map] at hparses
  exact hparses

private theorem qualifiedIdent_rejects {version : Token.Version}
    {state last : QualIdentState (Traits.Handler.«Sort» H)}
    {tokens : List Parser.Internal.Input} {token : Parser.Internal.Input} {kind : SyntaxErrorKind}
    (hmoves : Moves (qualStep (H := H) version) state tokens last)
    (hfail : qualStep (H := H) version last token = throw (.syntax kind)) :
    Rejects version (QualifiedIdentParser.mk state) (tokens ++ [token]) (pure () : PM H Unit)
      kind :=
  rejects_of_movesS_map (@qualifiedIdent_hparse H m _ _) (qualifiedIdent_sim version) hmoves hfail

/-- The qualified identifier parser on a first token that is neither a symbol nor `(`. -/
theorem qualifiedIdent_rejects_first {version : Token.Version} {token : Parser.Internal.Input}
    (hsymbol : ∀ symbol, token ≠ .symbol symbol) (hopen : token ≠ .parenOpen) :
    Rejects version (QualifiedIdentParser.new (H := H)) [token] (pure () : PM H Unit)
      .expectedIdent :=
  qualifiedIdent_rejects (tokens := []) (.nil _) (by
    cases token <;> first | exact absurd rfl (hsymbol _) | exact absurd rfl hopen |
      simp [qualStep, qualIdentStep, Parser.Internal.syntaxError])

/-- The qualified identifier parser on `(` and a token that is neither `_` nor `as`. -/
theorem qualifiedIdent_rejects_opened {version : Token.Version} {token : Parser.Internal.Input}
    (hunderscore : token ≠ .reserved (.general .underscore))
    (has : token ≠ .reserved (.general .as)) :
    Rejects version (QualifiedIdentParser.new (H := H)) [.parenOpen, token]
      (pure () : PM H Unit) .expectedUnderscoreOrAs := by
  have hu : token.isWord .underscore = false := by
    cases token with
    | reserved word =>
      cases word with
      | general w => cases w <;> first | exact absurd rfl hunderscore | rfl
      | _ => rfl
    | _ => rfl
  have ha : token.isWord .as = false := by
    cases token with
    | reserved word =>
      cases word with
      | general w => cases w <;> first | exact absurd rfl has | rfl
      | _ => rfl
    | _ => rfl
  exact qualifiedIdent_rejects (tokens := [.parenOpen])
    (.cons (middle := .opened) (by simp [qualStep, qualIdentStep]) (.nil _)) (by
      simp [qualStep, qualIdentStep, hu, ha, Parser.Internal.syntaxError])


/-- The steps of the qualified identifier parser on `(` `as` and the tokens of a valid
identifier, then the sort parser's steps within it. -/
private theorem qualifiedIdent_sortRuns {version : Token.Version} {identifier : Tree.Identifier}
    (hvalid : identifier.Valid (Bridge.version version))
    {identTokens : List Parser.Internal.Input} (hident : Stands identTokens identifier.tokens)
    {tokens : List Parser.Internal.Input} {α : Type} {program : PM H α}
    {next : α → PM H (Parser.Internal.Step (SortState (Traits.Handler.«Sort» H))
      (Traits.Handler.«Sort» H))}
    (hsort :
      RunsS noPoints (sortStep version) SortState.init tokens program next) :
    ∃ head : Nodes.Ident,
      RunsS noPoints (qualIdentStep (H := H) version) .start
        ([.parenOpen] ++ ([.reserved (.general .as)] ++ (identTokens ++ tokens))) program
        fun a => next a >>= Parser.Internal.Step.wrap
          (fun state => QualIdentState.sort head state)
          fun sort => pure (.more (.close head sort)) := by
  obtain ⟨head, _, hidentRuns⟩ := ident_runs (H := H) identifier hvalid hident
  refine ⟨head, ?_⟩
  have hidentEmbed := RunsS.embed (outer := qualIdentStep (H := H) version)
    (fun state => QualIdentState.qualifiedIdent state)
    (fun identifier => pure (.more (.sort identifier .init)))
    (fun state token => by
      simp only [qualIdentStep]
      congr 1
      funext step
      cases step <;> rfl) hidentRuns
  have hsortEmbed := RunsS.embed (outer := qualIdentStep (H := H) version)
    (fun state => QualIdentState.sort head state)
    (fun sort => pure (.more (.close head sort)))
    (fun state token => by
      simp only [qualIdentStep]
      congr 1
      funext step
      cases step <;> rfl) hsort
  refine (RunsS.append (middle := fun _ => QualIdentState.opened)
    (RunsS.token_more (by simp [qualIdentStep])) fun _ =>
      RunsS.append (middle := fun _ => QualIdentState.qualifiedIdent IdentState.start)
        (RunsS.token_more (by
          have hnu : (Parser.Internal.Input.reserved (.general .as)).isWord .underscore =
            false := rfl
          simp [qualIdentStep, hnu, Parser.Internal.Input.isWord_general])) fun _ =>
          RunsS.append (middle := fun _ => QualIdentState.sort head .init)
            (hidentEmbed.congr rfl (by funext; simp [Parser.Internal.Step.wrap])) fun _ =>
              hsortEmbed).congr ?_ rfl
  simp [tick_noPoints]

/-- A run of `qualIdentStep` that fails is one of `qualStep`. -/
private theorem runs_qualStep_throw {version : Token.Version}
    {state : QualIdentState (Traits.Handler.«Sort» H)} {tokens : List Parser.Internal.Input}
    {α : Type} {program : PM H α} {kind : SyntaxErrorKind}
    (h : RunsS noPoints (qualIdentStep version) state tokens program
      fun _ => throw (.syntax kind)) :
    RunsS noPoints (qualStep version) state tokens program fun _ => throw (.syntax kind) :=
  (RunsS.embed (outer := qualStep (H := H) version) id
    (fun (identifier, sort) => pure (.done { ident := identifier, sort }))
    (fun state token => by
      simp only [qualStep]
      congr 1
      funext step
      rcases step with state | ⟨identifier, sort⟩ <;> rfl) h).congr rfl (by
    funext a
    apply ExceptT.ext
    simp [ExceptT.run_throw])

/--
The qualified identifier parser on `(` `as`, the tokens of a valid identifier and tokens on whose
last token the sort parser fails with a syntax error, having made the calls of a program: it
rejects them with that error, having made those calls.
-/
theorem qualifiedIdent_rejects_sort_inner {version : Token.Version} {identifier : Tree.Identifier}
    (hvalid : identifier.Valid (Bridge.version version))
    {identTokens : List Parser.Internal.Input} (hident : Stands identTokens identifier.tokens)
    {tokens : List Parser.Internal.Input} {α : Type} {program : PM H α} {kind : SyntaxErrorKind}
    (hsort : RunsS noPoints (sortStep version) SortState.init tokens program
      fun _ => throw (.syntax kind)) :
    Rejects version (QualifiedIdentParser.new (H := H))
      (.parenOpen :: .reserved (.general .as) :: (identTokens ++ tokens))
      ((fun _ => ()) <$> program) kind := by
  obtain ⟨head, hruns⟩ := qualifiedIdent_sortRuns hvalid hident hsort
  have hruns' := hruns.congr (next' := fun _ => throw (Parser.ParseErrorCause.syntax kind)) rfl
    (by
      funext a
      apply ExceptT.ext
      simp [ExceptT.run_throw])
  exact rejects_of_runsS_map (state := QualIdentState.start) (@qualifiedIdent_hparse H m _ _)
    (qualifiedIdent_sim version) (runs_qualStep_throw hruns')

/--
The qualified identifier parser on `(` `as`, the tokens of a valid identifier and of a valid sort,
and a token that is not `)`: it rejects that token with `expectedToken [)]`, having made the
traversal's calls for the sort.
-/
theorem qualifiedIdent_rejects_close {version : Token.Version}
    {h : Traversal.Handler (StateT H m) (Traits.Handler.Error H) (valuesOf H)}
    (hA : TermAgrees h) {identifier : Tree.Identifier} {sort : Tree.«Sort»}
    (hvalid : (Tree.QualIdentifier.as identifier sort).Valid (Bridge.version version))
    {identTokens sortTokens : List Parser.Internal.Input}
    (hident : Stands identTokens identifier.tokens) (hsort : Stands sortTokens sort.tokens)
    {token : Parser.Internal.Input} (htoken : token ≠ .parenClose) :
    Rejects version (QualifiedIdentParser.new (H := H))
      (.parenOpen :: .reserved (.general .as) :: (identTokens ++ (sortTokens ++ [token])))
      ((fun _ => ()) <$> adaptRun (Traversal.sort noPoints h sort))
      (.expectedToken #[.parenClose]) := by
  obtain ⟨head, hruns⟩ := qualifiedIdent_sortRuns hvalid.1 hident
    (BSmtLib.Facts.Proofs.Parser.Category.StepsSort.sort_runs (points := noPoints) hA sort
      hvalid.2 hsort [])
  have hfail : ∀ handled : Traits.Handler.«Sort» H,
      RunsS noPoints (qualIdentStep version) (.close head handled) [token]
        (do tick noPoints token; pure ())
        fun _ => throw (.syntax (.expectedToken #[.parenClose])) :=
    fun handled => RunsS.token (by
      cases token <;> first | exact absurd rfl htoken |
        simp [qualIdentStep, Parser.Category.Token.Internal.expectClose, Parser.Internal.syntaxError])
  have hall := RunsS.append (middle := fun handled => QualIdentState.close head handled)
    (hruns.congr rfl (by
      funext
      simp [BSmtLib.Facts.Proofs.Parser.«Sort».sortPush, Parser.Internal.Step.wrap])) hfail
  have := rejects_of_runsS_map (state := QualIdentState.start) (@qualifiedIdent_hparse H m _ _)
    (qualifiedIdent_sim version) (runs_qualStep_throw hall)
  simp only [tick_noPoints, pure_bind, List.cons_append, List.nil_append, List.append_assoc]
    at this
  simp only [bind_pure_comp, Functor.map_map] at this
  exact this


/-! ## The qualified identifier parser on sorts that fail -/

/-- The qualified identifier parser on `(` `as`, the tokens of a valid identifier, `(` and a
token that starts no head of a sort. -/
theorem qualifiedIdent_rejects_sortInner {version : Token.Version} {identifier : Tree.Identifier}
    (hvalid : identifier.Valid (Bridge.version version))
    {identTokens : List Parser.Internal.Input} (hident : Stands identTokens identifier.tokens)
    {token : Parser.Internal.Input} (hsymbol : ∀ symbol, token ≠ .symbol symbol)
    (hopen : token ≠ .parenOpen) (hunderscore : token ≠ .reserved (.general .underscore)) :
    Rejects version (QualifiedIdentParser.new (H := H))
      (.parenOpen :: .reserved (.general .as) :: (identTokens ++ [.parenOpen, token]))
      (pure () : PM H Unit) .expectedSortInner := by
  have := qualifiedIdent_rejects_sort_inner (H := H) (m := m) hvalid hident
    (BSmtLib.Facts.Proofs.Parser.Category.SortedVar.sort_fails_inner (version := version)
      hsymbol hopen hunderscore)
  simpa using this

/-- The qualified identifier parser on `(` `as`, the tokens of a valid identifier, and `(`, a
symbol and `)`: a sort application without arguments. -/
theorem qualifiedIdent_rejects_sortEmpty {version : Token.Version} {identifier : Tree.Identifier}
    (hvalid : identifier.Valid (Bridge.version version))
    {identTokens : List Parser.Internal.Input} (hident : Stands identTokens identifier.tokens)
    (head : Plain.Symbol) :
    Rejects version (QualifiedIdentParser.new (H := H))
      (.parenOpen :: .reserved (.general .as) ::
        (identTokens ++ [.parenOpen, .symbol head, .parenClose]))
      (pure () : PM H Unit) .emptySortApplication := by
  have := qualifiedIdent_rejects_sort_inner (H := H) (m := m) hvalid hident
    (BSmtLib.Facts.Proofs.Parser.Category.SortedVar.sort_fails_empty (version := version) head)
  simpa using this

/-- The qualified identifier parser on `(` `as`, the tokens of a valid identifier, `(`, the
tokens of a valid identifier and of valid sorts and a token that neither starts another argument
of the sort nor ends it: it rejects that token with `expectedSort`, having made the traversal's
calls for the sorts. -/
theorem qualifiedIdent_rejects_sortArgument {version : Token.Version}
    {h : Traversal.Handler (StateT H m) (Traits.Handler.Error H) (valuesOf H)}
    (hA : TermAgrees h) {identifier : Tree.Identifier}
    (hvalid : identifier.Valid (Bridge.version version))
    {identTokens : List Parser.Internal.Input} (hident : Stands identTokens identifier.tokens)
    {head : Tree.Identifier} (hhead : head.Valid (Bridge.version version))
    {headTokens : List Parser.Internal.Input} (hsHead : Stands headTokens head.tokens)
    {sorts : List Tree.«Sort»} (hsorts : Tree.«Sort».ValidAll (Bridge.version version) sorts)
    {sortTokens : List Parser.Internal.Input}
    (hsSorts : Stands sortTokens (Tree.«Sort».tokensAll sorts))
    {token : Parser.Internal.Input} (hsymbol : ∀ symbol, token ≠ .symbol symbol)
    (hopen : token ≠ .parenOpen) (hclose : token ≠ .parenClose) :
    Rejects version (QualifiedIdentParser.new (H := H))
      (.parenOpen :: .reserved (.general .as) ::
        (identTokens ++ .parenOpen :: (headTokens ++ (sortTokens ++ [token]))))
      ((fun _ => ()) <$> adaptRun (Traversal.sorts noPoints h sorts)) .expectedSort := by
  have := qualifiedIdent_rejects_sort_inner (H := H) (m := m) hvalid hident
    (BSmtLib.Facts.Proofs.Parser.Category.SortedVar.sort_fails_argument hA hhead hsHead hsorts
      hsSorts hsymbol hopen hclose)
  simpa [Functor.map_map] using this


/-! ## The qualified identifier parser on sorts that fail inside open applications -/

open BSmtLib.Facts.Proofs.Parser.Category.SortedVar (frameTokens sortFrames_fails
  sortLevels_fails_argument sortLevels_fails_inner sortLevels_fails_empty)

/-- The qualified identifier parser on `(` `as`, the tokens of a valid identifier, of open sort
applications and a token that neither starts another argument nor ends an application: it
rejects that token with `expectedSort`, having made the traversal's calls for the applications'
argument sorts. -/
theorem qualifiedIdent_rejects_sortDeepArgument {version : Token.Version}
    {h : Traversal.Handler (StateT H m) (Traits.Handler.Error H) (valuesOf H)}
    (hA : TermAgrees h) {identifier : Tree.Identifier}
    (hvalid : identifier.Valid (Bridge.version version))
    {identTokens : List Parser.Internal.Input} (hident : Stands identTokens identifier.tokens)
    {frames : List (Tree.Identifier × List Tree.«Sort»)}
    (hframes : ∀ frame ∈ frames, frame.1.Valid (Bridge.version version) ∧
      Tree.«Sort».ValidAll (Bridge.version version) frame.2)
    {tokens : List Parser.Internal.Input} (hs : Stands tokens (frameTokens frames))
    {token : Parser.Internal.Input} (hsymbol : ∀ symbol, token ≠ .symbol symbol)
    (hopen : token ≠ .parenOpen) (hclose : token ≠ .parenClose) :
    Rejects version (QualifiedIdentParser.new (H := H))
      (.parenOpen :: .reserved (.general .as) :: (identTokens ++ (tokens ++ [token])))
      ((fun _ => ()) <$> adaptRun (frames.mapM fun frame => Traversal.sorts noPoints h frame.2))
      .expectedSort := by
  have := qualifiedIdent_rejects_sort_inner (H := H) (m := m) hvalid hident
    (sortFrames_fails hA hframes hs (sortLevels_fails_argument hsymbol hopen hclose))
  simpa [Functor.map_map] using this

/-- The qualified identifier parser on `(` `as`, the tokens of a valid identifier, of open sort
applications, `(` and a token that starts no head: it rejects that token with
`expectedSortInner`, having made the traversal's calls for the applications' argument sorts. -/
theorem qualifiedIdent_rejects_sortDeepInner {version : Token.Version}
    {h : Traversal.Handler (StateT H m) (Traits.Handler.Error H) (valuesOf H)}
    (hA : TermAgrees h) {identifier : Tree.Identifier}
    (hvalid : identifier.Valid (Bridge.version version))
    {identTokens : List Parser.Internal.Input} (hident : Stands identTokens identifier.tokens)
    {frames : List (Tree.Identifier × List Tree.«Sort»)}
    (hframes : ∀ frame ∈ frames, frame.1.Valid (Bridge.version version) ∧
      Tree.«Sort».ValidAll (Bridge.version version) frame.2)
    {tokens : List Parser.Internal.Input} (hs : Stands tokens (frameTokens frames))
    {token : Parser.Internal.Input} (hsymbol : ∀ symbol, token ≠ .symbol symbol)
    (hopen : token ≠ .parenOpen) (hunderscore : token ≠ .reserved (.general .underscore)) :
    Rejects version (QualifiedIdentParser.new (H := H))
      (.parenOpen :: .reserved (.general .as) :: (identTokens ++ (tokens ++ [.parenOpen, token])))
      ((fun _ => ()) <$> adaptRun (frames.mapM fun frame => Traversal.sorts noPoints h frame.2))
      .expectedSortInner := by
  have := qualifiedIdent_rejects_sort_inner (H := H) (m := m) hvalid hident
    (sortFrames_fails hA hframes hs (sortLevels_fails_inner hsymbol hopen hunderscore))
  simpa [Functor.map_map] using this

/-- The qualified identifier parser on `(` `as`, the tokens of a valid identifier, of open sort
applications, and `(`, a symbol and `)`: it rejects the `)` with `emptySortApplication`, having
made the traversal's calls for the applications' argument sorts. -/
theorem qualifiedIdent_rejects_sortDeepEmpty {version : Token.Version}
    {h : Traversal.Handler (StateT H m) (Traits.Handler.Error H) (valuesOf H)}
    (hA : TermAgrees h) {identifier : Tree.Identifier}
    (hvalid : identifier.Valid (Bridge.version version))
    {identTokens : List Parser.Internal.Input} (hident : Stands identTokens identifier.tokens)
    {frames : List (Tree.Identifier × List Tree.«Sort»)}
    (hframes : ∀ frame ∈ frames, frame.1.Valid (Bridge.version version) ∧
      Tree.«Sort».ValidAll (Bridge.version version) frame.2)
    {tokens : List Parser.Internal.Input} (hs : Stands tokens (frameTokens frames))
    (head : Plain.Symbol) :
    Rejects version (QualifiedIdentParser.new (H := H))
      (.parenOpen :: .reserved (.general .as) ::
        (identTokens ++ (tokens ++ [.parenOpen, .symbol head, .parenClose])))
      ((fun _ => ()) <$> adaptRun (frames.mapM fun frame => Traversal.sorts noPoints h frame.2))
      .emptySortApplication := by
  have := qualifiedIdent_rejects_sort_inner (H := H) (m := m) hvalid hident
    (sortFrames_fails hA hframes hs (sortLevels_fails_empty head))
  simpa [Functor.map_map] using this


/-- The qualified identifier parser from its start on the tokens of a valid qualified
identifier: it finishes with an identifier that is, through the bridge, the one the qualified
identifier names, plain or qualified by `as` with a sort, and the handled sort if any, making the
traversal's calls for that sort. -/
theorem qualifiedIdent_parses_any {version : Token.Version}
    {h : Traversal.Handler (StateT H m) (Traits.Handler.Error H) (valuesOf H)}
    (hA : TermAgrees h) (qualified : Tree.QualIdentifier)
    (hvalid : qualified.Valid (Bridge.version version)) {tokens : List Parser.Internal.Input}
    (hs : Stands tokens qualified.tokens) :
    ∃ identifier : Nodes.Ident,
      (qualified = .plain (Bridge.identifier identifier) ∨
        ∃ sort, qualified = .as (Bridge.identifier identifier) sort) ∧
      Finishes version (QualifiedIdentParser.new (H := H)) tokens
        ((fun result => ({ ident := identifier.intoOwned, sort := result.2 } :
            Nodes.QualifiedIdentBuf _)) <$>
          adaptRun (Traversal.qualIdentifier noPoints h qualified))
        QualifiedIdentParser.new := by
  obtain ⟨identifier, hidentifier, hparses⟩ := qualifiedIdent_parses hA qualified hvalid hs
  refine ⟨identifier, ?_, hparses⟩
  cases qualified with
  | plain name => exact .inl (by simp only at hidentifier; rw [hidentifier])
  | as name sort => exact .inr ⟨sort, by simp only at hidentifier; rw [hidentifier]⟩

end

end BSmtLib.Facts.Proofs.Parser.Category.QualifiedIdent
