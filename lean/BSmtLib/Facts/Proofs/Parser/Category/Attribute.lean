module

public import BSmtLib.Facts.Proofs.Parser.Category.Ident
public import BSmtLib.Facts.Proofs.Parser.Category.StepsAttribute
public import BSmtLib.Facts.Proofs.Parser.Attribute
import all BSmtLib.Parser
import all BSmtLib.Parser.Category.Attribute
import all BSmtLib.Parser.Category.Token
import all BSmtLib.Parser.Category.SExpr

@[expose] public section

/-!
# The attribute parsers on a cursor

Both attribute parsers step as `attributeStep`, whose lemmas against the traversal are the
attribute proofs' (`Category.StepsAttribute`): the parser of one attribute with `single`,
which finishes with the one attribute it handled, the parser of attributes up to a `)` without.
-/

namespace BSmtLib.Facts.Proofs.Parser.Category.Attribute

open BSmtLibSpec.Grammar
open BSmtLibSpec.Parser
open BSmtLibSpec.Parser.Traversal
open BSmtLib.Token (Produce)
open BSmtLib.Parser (Parse ParseState SyntaxErrorKind)
open BSmtLib.Parser.Internal (PM)
open BSmtLib.Parser.Category.Attribute
open BSmtLib.Parser.Category.Attribute.Internal
open BSmtLib.Facts.Parser.Adapters.Bridge BSmtLib.Facts.Parser.Adapters.Run
open BSmtLib.Facts.Parser.Adapters.Cursor (Takes Reads noPoints)
open BSmtLib.Facts.Parser.Adapters.Outcome (Finishes Rejects)
open BSmtLib.Facts.Proofs.Parser.Category.Cursor (Simulates Moves tick_noPoints flowOf)
open BSmtLib.Facts.Proofs.Parser.Category.Ident
open BSmtLib.Facts.Proofs.Parser.Category.Steps BSmtLib.Facts.Proofs.Parser.Category.CursorS
open BSmtLib.Facts.Proofs.Parser.Category.StepsAttribute (value_runs attributeSingle_runs
  attributes_runs_init)
open BSmtLib.Facts.Proofs.Parser.Attribute (valueTokens)
open BSmtLib.Facts.Proofs.Parser.Drive BSmtLib.Facts.Proofs.Parser.Tokens

section

variable {H : Type} {m : Type → Type} [Monad m] [LawfulMonad m] [Traits.Handler H m]

/-- The steps of the parser of one attribute: those of `attributeStep` with `single`, finishing
with the one attribute. -/
def singleStep (version : Token.Version)
    (state : AttributeState (Traits.Handler.SExpr H) (Traits.Handler.Attribute H))
    (token : Parser.Internal.Input) :
    PM H (Parser.Internal.Step (AttributeState (Traits.Handler.SExpr H) (Traits.Handler.Attribute H))
      (Traits.Handler.Attribute H)) := do
  match ← attributeStep true version state token with
  | .more state => return .more state
  | .done attributes =>
    match attributes[0]? with
    | some first => return .done first
    | none => Parser.Internal.syntaxError .expectedAttribute

private theorem closedAttribute_sim (version : Token.Version) :
    Simulates version (ClosedAttributeParser.mk (H := H)) (singleStep version)
      ClosedAttributeParser.new := by
  refine ⟨fun _ _ => rfl, fun state token => ?_, fun _ => rfl, fun _ _ => rfl⟩
  simp only [singleStep, map_bind]
  refine bind_congr fun step => ?_
  rcases step with state | attributes
  · simp [flowOf]
  · cases h0 : attributes[0]? <;> simp [h0, flowOf, Parser.Internal.syntaxError]

private theorem closedMultipleAttribute_sim (version : Token.Version) :
    Simulates version (ClosedMultipleAttributeParser.mk (H := H)) (attributeStep false version)
      ClosedMultipleAttributeParser.new := by
  refine ⟨fun _ _ => rfl, fun state token => ?_, fun _ => rfl, fun _ _ => rfl⟩
  show (do
      match ← attributeStep false version state token with
      | .more state => return Parser.Internal.Flow.more (ClosedMultipleAttributeParser.mk state)
      | .done result => return .done result) = _
  rw [map_eq_pure_bind]
  refine bind_congr fun step => ?_
  cases step <;> rfl

omit [LawfulMonad m] in
private theorem closedAttribute_hparse {Z : Type} [Produce Z] (p : ClosedAttributeParser H)
    (s : ParseState H) (c : Z) :
    Parse.parse (m := m) p s c = Parser.Internal.parseByToken p s c := rfl

omit [LawfulMonad m] in
private theorem closedMultipleAttribute_hparse {Z : Type} [Produce Z]
    (p : ClosedMultipleAttributeParser H) (s : ParseState H) (c : Z) :
    Parse.parse (m := m) p s c = Parser.Internal.parseByToken p s c := rfl

/-- A run of the attribute steps with `single`, as one of `singleStep`, its result an array. -/
private theorem singleStep_embed {version : Token.Version}
    {state : AttributeState (Traits.Handler.SExpr H) (Traits.Handler.Attribute H)}
    {tokens : List Parser.Internal.Input} {α : Type} {program : PM H α}
    {next : α → PM H (Parser.Internal.Step
      (AttributeState (Traits.Handler.SExpr H) (Traits.Handler.Attribute H))
      (Array (Traits.Handler.Attribute H)))}
    (h : RunsS noPoints (attributeStep true version) state tokens program next) :
    RunsS noPoints (singleStep version) state tokens program fun a =>
      next a >>= Parser.Internal.Step.wrap id fun attributes => match attributes[0]? with
        | some first => pure (.done first)
        | none => Parser.Internal.syntaxError .expectedAttribute :=
  RunsS.embed (outer := singleStep (H := H) version) id
    (fun attributes => match attributes[0]? with
      | some first => pure (.done first)
      | none => Parser.Internal.syntaxError .expectedAttribute)
    (fun state token => by
      simp only [singleStep]
      congr 1
      funext step
      cases step <;> rfl) h

/-- The parser of one attribute from its start on the tokens of a valid attribute and the `)`
after it: it finishes with the handled attribute, making the traversal's calls. -/
theorem closedAttribute_parses {version : Token.Version}
    {h : Traversal.Handler (StateT H m) (Traits.Handler.Error H) (valuesOf H)}
    (hA : TermAgrees h) (attr : Tree.Attribute)
    (hvalid : attr.Valid (Bridge.version version)) {tokens : List Parser.Internal.Input}
    (hs : Stands tokens (attr.tokens ++ [.parenClose])) :
    Finishes version (ClosedAttributeParser.new (H := H)) tokens
      (adaptRun (do
        take noPoints (.keyword attr.keyword)
        attributeThen noPoints h attr.keyword .parenClose attr.value) :
        PM H (Traits.Handler.Attribute H))
      ClosedAttributeParser.new := by
  obtain ⟨keyword, value⟩ := attr
  have hruns := attributeSingle_runs (H := H) (points := noPoints) hA keyword value hvalid hs
  have hembed := (singleStep_embed hruns).congr rfl (next' := fun r => pure (.done r)) (by
    funext
    simp [Parser.Internal.Step.wrap])
  exact parses_of_runsS (state := AttributeState.init) (@closedAttribute_hparse H m _ _)
    (closedAttribute_sim version) hembed

/-- The parser of attributes up to a `)` from its start on the tokens of valid attributes, at
least one, and the `)` after them: it finishes with the handled attributes, making the
traversal's calls. -/
theorem closedMultipleAttribute_parses {version : Token.Version}
    {h : Traversal.Handler (StateT H m) (Traits.Handler.Error H) (valuesOf H)}
    (hA : TermAgrees h) (first : Tree.Attribute) (rest : List Tree.Attribute)
    (hvalid : ∀ attr ∈ first :: rest, attr.Valid (Bridge.version version))
    {tokens : List Parser.Internal.Input}
    (hs : Stands tokens ((first :: rest).flatMap Tree.Attribute.tokens ++ [.parenClose])) :
    Finishes version (ClosedMultipleAttributeParser.new (H := H)) tokens
      ((fun handled : List (Traits.Handler.Attribute H) => handled.toArray) <$> adaptRun (do
        take noPoints (.keyword first.keyword)
        attributesThen noPoints h first.keyword first.value rest))
      ClosedMultipleAttributeParser.new := by
  have hruns := attributes_runs_init (H := H) (points := noPoints) hA first rest hvalid hs
  exact parses_of_runsS (state := AttributeState.init) (@closedMultipleAttribute_hparse H m _ _)
    (closedMultipleAttribute_sim version) (RunsS.map_program hruns)

/-- The parser of attributes up to a `)` from its start on the `)`: it finishes with no
attribute, making no call. -/
theorem closedMultipleAttribute_parses_none {version : Token.Version} :
    Finishes version (ClosedMultipleAttributeParser.new (H := H)) [.parenClose]
      (pure #[] : PM H (Array (Traits.Handler.Attribute H)))
      ClosedMultipleAttributeParser.new := by
  have hruns : RunsS noPoints (attributeStep (H := H) false version) AttributeState.init
      [.parenClose] (pure #[]) fun r => pure (.done r) :=
    (RunsS.token (program := pure #[]) (by
      simp [attributeStep, AttributeState.init])).congr (by simp) rfl
  exact parses_of_runsS (state := AttributeState.init) (@closedMultipleAttribute_hparse H m _ _)
    (closedMultipleAttribute_sim version) hruns

/-- The parser of one attribute on a first token that is not a keyword: no attribute starts
there, and a `)` would close an empty attribute. -/
theorem closedAttribute_rejects_first {version : Token.Version} {token : Parser.Internal.Input}
    (htoken : ∀ name, token ≠ .keyword name) :
    Rejects version (ClosedAttributeParser.new (H := H)) [token] (pure () : PM H Unit)
      .expectedAttribute := by
  have hfail : singleStep (H := H) version AttributeState.init token =
      throw (.syntax .expectedAttribute) := by
    cases token <;> first | exact absurd rfl (htoken _) |
      simp [singleStep, attributeStep, AttributeState.init, Parser.Internal.syntaxError]
  exact rejects_of_movesS (tokens := []) (@closedAttribute_hparse H m _ _)
    (closedAttribute_sim version) (.nil _) hfail

/-- The parser of attributes up to a `)` on a first token that is neither a keyword nor `)`. -/
theorem closedMultipleAttribute_rejects_first {version : Token.Version}
    {token : Parser.Internal.Input} (htoken : ∀ name, token ≠ .keyword name)
    (hclose : token ≠ .parenClose) :
    Rejects version (ClosedMultipleAttributeParser.new (H := H)) [token] (pure () : PM H Unit)
      .expectedAttribute := by
  have hfail : attributeStep (H := H) false version AttributeState.init token =
      throw (.syntax .expectedAttribute) := by
    cases token <;> first | exact absurd rfl (htoken _) | exact absurd rfl hclose |
      simp [attributeStep, AttributeState.init, Parser.Internal.syntaxError]
  exact rejects_of_movesS (tokens := []) (@closedMultipleAttribute_hparse H m _ _)
    (closedMultipleAttribute_sim version) (.nil _) hfail

/-- A token that starts the value of an attribute or ends one without a value: a symbol, a
constant, `(`, `)` or a keyword. -/
def AfterKeyword (token : Parser.Internal.Input) : Prop :=
  (∃ symbol, token = .symbol symbol) ∨ (∃ constant, token = .constant constant) ∨
    token = .parenOpen ∨ token = .parenClose ∨ (∃ name, token = .keyword name)

/-- The parser of one attribute on a keyword and a token that neither starts a value nor ends
the attribute. -/
theorem closedAttribute_rejects_value {version : Token.Version} (name : BSmtLib.Plain.KeywordView)
    {token : Parser.Internal.Input} (htoken : ¬ AfterKeyword token) :
    Rejects version (ClosedAttributeParser.new (H := H)) [.keyword name, token]
      (pure () : PM H Unit) .expectedAttribute := by
  simp only [AfterKeyword, not_or, not_exists] at htoken
  obtain ⟨hs, hc, ho, hcl, hk⟩ := htoken
  have hfail : singleStep (H := H) version { mode := .afterName name, attributes := #[] } token =
      throw (.syntax .expectedAttribute) := by
    cases token <;> first | exact absurd rfl (hs _) | exact absurd rfl (hc _) |
      exact absurd rfl ho | exact absurd rfl hcl | exact absurd rfl (hk _) |
      simp [singleStep, attributeStep, Parser.Internal.syntaxError]
  exact rejects_of_movesS (tokens := [.keyword name]) (@closedAttribute_hparse H m _ _)
    (closedAttribute_sim version)
    (.cons (by simp [singleStep, attributeStep, AttributeState.init]) (.nil _)) hfail

/-- The parser of attributes up to a `)` on a keyword and a token that neither starts a value
nor ends the attribute. -/
theorem closedMultipleAttribute_rejects_value {version : Token.Version}
    (name : BSmtLib.Plain.KeywordView)
    {token : Parser.Internal.Input} (htoken : ¬ AfterKeyword token) :
    Rejects version (ClosedMultipleAttributeParser.new (H := H)) [.keyword name, token]
      (pure () : PM H Unit) .expectedAttribute := by
  simp only [AfterKeyword, not_or, not_exists] at htoken
  obtain ⟨hs, hc, ho, hcl, hk⟩ := htoken
  have hfail : attributeStep (H := H) false version
      { mode := .afterName name, attributes := #[] } token =
      throw (.syntax .expectedAttribute) := by
    cases token <;> first | exact absurd rfl (hs _) | exact absurd rfl (hc _) |
      exact absurd rfl ho | exact absurd rfl hcl | exact absurd rfl (hk _) |
      simp [attributeStep, Parser.Internal.syntaxError]
  exact rejects_of_movesS (tokens := [.keyword name]) (@closedMultipleAttribute_hparse H m _ _)
    (closedMultipleAttribute_sim version)
    (.cons (by simp [attributeStep, AttributeState.init]) (.nil _)) hfail

/-- The parser of one attribute on a keyword and a keyword after it: the attribute would be
followed by another, where its `)` is due. -/
theorem closedAttribute_rejects_keyword {version : Token.Version}
    (name name' : BSmtLib.Plain.KeywordView) :
    Rejects version (ClosedAttributeParser.new (H := H)) [.keyword name, .keyword name']
      (pure () : PM H Unit) (.expectedToken #[.parenClose]) := by
  have hfail : singleStep (H := H) version { mode := .afterName name, attributes := #[] }
      (.keyword name') = throw (.syntax (.expectedToken #[.parenClose])) := by
    simp [singleStep, attributeStep, Parser.Internal.syntaxError]
  exact rejects_of_movesS (tokens := [.keyword name]) (@closedAttribute_hparse H m _ _)
    (closedAttribute_sim version)
    (.cons (by simp [singleStep, attributeStep, AttributeState.init]) (.nil _)) hfail

/-- The program of an attribute with a value: the traversal's calls for the value and the call
that handles the attribute. -/
abbrev valuedProgram (h : Traversal.Handler (StateT H m) (Traits.Handler.Error H) (valuesOf H))
    (keyword : BSmtLibSpec.Regex.Chars) (value : Tree.AttributeValue) : PM H Unit :=
  (fun _ => ()) <$> adaptRun (do
    let node ← attributeValue noPoints h value
    Traversal.call h (.handleAttribute keyword (some node)))

/-- The attribute steps on the keyword and the value of a valid attribute with a value. -/
private theorem valued_runs {version : Token.Version} (single : Bool)
    {h : Traversal.Handler (StateT H m) (Traits.Handler.Error H) (valuesOf H)}
    (hA : TermAgrees h) (keyword : BSmtLibSpec.Regex.Chars) (value : Tree.AttributeValue)
    (hvalid : (⟨keyword, some value⟩ : Tree.Attribute).Valid (Bridge.version version))
    {tokens : List Parser.Internal.Input}
    (hs : Stands tokens (Tree.Attribute.tokens ⟨keyword, some value⟩)) :
    RunsS noPoints (attributeStep single version) AttributeState.init tokens
      (adaptRun (do
        let node ← attributeValue noPoints h value
        Traversal.call h (.handleAttribute keyword (some node))))
      fun handled => pure (.more { mode := .start, attributes := #[handled] }) := by
  obtain ⟨name, valueTokens', rfl, rfl, hvalueTokens⟩ :=
    BSmtLib.Facts.Proofs.Parser.Attribute.Stands.attribute hs
  have hkeyword : RunsS noPoints (attributeStep (H := H) single version) AttributeState.init
      [.keyword name] (tick noPoints (.keyword name))
      fun _ => pure (.more { mode := .afterName name, attributes := #[] }) :=
    RunsS.token_more (by simp [AttributeState.init, attributeStep.eq_def])
  rw [show Parser.Internal.Input.keyword name :: valueTokens' = [.keyword name] ++ valueTokens'
    by rfl]
  refine (RunsS.append (middle := fun _ =>
      ({ mode := .afterName name, attributes := #[] } : AttributeState _ _)) hkeyword
    fun _ => (value_runs hA single value (by simpa [Tree.Attribute.Valid] using hvalid)
      hvalueTokens name #[]).congr rfl (by funext; simp)).congr ?_ rfl
  simp only [tick_noPoints, pure_bind, BSmtLibSpec.Facts.Proofs.Parser.Program.callAttribute]
  rfl

/-- The parser of one attribute on the tokens of a valid attribute with a value and a token
that is not `)`: it rejects that token with `expectedToken [)]`, having made the traversal's
calls for the attribute. -/
theorem closedAttribute_rejects_close {version : Token.Version}
    {h : Traversal.Handler (StateT H m) (Traits.Handler.Error H) (valuesOf H)}
    (hA : TermAgrees h) (keyword : BSmtLibSpec.Regex.Chars) (value : Tree.AttributeValue)
    (hvalid : (⟨keyword, some value⟩ : Tree.Attribute).Valid (Bridge.version version))
    {tokens : List Parser.Internal.Input}
    (hs : Stands tokens (Tree.Attribute.tokens ⟨keyword, some value⟩))
    {token : Parser.Internal.Input} (htoken : token ≠ .parenClose) :
    Rejects version (ClosedAttributeParser.new (H := H)) (tokens ++ [token])
      (valuedProgram h keyword value) (.expectedToken #[.parenClose]) := by
  have hfail : ∀ handled : Traits.Handler.Attribute H,
      RunsS noPoints (attributeStep true version) { mode := .start, attributes := #[handled] }
        [token] (do tick noPoints token; pure ())
        fun _ => throw (.syntax (.expectedToken #[.parenClose])) :=
    fun handled => RunsS.token (by
      cases token <;> first | exact absurd rfl htoken |
        simp [attributeStep.eq_def, Parser.Category.Token.Internal.expectClose, Parser.Internal.syntaxError])
  have hruns := RunsS.append (middle := fun handled =>
    ({ mode := .start, attributes := #[handled] } : AttributeState _ _))
    (valued_runs true hA keyword value hvalid hs) hfail
  have hembed := (singleStep_embed hruns).congr
    (next' := fun _ => throw (Parser.ParseErrorCause.syntax (.expectedToken #[.parenClose]))) rfl
    (by
      funext a
      apply ExceptT.ext
      simp [ExceptT.run_throw])
  have := rejects_of_runsS (state := AttributeState.init) (@closedAttribute_hparse H m _ _)
    (closedAttribute_sim version) hembed
  simp only [tick_noPoints, map_pure, bind_pure_comp, Functor.map_map] at this
  exact this

/-- The parser of attributes up to a `)` on the tokens of a valid attribute with a value and a
token that neither starts another attribute nor is `)`: it rejects that token, having made the
traversal's calls for the attribute. -/
theorem closedMultipleAttribute_rejects_after {version : Token.Version}
    {h : Traversal.Handler (StateT H m) (Traits.Handler.Error H) (valuesOf H)}
    (hA : TermAgrees h) (keyword : BSmtLibSpec.Regex.Chars) (value : Tree.AttributeValue)
    (hvalid : (⟨keyword, some value⟩ : Tree.Attribute).Valid (Bridge.version version))
    {tokens : List Parser.Internal.Input}
    (hs : Stands tokens (Tree.Attribute.tokens ⟨keyword, some value⟩))
    {token : Parser.Internal.Input} (hkeyword : ∀ name, token ≠ .keyword name)
    (hclose : token ≠ .parenClose) :
    Rejects version (ClosedMultipleAttributeParser.new (H := H)) (tokens ++ [token])
      (valuedProgram h keyword value) .expectedAttribute := by
  have hfail : ∀ handled : Traits.Handler.Attribute H,
      RunsS noPoints (attributeStep false version) { mode := .start, attributes := #[handled] }
        [token] (do tick noPoints token; pure ())
        fun _ => throw (.syntax .expectedAttribute) :=
    fun handled => RunsS.token (by
      cases token <;> first | exact absurd rfl hclose | exact absurd rfl (hkeyword _) |
        simp [attributeStep.eq_def, Parser.Internal.syntaxError])
  have hruns := RunsS.append (middle := fun handled =>
    ({ mode := .start, attributes := #[handled] } : AttributeState _ _))
    (valued_runs false hA keyword value hvalid hs) hfail
  have := rejects_of_runsS (state := AttributeState.init)
    (@closedMultipleAttribute_hparse H m _ _) (closedMultipleAttribute_sim version) hruns
  simp only [tick_noPoints, map_pure, bind_pure_comp, Functor.map_map] at this
  exact this


/-! ## Failures inside list values -/

open BSmtLib.Parser.Category.SExpr.Internal (SExprState sExprStep)

/-- The tokens of open lists of s-expressions, outermost first: each a `(` and its items so
far. -/
abbrev sExprFrameTokens (frames : List (List Tree.SExpr)) :
    List BSmtLibSpec.Grammar.SyntaxToken :=
  frames.flatMap fun items => .parenOpen :: Tree.SExpr.tokensAll items

/-- From any stack, the s-expression parser reads the tokens of open lists with the traversal's
calls for their items, and is then between items, the lists open on the stack. -/
theorem sExprFrames_runs {version : Token.Version}
    {h : Traversal.Handler (StateT H m) (Traits.Handler.Error H) (valuesOf H)}
    (hA : TermAgrees h) :
    (frames : List (List Tree.SExpr)) →
    (∀ items ∈ frames, Tree.SExpr.ValidAll (Bridge.version version) items) →
    ∀ {tokens : List Parser.Internal.Input}, Stands tokens (sExprFrameTokens frames) →
    ∀ levels : SExprState (Traits.Handler.SExpr H),
    ∃ build : List (List (Traits.Handler.SExpr H)) → SExprState (Traits.Handler.SExpr H),
      RunsS noPoints (sExprStep (H := H) version) levels tokens
        (adaptRun (frames.mapM fun items => Traversal.sExprs noPoints h items))
        fun handled => pure (.more (build handled))
  | [], _, _, hs, levels => by
    have := Stands.eq_nil hs
    subst this
    exact ⟨fun _ => levels, (RunsS.nil [] rfl).congr (by simp) rfl⟩
  | items :: frames, hvalid, _, hs, levels => by
    simp only [sExprFrameTokens, List.flatMap_cons] at hs
    obtain ⟨tokens₁, tokens₂, rfl, hs₁, hs₂⟩ := Stands.split hs
    obtain ⟨openToken, inner, rfl, hopen, hinner⟩ := Stands.split_cons hs₁
    rw [Parser.Internal.Input.received_parenOpen hopen]
    have hitems := BSmtLib.Facts.Proofs.Parser.Category.StepsSExpr.sExprs_runs (H := H)
      (version := version) (points := noPoints) hA items (hvalid items (List.mem_cons_self ..))
      hinner #[] levels
    have hrest := fun (handled : List (Traits.Handler.SExpr H)) =>
      sExprFrames_runs hA frames (fun f hf => hvalid f (List.mem_cons_of_mem _ hf)) hs₂
        ((#[] ++ handled.toArray) :: levels)
    refine ⟨fun all => match all with
      | first :: others => Classical.choose (hrest first) others
      | [] => levels, ?_⟩
    have hopen' : RunsS noPoints (sExprStep (H := H) version) levels [.parenOpen]
        (tick noPoints .parenOpen) fun _ => pure (.more (#[] :: levels)) :=
      RunsS.token_more (by simp [sExprStep])
    have h₂ := RunsS.append (middle := fun (handled : List (Traits.Handler.SExpr H)) =>
      (#[] ++ handled.toArray) :: levels)
      (next := fun all => pure (.more (match all with
        | first :: others => Classical.choose (hrest first) others
        | [] => levels)))
      hitems fun first =>
        (RunsS.map_program (f := (first :: ·)) (Classical.choose_spec (hrest first))).congr rfl rfl
    have h₁ := RunsS.append (middle := fun _ => #[] :: levels) hopen' fun _ => h₂
    simp only [List.cons_append, List.nil_append] at h₁ ⊢
    refine h₁.congr ?_ rfl
    simp [tick_noPoints, List.mapM_cons, bind_pure_comp]

/-- A token that starts no s-expression and does not end a list: the s-expression parser
fails at it, on any stack. -/
theorem sExprLevels_fails {version : Token.Version} {token : Parser.Internal.Input}
    (hopen : token ≠ .parenOpen) (hclose : token ≠ .parenClose)
    (hconstant : ∀ constant, token ≠ .constant constant)
    (hsymbol : ∀ symbol, token ≠ .symbol symbol)
    (hkeyword : ∀ name, token ≠ .keyword name)
    (hreserved : ∀ word, token = .reserved word → ¬ version ≥ .v2_6)
    (levels : SExprState (Traits.Handler.SExpr H)) :
    sExprStep (H := H) version levels token = throw (.syntax .expectedSExpr) := by
  cases token with
  | parenOpen => exact absurd rfl hopen
  | parenClose => exact absurd rfl hclose
  | constant c => exact absurd rfl (hconstant c)
  | symbol s => exact absurd rfl (hsymbol s)
  | keyword k => exact absurd rfl (hkeyword k)
  | reserved w =>
    have := hreserved w rfl
    simp [sExprStep, this, Parser.Internal.syntaxError]
  | _ => simp [sExprStep, Parser.Internal.syntaxError]

/-- The attribute steps on a keyword, `(`, the tokens of valid items, of open lists and a token
that starts no s-expression and does not end a list: they fail at that token with
`expectedSExpr`, having made the traversal's calls for the items. -/
private theorem sExpr_value_runs {version : Token.Version} (single : Bool)
    {h : Traversal.Handler (StateT H m) (Traits.Handler.Error H) (valuesOf H)}
    (hA : TermAgrees h) (name : BSmtLib.Plain.KeywordView) {items : List Tree.SExpr}
    (hitems : Tree.SExpr.ValidAll (Bridge.version version) items)
    {itemTokens : List Parser.Internal.Input}
    (hsItems : Stands itemTokens (Tree.SExpr.tokensAll items))
    {frames : List (List Tree.SExpr)}
    (hframes : ∀ items ∈ frames, Tree.SExpr.ValidAll (Bridge.version version) items)
    {tokens : List Parser.Internal.Input} (hs : Stands tokens (sExprFrameTokens frames))
    {token : Parser.Internal.Input}
    (hopen : token ≠ .parenOpen) (hclose : token ≠ .parenClose)
    (hconstant : ∀ constant, token ≠ .constant constant)
    (hsymbol : ∀ symbol, token ≠ .symbol symbol)
    (hkeyword : ∀ name, token ≠ .keyword name)
    (hreserved : ∀ word, token = .reserved word → ¬ version ≥ .v2_6) :
    RunsS noPoints (attributeStep (H := H) single version) AttributeState.init
      (.keyword name :: .parenOpen :: (itemTokens ++ (tokens ++ [token])))
      ((fun _ => ()) <$> (adaptRun (Traversal.sExprs noPoints h items) >>= fun _ =>
        adaptRun (frames.mapM fun items => Traversal.sExprs noPoints h items)))
      fun _ => throw (.syntax .expectedSExpr) := by
  -- the s-expression steps from the empty stack, to the failure
  obtain ⟨build, hframesRuns⟩ := sExprFrames_runs (version := version) hA frames hframes hs []
  have hfail : ∀ handled, RunsS noPoints (sExprStep (H := H) version) (build handled) [token]
      (do tick noPoints token; (pure () : PM H Unit))
      fun _ => throw (.syntax .expectedSExpr) := fun handled =>
    RunsS.token (by
      simp only [pure_bind]
      exact sExprLevels_fails hopen hclose hconstant hsymbol hkeyword hreserved _)
      (handlerOnly_pure ())
  have hsExpr := RunsS.append (middle := build) hframesRuns hfail
  -- within the list value, as attribute steps
  have hembed := fun (found : Array (Traits.Handler.SExpr H)) =>
    RunsS.embed (outer := attributeStep (H := H) single version)
      (fun state => ({ mode := .inside name found state false, attributes := #[] } :
        AttributeState _ _))
      (fun item => pure (.more
        { mode := .inside name (found.push item) [] true, attributes := #[] }))
      (fun state token => by
        simp only [attributeStep.eq_def]
        simp
        congr 1
        funext step
        cases step <;> rfl) hsExpr
  -- the first token of the open lists or the failing one steps as between items
  have hfirst : ∀ (found : Array (Traits.Handler.SExpr H)),
      RunsS noPoints (attributeStep (H := H) single version)
        { mode := .inside name found [] true, attributes := #[] } (tokens ++ [token])
        ((fun _ => ()) <$> adaptRun (frames.mapM fun items => Traversal.sExprs noPoints h items))
        fun _ => throw (.syntax .expectedSExpr) := by
    intro found
    have hne : ∃ first rest, tokens ++ [token] = first :: rest ∧ first ≠ .parenClose := by
      cases frames with
      | nil =>
        rw [Stands.eq_nil hs]
        exact ⟨token, [], rfl, hclose⟩
      | cons items' frames' =>
        simp only [sExprFrameTokens, List.flatMap_cons, List.cons_append] at hs
        obtain ⟨first, rest, rfl, hopen', _⟩ := Stands.split_cons hs
        rw [Parser.Internal.Input.received_parenOpen hopen']
        exact ⟨.parenOpen, _, rfl, by simp⟩
    obtain ⟨first, rest, heq, hfirst⟩ := hne
    rw [heq]
    rw [heq] at hembed
    refine RunsS.first ?_ ((hembed found).congr (by simp [tick_noPoints, bind_pure_comp]) ?_)
    · cases first <;> first | exact absurd rfl hfirst | simp [attributeStep.eq_def]
    · funext a
      apply ExceptT.ext
      simp [ExceptT.run_throw]
  -- the keyword, the `(` and the items
  have hkey : RunsS noPoints (attributeStep (H := H) single version) AttributeState.init
      [.keyword name] (tick noPoints (.keyword name))
      fun _ => pure (.more { mode := .afterName name, attributes := #[] }) :=
    RunsS.token_more (by simp [AttributeState.init, attributeStep.eq_def])
  have hopenValue : RunsS noPoints (attributeStep (H := H) single version)
      { mode := .afterName name, attributes := #[] } [.parenOpen] (tick noPoints .parenOpen)
      fun _ => pure (.more { mode := .inside name #[] [] true, attributes := #[] }) :=
    RunsS.token_more (by simp [attributeStep.eq_def])
  have hitemsRuns := BSmtLib.Facts.Proofs.Parser.Category.StepsAttribute.valueItems_runs
    (H := H) (points := noPoints) (version := version) hA single items hitems hsItems name #[] #[]
  have hall := RunsS.append (middle := fun _ =>
      ({ mode := .afterName name, attributes := #[] } : AttributeState _ _)) hkey fun _ =>
    RunsS.append (middle := fun _ =>
      ({ mode := .inside name #[] [] true, attributes := #[] } : AttributeState _ _))
      hopenValue fun _ =>
      RunsS.append (middle := fun (handled : List (Traits.Handler.SExpr H)) =>
        ({ mode := .inside name (#[] ++ handled.toArray) [] true, attributes := #[] } :
          AttributeState _ _)) hitemsRuns fun handled => hfirst (#[] ++ handled.toArray)
  simp only [List.cons_append, List.nil_append] at hall
  refine hall.congr ?_ rfl
  simp [tick_noPoints]


/--
The parser of one attribute on a keyword, `(`, the tokens of valid items, of open lists of
s-expressions and a token that starts no s-expression and does not end a list: it rejects that
token with `expectedSExpr`, having made the traversal's calls for the items.
-/
theorem closedAttribute_rejects_sExpr {version : Token.Version}
    {h : Traversal.Handler (StateT H m) (Traits.Handler.Error H) (valuesOf H)}
    (hA : TermAgrees h) (name : BSmtLib.Plain.KeywordView) {items : List Tree.SExpr}
    (hitems : Tree.SExpr.ValidAll (Bridge.version version) items)
    {itemTokens : List Parser.Internal.Input}
    (hsItems : Stands itemTokens (Tree.SExpr.tokensAll items))
    {frames : List (List Tree.SExpr)}
    (hframes : ∀ items ∈ frames, Tree.SExpr.ValidAll (Bridge.version version) items)
    {tokens : List Parser.Internal.Input} (hs : Stands tokens (sExprFrameTokens frames))
    {token : Parser.Internal.Input}
    (hopen : token ≠ .parenOpen) (hclose : token ≠ .parenClose)
    (hconstant : ∀ constant, token ≠ .constant constant)
    (hsymbol : ∀ symbol, token ≠ .symbol symbol) (hkeyword : ∀ name, token ≠ .keyword name)
    (hreserved : ∀ word, token = .reserved word → ¬ version ≥ .v2_6) :
    Rejects version (ClosedAttributeParser.new (H := H))
      (.keyword name :: .parenOpen :: (itemTokens ++ (tokens ++ [token])))
      ((fun _ => ()) <$> (adaptRun (Traversal.sExprs noPoints h items) >>= fun _ =>
        adaptRun (frames.mapM fun items => Traversal.sExprs noPoints h items)))
      .expectedSExpr := by
  have hruns := sExpr_value_runs true hA name hitems hsItems hframes hs hopen hclose hconstant
    hsymbol hkeyword hreserved
  have hembed := (singleStep_embed hruns).congr
    (next' := fun _ => throw (Parser.ParseErrorCause.syntax .expectedSExpr)) rfl (by
      funext a
      apply ExceptT.ext
      simp [ExceptT.run_throw])
  have := rejects_of_runsS (state := AttributeState.init) (@closedAttribute_hparse H m _ _)
    (closedAttribute_sim version) hembed
  simp only [Functor.map_map] at this
  exact this

/--
The parser of attributes up to a `)` on a keyword, `(`, the tokens of valid items, of open lists
of s-expressions and a token that starts no s-expression and does not end a list: it rejects that
token with `expectedSExpr`, having made the traversal's calls for the items.
-/
theorem closedMultipleAttribute_rejects_sExpr {version : Token.Version}
    {h : Traversal.Handler (StateT H m) (Traits.Handler.Error H) (valuesOf H)}
    (hA : TermAgrees h) (name : BSmtLib.Plain.KeywordView) {items : List Tree.SExpr}
    (hitems : Tree.SExpr.ValidAll (Bridge.version version) items)
    {itemTokens : List Parser.Internal.Input}
    (hsItems : Stands itemTokens (Tree.SExpr.tokensAll items))
    {frames : List (List Tree.SExpr)}
    (hframes : ∀ items ∈ frames, Tree.SExpr.ValidAll (Bridge.version version) items)
    {tokens : List Parser.Internal.Input} (hs : Stands tokens (sExprFrameTokens frames))
    {token : Parser.Internal.Input}
    (hopen : token ≠ .parenOpen) (hclose : token ≠ .parenClose)
    (hconstant : ∀ constant, token ≠ .constant constant)
    (hsymbol : ∀ symbol, token ≠ .symbol symbol) (hkeyword : ∀ name, token ≠ .keyword name)
    (hreserved : ∀ word, token = .reserved word → ¬ version ≥ .v2_6) :
    Rejects version (ClosedMultipleAttributeParser.new (H := H))
      (.keyword name :: .parenOpen :: (itemTokens ++ (tokens ++ [token])))
      ((fun _ => ()) <$> (adaptRun (Traversal.sExprs noPoints h items) >>= fun _ =>
        adaptRun (frames.mapM fun items => Traversal.sExprs noPoints h items)))
      .expectedSExpr := by
  have := rejects_of_runsS (state := AttributeState.init)
    (@closedMultipleAttribute_hparse H m _ _) (closedMultipleAttribute_sim version)
    (sExpr_value_runs false hA name hitems hsItems hframes hs hopen hclose hconstant hsymbol
      hkeyword hreserved)
  simp only [Functor.map_map] at this
  exact this

end

end BSmtLib.Facts.Proofs.Parser.Category.Attribute
