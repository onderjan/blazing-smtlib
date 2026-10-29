module

public import BSmtLib.Facts.Proofs.Parser.Category.StepsSExpr
public import BSmtLib.Facts.Proofs.Parser.Attribute
import all BSmtLib.Parser
import all BSmtLib.Parser.Category.Attribute
import all BSmtLib.Parser.Category.SExpr
import all BSmtLib.Parser.Category.Token

@[expose] public section

/-!
# The attribute parser's steps, keeping where they stop

The lemmas of `Facts.Proofs.Parser.Attribute`, for `RunsS`.
-/

namespace BSmtLib.Facts.Proofs.Parser.Category.StepsAttribute

open BSmtLibSpec.Grammar
open BSmtLib.Parser.Internal (PM)
open BSmtLib.Parser.Category.Attribute.Internal (AttributeState AttributeMode attributeStep)
open BSmtLib.Parser.Category.SExpr.Internal (SExprState sExprStep sExprComplete)
open BSmtLib.Facts.Parser.Adapters.Bridge BSmtLib.Facts.Parser.Adapters.Run
open BSmtLib.Facts.Proofs.Parser.Drive BSmtLib.Facts.Proofs.Parser.Lemmas
open BSmtLib.Facts.Proofs.Parser.Category.StepsSExpr BSmtLib.Facts.Proofs.Parser.Tokens
open BSmtLib.Lexicon.Value
open BSmtLib.Facts.Proofs.Parser.Category.Steps
open BSmtLib.Facts.Proofs.Parser.Attribute (valueTokens attribute_tokens sExpr_first afterNext
  FollowsAttribute Stands.attribute)

open BSmtLibSpec.Parser
open BSmtLibSpec.Parser.Traversal
open BSmtLibSpec.Facts.Proofs.Parser.Equations (attributeThen_some attributeThen_none)


section

variable {H : Type} {m : Type → Type} [Monad m] [LawfulMonad m] [Handler H m]
variable {points : Points (StateT H m)} {version : Version}
variable {h : Traversal.Handler (StateT H m) (Handler.Error H) (valuesOf H)}

/--
The items of an attribute's list value: from between items, the parser reads the tokens of
S-expressions with the traversal's effects, and appends them to the items.
-/
theorem valueItems_runs (hA : TermAgrees h) (single : Bool) : (items : List Tree.SExpr) →
    Tree.SExpr.ValidAll (Bridge.version version) items →
    ∀ {tokens : List Parser.Internal.Input}, Stands tokens (Tree.SExpr.tokensAll items) →
    ∀ (keyword : Keyword) (found : Array (Handler.SExpr H))
      (attributes : Array (Handler.Attribute H)),
    RunsS points (attributeStep single version)
      { mode := .inside keyword found [] true, attributes } tokens
      (adaptRun (Traversal.sExprs points h items))
      fun handled =>
        pure (.more { mode := .inside keyword (found ++ handled.toArray) [] true, attributes })
  | [], _, _, hs, keyword, found, attributes => by
    have := Stands.eq_nil hs
    subst this
    exact (RunsS.nil [] (by simp)).congr (by simp [Traversal.sExprs]) rfl
  | first :: rest, hvalid, _, hs, keyword, found, attributes => by
    obtain ⟨tokens₁, tokens₂, rfl, hs₁, hs₂⟩ := Stands.split hs
    obtain ⟨token, tokens', rfl, htoken⟩ := sExpr_first hs₁
    have hembed := RunsS.embed (outer := attributeStep single version)
      (fun state => ({ mode := .inside keyword found state false, attributes } :
        AttributeState _ _))
      (fun item => pure (.more { mode := .inside keyword (found.push item) [] true, attributes }))
      (fun state token => by
        simp only [Parser.Category.Attribute.Internal.attributeStep.eq_def]
        simp
        congr 1
        funext step
        cases step <;> rfl)
      (sExpr_runs (points := points) hA first hvalid.1 hs₁ [])
    have hitem := RunsS.first (state := { mode := .inside keyword found [] true, attributes })
      (by cases token <;> simp_all [Parser.Category.Attribute.Internal.attributeStep.eq_def]) hembed
    have htail : ∀ r, RunsS points (attributeStep single version)
        { mode := .inside keyword (found.push r) [] true, attributes } tokens₂
        ((r :: ·) <$> adaptRun (Traversal.sExprs points h rest))
        fun handled =>
          pure (.more { mode := .inside keyword (found ++ handled.toArray) [] true, attributes }) :=
      fun r => RunsS.map_program ((valueItems_runs hA single rest hvalid.2 hs₂ keyword
        (found.push r) attributes).congr rfl (by funext handled; simp))
    refine (RunsS.append (middle := fun r =>
        ({ mode := .inside keyword (found.push r) [] true, attributes } : AttributeState _ _))
      (hitem.congr rfl (by funext; simp [sExprComplete,
          Parser.Internal.Step.wrap])) htail).congr ?_ rfl
    simp [Traversal.sExprs]

/--
The value of an attribute, from the state after its keyword: the parser reads it with the
traversal's effects and handles the attribute, before the token after it.
-/
theorem value_runs (hA : TermAgrees h) (single : Bool) (value : Tree.AttributeValue)
    (hvalid : value.Valid (Bridge.version version)) {tokens : List Parser.Internal.Input}
    (hs : Stands tokens value.tokens) (keyword : Keyword)
    (attributes : Array (Handler.Attribute H)) :
    RunsS points (attributeStep single version) { mode := .afterName keyword, attributes } tokens
      (adaptRun (do
        let node ← attributeValue points h value
        BSmtLibSpec.Facts.Proofs.Parser.Program.callAttribute h
          (.handleAttribute (Bridge.keyword keyword) (some node))))
      fun handled => pure (.more { mode := .start, attributes := attributes.push handled }) := by
  cases value with
  | constant constant =>
    obtain ⟨constant', rfl, rfl⟩ := Stands.constant hs
    refine (RunsS.token (program := Parser.Internal.call (Handler.handleAttribute keyword
      (some (.specialConstant constant'))))
          (by simp [Parser.Category.Attribute.Internal.attributeStep.eq_def])).congr ?_ rfl
    simp [attributeValue, adaptRun_take (token := .constant constant') rfl, hA.handleAttribute,
      Bridge.attributeValue]
  | symbol name =>
    obtain ⟨token, rfl, htoken⟩ := Stands.split_single hs
    obtain ⟨symbol, rfl, rfl⟩ := Parser.Internal.Input.received_symbol htoken
    refine (RunsS.token (program := Parser.Internal.call (Handler.handleAttribute keyword
      (some (.symbol symbol)))) (by simp [Parser.Category.Attribute.Internal.attributeStep.eq_def])).congr
          ?_ rfl
    simp [attributeValue, adaptRun_take htoken, hA.handleAttribute, Bridge.attributeValue]
  | list items =>
    obtain ⟨inner, rfl, hinner⟩ := Stands.split_paren hs
    have hclose : ∀ handled : List (Handler.SExpr H),
        RunsS points (attributeStep single version)
          { mode := .inside keyword (#[] ++ handled.toArray) [] true, attributes } [.parenClose]
          (do tick points .parenClose
              Parser.Internal.call (Handler.handleAttribute keyword
                (some (.sExprs (.new (#[] ++ handled.toArray))))))
          fun handled => pure (.more { mode := .start, attributes := attributes.push handled }) :=
      fun _ => RunsS.token (by simp [Parser.Category.Attribute.Internal.attributeStep.eq_def])
    rw [show Parser.Internal.Input.parenOpen :: (inner ++ [.parenClose]) =
      [.parenOpen] ++ (inner ++ [.parenClose]) by simp]
    refine (RunsS.append (middle := fun _ =>
        ({ mode := .inside keyword #[] [] true, attributes } : AttributeState _ _))
      (RunsS.token_more (by simp [Parser.Category.Attribute.Internal.attributeStep.eq_def])) fun _ =>
        RunsS.append (valueItems_runs hA single items hvalid hinner keyword #[] attributes)
          fun handled => hclose handled).congr ?_ rfl
    simp [attributeValue, adaptRun_take (token := .parenOpen) rfl,
      adaptRun_take (token := .parenClose) rfl, hA.handleAttribute, Bridge.attributeValue]

/-- Where the annotation's attribute parser is after the token that follows an attribute. -/
theorem attributeThen_runs (hA : TermAgrees h) (value : Option Tree.AttributeValue)
    (hvalid : ∀ v, value = some v → v.Valid (Bridge.version version))
    {tokens : List Parser.Internal.Input} (hs : Stands tokens (valueTokens value))
        (keyword : Keyword)
    {next : Parser.Internal.Input} {following : BSmtLibSpec.Grammar.SyntaxToken}
    (hnext : FollowsAttribute next following)
    (attributes : Array (Handler.Attribute H)) :
    RunsS points (attributeStep false version) { mode := .afterName keyword, attributes }
      (tokens ++ [next])
      (adaptRun (attributeThen points h (Bridge.keyword keyword) following value))
      fun handled => pure (afterNext next (attributes.push handled)) := by
  have hreceived : Bridge.received next = some (.token following) := by
    rcases hnext with ⟨rfl, rfl⟩ | ⟨_, rfl, rfl⟩ <;> rfl
  cases value with
  | none =>
    have := Stands.eq_nil hs
    subst this
    refine (RunsS.token (program := Parser.Internal.call (Handler.handleAttribute keyword none))
      ?_).congr ?_ rfl
    · rcases hnext with ⟨rfl, rfl⟩ | ⟨_, rfl, rfl⟩ <;>
        simp [Parser.Category.Attribute.Internal.attributeStep.eq_def, afterNext]
    · simp [attributeThen_none, adaptRun_take hreceived, hA.handleAttribute]
  | some value =>
    have hafter : ∀ handled, RunsS points (attributeStep false version)
        { mode := .start, attributes := attributes.push handled } [next]
        (do tick points next; pure handled)
        fun handled => pure (afterNext next (attributes.push handled)) := fun handled =>
      RunsS.token (by
        rcases hnext with ⟨rfl, rfl⟩ | ⟨_, rfl, rfl⟩ <;>
          simp [Parser.Category.Attribute.Internal.attributeStep.eq_def, afterNext])
    refine (RunsS.append (value_runs hA false value (hvalid value rfl) hs keyword attributes)
      hafter).congr ?_ rfl
    simp [attributeThen_some, adaptRun_take hreceived]

/-- The keyword of an attribute, as the parser takes it, and the tokens of its value. -/
theorem attributes_runs (hA : TermAgrees h) : (rest : List Tree.Attribute) →
    (∀ attr ∈ rest, attr.Valid (Bridge.version version)) →
    ∀ (keyword : Keyword) (value : Option Tree.AttributeValue),
    (∀ v, value = some v → v.Valid (Bridge.version version)) →
    ∀ {valueTokens' restTokens : List Parser.Internal.Input},
        Stands valueTokens' (valueTokens value) →
    Stands restTokens (rest.flatMap Tree.Attribute.tokens) →
    ∀ attributes : Array (Handler.Attribute H),
    RunsS points (attributeStep false version) { mode := .afterName keyword, attributes }
      (valueTokens' ++ restTokens ++ [.parenClose])
      (adaptRun (attributesThen points h (Bridge.keyword keyword) value rest))
      fun handled => pure (.done (attributes ++ handled.toArray))
  | [], _, keyword, value, hvalue, _, _, hs₁, hs₂, attributes => by
    have := Stands.eq_nil hs₂
    subst this
    simp only [List.append_nil]
    refine (RunsS.map_program (f := fun handled => [handled])
      ((attributeThen_runs hA value hvalue hs₁ keyword (Or.inl ⟨rfl, rfl⟩)
        attributes).congr rfl ?_)).congr ?_ rfl
    · funext
      simp [afterNext]
    · simp [attributesThen]
  | ⟨secondKeyword, secondValue⟩ :: rest, hvalid, keyword, value, hvalue, valueTokens', _, hs₁, hs₂,
      attributes => by
    simp only [List.flatMap_cons] at hs₂
    obtain ⟨secondTokens, restTokens', rfl, hsecond, hrest⟩ := Stands.split hs₂
    obtain ⟨name, secondValueTokens, rfl, hname, hsecondValue⟩ := Stands.«attribute» hsecond
    have hsecondValid : ∀ v, secondValue = some v → v.Valid (Bridge.version version) := by
      intro v hv
      have := hvalid _ (List.mem_cons_self ..)
      subst hv
      simpa [Tree.Attribute.Valid] using this
    have htail : ∀ handled, RunsS points (attributeStep false version)
        { mode := .afterName name, attributes := attributes.push handled }
        (secondValueTokens ++ restTokens' ++ [.parenClose])
        ((handled :: ·) <$> adaptRun (attributesThen points h (Bridge.keyword name)
          secondValue rest))
        fun handled => pure (.done (attributes ++ handled.toArray)) :=
      fun handled => RunsS.map_program ((attributes_runs hA rest
        (fun a ha => hvalid a (List.mem_cons_of_mem _ ha)) name secondValue hsecondValid
        hsecondValue hrest (attributes.push handled)).congr rfl (by funext; simp))
    rw [show valueTokens' ++
        (Parser.Internal.Input.keyword name :: secondValueTokens ++ restTokens') ++
        [.parenClose] =
      (valueTokens' ++ [.keyword name]) ++ (secondValueTokens ++ restTokens' ++ [.parenClose])
      by simp]
    refine (RunsS.append (middle := fun handled =>
        ({ mode := .afterName name, attributes := attributes.push handled } :
          AttributeState _ _))
      ((attributeThen_runs hA value hvalue hs₁ keyword (Or.inr ⟨name, rfl, rfl⟩)
        attributes).congr rfl (by funext; simp [afterNext])) htail).congr ?_ rfl
    subst hname
    simp [attributesThen]

/--
The attributes of an annotation up to the `)` after them, from the attribute parser's initial
state: the parser takes the first keyword, then handles the attributes with the traversal's
effects.
-/
theorem attributes_runs_init (hA : TermAgrees h) (first : Tree.Attribute)
    (rest : List Tree.Attribute)
    (hvalid : ∀ attr ∈ first :: rest, attr.Valid (Bridge.version version))
    {tokens : List Parser.Internal.Input}
    (hs : Stands tokens ((first :: rest).flatMap Tree.Attribute.tokens ++ [.parenClose])) :
    RunsS points (attributeStep false version) Parser.Category.Attribute.Internal.AttributeState.init tokens
      (adaptRun (do
        take points (.keyword first.keyword)
        attributesThen points h first.keyword first.value rest))
      fun handled => pure (.done handled.toArray) := by
  obtain ⟨keyword, value⟩ := first
  simp only [List.flatMap_cons, List.append_assoc] at hs
  obtain ⟨firstTokens, others, rfl, hfirst, hothers⟩ := Stands.split hs
  obtain ⟨restTokens, closing, rfl, hrest, hclosing⟩ := Stands.split hothers
  obtain ⟨close, rfl, hclose⟩ := Stands.split_single hclosing
  rw [Parser.Internal.Input.received_parenClose hclose]
  obtain ⟨name, valueTokens', rfl, hname, hvalueTokens⟩ := Stands.«attribute» hfirst
  have hvalue : ∀ v, value = some v → v.Valid (Bridge.version version) := by
    intro v hv
    have := hvalid _ (List.mem_cons_self ..)
    subst hv
    simpa [Tree.Attribute.Valid] using this
  rw [show Parser.Internal.Input.keyword name :: valueTokens' ++ (restTokens ++ [.parenClose]) =
    [.keyword name] ++ (valueTokens' ++ restTokens ++ [.parenClose]) by simp]
  refine (RunsS.append (middle := fun _ =>
      ({ mode := .afterName name, attributes := #[] } : AttributeState _ _))
    (RunsS.token_more (by simp [Parser.Category.Attribute.Internal.AttributeState.init,
    Parser.Category.Attribute.Internal.attributeStep.eq_def]))
      fun _ => attributes_runs hA rest (fun a ha => hvalid a (List.mem_cons_of_mem _ ha)) name
        value hvalue hvalueTokens hrest #[]).congr ?_ ?_
  · subst hname
    simp [adaptRun_take (token := .keyword name) rfl]
  · funext
    simp

/--
From its start, the parser of a single attribute reads an attribute and the `)` after it, and
ends with the handled attribute, as `set-info` and `set-option` read it.
-/
theorem attributeSingle_runs (hA : TermAgrees h) (keyword : BSmtLibSpec.Regex.Chars)
    (value : Option Tree.AttributeValue)
    (hvalid : (⟨keyword, value⟩ : Tree.Attribute).Valid (Bridge.version version))
    {tokens : List Parser.Internal.Input}
    (hs : Stands tokens (Tree.Attribute.tokens ⟨keyword, value⟩ ++ [.parenClose])) :
    RunsS points (attributeStep true version) .init tokens
      (adaptRun (do
        take points (.keyword keyword)
        attributeThen points h keyword .parenClose value))
      fun r => pure (.done #[r]) := by
  obtain ⟨attributeTokens, closing, rfl, hattribute, hclosing⟩ := Stands.split hs
  obtain ⟨close, rfl, hclose⟩ := Stands.split_single hclosing
  rw [Parser.Internal.Input.received_parenClose hclose]
  obtain ⟨name, valueTokens', rfl, rfl, hvalueTokens⟩ := Stands.«attribute» hattribute
  have hkeyword : RunsS points (attributeStep true version)
      Parser.Category.Attribute.Internal.AttributeState.init
      [.keyword name] (tick points (.keyword name))
      fun _ => pure (.more { mode := .afterName name, attributes := #[] }) :=
    RunsS.token_more (by simp [Parser.Category.Attribute.Internal.AttributeState.init,
        Parser.Category.Attribute.Internal.attributeStep.eq_def])
  rw [List.cons_append, show Parser.Internal.Input.keyword name :: (valueTokens' ++ [.parenClose]) =
    [.keyword name] ++ (valueTokens' ++ [.parenClose]) by rfl]
  cases value with
  | none =>
    have := Stands.eq_nil hvalueTokens
    subst this
    refine (RunsS.append (middle := fun _ =>
        ({ mode := .afterName name, attributes := #[] } : AttributeState _ _)) hkeyword
      fun _ => RunsS.token (program := Parser.Internal.call (Handler.handleAttribute name none))
        (by simp [Parser.Category.Attribute.Internal.attributeStep.eq_def])).congr ?_ rfl
    simp [attributeThen_none, adaptRun_take (token := .keyword name) rfl,
      adaptRun_take (token := .parenClose) rfl, hA.handleAttribute]
  | some value =>
    have hclose : ∀ handled : Handler.Attribute H, RunsS points (attributeStep true version)
        { mode := .start, attributes := #[handled] } [.parenClose]
        (do tick points .parenClose; pure handled)
        fun handled => pure (.done #[handled]) :=
      fun handled => RunsS.token (by simp [Parser.Category.Attribute.Internal.attributeStep.eq_def,
          Parser.Category.Token.Internal.expectClose])
    refine (RunsS.append (middle := fun _ =>
        ({ mode := .afterName name, attributes := #[] } : AttributeState _ _)) hkeyword
      fun _ => RunsS.append (middle := fun handled =>
          ({ mode := .start, attributes := #[handled] } : AttributeState _ _))
        ((value_runs hA true value (by simpa [Tree.Attribute.Valid] using hvalid)
          hvalueTokens name #[]).congr rfl (by funext; simp)) hclose).congr ?_ rfl
    simp [attributeThen_some, adaptRun_take (token := .keyword name) rfl,
      adaptRun_take (token := .parenClose) rfl]

end

end BSmtLib.Facts.Proofs.Parser.Category.StepsAttribute
