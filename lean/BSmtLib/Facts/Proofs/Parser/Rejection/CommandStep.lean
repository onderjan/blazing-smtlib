module

public import BSmtLib.Facts.Proofs.Parser.Rejection.Payload
import all BSmtLib.Parser
import all BSmtLib.Parser.Command
import all BSmtLib.Parser.Command.Internal.Standard
import all BSmtLib.Lexicon.Reserved
import all BSmtLib.Parser.Category.Attribute

@[expose] public section

/-!
# The steps of the command parser advance

The command parser takes `(`, then a command's name, from which its payload parser starts: the
remainders of the payload's initial state, after the `(` and the name, are valid commands
(`payloadInit_command`), which needs the version to reserve the name, as a lexer
hands it over.
-/

namespace BSmtLib.Facts.Proofs.Parser.Rejection.CommandStep

open BSmtLibSpec.Grammar
open BSmtLibSpec.Parser.Properties
open BSmtLibSpec.Parser.Traversal
open BSmtLib.Parser.Command.Internal.Datatype (SortDecState DatatypeState)
open BSmtLib.Parser.Command.Internal.Standard (LiteralState Payload NamedCommand FinalCall
    Declaration
    payloadStep)
open BSmtLib.Parser.Command.Internal.Function (SignatureState FunctionDecState)
open BSmtLib.Parser.Command.Internal.Definition (DefinitionEnd)
open BSmtLib.Parser.Command (CommandOutcome)
open BSmtLib.Parser.Command.Internal (CommandState commandStep)
open BSmtLib.Facts.Parser.Adapters.Bridge BSmtLib.Facts.Proofs.Parser.Rejection.Basic
open BSmtLib.Facts.Proofs.Parser.Rejection.Command
open BSmtLib.Facts.Proofs.Parser.Rejection.CommandParts BSmtLib.Facts.Proofs.Parser.Rejection.Parts
open BSmtLib.Facts.Proofs.Parser.Rejection.Payload BSmtLib.Facts.Proofs.Parser.Rejection.SExpr
open BSmtLib.Facts.Proofs.Parser.Rejection.«Sort» BSmtLib.Facts.Proofs.Parser.Rejection.Term

open BSmtLib.Facts.Proofs.Parser.Rejection.Basic.Lang

/-! ## Command names -/

/-- The version a command first appears in. -/
def commandAddedIn : Lexicon.Reserved.CommandNameReserved → BSmtLibSpec.Lexicon.Version
  | .checkSatAssuming | .declareConst | .defineFunRec | .defineFunsRec | .echo | .getModel
  | .getUnsatAssumptions | .reset | .resetAssertions => .v2_5
  | .declareDatatype | .declareDatatypes => .v2_6
  | .declareSortParameter | .defineConst => .v2_7
  | _ => .v2_0

set_option maxHeartbeats 2000000 in
/-- A command name that the version reserves names a command that the version has. -/
theorem commandName_lexical {version : Version} {name : Lexicon.Reserved.CommandNameReserved}
    (h : (Received.token (.reserved (Bridge.reserved (.commandName name)))).OfVersion
      (Bridge.version version)) :
    versionAtLeast (Bridge.version version) (commandAddedIn name) := by
  simp only [Received.OfVersion] at h
  simp only [versionAtLeast]
  revert h
  cases version <;> cases name <;> decide

/-- How a `set-info` ends, from its tokens. -/
theorem cmdEnd_setInfo (v : BSmtLibSpec.Lexicon.Version) (keyword : BSmtLibSpec.Regex.Chars)
    (value : Option Tree.AttributeValue) :
    cmdEnd v (.setInfo ⟨keyword, value⟩) =
      setInfoEnd v .start (toks (Tree.Attribute.tokens ⟨keyword, value⟩) ++ [closeItem]) := by
  by_cases hk : keyword = BSmtLibSpec.Regex.chars "smt-lib-version"
  · subst hk
    rcases value with _ | ((_ | d | _ | _ | _) | s | items) <;>
      simp [cmdEnd, Tree.Command.modeAfter, Tree.Attribute.tokens, setInfoEnd, declarationEnd,
        Tree.AttributeValue.tokens, Tree.SpecConstant.token, paren]
    cases versionOfNumber d <;> rfl
  · rcases value with _ | value <;>
      simp [cmdEnd, Tree.Command.modeAfter, Tree.Attribute.tokens, setInfoEnd, hk]

/-! ## From the payload's start to the command -/

/-- The name of a command, as the item a lexer hands over for it. -/
abbrev nameItem (name : Lexicon.Reserved.CommandNameReserved) : Received :=
  .token (.reserved (Bridge.reserved (.commandName name)))

section

variable (version : Version) (follows : CmdEnd → Lang)

/-- A command's tokens, from its `(`, its name and the rest. -/
macro "command_tokens" : tactic => `(tactic|
  (simp [Tree.Command.tokens, commandTokens, paren, toks, word, Bridge.reserved,
    Lexicon.Reserved.CommandNameReserved.asStr, Tree.FunctionDef.tokens, Tree.Attribute.tokens,
    Tree.AttributeValue.tokens, Tree.PropLiteral.tokens, List.flatMap, Function.comp_def,
    termTokensAll_eq, sortTokensAll_eq] <;> rfl))

/-- The remainder of a command that ends at its next token, a `)`. -/
theorem closeNext_split {v : BSmtLibSpec.Lexicon.Version} {u : List Received}
    (h : closeNext v follows u) : ∃ w, follows (.next v) w ∧ u = closeItem :: w := by
  obtain ⟨_, w, rfl, hw, rfl⟩ := h
  exact ⟨w, hw, rfl⟩

theorem reps_exact {A : Lang} {T : Type} {P : T → Prop} {f : T → List Received}
    (hA : ∀ u, A u ↔ ∃ t, P t ∧ u = f t) {n : Nat} {u : List Received} (h : rep A n (some n) u) :
    ∃ ts : List T, (∀ t ∈ ts, P t) ∧ ts.length = n ∧ u = (ts.map f).flatten := by
  have h' : rep (fun w => ∃ t, P t ∧ w = f t) n (some n) u := by
    obtain ⟨ws, hws, hlo, hhi, rfl⟩ := h
    exact ⟨ws, fun w hw => (hA w).mp (hws w hw), hlo, hhi, rfl⟩
  obtain ⟨ts, hts, hlo, hhi, rfl⟩ := rep_trees h'
  exact ⟨ts, hts, by have := hhi n rfl; omega, rfl⟩

set_option maxHeartbeats 1000000 in
/-- After a command's `(` and name, the remainders of its payload's start are commands of the
version, followed by what follows each. -/
theorem payloadInit_command (name : Lexicon.Reserved.CommandNameReserved)
    (hlex : (nameItem name).OfVersion (Bridge.version version)) {u : List Received}
    (hu : payloadRem (Bridge.version version) follows (Payload.init name version) u) :
    CommandLang (Bridge.version version) follows (openItem :: nameItem name :: u) := by
  have hv := commandName_lexical hlex
  cases name <;> simp only [Payload.init] at hu
  case assert =>
    obtain ⟨t, w, ht, ⟨_, w, rfl, hw, rfl⟩, rfl⟩ := hu
    obtain ⟨term, hterm, rfl⟩ := termRem_init t ht
    exact ⟨.assert term, w, hterm, hw, by command_tokens⟩
  case checkSat =>
    obtain ⟨w, hw, rfl⟩ := closeNext_split follows hu
    exact ⟨.checkSat, w, trivial, hw, by command_tokens⟩
  case checkSatAssuming =>
    split at hu
    · rename_i h27
      obtain ⟨l, _, hl, ⟨_, w, rfl, hw, rfl⟩, rfl⟩ := hu
      obtain ⟨ts, hts, rfl⟩ := listRem_paren termRem_init hl
      obtain ⟨terms, hvalid, -, rfl⟩ := terms_rep hts
      exact ⟨.checkSatAssuming terms, w, ⟨atLeast_v2_7_of_ge' h27, hvalid⟩, hw, by command_tokens⟩
    · rename_i h27
      obtain ⟨l, _, hl, ⟨_, w, rfl, hw, rfl⟩, rfl⟩ := hu
      obtain ⟨ls, hls, rfl⟩ := listRem_paren literalRem_init hl
      obtain ⟨lits, hvalid, -, -, rfl⟩ := rep_trees hls
      exact ⟨.checkSatAssumingLiterals lits, w, ⟨hv, not_atLeast_v2_7_of_lt h27, hvalid⟩, hw,
        by command_tokens⟩
  case declareConst =>
    obtain ⟨_, _, ⟨s, rfl⟩, ⟨_, _, ⟨sort, hsort, rfl⟩, ⟨_, w, rfl, hw, rfl⟩, rfl⟩, rfl⟩ := hu
    exact ⟨.declareConst s sort, w, ⟨hv, hsort⟩, hw, by command_tokens⟩
  case declareDatatype =>
    obtain ⟨_, _, ⟨s, rfl⟩, ⟨_, _, ⟨d, hd, rfl⟩, ⟨_, w, rfl, hw, rfl⟩, rfl⟩, rfl⟩ := hu
    exact ⟨.declareDatatype s d, w, ⟨hv, hd⟩, hw, by command_tokens⟩
  case declareDatatypes =>
    obtain ⟨n, hn, l, _, hl, ⟨_, _, rfl, ⟨ds, _, hds, ⟨_, _, rfl, ⟨_, w, rfl, hw, rfl⟩, rfl⟩,
      rfl⟩, rfl⟩, rfl⟩ := hu
    obtain ⟨ss, hss, rfl⟩ := listRem_paren_hi (fun _ h => h) hl
    obtain ⟨sorts, -, hsorts, rfl⟩ := reps_exact (P := fun _ : Tree.SortDec => True)
      (f := fun d => toks d.tokens) (fun _ => ⟨fun ⟨d, h⟩ => ⟨d, trivial, h⟩,
        fun ⟨d, _, h⟩ => ⟨d, h⟩⟩) hss
    obtain ⟨datatypes, hvalid, hdatatypes, rfl⟩ := reps_exact (P := fun d : Tree.DatatypeDec =>
      d.Valid (Bridge.version version)) (f := fun d => toks d.tokens) (fun _ => Iff.rfl) hds
    refine ⟨.declareDatatypes sorts datatypes, w, ⟨hv, ?_, by omega, hvalid⟩, hw, by
      command_tokens⟩
    rintro rfl
    simp at hsorts
    omega
  case declareFun =>
    obtain ⟨_, _, ⟨s, rfl⟩, ⟨_, _, rfl, ⟨ps, _, hps, ⟨_, _, rfl, ⟨_, _, ⟨result, hresult, rfl⟩,
      ⟨_, w, rfl, hw, rfl⟩, rfl⟩, rfl⟩, rfl⟩, rfl⟩, rfl⟩ := hu
    obtain ⟨parameters, hvalid, -, rfl⟩ := sorts_rep hps
    exact ⟨.declareFun s parameters result, w, ⟨hvalid, hresult⟩, hw, by command_tokens⟩
  case declareSort =>
    obtain ⟨_, _, ⟨s, rfl⟩, ⟨_, _, ⟨d, rfl⟩, ⟨_, w, rfl, hw, rfl⟩, rfl⟩, rfl⟩ := hu
    exact ⟨.declareSort s d, w, trivial, hw, by command_tokens⟩
  case declareSortParameter =>
    obtain ⟨_, _, ⟨s, rfl⟩, ⟨_, w, rfl, hw, rfl⟩, rfl⟩ := hu
    exact ⟨.declareSortParameter s, w, hv, hw, by command_tokens⟩
  case defineConst =>
    obtain ⟨_, _, ⟨s, rfl⟩, ⟨_, _, ⟨sort, hsort, rfl⟩, ⟨_, _, ⟨term, hterm, rfl⟩,
      ⟨_, w, rfl, hw, rfl⟩, rfl⟩, rfl⟩, rfl⟩ := hu
    exact ⟨.defineConst s sort term, w, ⟨hv, hsort, hterm⟩, hw, by command_tokens⟩
  case defineFun =>
    obtain ⟨_, _, ⟨_, _, ⟨s, rfl⟩, ⟨_, _, rfl, ⟨ps, _, hps, ⟨_, _, rfl, ⟨result, hresult, rfl⟩,
      rfl⟩, rfl⟩, rfl⟩, rfl⟩, ⟨_, _, ⟨body, hbody, rfl⟩, ⟨_, w, rfl, hw, rfl⟩, rfl⟩, rfl⟩ := hu
    obtain ⟨parameters, hvalid, -, rfl⟩ := sortedVars_rep hps
    exact ⟨.defineFun ⟨s, parameters, result, body⟩, w, ⟨hvalid, hresult, hbody⟩, hw,
      by command_tokens⟩
  case defineFunRec =>
    obtain ⟨_, _, ⟨_, _, ⟨s, rfl⟩, ⟨_, _, rfl, ⟨ps, _, hps, ⟨_, _, rfl, ⟨result, hresult, rfl⟩,
      rfl⟩, rfl⟩, rfl⟩, rfl⟩, ⟨_, _, ⟨body, hbody, rfl⟩, ⟨_, w, rfl, hw, rfl⟩, rfl⟩, rfl⟩ := hu
    obtain ⟨parameters, hvalid, -, rfl⟩ := sortedVars_rep hps
    exact ⟨.defineFunRec ⟨s, parameters, result, body⟩, w, ⟨hv, hvalid, hresult, hbody⟩, hw,
      by command_tokens⟩
  case defineFunsRec =>
    obtain ⟨n, hn, l, _, hl, ⟨_, _, rfl, ⟨bs, _, hbs, ⟨_, _, rfl, ⟨_, w, rfl, hw, rfl⟩, rfl⟩,
      rfl⟩, rfl⟩, rfl⟩ := hu
    obtain ⟨fs, hfs, rfl⟩ := listRem_paren_hi (fun _ h => h) hl
    obtain ⟨decls, hdecls, hlen, rfl⟩ := reps_exact (P := fun d : Tree.FunctionDec =>
      d.Valid (Bridge.version version)) (f := fun d => toks d.tokens) (fun _ => Iff.rfl) hfs
    obtain ⟨bodies, hbodies, hlen', rfl⟩ := reps_exact (P := fun t : Tree.Term =>
      t.Valid (Bridge.version version)) (f := fun t => toks t.tokens) (fun _ => Iff.rfl) hbs
    refine ⟨.defineFunsRec decls bodies, w, ⟨hv, ?_, by omega, hdecls, termValidAll_of hbodies⟩,
      hw, by command_tokens⟩
    rintro rfl
    simp at hlen
    omega
  case defineSort =>
    obtain ⟨_, _, ⟨s, rfl⟩, ⟨_, _, rfl, ⟨ps, _, hps, ⟨_, _, rfl, ⟨_, _, ⟨sort, hsort, rfl⟩,
      ⟨_, w, rfl, hw, rfl⟩, rfl⟩, rfl⟩, rfl⟩, rfl⟩, rfl⟩ := hu
    obtain ⟨parameters, -, rfl⟩ := symbols_rep hps
    exact ⟨.defineSort s parameters sort, w, hsort, hw, by command_tokens⟩
  case echo =>
    obtain ⟨_, _, ⟨c, rfl⟩, ⟨_, w, rfl, hw, rfl⟩, rfl⟩ := hu
    exact ⟨.echo c, w, hv, hw, by command_tokens⟩
  case exit =>
    obtain ⟨_, w, rfl, hw, rfl⟩ := hu
    exact ⟨.exit, w, trivial, hw, by command_tokens⟩
  case getAssertions =>
    obtain ⟨w, hw, rfl⟩ := closeNext_split follows hu
    exact ⟨.getAssertions, w, trivial, hw, by command_tokens⟩
  case getAssignment =>
    obtain ⟨w, hw, rfl⟩ := closeNext_split follows hu
    exact ⟨.getAssignment, w, trivial, hw, by command_tokens⟩
  case getInfo =>
    obtain ⟨_, _, ⟨k, rfl⟩, ⟨_, w, rfl, hw, rfl⟩, rfl⟩ := hu
    exact ⟨.getInfo k, w, trivial, hw, by command_tokens⟩
  case getModel =>
    obtain ⟨w, hw, rfl⟩ := closeNext_split follows hu
    exact ⟨.getModel, w, hv, hw, by command_tokens⟩
  case getOption =>
    obtain ⟨_, _, ⟨k, rfl⟩, ⟨_, w, rfl, hw, rfl⟩, rfl⟩ := hu
    exact ⟨.getOption k, w, trivial, hw, by command_tokens⟩
  case getProof =>
    obtain ⟨w, hw, rfl⟩ := closeNext_split follows hu
    exact ⟨.getProof, w, trivial, hw, by command_tokens⟩
  case getUnsatAssumptions =>
    obtain ⟨w, hw, rfl⟩ := closeNext_split follows hu
    exact ⟨.getUnsatAssumptions, w, hv, hw, by command_tokens⟩
  case getUnsatCore =>
    obtain ⟨w, hw, rfl⟩ := closeNext_split follows hu
    exact ⟨.getUnsatCore, w, trivial, hw, by command_tokens⟩
  case getValue =>
    obtain ⟨l, _, hl, ⟨_, w, rfl, hw, rfl⟩, rfl⟩ := hu
    obtain ⟨ts, hts, rfl⟩ := listRem_paren termRem_init hl
    obtain ⟨terms, hvalid, hlen, rfl⟩ := terms_rep hts
    refine ⟨.getValue terms, w, ⟨?_, hvalid⟩, hw, by command_tokens⟩
    rintro rfl
    simp at hlen
  case pop =>
    obtain ⟨_, _, ⟨d, rfl⟩, ⟨_, w, rfl, hw, rfl⟩, rfl⟩ := hu
    exact ⟨.pop d, w, trivial, hw, by command_tokens⟩
  case push =>
    obtain ⟨_, _, ⟨d, rfl⟩, ⟨_, w, rfl, hw, rfl⟩, rfl⟩ := hu
    exact ⟨.push d, w, trivial, hw, by command_tokens⟩
  case reset =>
    obtain ⟨w, hw, rfl⟩ := closeNext_split follows hu
    exact ⟨.reset, w, hv, hw, by command_tokens⟩
  case resetAssertions =>
    obtain ⟨w, hw, rfl⟩ := closeNext_split follows hu
    exact ⟨.resetAssertions, w, hv, hw, by command_tokens⟩
  case setInfo =>
    obtain ⟨-, a, b, ha, hb, rfl⟩ := hu
    simp only [attrRem, ite_true, Parser.Category.Attribute.Internal.AttributeState.init,
        Array.isEmpty_empty] at ha
    obtain ⟨_, _, ⟨⟨keyword, value⟩, hvalid, rfl⟩, rfl, rfl⟩ := ha
    refine ⟨.setInfo ⟨keyword, value⟩, b, hvalid, ?_, by command_tokens⟩
    rw [cmdEnd_setInfo]
    exact hb
  case setLogic =>
    obtain ⟨_, _, ⟨s, rfl⟩, ⟨_, w, rfl, hw, rfl⟩, rfl⟩ := hu
    exact ⟨.setLogic s, w, trivial, hw, by command_tokens⟩
  case setOption =>
    obtain ⟨a, w, ha, hw, rfl⟩ := hu
    simp only [attrRem, ite_true, Parser.Category.Attribute.Internal.AttributeState.init,
        Array.isEmpty_empty] at ha
    obtain ⟨_, _, ⟨attr, hvalid, rfl⟩, rfl, rfl⟩ := ha
    exact ⟨.setOption attr, w, hvalid, hw, by command_tokens⟩

variable (hfollows : ∀ e, ∃ w, follows e w)

include hfollows in
/-- The payload's start has a remainder. -/
theorem payloadInit_nonempty (name : Lexicon.Reserved.CommandNameReserved) :
    ∃ u, payloadRem (Bridge.version version) follows (Payload.init name version) u := by
  have hnext := closeNext_nonempty version follows (hfollows _)
  have hsym := symbolLang_nonempty
  have hsort := sortLang_nonempty (Bridge.version version)
  have hterm := termLang_nonempty (Bridge.version version)
  have htok : ∀ x, ∃ u, tok x u := fun x => ⟨_, tok_intro x⟩
  cases name <;> simp only [Payload.init]
  case assert => exact cat_nonempty (termRem_init_nonempty _) hnext
  case checkSatAssuming =>
    split
    · exact cat_nonempty (listRem_paren_nonempty (termRem_init_nonempty _) hterm (by simp)) hnext
    · exact cat_nonempty (listRem_paren_nonempty ⟨_, rfl, literalLang_nonempty.choose_spec⟩
        literalLang_nonempty (by simp)) hnext
  case declareConst => exact cat_nonempty hsym (cat_nonempty hsort hnext)
  case declareDatatype => exact cat_nonempty hsym (cat_nonempty (datatypeLang_nonempty _) hnext)
  case declareDatatypes =>
    obtain ⟨u, hu⟩ := cat_nonempty (listRem_paren_nonempty (lo := 1) (hi := some 1) (ρ := _)
      (sortDecRem_nonempty .start) (sortDecRem_nonempty .start) (by simp))
      (cat_nonempty (htok openItem) (cat_nonempty (rep_nonempty (datatypeLang_nonempty _) 1
        (some 1) (by simp)) (cat_nonempty (htok closeItem) hnext)))
    exact ⟨u, 1, Nat.le_refl _, hu⟩
  case declareFun =>
    exact cat_nonempty hsym (cat_nonempty (htok _) (cat_nonempty ⟨[], rep_nil⟩
      (cat_nonempty (htok _) (cat_nonempty hsort hnext))))
  case declareSort => exact cat_nonempty hsym (cat_nonempty ⟨_, [], rfl⟩ hnext)
  case declareSortParameter => exact cat_nonempty hsym hnext
  case defineConst => exact cat_nonempty hsym (cat_nonempty hsort (cat_nonempty hterm hnext))
  case defineFun =>
    exact cat_nonempty (signatureRem_start_nonempty _) (cat_nonempty hterm hnext)
  case defineFunRec =>
    exact cat_nonempty (signatureRem_start_nonempty _) (cat_nonempty hterm hnext)
  case defineFunsRec =>
    obtain ⟨u, hu⟩ := cat_nonempty (listRem_paren_nonempty (lo := 1) (hi := some 1) (ρ := _)
      (inner := functionDecRem (Bridge.version version)) (init := FunctionDecState.start)
      (functionDecLang_nonempty _) (functionDecLang_nonempty _) (by simp))
      (cat_nonempty (htok openItem) (cat_nonempty (rep_nonempty hterm 1 (some 1) (by simp))
        (cat_nonempty (htok closeItem) hnext)))
    exact ⟨u, 1, Nat.le_refl _, hu⟩
  case defineSort =>
    exact cat_nonempty hsym (cat_nonempty (htok _) (cat_nonempty ⟨[], rep_nil⟩
      (cat_nonempty (htok _) (cat_nonempty hsort hnext))))
  case echo => exact cat_nonempty ⟨_, [], rfl⟩ hnext
  case exit => exact cat_nonempty (htok _) (hfollows _)
  case getInfo => exact cat_nonempty ⟨_, [], rfl⟩ hnext
  case getOption => exact cat_nonempty ⟨_, [], rfl⟩ hnext
  case getValue =>
    exact cat_nonempty (listRem_paren_nonempty (termRem_init_nonempty _) hterm (by simp)) hnext
  case pop => exact cat_nonempty ⟨_, [], rfl⟩ hnext
  case push => exact cat_nonempty ⟨_, [], rfl⟩ hnext
  case setInfo =>
    obtain ⟨b, hb⟩ := hfollows (.next (Bridge.version version))
    refine ⟨_, rfl, [.token (.keyword []), closeItem], b, ?_, ?_, rfl⟩
    · simp only [attrRem, ite_true, Parser.Category.Attribute.Internal.AttributeState.init,
        Array.isEmpty_empty]
      exact cat_intro' ⟨⟨[], none⟩, trivial, rfl⟩ (tok_intro _) rfl
    · have hne : BSmtLibSpec.Regex.chars "smt-lib-version" ≠ [] := by decide
      simpa [setInfoEnd, hne] using hb
  case setLogic => exact cat_nonempty hsym hnext
  case setOption =>
    exact cat_nonempty (attrRem_nonempty _ _ _ _) (hfollows _)
  all_goals exact hnext

/-- What follows the command parser's last item, as the outcome says. -/
def commandFin (state : CommandState Nat Nat Nat Nat Nat Empty) (outcome : CommandOutcome)
    (u : List Received) : Prop :=
  ∀ w, follows (outcomeEnd (Bridge.version version) outcome) w →
    commandRem (Bridge.version version) follows state (u ++ w)

/-- The recording handler rejects every non-standard command at its name. -/
private theorem commandStep_symbol (version : Version) (symbol : Lexicon.Value.Symbol) :
    commandStep (H := List Event) version .opened (.symbol symbol) = throw (.handler ()) :=
  rfl

include hfollows in
/-- Every step of the command parser advances. -/
theorem commandStep_advances
    (state : CommandState Nat Nat Nat Nat Nat Empty) {token : Parser.Internal.Input}
    {item : Received} (hitem : Bridge.received token = some item)
    (hlex : item.OfVersion (Bridge.version version)) :
    Sound (Advances (commandRem (Bridge.version version) follows) (commandFin version follows)
        state item)
      (CmdFailure follows (commandRem (Bridge.version version) follows state) item)
      (commandStep (H := List Event) version state token) := by
  cases state with
  | awaiting =>
    cases token <;> simp only [commandStep]
    case parenOpen =>
      item_of hitem
      refine Sound.pure fun _ => ⟨fun u hu => Or.inl hu, ?_⟩
      obtain ⟨w, hw⟩ := hfollows (.next (Bridge.version version))
      exact ⟨_, .checkSat, w, trivial, hw, rfl⟩
    case endOfInput =>
      item_of hitem
      exact Sound.pure fun _ w hw => Or.inr (cat_tok hw)
    all_goals fail_step
  | opened =>
    cases token
    case symbol s =>
      rw [commandStep_symbol]
      exact Sound.throw (Or.inl trivial)
    all_goals simp only [commandStep]
    case reserved r =>
      cases r with
      | commandName name =>
        item_of hitem
        exact Sound.pure fun _ => ⟨fun u hu => payloadInit_command version follows name hlex hu,
          payloadInit_nonempty version follows hfollows name⟩
      | general => fail_step
    all_goals fail_step
  | payload payload =>
    simp only [commandStep]
    refine Sound.bind (payloadStep_advances version follows hfollows hitem hlex payload)
      fun r hr => ?_
    cases r with
    | more payload' => exact Sound.pure hr
    | done outcome => exact Sound.pure hr
  | nonstandard parser => nomatch parser

end

end BSmtLib.Facts.Proofs.Parser.Rejection.CommandStep
