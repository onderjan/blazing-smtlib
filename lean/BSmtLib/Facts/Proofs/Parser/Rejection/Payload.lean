module

public import BSmtLib.Facts.Proofs.Parser.Rejection.Command
import all BSmtLib.Parser
import all BSmtLib.Parser.Category.Attribute
import all BSmtLib.Parser.Category.Sort
import all BSmtLib.Parser.Category.Token
import all BSmtLib.Parser.Command.Standard

@[expose] public section

/-!
# The steps of the payload parser advance

Each state of the payload parser, its step against its remainders. A step that finishes the
command, with the command parser's outcome, takes the command's `)` as the last item before what
follows the command as the outcome says (`cmdFin`). Only the `)` of a version declaration that
names no supported version fails with a rejection of a version declaration, and that `)` is the
last item before what follows a refused declaration (`CmdFailure`).
-/

namespace BSmtLib.Facts.Proofs.Parser.Rejection.Payload

open BSmtLibSpec.Grammar
open BSmtLibSpec.Parser.Properties
open BSmtLibSpec.Parser.Traversal
open BSmtLib.Parser (PM)
open BSmtLib.Parser.Category.Term (TermState)
open BSmtLib.Parser.Category.Combinator (ListState)
open BSmtLib.Parser.Command.Datatype (SortDecState DatatypeState)
open BSmtLib.Parser.Command.Standard (LiteralState Payload NamedCommand FinalCall Declaration
    payloadStep finalCall)
open BSmtLib.Parser.Command.Function (SignatureState FunctionDecState)
open BSmtLib.Parser.Command.Definition (DefinitionEnd)
open BSmtLib.Parser.Command (CommandState CommandOutcome)
open BSmtLib.Parser.Category.Attribute (AttributeState)
open BSmtLib.Parser.Category.Sort (SortState)
open BSmtLib.Facts.Parser.Adapters.Bridge BSmtLib.Facts.Proofs.Parser.Commands.Bytes
open BSmtLib.Facts.Proofs.Parser.Rejection.Basic BSmtLib.Facts.Proofs.Parser.Rejection.Command
open BSmtLib.Facts.Proofs.Parser.Rejection.CommandParts BSmtLib.Facts.Proofs.Parser.Rejection.Parts
open BSmtLib.Facts.Proofs.Parser.Rejection.SExpr BSmtLib.Facts.Proofs.Parser.Rejection.«Sort»
open BSmtLib.Facts.Proofs.Parser.Rejection.Term BSmtLib.Plain

open BSmtLib.Facts.Proofs.Parser.Rejection.Basic.Lang

section

variable (version : Token.Version) (follows : CmdEnd → Lang)
  (hfollows : ∀ e, ∃ w, follows e w)

/-- The command's last item, before what follows the command as the outcome says. -/
def cmdFin (state : Payload Nat Nat Nat Nat Nat) (outcome : CommandOutcome)
    (u : List Received) : Prop :=
  ∀ w, follows (outcomeEnd (Bridge.version version) outcome) w →
    payloadRem (Bridge.version version) follows state (u ++ w)

/-- The advance of a payload parser's step from the state. -/
abbrev PayloadAdvance (state : Payload Nat Nat Nat Nat Nat) (item : Received)
    (x : Quiet.RPM (Parser.Internal.Step (Payload Nat Nat Nat Nat Nat) CommandOutcome)) : Prop :=
  Sound (Advances (payloadRem (Bridge.version version) follows) (cmdFin version follows) state
    item) Benign x

theorem finalCall_sound (final : FinalCall Nat Nat Nat) :
    Sound (fun _ => True) Benign (finalCall (H := List Event) final) := by
  cases final <;> exact Sound.ofCall fun _ => ⟨_, _, rfl⟩

/-- The `)` of a command, before what follows it. -/
theorem closeNext_intro {w : List Received} (hw : follows (.next (Bridge.version version)) w) :
    closeNext (Bridge.version version) follows (closeItem :: w) :=
  cat_tok hw

theorem closeNext_nonempty (h : ∃ w, follows (.next (Bridge.version version)) w) :
    ∃ u, closeNext (Bridge.version version) follows u :=
  cat_nonempty ⟨_, tok_intro _⟩ h

variable {token : Parser.Internal.Input} {item : Received}
    (hitem : Bridge.received token = some item)
  (hlex : item.OfVersion (Bridge.version version))

include hitem in
theorem payload_closing (final : FinalCall Nat Nat Nat) :
    PayloadAdvance version follows (.closing final) item
      (payloadStep (H := List Event) version (.closing final) token) := by
  cases token <;> simp only [payloadStep, Parser.Category.Token.expectClose, pure_bind]
  case parenClose =>
    item_of hitem
    refine Sound.bind (finalCall_sound final) fun _ _ => ?_
    cases final <;> exact Sound.pure fun _ w hw => cat_intro' (tok_intro _) hw rfl
  all_goals fail_step

theorem closing_rem {v : BSmtLibSpec.Lexicon.Version} {follows : CmdEnd → Lang}
    {final : FinalCall Nat Nat Nat}
    (h : final ≠ .exit) : payloadRem v follows (.closing final) = closeNext v follows := by
  cases final <;> first | rfl | exact absurd rfl h

theorem sortRem_init {v : BSmtLibSpec.Lexicon.Version} :
    ∀ u, sortRem v Parser.Category.«Sort».SortState.init u → SortLang v u := fun _ h => by
  simpa [sortRem, Parser.Category.«Sort».SortState.init] using h

theorem sortRem_init_nonempty (v : BSmtLibSpec.Lexicon.Version) :
    ∃ u, sortRem v Parser.Category.«Sort».SortState.init u := sortRem_nonempty v _

include hitem hfollows in
theorem payload_named (command : NamedCommand) :
    PayloadAdvance version follows (.named command) item
      (payloadStep (H := List Event) version (.named command) token) := by
  have hnext := closeNext_nonempty version follows (hfollows _)
  cases token <;> simp only [payloadStep, Parser.Category.Token.expectSymbol, pure_bind]
  case symbol s =>
    item_of hitem
    have sym := symbolLang_intro (Bridge.symbol s)
    cases command
    case declareConst =>
      exact Sound.pure fun _ => ⟨fun u hu =>
        cat_intro' sym (cat_mono sortRem_init (fun _ h => h) hu) rfl,
        cat_nonempty (sortRem_init_nonempty _) hnext⟩
    case declareDatatype =>
      exact Sound.pure fun _ => ⟨fun u hu => cat_intro' sym hu rfl,
        cat_nonempty (datatypeLang_nonempty _) hnext⟩
    case declareFun =>
      refine Sound.pure fun _ => ⟨fun u hu => ?_, cat_nonempty (listRem_paren_nonempty
        (sortRem_init_nonempty _) (sortLang_nonempty _) (by simp))
        (cat_nonempty (sortLang_nonempty _) hnext)⟩
      obtain ⟨l, r, hl, hr, rfl⟩ := hu
      obtain ⟨w, hw, rfl⟩ := listRem_paren sortRem_init hl
      exact cat_intro' sym (cat_tok (cat_intro' hw (cat_tok hr) (by simp))) rfl
    case declareSort =>
      exact Sound.pure fun _ => ⟨fun u hu => cat_intro' sym hu rfl,
        cat_nonempty ⟨_, [], rfl⟩ hnext⟩
    case declareSortParameter =>
      exact Sound.pure fun _ => ⟨fun u hu => cat_intro' sym hu rfl, hnext⟩
    case defineConst =>
      exact Sound.pure fun _ => ⟨fun u hu =>
        cat_intro' sym (cat_mono sortRem_init (fun _ h => h) hu) rfl,
        cat_nonempty (sortRem_init_nonempty _) (cat_nonempty (termLang_nonempty _) hnext)⟩
    case defineSort =>
      refine Sound.pure fun _ => ⟨fun u hu => ?_, cat_nonempty (listRem_paren_nonempty
        symbolLang_nonempty symbolLang_nonempty (by simp))
        (cat_nonempty (sortLang_nonempty _) hnext)⟩
      obtain ⟨l, r, hl, hr, rfl⟩ := hu
      obtain ⟨w, hw, rfl⟩ := listRem_paren (fun _ h => h) hl
      exact cat_intro' sym (cat_tok (cat_intro' hw (cat_tok hr) (by simp))) rfl
    case setLogic =>
      exact Sound.pure fun _ => ⟨fun u hu => cat_intro' sym hu rfl, hnext⟩
  all_goals fail_step

include hitem hlex hfollows in
theorem payload_assert (state : TermState Nat Nat Nat Nat Nat) :
    PayloadAdvance version follows (.assert state) item
      (payloadStep (H := List Event) version (.assert state) token) := by
  have hnext := closeNext_nonempty version follows (hfollows _)
  simp only [payloadStep]
  refine Sound.bind (termStep_advances version state token item hitem hlex) fun r hr => ?_
  cases r with
  | more state' =>
    refine Sound.pure fun hne => ?_
    have hr := hr (cat_nonempty_left hne)
    exact ⟨fun u hu => cat_left hr.1 hu, cat_nonempty hr.2 hnext⟩
  | done term =>
    exact Sound.pure fun hne => ⟨fun u hu => cat_intro' (hr (cat_nonempty_left hne)) hu rfl, hnext⟩

include hitem hlex hfollows in
theorem payload_checkSatAssuming (state : ListState (TermState Nat Nat Nat Nat Nat) Nat) :
    PayloadAdvance version follows (.checkSatAssuming state) item
      (payloadStep (H := List Event) version (.checkSatAssuming state) token) := by
  have hnext := closeNext_nonempty version follows (hfollows _)
  simp only [payloadStep]
  refine Sound.bind (listStep_advances version Parser.Category.Term.TermState.init
      (termStep_advances version)
    (element := TermLang _) termRem_init (termRem_init_nonempty _) (termLang_nonempty _) 0 none
    (by simp) state token item hitem hlex) fun r hr => ?_
  cases r with
  | more state' =>
    refine Sound.pure fun hne => ?_
    have hr := hr (cat_nonempty_left hne)
    exact ⟨fun u hu => cat_left hr.1 hu, cat_nonempty hr.2 hnext⟩
  | done terms =>
    exact Sound.pure fun hne => ⟨fun u hu =>
      cat_intro' (hr (cat_nonempty_left hne) (Nat.zero_le _) (by simp)) hu rfl, hnext⟩

include hitem hlex hfollows in
theorem payload_checkSatAssumingLiterals
    (state : ListState (LiteralState Nat Nat Nat Nat Nat) Nat) :
    PayloadAdvance version follows (.checkSatAssumingLiterals state) item
      (payloadStep (H := List Event) version (.checkSatAssumingLiterals state) token) := by
  have hnext := closeNext_nonempty version follows (hfollows _)
  simp only [payloadStep]
  refine Sound.bind (listStep_advances version Parser.Command.Standard.LiteralState.init
    (literalStep_advances version) (element := LiteralLang) literalRem_init
    ⟨_, rfl, (literalLang_nonempty).choose_spec⟩ literalLang_nonempty 0 none (by simp) state token
    item hitem hlex) fun r hr => ?_
  cases r with
  | more state' =>
    refine Sound.pure fun hne => ?_
    have hr := hr (cat_nonempty_left hne)
    exact ⟨fun u hu => cat_left hr.1 hu, cat_nonempty hr.2 hnext⟩
  | done terms =>
    exact Sound.pure fun hne => ⟨fun u hu =>
      cat_intro' (hr (cat_nonempty_left hne) (Nat.zero_le _) (by simp)) hu rfl, hnext⟩

/-- A step of the payload parser that reads a sort, then the command's `)`. -/
macro "sort_then_close" hfollows:ident hitem:ident hlex:ident : tactic => `(tactic| (
  have hnext := closeNext_nonempty version follows ($hfollows _)
  simp only [payloadStep]
  refine Sound.bind (sortStep_advances version _ _ item $hitem $hlex) fun r hr => ?_
  replace hr := hr.from (sortRem_nonempty _ _)
  cases r with
  | more state' => exact Sound.pure fun _ => ⟨fun u hu => cat_left hr.1 hu, cat_nonempty hr.2 hnext⟩
  | done sort => exact Sound.pure fun _ => ⟨fun u hu => cat_intro' hr hu rfl, hnext⟩))

include hitem hlex hfollows in
theorem payload_declareConst (symbol : Nodes.Symbol) (state : SortState Nat) :
    PayloadAdvance version follows (.declareConst symbol state) item
      (payloadStep (H := List Event) version (.declareConst symbol state) token) := by
  sort_then_close hfollows hitem hlex

include hitem hlex hfollows in
theorem payload_declareFunResult (symbol : Nodes.Symbol) (parameters : Array Nat)
    (state : SortState Nat) :
    PayloadAdvance version follows (.declareFunResult symbol parameters state) item
      (payloadStep (H := List Event) version (.declareFunResult symbol parameters state)
        token) := by
  sort_then_close hfollows hitem hlex

include hitem hlex hfollows in
theorem payload_defineSortBody (state : SortState Nat) :
    PayloadAdvance version follows (.defineSortBody state) item
      (payloadStep (H := List Event) version (.defineSortBody state) token) := by
  sort_then_close hfollows hitem hlex

include hitem hlex hfollows in
theorem payload_declareFunParameters (symbol : Nodes.Symbol)
    (state : ListState (SortState Nat) Nat) :
    PayloadAdvance version follows (.declareFunParameters symbol state) item
      (payloadStep (H := List Event) version (.declareFunParameters symbol state) token) := by
  have hnext := closeNext_nonempty version follows (hfollows _)
  simp only [payloadStep]
  refine Sound.bind (listStep_advances version Parser.Category.«Sort».SortState.init
      (sortStep_advances version)
    (element := SortLang _) sortRem_init (sortRem_init_nonempty _) (sortLang_nonempty _) 0 none
    (by simp) state token item hitem hlex) fun r hr => ?_
  cases r with
  | more state' =>
    refine Sound.pure fun hne => ?_
    have hr := hr (cat_nonempty_left hne)
    exact ⟨fun u hu => cat_left hr.1 hu, cat_nonempty hr.2 (cat_nonempty (sortLang_nonempty _)
      hnext)⟩
  | done parameters =>
    exact Sound.pure fun hne => ⟨fun u hu => cat_intro'
      (hr (cat_nonempty_left hne) (Nat.zero_le _) (by simp))
      (cat_mono sortRem_init (fun _ h => h) hu) rfl,
      cat_nonempty (sortRem_init_nonempty _) hnext⟩

include hitem hfollows in
theorem payload_declareSort (symbol : Nodes.Symbol) :
    PayloadAdvance version follows (.declareSort symbol) item
      (payloadStep (H := List Event) version (.declareSort symbol) token) := by
  have hnext := closeNext_nonempty version follows (hfollows _)
  cases token <;> simp only [payloadStep, Parser.Category.Token.expectNumeral, bind_pure_comp]
  case constant c =>
    cases c <;> simp only <;> try fail_step
    item_of hitem
    exact Sound.pure fun _ => ⟨fun u hu => cat_intro' ⟨_, rfl⟩ hu rfl, hnext⟩
  all_goals fail_step

include hitem hfollows in
theorem payload_echo :
    PayloadAdvance version follows .echo item
      (payloadStep (H := List Event) version .echo token) := by
  have hnext := closeNext_nonempty version follows (hfollows _)
  cases token <;> simp only [payloadStep, Parser.Category.Token.expectString, bind_pure_comp]
  case constant c =>
    cases c <;> simp only <;> try fail_step
    item_of hitem
    exact Sound.pure fun _ => ⟨fun u hu => cat_intro' ⟨_, rfl⟩ hu rfl, hnext⟩
  all_goals fail_step

include hitem hfollows in
theorem payload_getInfo :
    PayloadAdvance version follows .getInfo item
      (payloadStep (H := List Event) version .getInfo token) := by
  have hnext := closeNext_nonempty version follows (hfollows _)
  cases token <;> simp only [payloadStep, Parser.Category.Token.expectKeyword, bind_pure_comp]
  case keyword k =>
    item_of hitem
    exact Sound.pure fun _ => ⟨fun u hu => cat_intro' ⟨_, rfl⟩ hu rfl, hnext⟩
  all_goals fail_step

include hitem hfollows in
theorem payload_getOption :
    PayloadAdvance version follows .getOption item
      (payloadStep (H := List Event) version .getOption token) := by
  have hnext := closeNext_nonempty version follows (hfollows _)
  cases token <;> simp only [payloadStep, Parser.Category.Token.expectKeyword, bind_pure_comp]
  case keyword k =>
    item_of hitem
    exact Sound.pure fun _ => ⟨fun u hu => cat_intro' ⟨_, rfl⟩ hu rfl, hnext⟩
  all_goals fail_step

include hitem hfollows in
theorem payload_pop :
    PayloadAdvance version follows .pop item
      (payloadStep (H := List Event) version .pop token) := by
  have hnext := closeNext_nonempty version follows (hfollows _)
  cases token <;> simp only [payloadStep, Parser.Category.Token.expectNumeral, bind_pure_comp]
  case constant c =>
    cases c <;> simp only <;> try fail_step
    item_of hitem
    exact Sound.pure fun _ => ⟨fun u hu => cat_intro' ⟨_, rfl⟩ hu rfl, hnext⟩
  all_goals fail_step

include hitem hfollows in
theorem payload_push :
    PayloadAdvance version follows .push item
      (payloadStep (H := List Event) version .push token) := by
  have hnext := closeNext_nonempty version follows (hfollows _)
  cases token <;> simp only [payloadStep, Parser.Category.Token.expectNumeral, bind_pure_comp]
  case constant c =>
    cases c <;> simp only <;> try fail_step
    item_of hitem
    exact Sound.pure fun _ => ⟨fun u hu => cat_intro' ⟨_, rfl⟩ hu rfl, hnext⟩
  all_goals fail_step

include hitem hlex hfollows in
theorem payload_declareDatatype (symbol : Nodes.Symbol) (state : DatatypeState Nat) :
    PayloadAdvance version follows (.declareDatatype symbol state) item
      (payloadStep (H := List Event) version (.declareDatatype symbol state) token) := by
  have hnext := closeNext_nonempty version follows (hfollows _)
  simp only [payloadStep]
  refine Sound.bind (datatypeStep_advances version (fun _ => Sound.ofCall fun _ => ⟨_, _, rfl⟩)
    state token item hitem hlex) fun r hr => ?_
  cases r with
  | more state' =>
    refine Sound.pure fun hne => ?_
    have hr := hr (cat_nonempty_left hne)
    exact ⟨fun u hu => cat_left hr.1 hu, cat_nonempty hr.2 hnext⟩
  | done constructors =>
    exact Sound.pure fun hne => ⟨fun u hu => cat_intro' (hr (cat_nonempty_left hne)) hu rfl, hnext⟩

include hitem hlex hfollows in
theorem payload_defineSortParameters (symbol : Nodes.Symbol)
    (state : ListState Unit Nodes.Symbol) :
    PayloadAdvance version follows (.defineSortParameters symbol state) item
      (payloadStep (H := List Event) version (.defineSortParameters symbol state) token) := by
  have hnext := closeNext_nonempty version follows (hfollows _)
  simp only [payloadStep]
  refine Sound.bind (listStep_advances version () (symbolStep_advances version) (fun _ h => h)
    symbolLang_nonempty symbolLang_nonempty 0 none (by simp) state token item hitem hlex)
    fun r hr => ?_
  cases r with
  | more state' =>
    refine Sound.pure fun hne => ?_
    have hr := hr (cat_nonempty_left hne)
    exact ⟨fun u hu => cat_left hr.1 hu, cat_nonempty hr.2 (cat_nonempty (sortLang_nonempty _)
      hnext)⟩
  | done parameters =>
    call_step
    exact Sound.pure fun hne => ⟨fun u hu => cat_intro'
      (hr (cat_nonempty_left hne) (Nat.zero_le _) (by simp))
      (cat_mono sortRem_init (fun _ h => h) hu) rfl,
      cat_nonempty (sortRem_init_nonempty _) hnext⟩

include hitem hlex hfollows in
theorem payload_defineConstSort (symbol : Nodes.Symbol) (state : SortState Nat) :
    PayloadAdvance version follows (.defineConstSort symbol state) item
      (payloadStep (H := List Event) version (.defineConstSort symbol state) token) := by
  have hnext := closeNext_nonempty version follows (hfollows _)
  simp only [payloadStep]
  refine Sound.bind (sortStep_advances version state token item hitem hlex) fun r hr => ?_
  replace hr := hr.from (sortRem_nonempty _ _)
  cases r with
  | more state' =>
    exact Sound.pure fun _ => ⟨fun u hu => cat_left hr.1 hu, cat_nonempty hr.2
      (cat_nonempty (termLang_nonempty _) hnext)⟩
  | done sort =>
    exact Sound.pure fun _ => ⟨fun u hu => cat_intro' hr (cat_mono termRem_init (fun _ h => h) hu)
      rfl, cat_nonempty (termRem_init_nonempty _) hnext⟩

include hitem hlex hfollows in
theorem payload_defineSignature (definition : DefinitionEnd Nat) (state : SignatureState Nat) :
    PayloadAdvance version follows (.defineSignature definition state) item
      (payloadStep (H := List Event) version (.defineSignature definition state) token) := by
  have hnext := closeNext_nonempty version follows (hfollows _)
  simp only [payloadStep]
  refine Sound.bind (signatureStep_advances version state token item hitem hlex) fun r hr => ?_
  cases r with
  | more state' =>
    refine Sound.pure fun hne => ?_
    have hr := hr (cat_nonempty_left hne)
    exact ⟨fun u hu => cat_left hr.1 hu, cat_nonempty hr.2
      (cat_nonempty (termLang_nonempty _) hnext)⟩
  | done signature =>
    simp only
    split <;>
    · call_step
      exact Sound.pure fun hne => ⟨fun u hu => cat_intro' (hr (cat_nonempty_left hne))
        (cat_mono termRem_init (fun _ h => h) hu) rfl,
        cat_nonempty (termRem_init_nonempty _) hnext⟩

include hitem hlex hfollows in
theorem payload_defineBody (definition : DefinitionEnd Nat)
    (state : TermState Nat Nat Nat Nat Nat) :
    PayloadAdvance version follows (.defineBody definition state) item
      (payloadStep (H := List Event) version (.defineBody definition state) token) := by
  have hnext := closeNext_nonempty version follows (hfollows _)
  simp only [payloadStep]
  refine Sound.bind (termStep_advances version state token item hitem hlex) fun r hr => ?_
  cases r with
  | more state' =>
    refine Sound.pure fun hne => ?_
    have hr := hr (cat_nonempty_left hne)
    exact ⟨fun u hu => cat_left hr.1 hu, cat_nonempty hr.2 hnext⟩
  | done body =>
    refine Sound.pure fun hne => ⟨fun u hu => ?_, ?_⟩
    · have hu : closeNext (Bridge.version version) follows u := by
        revert hu; cases definition <;> exact id
      exact cat_intro' (hr (cat_nonempty_left hne)) hu rfl
    · cases definition <;> exact hnext

include hitem hlex hfollows in
theorem payload_defineFunsRecBodies (signatures : Array (Nodes.Signature Nat))
    (state : ListState (TermState Nat Nat Nat Nat Nat) Unit) :
    PayloadAdvance version follows (.defineFunsRecBodies signatures state) item
      (payloadStep (H := List Event) version (.defineFunsRecBodies signatures state) token) := by
  have hnext := closeNext_nonempty version follows (hfollows _)
  simp only [payloadStep]
  refine Sound.bindOn (bodiesStep_advances version signatures.size state token item hitem hlex)
    (fun r => ∃ v, r = .done v) (bodiesStep_quiet _ _ _ _) fun r hr => ?_
  cases r with
  | more state' =>
    refine Sound.pure fun hne => ?_
    have hr := hr (cat_nonempty_left hne)
    exact ⟨fun u hu => cat_left hr.1 hu, cat_nonempty hr.2 hnext⟩
  | done bodies =>
    refine Sound.quietly ?_ ⟨bodies, rfl⟩
    simp only
    split
    · fail_step
    · rename_i hcount
      have hsize : bodies.size = signatures.size := by simpa using hcount
      exact Sound.pure fun hne => ⟨fun u hu => cat_intro' (hr (cat_nonempty_left hne)
        (by omega) (fun l hl => by cases hl; omega)) hu rfl, hnext⟩

include hitem hlex hfollows in
theorem payload_getValue (state : ListState (TermState Nat Nat Nat Nat Nat) Nat) :
    PayloadAdvance version follows (.getValue state) item
      (payloadStep (H := List Event) version (.getValue state) token) := by
  have hnext := closeNext_nonempty version follows (hfollows _)
  simp only [payloadStep]
  refine Sound.bindOn (listStep_advances version Parser.Category.Term.TermState.init
      (termStep_advances version)
    (element := TermLang _) termRem_init (termRem_init_nonempty _) (termLang_nonempty _) 1 none
    (by simp) state token item hitem hlex) (fun r => ∃ v, r = .done v) (listStep_quiet _ _ _ _ _)
    fun r hr => ?_
  cases r with
  | more state' =>
    refine Sound.pure fun hne => ?_
    have hr := hr (cat_nonempty_left hne)
    exact ⟨fun u hu => cat_left hr.1 hu, cat_nonempty hr.2 hnext⟩
  | done values =>
    refine Sound.quietly ?_ ⟨values, rfl⟩
    simp only
    split
    · fail_step
    · rename_i hne'
      have hlen : 1 ≤ values.size := by
        cases values using Array.casesOn with
        | mk l => cases l <;> simp_all
      exact Sound.pure fun hne => ⟨fun u hu => cat_intro' (hr (cat_nonempty_left hne) hlen
        (by simp)) hu rfl, hnext⟩

include hitem hlex hfollows in
theorem payload_setOption (state : AttributeState Nat Nat) :
    PayloadAdvance version follows (.setOption state) item
      (payloadStep (H := List Event) version (.setOption state) token) := by
  simp only [payloadStep]
  refine Sound.bindOn (attributeStep_advances version true false state token item hitem hlex)
    (fun r => ∃ a, r = .done a ∧ a.isEmpty = true) (attributeStep_quiet _ _ _ _) fun r hr => ?_
  replace hr := hr.from (attrRem_nonempty _ _ _ _)
  cases r with
  | more state' =>
    exact Sound.pure fun _ => ⟨fun u hu => cat_left hr.1 hu, cat_nonempty hr.2 (hfollows _)⟩
  | done attributes =>
    simp only
    split
    · refine Sound.loudly ?_
      call_step
      exact Sound.pure fun _ w hw => cat_intro' (hr nofun) hw rfl
    · rename_i hnone
      exact Sound.quietly (Sound.syntaxError trivial) ⟨attributes, rfl, isEmpty_of_none hnone⟩

include hitem hlex hfollows in
theorem payload_declareDatatypesSorts
    (state : ListState SortDecState (Nodes.Symbol × NumeralView)) :
    PayloadAdvance version follows (.declareDatatypesSorts state) item
      (payloadStep (H := List Event) version (.declareDatatypesSorts state) token) := by
  have hnext := closeNext_nonempty version follows (hfollows _)
  have hinit : ∃ u, sortDecRem .start u := sortDecRem_nonempty _
  have hwf : (∃ u, payloadRem (Bridge.version version) follows (.declareDatatypesSorts state) u) →
      ListWF sortDecRem .start state := by
    intro ⟨_, n, _, l, _, hl, _, _⟩
    exact listWF_of_rem hinit ⟨l, hl⟩
  simp only [payloadStep]
  refine Sound.bindOn (Sound.«forall» 1 fun n => listStep_implies version SortDecState.start
    (sortDecStep_advances version) (element := SortDecLang) (fun _ h => h) hinit hinit n (some n)
    (by simp) none state hitem hlex) (fun r => ∃ v, r = .done v) (listStep_quiet _ _ _ _ _)
    fun r hr => ?_
  cases r with
  | more state' =>
    refine Sound.pure fun hne => ⟨fun u hu => ?_, ?_⟩
    · obtain ⟨n, hn, l, b, hl, hb, rfl⟩ := hu
      exact ⟨n, hn, cat_intro' ((hr n (hwf hne)).1 l hl) hb rfl⟩
    · have hwf' := (hr 1 (hwf hne)).2.1
      have hopened := (hr 1 (hwf hne)).2.2.1
      obtain ⟨n, hn, l, hl⟩ := listRem_counted_nonempty hinit hinit hwf' hopened
      exact ⟨_, n, hn, cat_intro' hl (cat_tok (cat_intro' (rep_nonempty (datatypeLang_nonempty _)
        n (some n) (by simp)).choose_spec (cat_tok hnext.choose_spec) rfl)) rfl⟩
  | done sorts =>
    refine Sound.quietly ?_ ⟨sorts, rfl⟩
    simp only
    split
    · fail_step
    · rename_i hempty
      call_step
      have hlen : 1 ≤ sorts.size := by
        cases sorts using Array.casesOn with
        | mk l => cases l <;> simp_all
      refine Sound.pure fun hne => ⟨fun u hu => ?_, ?_⟩
      · obtain ⟨l, c, hl, hc, rfl⟩ := hu
        obtain ⟨w, hw, rfl⟩ := listRem_paren_hi (fun _ h => h) hl
        exact ⟨sorts.size, hlen, cat_intro' ((hr sorts.size) (hwf hne) (Nat.le_refl _)
          (fun l hl => by cases hl; omega)) (cat_tok (cat_intro' hw (cat_tok hc) rfl)) (by simp)⟩
      · exact cat_nonempty (listRem_paren_nonempty (inner := datatypeRem _)
          (init := DatatypeState.start) (datatypeLang_nonempty _)
          (datatypeLang_nonempty _) (by simp)) hnext

include hitem hlex hfollows in
theorem payload_defineFunsRecDeclarations
    (state : ListState (FunctionDecState Nat) (Nodes.Signature Nat)) :
    PayloadAdvance version follows (.defineFunsRecDeclarations state) item
      (payloadStep (H := List Event) version (.defineFunsRecDeclarations state) token) := by
  have hnext := closeNext_nonempty version follows (hfollows _)
  have hinit : ∃ u, functionDecRem (Bridge.version version) .start u :=
    functionDecLang_nonempty _
  have hwf : (∃ u, payloadRem (Bridge.version version) follows
      (.defineFunsRecDeclarations state) u) →
      ListWF (functionDecRem (Bridge.version version)) .start state := by
    intro ⟨_, n, _, l, _, hl, _, _⟩
    exact listWF_of_rem hinit ⟨l, hl⟩
  simp only [payloadStep]
  refine Sound.bindOn (Sound.«forall» 1 fun n => listStep_implies version FunctionDecState.start
    (functionDecStep_advances version) (element := FunctionDecLang _) (fun _ h => h) hinit hinit
    n (some n) (by simp) none state hitem hlex) (fun r => ∃ v, r = .done v)
    (listStep_quiet _ _ _ _ _) fun r hr => ?_
  cases r with
  | more state' =>
    refine Sound.pure fun hne => ⟨fun u hu => ?_, ?_⟩
    · obtain ⟨n, hn, l, b, hl, hb, rfl⟩ := hu
      exact ⟨n, hn, cat_intro' ((hr n (hwf hne)).1 l hl) hb rfl⟩
    · obtain ⟨n, hn, l, hl⟩ := listRem_counted_nonempty hinit hinit (hr 1 (hwf hne)).2.1
        (hr 1 (hwf hne)).2.2.1
      exact ⟨_, n, hn, cat_intro' hl (cat_tok (cat_intro' (rep_nonempty (termLang_nonempty _)
        n (some n) (by simp)).choose_spec (cat_tok hnext.choose_spec) rfl)) rfl⟩
  | done signatures =>
    refine Sound.quietly ?_ ⟨signatures, rfl⟩
    simp only
    split
    · fail_step
    · rename_i hempty
      call_step
      have hlen : 1 ≤ signatures.size := by
        cases signatures using Array.casesOn with
        | mk l => cases l <;> simp_all
      refine Sound.pure fun hne => ⟨fun u hu => ?_, ?_⟩
      · obtain ⟨l, c, hl, hc, rfl⟩ := hu
        obtain ⟨w, hw, rfl⟩ := listRem_paren_hi termRem_init hl
        exact ⟨signatures.size, hlen, cat_intro' ((hr signatures.size) (hwf hne) (Nat.le_refl _)
          (fun l hl => by cases hl; omega)) (cat_tok (cat_intro' hw (cat_tok hc) rfl)) (by simp)⟩
      · exact cat_nonempty (listRem_paren_nonempty (termRem_init_nonempty _)
          (termLang_nonempty _) (by simp)) hnext

include hitem hlex hfollows in
theorem payload_declareDatatypesDatatypes (count : Nat)
    (state : ListState (DatatypeState Nat) Unit) :
    PayloadAdvance version follows (.declareDatatypesDatatypes count state) item
      (payloadStep (H := List Event) version (.declareDatatypesDatatypes count state) token) := by
  have hnext := closeNext_nonempty version follows (hfollows _)
  simp only [payloadStep]
  refine Sound.bindOn (listStep_advances version DatatypeState.start ?step
    (inner := datatypeRem (Bridge.version version))
    (element := DatatypeLang (Bridge.version version))
    (fun _ h => h) (datatypeLang_nonempty _) (datatypeLang_nonempty _) count (some count)
    (by simp) state token item hitem hlex) (fun r => ∃ v, r = .done v) (listStep_quiet _ _ _ _ _)
    fun r hr => ?_
  case step =>
    intro state token item hitem hlex
    simp only
    refine Sound.bind (datatypeStep_advances version (fun _ => Sound.ofCall fun _ => ⟨_, _, rfl⟩)
      state token item hitem hlex) fun r hr => ?_
    cases r with
    | more state' => exact Sound.pure hr
    | done constructors =>
      call_step
      exact Sound.pure hr
  cases r with
  | more state' =>
    refine Sound.pure fun hne => ?_
    have hr := hr (cat_nonempty_left hne)
    exact ⟨fun u hu => cat_left hr.1 hu, cat_nonempty hr.2 hnext⟩
  | done datatypes =>
    refine Sound.quietly ?_ ⟨datatypes, rfl⟩
    simp only
    split
    · fail_step
    · rename_i hcount
      have hsize : datatypes.size = count := by simpa using hcount
      exact Sound.pure fun hne => ⟨fun u hu => cat_intro' (hr (cat_nonempty_left hne)
        (by omega) (fun l hl => by cases hl; omega)) hu rfl, hnext⟩

end

/-! ## `set-info` -/

theorem version_libVersion (v : BSmtLibSpec.Lexicon.Version) :
    Bridge.version (Bridge.libVersion v) = v := by
  cases v <;> rfl

/-- A single attribute's remainder of one item is its `)`. -/
theorem attrRem_single_one {v : BSmtLibSpec.Lexicon.Version} {state : AttributeState Nat Nat}
    {x : Received} (h : attrRem v true false state [x]) : x = closeItem := by
  obtain ⟨mode, attributes⟩ := state
  have hrest : ∀ u, valueRest v true u → 2 ≤ u.length := by
    rintro u ⟨s, _, -, ⟨_, t, rfl, ht, rfl⟩, rfl⟩
    simp only [attrTail, ite_true, tok] at ht
    subst ht
    simp
  cases mode with
  | start =>
    simp only [attrRem, ite_true] at h
    split at h
    · obtain ⟨a, b, ⟨attr, -, rfl⟩, rfl, hab⟩ := h
      rcases attr with ⟨k, _ | value⟩ <;> simp [Tree.Attribute.tokens] at hab
    · cases h
      rfl
  | afterName _ =>
    obtain ⟨a, b, ha, hb, hab⟩ := h
    simp only [attrTail, ite_true, tok] at hb
    subst hb
    rcases ha with ⟨value, -, rfl⟩ | rfl
    · rcases value with (c | s | items) <;> simp [Tree.AttributeValue.tokens, paren] at hab
    · simp at hab
      exact hab
  | inside _ _ sExpr outside =>
    simp only [attrRem] at h
    split at h
    · rcases h with ⟨_, t, rfl, ht, h⟩ | ⟨a, b, -, hb, hab⟩
      · simp only [attrTail, ite_true, tok] at ht
        subst ht
        simp at h
      · have := hrest b hb
        have := congrArg List.length hab
        simp at this
        omega
    · obtain ⟨a, b, -, hb, hab⟩ := h
      have := hrest b hb
      have := congrArg List.length hab
      simp at this
      omega

/-- The tracker of a version declaration follows how a `set-info` ends: after the item a token
stands for, the end from the new tracker on the rest is the end from the old one on the item and
the rest. -/
theorem setInfoEnd_next (v : BSmtLibSpec.Lexicon.Version) (declaration : Declaration)
    {token : Parser.Internal.Input}
    {x : Received} (hx : Bridge.received token = some x) (rest : List Received)
    (hvalue : declaration = .keyword → ∀ d, token = .constant (.decimal d) → rest = [closeItem]) :
    setInfoEnd v (declaration.next token) rest = setInfoEnd v declaration (x :: rest) := by
  cases declaration with
  | start =>
    cases token
    case layout => simp [Bridge.received] at hx
    case keyword k =>
      item_of hx
      simp only [Declaration.next]
      rw [isVersionKeyword_eq]
      by_cases hk : Bridge.keyword k = BSmtLibSpec.Regex.chars "smt-lib-version"
      · simp [hk, setInfoEnd]
      · simp [hk, setInfoEnd]
    case constant c => item_of hx; cases c <;> rfl
    all_goals item_of hx; rfl
  | other => rfl
  | keyword =>
    cases token
    case layout => simp [Bridge.received] at hx
    case constant c =>
      item_of hx
      cases c
      case decimal d =>
        simp only [Declaration.next]
        rw [hvalue rfl d rfl, fromDecimal_eq]
        simp only [setInfoEnd, declarationEnd]
        cases versionOfNumber (Bridge.chars d.asSlice) <;> simp [version_libVersion]
      all_goals rfl
    all_goals item_of hx; rfl
  | value r => cases r <;> rfl

section

variable (version : Token.Version) (follows : CmdEnd → Lang)
  (hfollows : ∀ e, ∃ w, follows e w)

/-- A failure of the command parser's step: no rejection of a version declaration, or the
rejection of one that names no supported version, whose item is the last before what follows
such a declaration. -/
def CmdFailure (rem : Lang) (item : Received) (e : Parser.ParseErrorCause Unit) : Prop :=
  Benign e ∨ ((∃ u, rem u) → e = .syntax .unsupportedVersion ∧
    ∀ w, follows .refused w → rem (item :: w))

variable {token : Parser.Internal.Input} {item : Received}
    (hitem : Bridge.received token = some item)
  (hlex : item.OfVersion (Bridge.version version))

include hitem hlex in
/-- Every `set-info` step makes no call before a rejection, from every state. -/
theorem setInfo_quiet (declaration : Declaration) (state : AttributeState Nat Nat) :
    Sound (fun _ => True) (fun _ => True)
      (payloadStep (H := List Event) version (.setInfo declaration state) token) := by
  simp only [payloadStep]
  refine Sound.bindOn ((attributeStep_advances version true false state token item hitem
    hlex).mono (fun _ _ => trivial) fun _ _ => trivial)
    (fun r => ∃ a, r = .done a ∧ a.isEmpty = true) (attributeStep_quiet _ _ _ _) fun r _ => ?_
  cases r with
  | more s => exact Sound.pure trivial
  | done attributes =>
    simp only
    split
    · refine Sound.loudly ?_
      call_step
      split <;> first | exact Sound.pure trivial | exact Sound.syntaxError ⟨⟨trivial, id⟩, id⟩
    · rename_i hnone
      exact Sound.quietly (Sound.syntaxError trivial) ⟨attributes, rfl, isEmpty_of_none hnone⟩

include hitem hlex in
/-- A `set-info` step from a state where the tracker and the attribute parser disagree: the state
has no remainder. -/
theorem setInfo_unsynced {declaration : Declaration} {state : AttributeState Nat Nat}
    (h : ¬ SetInfoSync declaration state) :
    Sound (Advances (payloadRem (Bridge.version version) follows) (cmdFin version follows)
        (.setInfo declaration state) item)
      (CmdFailure follows (payloadRem (Bridge.version version) follows (.setInfo declaration state))
        item) (payloadStep (H := List Event) version (.setInfo declaration state) token) := by
  refine (setInfo_quiet version hitem hlex declaration state).mono (fun r _ => ?_)
    fun _ _ => Or.inr fun ⟨_, hsync, _⟩ => absurd hsync h
  cases r <;> exact fun ⟨_, hsync, _⟩ => absurd hsync h

include hitem hlex hfollows in
theorem payload_setInfo (declaration : Declaration) (state : AttributeState Nat Nat) :
    Sound (Advances (payloadRem (Bridge.version version) follows) (cmdFin version follows)
        (.setInfo declaration state) item)
      (CmdFailure follows (payloadRem (Bridge.version version) follows (.setInfo declaration state))
        item)
      (payloadStep (H := List Event) version (.setInfo declaration state) token) := by
  by_cases hsync : SetInfoSync declaration state
  case neg => exact setInfo_unsynced version follows hitem hlex hsync
  cases declaration with
  | start =>
    obtain rfl : state = ⟨.start, #[]⟩ := hsync
    cases token <;> simp only [payloadStep, Parser.Category.Attribute.attributeStep,
        Declaration.next, pure_bind,
      Array.isEmpty_empty, Bool.and_true, Bool.not_true, Bool.and_false, Bool.false_eq_true,
      ite_false, ite_true, Parser.Category.Token.expectClose]
    case keyword name =>
      item_of hitem
      refine Sound.pure fun _ => ⟨fun u hu => ?_, ?_⟩
      · obtain ⟨-, a, b, ha, hb, rfl⟩ := hu
        refine ⟨rfl, .token (.keyword (Bridge.keyword name)) :: a, b, ?_, ?_, rfl⟩
        · obtain ⟨v, c, hv, hc, rfl⟩ := ha
          simp only [attrRem, ite_true, Array.isEmpty_empty]
          exact cat_intro' (attrLang_keyword _ (Bridge.keyword name) hv) hc (by simp)
        · rw [← setInfoEnd_next _ .start (token := .keyword name) rfl a (fun h => by cases h)]
          exact hb
      · obtain ⟨b, hb⟩ := hfollows (setInfoEnd (Bridge.version version)
          (if Parser.Command.Standard.isVersionKeyword name = true then Declaration.keyword else
              Declaration.other)
          [closeItem])
        refine ⟨_, ?_, [closeItem], b, cat_intro' (a := []) (Or.inr rfl) (tok_intro _) rfl, hb, rfl⟩
        split <;> first | exact ⟨name, rfl⟩ | trivial
    all_goals fail_step
  | keyword =>
    obtain ⟨k, rfl⟩ : ∃ k, state = ⟨.afterName k, #[]⟩ := hsync
    cases token <;> simp only [payloadStep, Parser.Category.Attribute.attributeStep,
        Declaration.next, pure_bind,
      bind_assoc]
    case symbol s =>
      item_of hitem
      call_step
      refine Sound.pure fun _ => ⟨fun u hu => ?_, ?_⟩
      · obtain ⟨-, a, b, ha, hb, rfl⟩ := hu
        simp only [attrRem, ite_true, push_isEmpty, Bool.false_eq_true, ite_false, tok] at ha
        subst ha
        exact ⟨⟨k, rfl⟩, _, b, cat_intro' (Or.inl ⟨.symbol _, trivial, rfl⟩) (tok_intro _) rfl,
          hb, rfl⟩
      · obtain ⟨b, hb⟩ := hfollows .refused
        exact ⟨_, by first | trivial | (cases c <;> trivial), [closeItem], b,
          by simp [attrRem, tok], hb, rfl⟩
    case constant c =>
      item_of hitem
      call_step
      refine Sound.pure fun _ => ⟨fun u hu => ?_, ?_⟩
      · obtain ⟨-, a, b, ha, hb, rfl⟩ := hu
        simp only [attrRem, ite_true, push_isEmpty, Bool.false_eq_true, ite_false, tok] at ha
        subst ha
        refine ⟨⟨k, rfl⟩, _, b, cat_intro' (Or.inl ⟨.constant (Bridge.constant c), trivial, rfl⟩)
          (tok_intro _) rfl, ?_, rfl⟩
        rw [show toks (Tree.AttributeValue.constant (Bridge.constant c)).tokens ++ [closeItem] =
          .token (Bridge.constant c).token :: [closeItem] from rfl,
          ← setInfoEnd_next _ .keyword (token := .constant c) rfl [closeItem]
          fun _ _ _ => rfl]
        exact hb
      · obtain ⟨b, hb⟩ := hfollows (setInfoEnd (Bridge.version version)
          (Declaration.keyword.next (.constant c)) [closeItem])
        exact ⟨_, by first | trivial | (cases c <;> trivial), [closeItem], b,
          by simp [attrRem, tok], hb, rfl⟩
    case parenOpen =>
      item_of hitem
      refine Sound.pure fun _ => ⟨fun u hu => ?_, ?_⟩
      · obtain ⟨-, a, b, ha, hb, rfl⟩ := hu
        refine ⟨⟨k, rfl⟩, openItem :: a, b, ?_, hb, rfl⟩
        simp only [attrRem, ite_true] at ha
        rcases ha with ⟨c, t, rfl, ht, rfl⟩ |
          ⟨w, r, hw, ⟨s, t, hs, ⟨c, t', rfl, ht', rfl⟩, rfl⟩, rfl⟩
        · exact cat_intro' (Or.inl (valueLang_list _ (a := []) rep_nil)) ht (by simp)
        · exact cat_intro' (Or.inl (valueLang_list _ (star_cons hw hs))) ht' (by simp)
      · obtain ⟨b, hb⟩ := hfollows .refused
        refine ⟨_, trivial, [closeItem, closeItem], b, ?_, hb, rfl⟩
        simp only [attrRem, ite_true]
        exact Or.inl (cat_intro' (tok_intro _) (by simp [attrTail, tok]) rfl)
    case parenClose =>
      item_of hitem
      call_step
      simp only [push_isEmpty, Bool.true_and, Bool.false_eq_true, ite_false, pure_bind]
      call_step
      refine Sound.syntaxError ⟨⟨?_, id⟩, id⟩
      refine Or.inr fun _ => ⟨rfl, fun w hw => ⟨⟨k, rfl⟩, [closeItem], w, ?_, hw, rfl⟩⟩
      exact cat_intro' (a := []) (Or.inr rfl) (by simp [attrTail, tok]) rfl
    case keyword k' =>
      item_of hitem
      simp only [ite_true]
      fail_step
    all_goals fail_step
  | other =>
    have hnext : Declaration.other.next token = .other := by cases token <;> rfl
    simp only [payloadStep, hnext]
    refine Sound.bindOn ((attributeStep_advances version true false state token item hitem
      hlex).mono (fun r h => h) fun _ h => Or.inl h)
      (fun r => ∃ a, r = .done a ∧ a.isEmpty = true) (attributeStep_quiet _ _ _ _) fun r hr => ?_
    replace hr := hr.from (attrRem_nonempty _ _ _ _)
    cases r with
    | more state' =>
      refine Sound.pure fun _ => ⟨fun u hu => ?_, ?_⟩
      · obtain ⟨-, a, b, ha, hb, rfl⟩ := hu
        exact ⟨trivial, item :: a, b, hr.1 a ha, hb, rfl⟩
      · obtain ⟨a, ha⟩ := hr.2
        obtain ⟨b, hb⟩ := hfollows (.next (Bridge.version version))
        exact ⟨a ++ b, trivial, a, b, ha, hb, rfl⟩
    | done attributes =>
      simp only
      split
      · refine Sound.loudly ?_
        call_step
        exact Sound.pure fun _ w hw => ⟨trivial, [item], w, hr nofun, hw, rfl⟩
      · rename_i hnone
        exact Sound.quietly (Sound.syntaxError (Or.inl trivial))
          ⟨attributes, rfl, isEmpty_of_none hnone⟩
  | value r =>
    have hnext : (Declaration.value r).next token = .value r := by cases token <;> rfl
    simp only [payloadStep, hnext]
    refine Sound.bindOn ((attributeStep_advances version true false state token item hitem
      hlex).mono (fun r h => h) fun _ h => Or.inl h)
      (fun r => ∃ a, r = .done a ∧ a.isEmpty = true) (attributeStep_quiet _ _ _ _) fun r' hr => ?_
    replace hr := hr.from (attrRem_nonempty _ _ _ _)
    cases r' with
    | more state' =>
      refine Sound.pure fun _ => ⟨fun u hu => ?_, ?_⟩
      · obtain ⟨-, a, b, ha, hb, rfl⟩ := hu
        exact ⟨trivial, item :: a, b, hr.1 a ha, by cases r <;> exact hb, rfl⟩
      · obtain ⟨a, ha⟩ := hr.2
        obtain ⟨b, hb⟩ := hfollows (setInfoEnd (Bridge.version version) (.value r) a)
        exact ⟨a ++ b, trivial, a, b, ha, hb, rfl⟩
    | done attributes =>
      simp only
      split
      · refine Sound.loudly ?_
        call_step
        cases r with
        | some declared =>
          exact Sound.pure fun _ w hw => ⟨trivial, [item], w, hr nofun, hw, rfl⟩
        | none =>
          refine Sound.syntaxError ⟨⟨?_, id⟩, id⟩
          exact Or.inr fun _ => ⟨rfl, fun w hw => ⟨trivial, [item], w, hr nofun, hw, rfl⟩⟩
      · rename_i hnone
        exact Sound.quietly (Sound.syntaxError (Or.inl trivial))
          ⟨attributes, rfl, isEmpty_of_none hnone⟩

include hitem hlex hfollows in
/-- Every step of the payload parser advances. -/
theorem payloadStep_advances (payload : Payload Nat Nat Nat Nat Nat) :
    Sound (Advances (payloadRem (Bridge.version version) follows) (cmdFin version follows)
        payload item)
      (CmdFailure follows (payloadRem (Bridge.version version) follows payload) item)
      (payloadStep (H := List Event) version payload token) := by
  have lift : ∀ {x : Quiet.RPM (Parser.Internal.Step (Payload Nat Nat Nat Nat Nat) CommandOutcome)},
      PayloadAdvance version follows payload item x →
      Sound (Advances (payloadRem (Bridge.version version) follows) (cmdFin version follows)
        payload item)
      (CmdFailure follows (payloadRem (Bridge.version version) follows payload) item) x :=
    fun h => h.mono (fun _ h => h) fun _ h => Or.inl h
  cases payload with
  | closing final => exact lift (payload_closing version follows hitem final)
  | named command => exact lift (payload_named version follows hfollows hitem command)
  | assert state => exact lift (payload_assert version follows hfollows hitem hlex state)
  | checkSatAssuming state =>
    exact lift (payload_checkSatAssuming version follows hfollows hitem hlex state)
  | checkSatAssumingLiterals state =>
    exact lift (payload_checkSatAssumingLiterals version follows hfollows hitem hlex state)
  | declareConst symbol state =>
    exact lift (payload_declareConst version follows hfollows hitem hlex symbol state)
  | declareFunParameters symbol state =>
    exact lift (payload_declareFunParameters version follows hfollows hitem hlex symbol state)
  | declareFunResult symbol parameters state =>
    exact lift (payload_declareFunResult version follows hfollows hitem hlex symbol parameters
      state)
  | declareSort symbol => exact lift (payload_declareSort version follows hfollows hitem symbol)
  | declareDatatype symbol state =>
    exact lift (payload_declareDatatype version follows hfollows hitem hlex symbol state)
  | declareDatatypesSorts state =>
    exact lift (payload_declareDatatypesSorts version follows hfollows hitem hlex state)
  | declareDatatypesDatatypes count state =>
    exact lift (payload_declareDatatypesDatatypes version follows hfollows hitem hlex count state)
  | defineSortParameters symbol state =>
    exact lift (payload_defineSortParameters version follows hfollows hitem hlex symbol state)
  | defineSortBody state =>
    exact lift (payload_defineSortBody version follows hfollows hitem hlex state)
  | defineConstSort symbol state =>
    exact lift (payload_defineConstSort version follows hfollows hitem hlex symbol state)
  | defineSignature definition state =>
    exact lift (payload_defineSignature version follows hfollows hitem hlex definition state)
  | defineBody definition state =>
    exact lift (payload_defineBody version follows hfollows hitem hlex definition state)
  | defineFunsRecDeclarations state =>
    exact lift (payload_defineFunsRecDeclarations version follows hfollows hitem hlex state)
  | defineFunsRecBodies signatures state =>
    exact lift (payload_defineFunsRecBodies version follows hfollows hitem hlex signatures state)
  | echo => exact lift (payload_echo version follows hfollows hitem)
  | getInfo => exact lift (payload_getInfo version follows hfollows hitem)
  | getOption => exact lift (payload_getOption version follows hfollows hitem)
  | getValue state => exact lift (payload_getValue version follows hfollows hitem hlex state)
  | pop => exact lift (payload_pop version follows hfollows hitem)
  | push => exact lift (payload_push version follows hfollows hitem)
  | setInfo declaration state =>
    exact payload_setInfo version follows hfollows hitem hlex declaration state
  | setOption state => exact lift (payload_setOption version follows hfollows hitem hlex state)

end

end BSmtLib.Facts.Proofs.Parser.Rejection.Payload
