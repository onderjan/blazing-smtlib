module

public import BSmtLib.Facts.Proofs.Parser.Rejection.Term
public import BSmtLib.Facts.Proofs.Parser.Commands.Bytes
import all BSmtLib.Parser.Category.Combinator
import all BSmtLib.Parser.Category.Sort
import all BSmtLib.Parser.Category.Term
import all BSmtLib.Parser.Category.Token
import all BSmtLib.Parser.Command.Internal.Datatype
import all BSmtLib.Parser.Command.Internal.Function
import all BSmtLib.Parser.Command.Internal.Standard
import all BSmtLib.Token.Reserved

@[expose] public section

/-!
# What the parts of commands can still take

Symbols as list elements, sort declarations, propositional literals, signatures and function
declarations, constructors, datatype declarations, and the bodies of recursive functions.

The literal parser runs the term parser beside a shape of the literal; a state is one that its
input can lead to only where the two agree (`LiteralSync`), and only such a state has remainders.
-/

namespace BSmtLib.Facts.Proofs.Parser.Rejection.CommandParts

open BSmtLibSpec.Grammar
open BSmtLibSpec.Parser.Properties
open BSmtLibSpec.Parser.Traversal
open BSmtLib.Parser.Category.Term.Internal (TermState TermMode TermLevel termStep termComplete)
open BSmtLib.Parser.Category.Combinator.Internal (ListState)
open BSmtLib.Parser.Command.Internal.Datatype (SortDecState ConstructorState constructorStep
    DatatypeState
    datatypeStep)
open BSmtLib.Parser.Command.Internal.Standard (LiteralShape LiteralState literalStep)
open BSmtLib.Parser.Command.Internal.Function
    (SignatureState signatureStep FunctionDecState functionDecStep
    bodyStep bodiesStep)
open BSmtLib.Parser.Category.Token.Internal (symbolStep)
open BSmtLib.Facts.Parser.Adapters.Bridge BSmtLib.Facts.Proofs.Parser.Commands.Bytes
open BSmtLib.Facts.Proofs.Parser.Rejection.Basic BSmtLib.Facts.Proofs.Parser.Rejection.Parts
open BSmtLib.Facts.Proofs.Parser.Rejection.«Sort» BSmtLib.Facts.Proofs.Parser.Rejection.Term
open BSmtLib.Parser.Command.Internal.Standard.Symbol

open BSmtLib.Facts.Proofs.Parser.Rejection.Basic.Lang

/-! ## Symbols and sort declarations -/

/-- Every step of the parser of a symbol as a list element advances. -/
theorem symbolStep_advances (version : Token.Version) :
    StepsAdvance version (symbolStep (H := List Event)) (fun _ => SymbolLang)
      fun _ _ => SymbolLang := by
  intro _ token item hitem _
  cases token <;> simp only [symbolStep, Parser.Category.Token.Internal.expectSymbol,
      bind_pure_comp] <;>
      try fail_step
  item_of hitem
  exact Sound.pure fun _ => symbolLang_intro _

/-- A numeral, any. -/
def NumeralLang : Lang := fun u => ∃ digits, u = [.token (.numeral digits)]

/-- A sort declaration. -/
def SortDecLang : Lang := fun u => ∃ dec : Tree.SortDec, u = toks dec.tokens

/-- The remainders of the sort declaration parser's states. -/
def sortDecRem : SortDecState → Lang
  | .start => SortDecLang
  | .opened => cat SymbolLang (cat NumeralLang (tok closeItem))
  | .arity _ => cat NumeralLang (tok closeItem)
  | .close _ _ => tok closeItem

theorem sortDecRem_nonempty (state : SortDecState) : ∃ u, sortDecRem state u := by
  have hnum : ∃ u, NumeralLang u := ⟨_, [], rfl⟩
  cases state with
  | start => exact ⟨_, ⟨⟨⟨[], false⟩, []⟩, rfl⟩⟩
  | opened => exact cat_nonempty symbolLang_nonempty (cat_nonempty hnum ⟨_, tok_intro _⟩)
  | arity _ => exact cat_nonempty hnum ⟨_, tok_intro _⟩
  | close _ _ => exact ⟨_, tok_intro _⟩

/-- Every step of the sort declaration parser advances. -/
theorem sortDecStep_advances (version : Token.Version) :
    StepsAdvance version (SortDecState.step (H := List Event)) sortDecRem
      fun state _ => sortDecRem state := by
  intro state token item hitem _
  cases state with
  | start =>
    cases token <;> simp only [SortDecState.step, Parser.Category.Token.Internal.expectOpen,
        pure_bind] <;>
        try fail_step
    item_of hitem
    refine Sound.pure fun _ => ⟨fun u hu => ?_, sortDecRem_nonempty _⟩
    obtain ⟨_, _, ⟨name, rfl⟩, ⟨_, _, ⟨digits, rfl⟩, rfl, rfl⟩, rfl⟩ := hu
    exact ⟨⟨name, digits⟩, rfl⟩
  | opened =>
    cases token <;> simp only [SortDecState.step, Parser.Category.Token.Internal.expectSymbol,
      bind_pure_comp] <;> try fail_step
    item_of hitem
    exact Sound.pure fun _ => ⟨fun u hu => cat_intro' (symbolLang_intro _) hu rfl,
      sortDecRem_nonempty _⟩
  | arity _ =>
    cases token <;> simp only [SortDecState.step, Parser.Category.Token.Internal.expectNumeral,
      bind_pure_comp] <;> try fail_step
    rename_i constant
    cases constant <;> simp only <;> try fail_step
    item_of hitem
    exact Sound.pure fun _ => ⟨fun u hu => cat_intro' ⟨_, rfl⟩ hu rfl, sortDecRem_nonempty _⟩
  | close _ _ =>
    cases token <;> simp only [SortDecState.step, Parser.Category.Token.Internal.expectClose,
        pure_bind] <;>
        try fail_step
    item_of hitem
    exact Sound.pure fun _ => tok_intro _

/-! ## Propositional literals -/

/-- The symbol `not`, quoted or not. -/
def NotLang : Lang := fun u => ∃ s : Tree.Symbol, s.name = BSmtLibSpec.Regex.chars "not" ∧
  u = [.token (.symbol s)]

/-- A propositional literal. -/
def LiteralLang : Lang := fun u => ∃ literal : Tree.PropLiteral, literal.Valid ∧
  u = toks literal.tokens

/-- The remainders of a literal by its shape so far. -/
def literalShapeRem : LiteralShape → Lang
  | .start => LiteralLang
  | .negation => cat NotLang (cat SymbolLang (tok closeItem))
  | .negated => cat SymbolLang (tok closeItem)
  | .close => tok closeItem

/-- The term parser is where the shape of the literal says. -/
def LiteralSync : LiteralShape → TermState Nat Nat Nat Nat Nat → Prop
  | .start, term => term = .init
  | .negation, term => term = ⟨.opened, []⟩
  | .negated, term => ∃ f, term = ⟨.start, [.application f none #[]]⟩
  | .close, term => ∃ f a, term = ⟨.start, [.application f none #[a]]⟩

/-- The remainders of the literal parser's states. -/
def literalRem (state : LiteralState Nat Nat Nat Nat Nat) : Lang :=
  fun u => LiteralSync state.shape state.term ∧ literalShapeRem state.shape u

theorem literalLang_nonempty : ∃ u, LiteralLang u := ⟨_, ⟨.positive ⟨[], false⟩, trivial, rfl⟩⟩

theorem notLang_symbol {s : Nodes.Symbol} (h : (isNot s) = true) :
    NotLang [.token (.symbol (Bridge.symbol s))] := by
  refine ⟨Bridge.symbol s, ?_, rfl⟩
  unfold Parser.Command.Internal.Standard.Symbol.isNot at h
  rw [slice_beq_utf8 _ _ utf8_not] at h
  exact of_decide_eq_true h

theorem notLang_nonempty : ∃ u, NotLang u := ⟨_, ⟨⟨BSmtLibSpec.Regex.chars "not", false⟩, rfl, rfl⟩⟩

theorem literalRem_init : ∀ u, literalRem .init u → LiteralLang u := fun _ h => h.2

/-- A step of the literal parser fails with no rejection of a version declaration. -/
theorem literalStep_benign (version : Token.Version) (state : LiteralState Nat Nat Nat Nat Nat)
    {token : Parser.Internal.Input} {item : Received} (hitem : Bridge.received token = some item)
    (hlex : item.OfVersion (Bridge.version version)) :
    Sound (fun _ => True) Benign (literalStep (H := List Event) version state token) := by
  obtain ⟨shape, term⟩ := state
  have hterm := (termStep_advances version term token item hitem hlex).mono
    (P' := fun _ => True) (fun _ _ => trivial) fun _ h => h
  unfold literalStep
  cases shape <;> cases token <;> simp only [pure_bind]
  case start.symbol => exact Sound.bind hterm fun r _ => by cases r <;> exact Sound.pure trivial
  case start.parenOpen => exact Sound.bind hterm fun r _ => by cases r <;> exact Sound.pure trivial
  case negation.symbol =>
    split
    · exact Sound.bind hterm fun r _ => by cases r <;> exact Sound.pure trivial
    · fail_step
  case negated.symbol => exact Sound.bind hterm fun r _ => by cases r <;> exact Sound.pure trivial
  case close.parenClose => exact Sound.bind hterm fun r _ => by cases r <;> exact Sound.pure trivial
  all_goals fail_step

/-- Every step of the literal parser advances. -/
theorem literalStep_advances (version : Token.Version) :
    StepsAdvance version (literalStep (H := List Event) version) literalRem
      fun state _ => literalRem state := by
  intro ⟨shape, term⟩ token item hitem hlex
  by_cases hsync : LiteralSync shape term
  case neg =>
    refine (literalStep_benign version _ hitem hlex).mono (fun r _ => ?_) fun _ h => h
    cases r <;> exact fun ⟨_, hu⟩ => absurd hu.1 hsync
  unfold literalStep
  cases shape with
  | start =>
    obtain rfl : term = .init := hsync
    cases token <;> simp only [pure_bind]
    case parenOpen =>
      item_of hitem
      rw [show termStep (H := List Event) version .init .parenOpen =
        pure (.more ⟨.opened, []⟩) from rfl, pure_bind]
      refine Sound.pure fun _ => ⟨fun u hu => ?_, ⟨_, rfl, (cat_nonempty notLang_nonempty
        (cat_nonempty symbolLang_nonempty ⟨_, tok_intro _⟩)).choose_spec⟩⟩
      obtain ⟨-, _, _, ⟨negation, hnot, rfl⟩, ⟨_, _, ⟨s, rfl⟩, rfl, rfl⟩, rfl⟩ := hu
      exact ⟨rfl, .negative negation s, hnot, rfl⟩
    case symbol s =>
      item_of hitem
      rw [show termStep (H := List Event) version .init (.symbol s) =
        (Parser.Internal.call
            (Traits.Handler.handleTerm (H := List Event) (.identifier ⟨s, #[]⟩ none)) >>=
          fun t => termComplete [] t) from rfl, bind_assoc]
      call_step
      rw [show ∀ t, termComplete (H := List Event) [] t = pure (.done t) from fun _ => rfl,
        pure_bind]
      exact Sound.pure fun _ => ⟨rfl, .positive _, trivial, rfl⟩
    all_goals fail_step
  | negation =>
    obtain rfl : term = ⟨.opened, []⟩ := hsync
    cases token <;> simp only [pure_bind]
    case symbol s =>
      split
      · rename_i hnot
        item_of hitem
        rw [show termStep (H := List Event) version ⟨.opened, []⟩ (.symbol s) =
          pure (.more ⟨.start, [.application ⟨s, #[]⟩ none #[]]⟩) from rfl, pure_bind]
        refine Sound.pure fun _ => ⟨fun u hu => ?_, ⟨_, ⟨_, rfl⟩,
          (cat_nonempty symbolLang_nonempty ⟨_, tok_intro _⟩).choose_spec⟩⟩
        exact ⟨rfl, cat_intro' (notLang_symbol hnot) hu.2 rfl⟩
      · fail_step
    all_goals fail_step
  | negated =>
    obtain ⟨f, rfl⟩ : ∃ f, term = ⟨.start, [.application f none #[]]⟩ := hsync
    cases token <;> simp only [pure_bind]
    case symbol s =>
      item_of hitem
      rw [show termStep (H := List Event) version ⟨.start, [.application f none #[]]⟩
          (.symbol s) =
        (Parser.Internal.call
            (Traits.Handler.handleTerm (H := List Event) (.identifier ⟨s, #[]⟩ none)) >>=
          fun t => termComplete [.application f none #[]] t) from rfl, bind_assoc]
      refine Sound.bind (Sound.ofCall fun _ => ⟨_, _, rfl⟩) fun t _ => ?_
      rw [show termComplete (H := List Event) [.application f none #[]] t =
        pure (.more ⟨.start, [.application f none #[t]]⟩) from rfl, pure_bind]
      exact Sound.pure fun _ => ⟨fun u hu => ⟨⟨f, rfl⟩, cat_intro' (symbolLang_intro _) hu.2 rfl⟩,
        ⟨_, ⟨f, _, rfl⟩, tok_intro _⟩⟩
    all_goals fail_step
  | close =>
    obtain ⟨f, a, rfl⟩ : ∃ f a, term = ⟨.start, [.application f none #[a]]⟩ := hsync
    cases token <;> simp only [pure_bind]
    case parenClose =>
      item_of hitem
      rw [show termStep (H := List Event) version ⟨.start, [.application f none #[a]]⟩
          .parenClose =
        (Parser.Internal.call
            (Traits.Handler.handleTerm (H := List Event) (.application f none #[a])) >>=
          fun t => termComplete [] t) from rfl, bind_assoc]
      call_step
      rw [show ∀ t, termComplete (H := List Event) [] t = pure (.done t) from fun _ => rfl,
        pure_bind]
      exact Sound.pure fun _ => ⟨⟨f, a, rfl⟩, tok_intro _⟩
    all_goals fail_step

/-! ## Signatures and function declarations -/

section

variable (version : BSmtLibSpec.Lexicon.Version)

/-- The sorted variables of a signature, their `)` and the result sort. -/
def paramsTail : Lang := cat (tok closeItem) (SortLang version)

/-- The remainders of the signature parser's states. -/
def signatureRem : SignatureState Nat → Lang
  | .start => cat SymbolLang (cat (tok openItem) (cat (star (SortedVarLang version))
      (paramsTail version)))
  | .parameters _ state =>
    cat (listRem (sortedVarRem version) (SortedVarLang version) .start 0 none state)
      (SortLang version)
  | .result _ _ state => sortRem version state

/-- A function declaration of the version. -/
def FunctionDecLang : Lang :=
  fun u => ∃ dec : Tree.FunctionDec, dec.Valid version ∧ u = toks dec.tokens

/-- The remainders of the function declaration parser's states. -/
def functionDecRem : FunctionDecState Nat → Lang
  | .start => FunctionDecLang version
  | .signature state => cat (signatureRem version state) (tok closeItem)
  | .close _ => tok closeItem

theorem signatureRem_start_nonempty : ∃ u, signatureRem version .start u :=
  cat_nonempty symbolLang_nonempty (cat_nonempty ⟨_, tok_intro _⟩ (cat_nonempty ⟨[], rep_nil⟩
    (cat_nonempty ⟨_, tok_intro _⟩ (sortLang_nonempty version))))

theorem functionDecLang_nonempty : ∃ u, FunctionDecLang version u :=
  ⟨_, ⟨⟨⟨[], false⟩, [], ⟨⟨⟨[], false⟩, []⟩, []⟩⟩, ⟨by simp, by simp [Tree.«Sort».Valid,
    Tree.«Sort».ValidAll, Tree.Identifier.Valid]⟩, rfl⟩⟩

end

/-- Every step of the signature parser advances. -/
theorem signatureStep_advances (version : Token.Version) :
    StepsAdvance version (signatureStep (H := List Event) version)
      (signatureRem (Bridge.version version))
      fun state _ => signatureRem (Bridge.version version) state := by
  intro state token item hitem hlex
  cases state with
  | start =>
    cases token <;> simp only [signatureStep, Parser.Category.Token.Internal.expectSymbol,
        bind_pure_comp]
    case symbol s =>
      item_of hitem
      refine Sound.pure fun _ => ⟨fun u hu => ?_, ?_⟩
      · obtain ⟨l, r, hl, hr, rfl⟩ := hu
        obtain ⟨w, hw, rfl⟩ := listRem_paren (fun _ h => h) hl
        exact cat_intro' (symbolLang_intro (Bridge.symbol s)) (cat_tok (cat_intro' hw
          (cat_intro (tok_intro _) hr)
          rfl)) (by simp)
      · exact cat_nonempty (listRem_paren_nonempty (sortedVarRem_nonempty _ .start)
          (sortedVarRem_nonempty _ .start) (by simp)) (sortLang_nonempty _)
    all_goals fail_step
  | parameters s state =>
    simp only [signatureStep]
    refine Sound.bind (listStep_advances version .start (sortedVarStep_advances version)
      (fun _ h => h) (sortedVarRem_nonempty _ .start) (sortedVarRem_nonempty _ .start) 0 none
      (by simp) state token item hitem hlex) fun r hr => ?_
    have hlist : (∃ u, signatureRem (Bridge.version version) (.parameters s state) u) →
        ∃ u, listRem (sortedVarRem (Bridge.version version))
          (SortedVarLang (Bridge.version version)) .start 0 none state u := by
      intro ⟨_, l, _, hl, _, rfl⟩
      exact ⟨l, hl⟩
    cases r with
    | more state' =>
      refine Sound.pure fun hne => ?_
      have hr := hr (hlist hne)
      exact ⟨fun u hu => cat_left hr.1 hu, cat_nonempty hr.2 (sortLang_nonempty _)⟩
    | done parameters =>
      refine Sound.pure fun hne => ⟨fun u hu => ?_, by
        simpa [signatureRem] using sortRem_nonempty (Bridge.version version) .init⟩
      exact cat_intro' (hr (hlist hne) (Nat.zero_le _) (by simp)) (by
        simpa [signatureRem, sortRem, Parser.Category.«Sort».Internal.SortState.init] using hu) rfl
  | result s parameters state =>
    simp only [signatureStep]
    refine Sound.bind (sortStep_advances version state token item hitem hlex) fun r hr => ?_
    replace hr := hr.from (sortRem_nonempty _ _)
    cases r with
    | more state' => exact Sound.pure fun _ => ⟨fun u hu => hr.1 u hu, sortRem_nonempty _ _⟩
    | done result => exact Sound.pure fun _ => hr

/-- Every step of the function declaration parser advances. -/
theorem functionDecStep_advances (version : Token.Version) :
    StepsAdvance version (functionDecStep (H := List Event) version)
      (functionDecRem (Bridge.version version))
      fun state _ => functionDecRem (Bridge.version version) state := by
  intro state token item hitem hlex
  cases state with
  | start =>
    cases token <;> simp only [functionDecStep, Parser.Category.Token.Internal.expectOpen,
        pure_bind]
    case parenOpen =>
      item_of hitem
      refine Sound.pure fun _ => ⟨fun u hu => ?_, cat_nonempty (signatureRem_start_nonempty _)
        ⟨_, tok_intro _⟩⟩
      obtain ⟨_, c, ⟨_, _, ⟨s, rfl⟩, ⟨_, _, rfl, ⟨w, _, hw, ⟨_, r, rfl, hr, rfl⟩, rfl⟩, rfl⟩,
        rfl⟩, rfl, rfl⟩ := hu
      obtain ⟨params, hparams, -, rfl⟩ := sortedVars_rep hw
      obtain ⟨result, hresult, rfl⟩ := hr
      exact ⟨⟨s, params, result⟩, ⟨hparams, hresult⟩,
        by simp [Tree.FunctionDec.tokens, paren, toks]⟩
    all_goals fail_step
  | signature state =>
    simp only [functionDecStep]
    refine Sound.bind (signatureStep_advances version state token item hitem hlex) fun r hr => ?_
    have hsig : (∃ u, functionDecRem (Bridge.version version) (.signature state) u) →
        ∃ u, signatureRem (Bridge.version version) state u := by
      intro ⟨_, a, _, ha, _, rfl⟩
      exact ⟨a, ha⟩
    cases r with
    | more state' =>
      refine Sound.pure fun hne => ?_
      have hr := hr (hsig hne)
      exact ⟨fun u hu => cat_left hr.1 hu, cat_nonempty hr.2 ⟨_, tok_intro _⟩⟩
    | done signature =>
      exact Sound.pure fun hne => ⟨fun u hu => cat_intro' (hr (hsig hne)) hu rfl,
        ⟨_, tok_intro _⟩⟩
  | close signature =>
    cases token <;> simp only [functionDecStep, Parser.Category.Token.Internal.expectClose,
        pure_bind]
    case parenClose =>
      item_of hitem
      exact Sound.pure fun _ => tok_intro _
    all_goals fail_step

/-! ## Lists whose `(` is another's -/

section

variable {σ ρ : Type} {inner : σ → Lang} {element : Lang} {init : σ}

/-- The remainders of a list whose `(` belongs to someone else are its elements and its `)`. -/
theorem listRem_closed (hinit : ∀ u, inner init u → element u) {lo : Nat} {u : List Received}
    (h : listRem inner element init lo none (ListState.closed (ρ := ρ) init) u) :
    ∃ w, rep element lo none w ∧ u = w ++ [closeItem] := by
  simp only [listRem, ListState.closed, ite_true, listOpenRem, List.size_toArray,
    List.length_nil] at h
  rcases h with ⟨-, ⟨rfl, hlo, -⟩ | ⟨-, a, b, ha, ⟨r, c, hr, rfl, rfl⟩, rfl⟩⟩
  · exact ⟨[], by simpa [show lo = 0 by omega] using (rep_nil (A := element) (hi := none)), rfl⟩
  · refine ⟨a ++ r, rep_cons (hinit a ha) (by simpa using hr) (by simp), by simp⟩

theorem listRem_closed_nonempty (hinit : ∃ u, inner init u) (helement : ∃ u, element u)
    (lo : Nat) : ∃ u, listRem inner element init lo none (ListState.closed (ρ := ρ) init) u := by
  simp only [listRem, ListState.closed]
  exact listOpenRem_outside_nonempty hinit helement (by simp) true #[] (Or.inr (by simp))

end

/-! ## Constructors -/

section

variable (version : BSmtLibSpec.Lexicon.Version)

/-- A constructor declaration of the version. -/
def ConstructorLang : Lang :=
  fun u => ∃ c : Tree.ConstructorDec, c.Valid version ∧ u = toks c.tokens

/-- The remainders of the constructor parser's states; the selectors are read as sorted
variables. -/
def constructorRem : ConstructorState Nat → Lang
  | .start => ConstructorLang version
  | .opened => cat SymbolLang (cat (star (SortedVarLang version)) (tok closeItem))
  | .selectors _ state => listRem (sortedVarRem version) (SortedVarLang version) .start 0 none state

theorem constructorLang_nonempty : ∃ u, ConstructorLang version u :=
  ⟨_, ⟨⟨⟨[], false⟩, []⟩, by simp [Tree.ConstructorDec.Valid], rfl⟩⟩

theorem constructorRem_opened_nonempty : ∃ u, constructorRem version .opened u :=
  cat_nonempty symbolLang_nonempty (cat_nonempty ⟨[], rep_nil⟩ ⟨_, tok_intro _⟩)

/-- A constructor, after its `(`. -/
theorem constructorLang_opened {u : List Received} (h : constructorRem version .opened u) :
    ConstructorLang version (openItem :: u) := by
  obtain ⟨_, _, ⟨s, rfl⟩, ⟨w, _, hw, rfl, rfl⟩, rfl⟩ := h
  obtain ⟨vars, hvars, -, rfl⟩ := sortedVars_rep hw
  refine ⟨⟨s, vars.map fun v => ⟨v.symbol, v.sort⟩⟩, fun sel hsel => ?_, ?_⟩
  · obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hsel
    exact hvars v hv
  · simp only [Tree.ConstructorDec.tokens, paren, toks]
    simp [List.flatMap, Function.comp_def, Tree.SelectorDec.tokens, Tree.SortedVar.tokens]

end

/-- Every step of the constructor parser advances. -/
theorem constructorStep_advances (version : Token.Version) :
    StepsAdvance version (constructorStep (H := List Event) version)
      (constructorRem (Bridge.version version))
      fun state _ => constructorRem (Bridge.version version) state := by
  intro state token item hitem hlex
  cases state with
  | start =>
    cases token <;> simp only [constructorStep, Parser.Category.Token.Internal.expectOpen,
        pure_bind]
    case parenOpen =>
      item_of hitem
      exact Sound.pure fun _ => ⟨fun u hu => constructorLang_opened _ hu,
        constructorRem_opened_nonempty _⟩
    all_goals fail_step
  | opened =>
    cases token <;> simp only [constructorStep, Parser.Category.Token.Internal.expectSymbol,
        bind_pure_comp]
    case symbol s =>
      item_of hitem
      refine Sound.pure fun _ => ⟨fun u hu => ?_, listRem_closed_nonempty
        (sortedVarRem_nonempty _ .start) (sortedVarRem_nonempty _ .start) 0⟩
      obtain ⟨w, hw, rfl⟩ := listRem_closed (fun _ h => h) hu
      exact cat_intro' (symbolLang_intro (Bridge.symbol s)) (cat_intro hw (tok_intro _)) rfl
    all_goals fail_step
  | selectors s state =>
    simp only [constructorStep]
    refine Sound.bind (listStep_advances version .start (sortedVarStep_advances version)
      (fun _ h => h) (sortedVarRem_nonempty _ .start) (sortedVarRem_nonempty _ .start) 0 none
      (by simp) state token item hitem hlex) fun r hr => ?_
    cases r with
    | more state' => exact Sound.pure hr
    | done selectors =>
      exact Sound.pure fun hne => hr hne (Nat.zero_le _) (by simp)

/-! ## Datatype declarations -/

section

variable (version : BSmtLibSpec.Lexicon.Version)

/-- A datatype declaration of the version. -/
def DatatypeLang : Lang :=
  fun u => ∃ d : Tree.DatatypeDec, d.Valid version ∧ u = toks d.tokens

/-- The constructors of the form with `par`, after its sort parameters: `(`, the constructors, the
`)` and the declaration's `)`. -/
def parTail : Lang :=
  cat (tok openItem) (cat (plus (ConstructorLang version)) (cat (tok closeItem) (tok closeItem)))

/-- The remainders of the datatype declaration parser's states. -/
def datatypeRem : DatatypeState Nat → Lang
  | .start => DatatypeLang version
  | .kind =>
    union (cat (plus (ConstructorLang version)) (tok closeItem))
      (cat (tok (wordItem "par")) (cat (tok openItem) (cat (plus SymbolLang)
        (cat (tok closeItem) (parTail version)))))
  | .parameters state =>
    cat (listRem (fun _ => SymbolLang) SymbolLang () 1 none state) (parTail version)
  | .constructorsOpen => parTail version
  | .constructors parametric state =>
    cat (listRem (constructorRem version) (ConstructorLang version) .start 1 none state)
      (if parametric then tok closeItem else eps)
  | .close _ => tok closeItem

theorem parTail_nonempty : ∃ u, parTail version u :=
  cat_nonempty ⟨_, tok_intro _⟩ (cat_nonempty
    (rep_nonempty (constructorLang_nonempty version) 1 none (by simp))
    (cat_nonempty ⟨_, tok_intro _⟩ ⟨_, tok_intro _⟩))

theorem datatypeLang_nonempty : ∃ u, DatatypeLang version u :=
  ⟨_, ⟨⟨[], [⟨⟨[], false⟩, []⟩]⟩, ⟨by simp, by simp [Tree.ConstructorDec.Valid]⟩, rfl⟩⟩

theorem constructors_rep {lo : Nat} {u : List Received}
    (h : rep (ConstructorLang version) lo none u) :
    ∃ cs : List Tree.ConstructorDec, (∀ c ∈ cs, c.Valid version) ∧ lo ≤ cs.length ∧
      u = toks (cs.flatMap Tree.ConstructorDec.tokens) := by
  obtain ⟨cs, hvalid, hlo, -, rfl⟩ := rep_trees h
  exact ⟨cs, hvalid, hlo, by simp [List.flatMap, Function.comp_def]⟩

theorem symbols_rep {lo : Nat} {u : List Received} (h : rep SymbolLang lo none u) :
    ∃ ss : List Tree.Symbol, lo ≤ ss.length ∧ u = toks (ss.map .symbol) := by
  have h' : rep (fun w => ∃ s : Tree.Symbol, True ∧ w = [.token (.symbol s)]) lo none u := by
    obtain ⟨ws, hws, hlo, hhi, rfl⟩ := h
    refine ⟨ws, fun w hw => ?_, hlo, hhi, rfl⟩
    obtain ⟨s, rfl⟩ := hws w hw
    exact ⟨s, trivial, rfl⟩
  obtain ⟨ss, -, hlo, -, rfl⟩ := rep_trees h'
  exact ⟨ss, hlo, by simp [flatten_singletons, Function.comp_def]⟩

/-- A datatype declaration, after its `(`. -/
theorem datatypeLang_kind {u : List Received} (h : datatypeRem version .kind u) :
    DatatypeLang version (openItem :: u) := by
  rcases h with ⟨c, _, hc, rfl, rfl⟩ |
    ⟨_, _, rfl, ⟨_, _, rfl, ⟨p, _, hp, ⟨_, _, rfl, ⟨_, _, rfl, ⟨c, _, hc, ⟨_, _, rfl, rfl, rfl⟩,
      rfl⟩, rfl⟩, rfl⟩, rfl⟩, rfl⟩, rfl⟩
  · obtain ⟨cs, hvalid, hlen, rfl⟩ := constructors_rep _ hc
    refine ⟨⟨[], cs⟩, ⟨by rintro rfl; simp at hlen, hvalid⟩, ?_⟩
    simp [Tree.DatatypeDec.tokens, paren, toks]
  · obtain ⟨ps, hps, rfl⟩ := symbols_rep hp
    obtain ⟨cs, hvalid, hlen, rfl⟩ := constructors_rep _ hc
    refine ⟨⟨ps, cs⟩, ⟨by rintro rfl; simp at hlen, hvalid⟩, ?_⟩
    cases ps with
    | nil => simp at hps
    | cons p ps => simp [Tree.DatatypeDec.tokens, paren, toks, word]

end

/-- Every step of the datatype declaration parser advances, whatever it calls at the start of a
declaration, as long as that never fails. -/
theorem datatypeStep_advances (version : Token.Version)
    {start : Array Nodes.Symbol → Quiet.RPM Unit}
    (hstart : ∀ parameters, Sound (fun _ => True) Benign (start parameters)) :
    StepsAdvance version (datatypeStep (H := List Event) start version)
      (datatypeRem (Bridge.version version))
      fun state _ => datatypeRem (Bridge.version version) state := by
  intro state token item hitem hlex
  cases state with
  | start =>
    cases token <;> simp only [datatypeStep, Parser.Category.Token.Internal.expectOpen, pure_bind]
    case parenOpen =>
      item_of hitem
      refine Sound.pure fun _ => ⟨fun u hu => datatypeLang_kind _ hu, ?_⟩
      exact (cat_nonempty (rep_nonempty (constructorLang_nonempty _) 1 none (by simp))
        ⟨_, tok_intro closeItem⟩).elim fun u hu => ⟨u, Or.inl hu⟩
    all_goals fail_step
  | kind =>
    simp only [datatypeStep]
    split
    · item_of hitem
      refine Sound.bind (hstart #[]) fun _ _ => ?_
      refine Sound.pure fun _ => ⟨fun u hu => ?_, ?_⟩
      · obtain ⟨l, e, hl, rfl, rfl⟩ := hu
        simp only [listRem, ite_true, listOpenRem, Bool.false_eq_true, ite_false,
          List.size_toArray, List.length_nil] at hl
        obtain ⟨-, o, m, ho, ⟨r, c, hr, hc, rfl⟩, rfl⟩ := hl
        refine Or.inl (cat_intro' (rep_cons (constructorLang_opened _ ho) (by simpa using hr)
          (by simp)) hc (by simp))
      · refine cat_nonempty ?_ ⟨[], rfl⟩
        simp only [listRem, ite_true]
        exact listOpenRem_inside_nonempty (hi := none) (constructorLang_nonempty _) (by simp) true
          ConstructorState.opened #[]
          (constructorRem_opened_nonempty _) (by simp)
    · split
      · rename_i hword
        rw [isWord_eq hword] at hitem
        item_of hitem
        refine Sound.pure fun _ => ⟨fun u hu => ?_, cat_nonempty (listRem_paren_nonempty
          ⟨_, symbolLang_intro ⟨[], false⟩⟩ symbolLang_nonempty (by simp)) (parTail_nonempty _)⟩
        obtain ⟨l, t, hl, ht, rfl⟩ := hu
        obtain ⟨w, hw, rfl⟩ := listRem_paren (fun _ h => h) hl
        exact Or.inr (cat_tok (cat_tok (cat_intro' hw (cat_intro (tok_intro _) ht) (by simp))))
      · fail_step
  | parameters state =>
    simp only [datatypeStep]
    refine Sound.bindOn (listStep_advances version () (symbolStep_advances version) (fun _ h => h)
      symbolLang_nonempty symbolLang_nonempty 1 none (by simp) state token item hitem hlex)
      (fun r => ∃ v, r = .done v) (listStep_quiet _ _ _ _ _) fun r hr => ?_
    have hlist : (∃ u, datatypeRem (Bridge.version version) (.parameters state) u) →
        ∃ u, listRem (fun _ => SymbolLang) SymbolLang () 1 none state u := by
      intro ⟨_, l, _, hl, _, rfl⟩
      exact ⟨l, hl⟩
    cases r with
    | more state' =>
      refine Sound.pure fun hne => ?_
      have hr := hr (hlist hne)
      exact ⟨fun u hu => cat_left hr.1 hu, cat_nonempty hr.2 (parTail_nonempty _)⟩
    | done parameters =>
      refine Sound.quietly ?_ ⟨parameters, rfl⟩
      simp only
      split
      · fail_step
      · rename_i hempty
        refine Sound.bind (hstart parameters) fun _ _ => ?_
        refine Sound.pure fun hne => ⟨fun u hu => cat_intro' (hr (hlist hne) ?_ (by simp)) hu rfl,
          parTail_nonempty _⟩
        cases parameters using Array.casesOn with
        | mk l => cases l <;> simp_all
  | constructorsOpen =>
    cases token <;> simp only [datatypeStep, Parser.Category.Token.Internal.expectOpen, pure_bind]
    case parenOpen =>
      item_of hitem
      refine Sound.pure fun _ => ⟨fun u hu => ?_, cat_nonempty (listRem_closed_nonempty
        (inner := constructorRem _) (init := ConstructorState.start)
        (constructorLang_nonempty _) (constructorLang_nonempty _) 1) ⟨_, tok_intro _⟩⟩
      obtain ⟨l, t, hl, rfl, rfl⟩ := hu
      obtain ⟨w, hw, rfl⟩ := listRem_closed (fun _ h => h) hl
      exact cat_tok (cat_intro' hw (cat_intro (tok_intro _) (tok_intro _)) (by simp))
    all_goals fail_step
  | constructors parametric state =>
    simp only [datatypeStep]
    refine Sound.bindOn (listStep_advances version ConstructorState.start
      (constructorStep_advances version)
      (fun _ h => h) (constructorLang_nonempty _) (constructorLang_nonempty _) 1 none (by simp)
      state token item hitem hlex) (fun r => ∃ v, r = .done v) (listStep_quiet _ _ _ _ _)
      fun r hr => ?_
    have hlist : (∃ u, datatypeRem (Bridge.version version) (.constructors parametric state) u) →
        ∃ u, listRem (constructorRem (Bridge.version version))
          (ConstructorLang (Bridge.version version)) .start 1 none state u := by
      intro ⟨_, l, _, hl, _, rfl⟩
      exact ⟨l, hl⟩
    cases r with
    | more state' =>
      refine Sound.pure fun hne => ?_
      have hr := hr (hlist hne)
      exact ⟨fun u hu => cat_left hr.1 hu, cat_nonempty hr.2 (by split <;> exact ⟨_, rfl⟩)⟩
    | done constructors =>
      refine Sound.quietly ?_ ⟨constructors, rfl⟩
      simp only
      split
      · fail_step
      · rename_i hempty
        have hlen : 1 ≤ constructors.size := by
          cases constructors using Array.casesOn with
          | mk l => cases l <;> simp_all
        split
        · rename_i hparametric
          subst hparametric
          exact Sound.pure fun hne => ⟨fun u hu => cat_intro' (hr (hlist hne) hlen (by simp)) (by
            simpa [datatypeRem] using hu) rfl, ⟨_, tok_intro _⟩⟩
        · rename_i hparametric
          simp only [Bool.not_eq_true] at hparametric
          subst hparametric
          exact Sound.pure fun hne => cat_intro' (hr (hlist hne) hlen (by simp)) rfl rfl
  | close constructors =>
    cases token <;> simp only [datatypeStep, Parser.Category.Token.Internal.expectClose, pure_bind]
    case parenClose =>
      item_of hitem
      exact Sound.pure fun _ => tok_intro _
    all_goals fail_step

/-! ## The bodies of recursive functions -/

/-- Every step of the parser of a recursive body advances, as the term parser's. -/
theorem bodyStep_advances (version : Token.Version) :
    StepsAdvance version (bodyStep (H := List Event) version) (termRem (Bridge.version version))
      fun state _ => termRem (Bridge.version version) state := by
  intro state token item hitem hlex
  simp only [bodyStep]
  refine Sound.bind (termStep_advances version state token item hitem hlex) fun r hr => ?_
  cases r with
  | more state' => exact Sound.pure hr
  | done body =>
    call_step
    exact Sound.pure hr

theorem termRem_init {version : BSmtLibSpec.Lexicon.Version} :
    ∀ u, termRem version Parser.Category.Term.Internal.TermState.init u → TermLang version u := by
  intro u hu
  obtain ⟨t, _, ht, rfl, rfl⟩ := hu
  simpa using ht

theorem termRem_init_nonempty (version : BSmtLibSpec.Lexicon.Version) :
    ∃ u, termRem version Parser.Category.Term.Internal.TermState.init u :=
  termRem_nonempty version _ trivial

/-- Every step of the parser of the recursive bodies advances, for exactly `count` bodies. -/
theorem bodiesStep_advances (version : Token.Version) (count : Nat) :
    StepsAdvance version (bodiesStep (H := List Event) count version)
      (listRem (termRem (Bridge.version version)) (TermLang (Bridge.version version))
        Parser.Category.Term.Internal.TermState.init count (some count))
      fun state (items : Array Unit) u => count ≤ items.size →
        (∀ limit, some count = some limit → items.size ≤ limit) →
        listRem (termRem (Bridge.version version)) (TermLang (Bridge.version version))
          Parser.Category.Term.Internal.TermState.init count (some count) state u := by
  intro state token item hitem hlex
  simp only [bodiesStep]
  exact listStep_advances version Parser.Category.Term.Internal.TermState.init
      (bodyStep_advances version)
    (element := TermLang _)
    termRem_init (termRem_init_nonempty _) (termLang_nonempty _) count (some count) (by simp)
    state token item hitem hlex

/-- The parser of recursive bodies writes no event where it finishes. -/
theorem bodiesStep_quiet (count : Nat) (version : Token.Version)
    (state : ListState (Parser.Category.Term.Internal.TermStateOf (List Event)) Unit)
        (token : Parser.Internal.Input) :
    ∀ events b events', (bodiesStep (H := List Event) count version state token).run.run events =
      (.ok b, events') → (∃ v, b = .done v) → events' = events := by
  intro events b events' h ⟨v, hv⟩
  subst hv
  simp only [bodiesStep] at h
  exact listStep_done_silent _ _ _ _ _ _ _ _ h

end BSmtLib.Facts.Proofs.Parser.Rejection.CommandParts
