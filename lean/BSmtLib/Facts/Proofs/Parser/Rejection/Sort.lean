module

public import BSmtLib.Facts.Proofs.Parser.Rejection.Basic
import all BSmtLib.Parser
import all BSmtLib.Parser.Category.Ident
import all BSmtLib.Parser.Category.Sort
import all BSmtLib.Token.Reserved

@[expose] public section

/-!
# What identifiers and sorts can still take

The remainders of the identifier parser's and the sort parser's states. A sort state is a mode
and the open applications, innermost first; after a sort that is an argument of the innermost
application come its further arguments and its `)`, then what follows that application in turn
(`sortAfter`).
-/

namespace BSmtLib.Facts.Proofs.Parser.Rejection.«Sort»

open BSmtLibSpec.Grammar
open BSmtLibSpec.Parser.Properties
open BSmtLibSpec.Parser.Traversal
open BSmtLib.Parser (Input PM Step)
open BSmtLib.Parser.Category.Ident (IdentState)
open BSmtLib.Parser.Category.Sort (SortState SortMode SortLevel sortStep sortComplete)
open BSmtLib.Facts.Proofs.Parser.Rejection.Basic.Lang
open BSmtLib.Facts.Parser.Adapters.Bridge BSmtLib.Facts.Proofs.Parser.Rejection.Basic

/-! ## Items -/

/-- The item `)`. -/
abbrev closeItem : Received := .token .parenClose

/-- The item `(`. -/
abbrev openItem : Received := .token .parenOpen

/-- The item of the reserved word. -/
abbrev wordItem (w : String) : Received := .token (word w)

/-- A symbol, any. -/
def SymbolLang : Lang := fun u => ∃ name, u = [.token (.symbol name)]

/-- An index of the version. -/
def IndexLang (version : BSmtLibSpec.Lexicon.Version) : Lang :=
  fun u => ∃ index : Tree.Index, index.Valid version ∧ u = toks index.tokens

/-- An identifier of the version. -/
def IdentLang (version : BSmtLibSpec.Lexicon.Version) : Lang :=
  fun u => ∃ identifier : Tree.Identifier, identifier.Valid version ∧ u = toks identifier.tokens

/-- A sort of the version. -/
def SortLang (version : BSmtLibSpec.Lexicon.Version) : Lang :=
  fun u => ∃ sort : Tree.«Sort», sort.Valid version ∧ u = toks sort.tokens

theorem symbolLang_intro (name : Tree.Symbol) : SymbolLang [.token (.symbol name)] := ⟨name, rfl⟩

theorem symbolLang_nonempty : ∃ u, SymbolLang u := ⟨_, symbolLang_intro ⟨[], false⟩⟩

theorem identLang_symbol (version : BSmtLibSpec.Lexicon.Version) (name : Tree.Symbol) :
    IdentLang version [.token (.symbol name)] :=
  ⟨⟨name, []⟩, by simp [Tree.Identifier.Valid], rfl⟩

theorem sortLang_symbol (version : BSmtLibSpec.Lexicon.Version) (name : Tree.Symbol) :
    SortLang version [.token (.symbol name)] :=
  ⟨⟨⟨name, []⟩, []⟩, by simp [Tree.«Sort».Valid, Tree.«Sort».ValidAll, Tree.Identifier.Valid], rfl⟩

theorem sortLang_nonempty (version : BSmtLibSpec.Lexicon.Version) : ∃ u, SortLang version u :=
  ⟨_, sortLang_symbol version ⟨[], false⟩⟩

theorem identLang_nonempty (version : BSmtLibSpec.Lexicon.Version) : ∃ u, IdentLang version u :=
  ⟨_, identLang_symbol version ⟨[], false⟩⟩

theorem indexLang_nonempty (version : BSmtLibSpec.Lexicon.Version) : ∃ u, IndexLang version u :=
  ⟨_, ⟨.numeral [], trivial, rfl⟩⟩

/-! ## Identifiers -/

/-- The remainders of the identifier parser's states. -/
def identRem (version : BSmtLibSpec.Lexicon.Version) : IdentState → Lang
  | .start => IdentLang version
  | .opened => cat (tok (wordItem "_")) (cat SymbolLang
      (cat (plus (IndexLang version)) (tok closeItem)))
  | .afterUnderscore => cat SymbolLang (cat (plus (IndexLang version)) (tok closeItem))
  | .indices _ found =>
    cat (rep (IndexLang version) (if found.isEmpty then 1 else 0) none) (tok closeItem)

theorem identRem_nonempty (version : BSmtLibSpec.Lexicon.Version) (state : IdentState) :
    ∃ u, identRem version state u := by
  have hplus := rep_nonempty (indexLang_nonempty version) 1 none (by simp)
  cases state with
  | start => exact identLang_nonempty version
  | opened =>
    exact cat_nonempty ⟨_, tok_intro _⟩ (cat_nonempty symbolLang_nonempty
      (cat_nonempty hplus ⟨_, tok_intro _⟩))
  | afterUnderscore =>
    exact cat_nonempty symbolLang_nonempty (cat_nonempty hplus ⟨_, tok_intro _⟩)
  | indices _ found =>
    exact cat_nonempty (rep_nonempty (indexLang_nonempty version) _ none (by simp))
      ⟨_, tok_intro _⟩

/-- An indexed identifier, after its `(`: `_`, its symbol, its indices and its `)`. -/
theorem identLang_indexed {version : BSmtLibSpec.Lexicon.Version} {u : List Received}
    (h : identRem version .opened u) : IdentLang version (openItem :: u) := by
  obtain ⟨_, _, rfl, ⟨_, _, ⟨name, rfl⟩, ⟨_, _, hindices, rfl, rfl⟩, rfl⟩, rfl⟩ := h
  obtain ⟨indices, hvalid, hlen, -, rfl⟩ := rep_trees hindices
  refine ⟨⟨name, indices⟩, fun index hindex => hvalid index hindex, ?_⟩
  cases indices with
  | nil => simp at hlen
  | cons first rest =>
    simp [Tree.Identifier.tokens, paren, word, toks, List.flatMap, Function.comp_def]

theorem isWord_eq {token : Input} {w : Token.Reserved.GeneralReserved} (h : token.isWord w = true) :
    token = .reserved (.general w) := by
  cases token with
  | reserved r =>
    cases r with
    | general w' =>
      cases w <;> cases w' <;> first | rfl | exact absurd h (by decide)
    | commandName => simp [Input.isWord] at h
  | _ => simp [Input.isWord] at h

theorem received_eq {token : Input} {item : Received} (h : Bridge.received token = some item) :
    item = (Bridge.received token).get (by simp [h]) := by
  simp [h]

/-- Every step of the identifier parser advances. -/
theorem identStep_advances (version : Token.Version) :
    StepsAdvance version (IdentState.step (H := List Event) version)
      (identRem (Bridge.version version))
      fun state _ => identRem (Bridge.version version) state := by
  intro state token item hitem _
  cases state with
  | start =>
    cases token with
    | symbol s =>
      item_of hitem
      exact Sound.pure fun _ => identLang_symbol _ _
    | parenOpen =>
      item_of hitem
      exact Sound.pure fun _ => ⟨fun u hu => identLang_indexed hu, identRem_nonempty _ _⟩
    | _ => exact Sound.syntaxError trivial
  | opened =>
    show Sound _ _ (if token.isWord .underscore then _ else _)
    split
    · rename_i hword
      obtain rfl := isWord_eq hword
      item_of hitem
      exact Sound.pure fun _ => ⟨fun u hu => cat_tok hu, identRem_nonempty _ _⟩
    · exact Sound.syntaxError trivial
  | afterUnderscore =>
    cases token with
    | symbol s =>
      item_of hitem
      refine Sound.pure fun _ => ⟨fun u hu => ?_, identRem_nonempty _ _⟩
      exact cat_intro' (symbolLang_intro _) (by simpa [identRem] using hu) rfl
    | _ => exact Sound.syntaxError trivial
  | indices s found =>
    cases token with
    | parenClose =>
      item_of hitem
      show Sound _ _ (if found.isEmpty then _ else _)
      split
      · exact Sound.syntaxError trivial
      · rename_i hempty
        refine Sound.pure fun _ => ?_
        show identRem _ (.indices s found) [_]
        simp only [identRem, hempty]
        exact cat_intro' rep_nil (tok_intro _) rfl
    | constant c =>
      cases c with
      | numeral d =>
        item_of hitem
        refine Sound.pure fun _ => ⟨fun u hu => ?_, identRem_nonempty _ _⟩
        obtain ⟨a, b, ha, hb, rfl⟩ := hu
        simp only [identRem] at ha ⊢
        refine cat_intro' (rep_cons (A := IndexLang _) ⟨.numeral (Bridge.chars d.asSlice), trivial,
          rfl⟩ (by rw [push_isEmpty] at ha; split <;> simpa using ha) (by simp)) hb ?_
        rfl
      | _ => exact Sound.syntaxError trivial
    | symbol i =>
      show Sound _ _ (if version ≥ .v2_5 then _ else _)
      split
      · rename_i hversion
        item_of hitem
        refine Sound.pure fun _ => ⟨fun u hu => ?_, identRem_nonempty _ _⟩
        obtain ⟨a, b, ha, hb, rfl⟩ := hu
        simp only [identRem] at ha ⊢
        refine cat_intro' (rep_cons (A := IndexLang _) ⟨.symbol (Bridge.symbol i),
          atLeast_v2_5_of_ge hversion, rfl⟩
          (by rw [push_isEmpty] at ha; split <;> simpa using ha) (by simp))
          hb ?_
        rfl
      · exact Sound.syntaxError trivial
    | _ => exact Sound.syntaxError trivial

/-! ## Sorts -/

section

variable (version : BSmtLibSpec.Lexicon.Version)

/-- What follows a sort that is an argument of the innermost open application: the application's
further arguments and its `)`, then what follows the application, outwards. -/
def sortAfter : List (SortLevel Nat) → Lang
  | [] => eps
  | _ :: outer => cat (star (SortLang version)) (cat (tok closeItem) (sortAfter outer))

/-- The remainders of the sort parser's states. -/
def sortRem (state : SortState Nat) : Lang :=
  match state.mode with
  | .start =>
    match state.levels with
    | [] => SortLang version
    | level :: outer =>
      cat (rep (SortLang version) (if level.arguments.isEmpty then 1 else 0) none)
        (cat (tok closeItem) (sortAfter version outer))
  | .opened =>
    cat (union (identRem version .opened)
      (cat (IdentLang version) (cat (plus (SortLang version)) (tok closeItem))))
      (sortAfter version state.levels)
  | .identOnly ident => cat (identRem version ident) (sortAfter version state.levels)
  | .startingIdent ident =>
    cat (identRem version ident)
      (cat (plus (SortLang version)) (cat (tok closeItem) (sortAfter version state.levels)))

theorem sortAfter_nonempty (levels : List (SortLevel Nat)) : ∃ u, sortAfter version levels u := by
  induction levels with
  | nil => exact ⟨[], rfl⟩
  | cons _ outer ih =>
    exact cat_nonempty ⟨[], rep_nil⟩ (cat_nonempty ⟨_, tok_intro _⟩ ih)

theorem sortRem_nonempty (state : SortState Nat) : ∃ u, sortRem version state u := by
  obtain ⟨mode, levels⟩ := state
  have hplus := rep_nonempty (sortLang_nonempty version) 1 none (by simp)
  cases mode with
  | start =>
    cases levels with
    | nil => exact sortLang_nonempty version
    | cons level outer =>
      exact cat_nonempty (rep_nonempty (sortLang_nonempty version) _ none (by simp))
        (cat_nonempty ⟨_, tok_intro _⟩ (sortAfter_nonempty version outer))
  | opened =>
    exact cat_nonempty ((identRem_nonempty version .opened).elim fun u hu => ⟨u, Or.inl hu⟩)
      (sortAfter_nonempty version levels)
  | identOnly ident =>
    exact cat_nonempty (identRem_nonempty version ident) (sortAfter_nonempty version levels)
  | startingIdent ident =>
    exact cat_nonempty (identRem_nonempty version ident) (cat_nonempty hplus
      (cat_nonempty ⟨_, tok_intro _⟩ (sortAfter_nonempty version levels)))

/-- A sort, then what follows it, is a remainder of the parser before it. -/
theorem sortRem_start {levels : List (SortLevel Nat)} {w v : List Received}
    (hw : SortLang version w) (hv : sortAfter version levels v) :
    sortRem version { mode := .start, levels } (w ++ v) := by
  cases levels with
  | nil =>
    simp only [sortAfter, eps] at hv
    subst hv
    simpa [sortRem] using hw
  | cons level outer =>
    obtain ⟨a, b, ha, hb, rfl⟩ := hv
    simp only [sortRem]
    rw [← List.append_assoc]
    exact cat_intro (rep_cons hw (by split <;> simpa using ha) (by simp)) hb

end

/-- The sort parser's step at the end of a sort: the sort is the result, or the next argument
of the innermost open application. -/
theorem sortComplete_advances {version : BSmtLibSpec.Lexicon.Version} {state : SortState Nat}
    {item : Received} {levels : List (SortLevel Nat)} (head : Nodes.Identifier)
    (arguments : Array Nat)
    {Q : Parser.ParseErrorCause Unit → Prop}
    (h : ∀ v, sortAfter version levels v → sortRem version state (item :: v)) :
    Sound (Advances (sortRem version) (fun state _ => sortRem version state) state item) Q
      (sortComplete (H := List Event) levels head arguments) := by
  unfold sortComplete
  refine Sound.bind (Sound.ofCall fun _ => ⟨_, _, rfl⟩) fun _ _ => ?_
  cases levels with
  | nil => exact Sound.pure fun _ => h [] rfl
  | cons level outer =>
    refine Sound.pure fun _ => ⟨fun u hu => h u ?_, sortRem_nonempty version _⟩
    simpa [sortRem, sortAfter, push_isEmpty] using hu

theorem sortTokensAll_eq (sorts : List Tree.«Sort») :
    Tree.«Sort».tokensAll sorts = (sorts.map Tree.«Sort».tokens).flatten := by
  induction sorts with
  | nil => rfl
  | cons first rest ih => simp [Tree.«Sort».tokensAll, ih]

theorem sortValidAll_of {version : BSmtLibSpec.Lexicon.Version} {sorts : List Tree.«Sort»}
    (h : ∀ sort ∈ sorts, sort.Valid version) : Tree.«Sort».ValidAll version sorts := by
  induction sorts with
  | nil => trivial
  | cons first rest ih =>
    exact ⟨h first (by simp), ih fun sort hsort => h sort (by simp [hsort])⟩

/-- Sorts, one after another, as a repetition. -/
theorem sorts_rep {version : BSmtLibSpec.Lexicon.Version} {lo : Nat} {hi : Option Nat}
    {u : List Received} (h : rep (SortLang version) lo hi u) :
    ∃ sorts : List Tree.«Sort», Tree.«Sort».ValidAll version sorts ∧ lo ≤ sorts.length ∧
      u = toks (Tree.«Sort».tokensAll sorts) := by
  obtain ⟨sorts, hvalid, hlo, -, rfl⟩ := rep_trees h
  exact ⟨sorts, sortValidAll_of hvalid, hlo, by simp [sortTokensAll_eq, Function.comp_def]⟩

/-- After a sort's `(`, the rest of the sort. -/
theorem sortLang_of_opened {version : BSmtLibSpec.Lexicon.Version} {a : List Received}
    (h : union (identRem version .opened)
      (cat (IdentLang version) (cat (plus (SortLang version)) (tok closeItem))) a) :
    SortLang version (openItem :: a) := by
  rcases h with h | ⟨i, _, ⟨identifier, hident, rfl⟩, ⟨p, _, hp, rfl, rfl⟩, rfl⟩
  · obtain ⟨identifier, hident, htokens⟩ := identLang_indexed h
    refine ⟨⟨identifier, []⟩, ⟨hident, trivial⟩, ?_⟩
    simpa [Tree.«Sort».tokens] using htokens
  · obtain ⟨arguments, hvalid, hlen, rfl⟩ := sorts_rep hp
    refine ⟨⟨identifier, arguments⟩, ⟨hident, hvalid⟩, ?_⟩
    cases arguments with
    | nil => simp at hlen
    | cons first rest => simp [Tree.«Sort».tokens, paren, toks]

/-- Every step of the sort parser advances. -/
theorem sortStep_advances (version : Token.Version) :
    StepsAdvance version (sortStep (H := List Event) version)
      (sortRem (Bridge.version version)) fun state _ => sortRem (Bridge.version version) state := by
  intro ⟨mode, levels⟩ token item hitem hlex
  cases mode with
  | start =>
    cases token with
    | symbol name =>
      item_of hitem
      exact sortComplete_advances _ _ fun v hv => sortRem_start _ (sortLang_symbol _ _) hv
    | parenOpen =>
      item_of hitem
      refine Sound.pure fun _ => ⟨fun u hu => ?_, sortRem_nonempty _ _⟩
      obtain ⟨a, b, ha, hb, rfl⟩ := hu
      rw [← List.cons_append]
      exact sortRem_start _ (sortLang_of_opened ha) hb
    | parenClose =>
      cases levels with
      | nil => exact Sound.syntaxError trivial
      | cons level outer =>
        show Sound _ _ (if level.arguments.isEmpty then _ else _)
        split
        · exact Sound.syntaxError trivial
        · rename_i hne
          item_of hitem
          refine sortComplete_advances _ _ fun v hv => ?_
          simp only [sortRem, hne]
          exact cat_intro' rep_nil (cat_intro (tok_intro _) hv) rfl
    | _ => exact Sound.syntaxError trivial
  | opened =>
    cases token with
    | symbol name =>
      item_of hitem
      refine Sound.pure fun _ => ⟨fun u hu => ?_, sortRem_nonempty _ _⟩
      obtain ⟨p, _, hp, ⟨c, r, hc, hr, rfl⟩, rfl⟩ := hu
      simp only [Array.isEmpty_empty, ite_true] at hp
      refine cat_intro' (Or.inr (cat_intro' (identLang_symbol _ (Bridge.symbol name))
        (cat_intro hp hc) rfl)) hr ?_
      simp
    | parenOpen =>
      item_of hitem
      refine Sound.pure fun _ => ⟨fun u hu => ?_, sortRem_nonempty _ _⟩
      obtain ⟨i, _, hi, ⟨p, _, hp, ⟨c, r, hc, hr, rfl⟩, rfl⟩, rfl⟩ := hu
      refine cat_intro' (Or.inr (cat_intro' (identLang_indexed hi) (cat_intro hp hc) rfl)) hr ?_
      simp
    | reserved r =>
      show Sound _ _ (if (Input.reserved r).isWord .underscore then _ else _)
      split
      · rename_i hword
        rw [isWord_eq hword] at hitem
        item_of hitem
        refine Sound.pure fun _ => ⟨fun u hu => ?_, sortRem_nonempty _ _⟩
        obtain ⟨a, b, ha, hb, rfl⟩ := hu
        exact cat_intro' (Or.inl (cat_tok ha)) hb rfl
      · exact Sound.syntaxError trivial
    | _ => exact Sound.syntaxError trivial
  | identOnly ident =>
    refine Sound.bind (identStep_advances version ident token item hitem hlex) fun r hr => ?_
    replace hr := hr.from (identRem_nonempty _ _)
    cases r with
    | more ident' =>
      refine Sound.pure fun _ => ⟨fun u hu => ?_, sortRem_nonempty _ _⟩
      obtain ⟨a, b, ha, hb, rfl⟩ := hu
      exact cat_intro' (hr.1 a ha) hb rfl
    | done head =>
      exact sortComplete_advances head #[] fun v hv => cat_intro' hr hv rfl
  | startingIdent ident =>
    refine Sound.bind (identStep_advances version ident token item hitem hlex) fun r hr => ?_
    replace hr := hr.from (identRem_nonempty _ _)
    cases r with
    | more ident' =>
      refine Sound.pure fun _ => ⟨fun u hu => ?_, sortRem_nonempty _ _⟩
      obtain ⟨a, b, ha, hb, rfl⟩ := hu
      exact cat_intro' (hr.1 a ha) hb rfl
    | done head =>
      refine Sound.pure fun _ => ⟨fun u hu => ?_, sortRem_nonempty _ _⟩
      obtain ⟨p, _, hp, hrest, rfl⟩ := hu
      simp only [Array.isEmpty_empty, ite_true] at hp
      exact cat_intro' hr (cat_intro hp hrest) rfl

end BSmtLib.Facts.Proofs.Parser.Rejection.«Sort»
