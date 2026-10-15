module

public import BSmtLib.Facts.Proofs.Parser.Category.Ident
import all BSmtLib.Parser
import all BSmtLib.Parser.Category.Token
import all BSmtLib.Parser.Category.Sort
import all BSmtLib.Parser.Category.SortedVar
import all BSmtLib.Token.Reserved

@[expose] public section

/-!
# The sorted variable parser on a cursor

The sorted variable parser runs the sort parser inside its `sort` state; the sort's lemma is the
sort proofs' (`Facts.Proofs.Parser.Sort.sort_runs`), taken over by `RunsS.embed`.
-/

namespace BSmtLib.Facts.Proofs.Parser.Category.SortedVar

open BSmtLibSpec.Grammar
open BSmtLibSpec.Parser
open BSmtLibSpec.Parser.Traversal
open BSmtLib.Token (Produce)
open BSmtLib.Parser (Parse ParseState SyntaxErrorKind)
open BSmtLib.Parser.Internal (PM)
open BSmtLib.Parser.Category.SortedVar BSmtLib.Parser.Category.Sort
open BSmtLib.Parser.Category.SortedVar.Internal
open BSmtLib.Parser.Category.Sort.Internal
open BSmtLib.Parser.Category.SortedVar.Internal
open BSmtLib.Parser.Category.Sort.Internal
open BSmtLib.Facts.Parser.Adapters.Bridge BSmtLib.Facts.Parser.Adapters.Run
open BSmtLib.Facts.Parser.Adapters.Cursor (Takes Reads noPoints)
open BSmtLib.Facts.Parser.Adapters.Outcome (Finishes Rejects)
open BSmtLib.Facts.Proofs.Parser.Category.Cursor (Simulates Moves tick_noPoints)
open BSmtLib.Facts.Proofs.Parser.Category.Ident
open BSmtLib.Facts.Proofs.Parser.Category.Steps BSmtLib.Facts.Proofs.Parser.Category.CursorS
open BSmtLib.Facts.Proofs.Parser.Drive BSmtLib.Facts.Proofs.Parser.Tokens
open BSmtLib.Facts.Proofs.Parser.Tokens.Stands

section

variable {H : Type} {m : Type → Type} [Monad m] [LawfulMonad m] [Traits.Handler H m]

private theorem sortedVar_sim (version : Token.Version) :
    Simulates version (SortedVarParser.mk (H := H)) (sortedVarStep version)
      SortedVarParser.new := by
  refine ⟨fun _ _ => rfl, fun state token => ?_, fun _ => rfl⟩
  show (do
      match ← sortedVarStep version state token with
      | .more state => return Parser.Internal.Flow.more (SortedVarParser.mk state)
      | .done result => return .done result) = _
  rw [map_eq_pure_bind]
  refine bind_congr fun step => ?_
  cases step <;> rfl

/-- From its start, the sorted variable parser reads the tokens of a valid sorted variable with
the traversal's calls for its sort. -/
theorem sortedVar_runs {version : Token.Version}
    {h : Handler (StateT H m) (Traits.Handler.Error H) (valuesOf H)} (hA : TermAgrees h)
    (sortedVar : Tree.SortedVar) (hvalid : sortedVar.Valid (Bridge.version version))
    {tokens : List Parser.Internal.Input} (hs : Stands tokens sortedVar.tokens) :
    ∃ symbol : Nodes.Symbol, Bridge.symbol symbol = sortedVar.symbol ∧
      RunsS noPoints (sortedVarStep version) .start tokens
        ((fun sort => (symbol, sort)) <$> adaptRun (Traversal.sort noPoints h sortedVar.sort))
        fun result => pure (.done result) := by
  obtain ⟨name, sort⟩ := sortedVar
  obtain ⟨inner, rfl, hinner⟩ := Stands.split_paren hs
  obtain ⟨symbolToken, sortTokens, rfl, hsymbol, hsort⟩ := Stands.split_cons hinner
  obtain ⟨symbol, rfl, rfl⟩ := Parser.Internal.Input.received_symbol hsymbol
  refine ⟨symbol, rfl, ?_⟩
  have hsortRuns := RunsS.embed (outer := sortedVarStep (H := H) version)
    (fun state => SortedVarState.sort symbol state)
    (fun sort => pure (.more (.close symbol sort)))
    (fun state token => by
      simp only [sortedVarStep]
      congr 1
      funext step
      cases step <;> rfl)
    (BSmtLib.Facts.Proofs.Parser.Category.StepsSort.sort_runs (points := noPoints) hA sort
      hvalid hsort [])
  have hclose : ∀ sort : Traits.Handler.«Sort» H,
      RunsS noPoints (sortedVarStep version) (.close symbol sort) [.parenClose]
        (do tick noPoints .parenClose; pure (symbol, sort)) fun result => pure (.done result) :=
    fun sort => RunsS.token (by simp [sortedVarStep, Parser.Category.Token.Internal.expectClose])
  rw [show Parser.Internal.Input.parenOpen :: (Parser.Internal.Input.symbol symbol :: sortTokens ++
      [.parenClose]) = [.parenOpen] ++ ([.symbol symbol] ++ (sortTokens ++ [.parenClose])) by
    simp]
  refine (RunsS.append (middle := fun _ => SortedVarState.opened)
    (RunsS.token_more (by simp [sortedVarStep, Parser.Category.Token.Internal.expectOpen])) fun _ =>
      RunsS.append (middle := fun _ => SortedVarState.sort symbol .init)
        (RunsS.token_more (by simp [sortedVarStep, Parser.Category.Token.Internal.expectSymbol])) fun _ =>
          RunsS.append (middle := fun sort => SortedVarState.close symbol sort)
            (hsortRuns.congr rfl (by
              funext
              simp [BSmtLib.Facts.Proofs.Parser.«Sort».sortPush, Parser.Internal.Step.wrap]))
            hclose).congr ?_ rfl
  simp only [tick_noPoints, pure_bind]
  rw [bind_pure_comp]

omit [LawfulMonad m] in
private theorem sortedVar_hparse {Z : Type} [Produce Z] (p : SortedVarParser H) (s : ParseState H)
    (c : Z) : Parse.parse (m := m) p s c = Parser.Internal.parseByToken p s c := rfl

/-- The sorted variable parser from its start on the tokens of a valid sorted variable: it
finishes with its symbol, through the bridge, and the handled sort, making the traversal's calls
for its sort. -/
theorem sortedVar_parses {version : Token.Version}
    {h : Handler (StateT H m) (Traits.Handler.Error H) (valuesOf H)} (hA : TermAgrees h)
    (sortedVar : Tree.SortedVar) (hvalid : sortedVar.Valid (Bridge.version version))
    {tokens : List Parser.Internal.Input} (hs : Stands tokens sortedVar.tokens) :
    ∃ symbol : Nodes.Symbol, Bridge.symbol symbol = sortedVar.symbol ∧
      Finishes version (SortedVarParser.new (H := H)) tokens
        ((fun sort => (symbol, sort)) <$> adaptRun (Traversal.sort noPoints h sortedVar.sort))
        SortedVarParser.new := by
  obtain ⟨symbol, hsymbol, hruns⟩ := sortedVar_runs hA sortedVar hvalid hs
  exact ⟨symbol, hsymbol, parses_of_runsS (state := SortedVarState.start)
    (@sortedVar_hparse H m _ _) (sortedVar_sim version) hruns⟩

private theorem sortedVar_rejects {version : Token.Version}
    {state last : SortedVarState (Traits.Handler.«Sort» H)}
    {tokens : List Parser.Internal.Input} {token : Parser.Internal.Input} {kind : SyntaxErrorKind}
    (hmoves : Moves (sortedVarStep (H := H) version) state tokens last)
    (hfail : sortedVarStep (H := H) version last token = throw (.syntax kind)) :
    Rejects version (SortedVarParser.mk state) (tokens ++ [token]) (pure () : PM H Unit) kind :=
  rejects_of_movesS (@sortedVar_hparse H m _ _) (sortedVar_sim version) hmoves hfail

/-- The sorted variable parser on a first token that is not `(`. -/
theorem sortedVar_rejects_open {version : Token.Version} {token : Parser.Internal.Input}
    (htoken : token ≠ .parenOpen) :
    Rejects version (SortedVarParser.new (H := H)) [token] (pure () : PM H Unit)
      (.expectedToken #[.parenOpen]) :=
  sortedVar_rejects (tokens := []) (.nil _) (by
    cases token <;> first | exact absurd rfl htoken |
      simp [sortedVarStep, Parser.Category.Token.Internal.expectOpen, Parser.Internal.syntaxError])

/-- The sorted variable parser on `(` and a token that is not a symbol. -/
theorem sortedVar_rejects_symbol {version : Token.Version} {token : Parser.Internal.Input}
    (htoken : ∀ symbol, token ≠ .symbol symbol) :
    Rejects version (SortedVarParser.new (H := H)) [.parenOpen, token] (pure () : PM H Unit)
      .expectedSymbol :=
  sortedVar_rejects (tokens := [.parenOpen])
    (.cons (middle := .opened) (by simp [sortedVarStep, Parser.Category.Token.Internal.expectOpen])
      (.nil _)) (by
    cases token <;> first | exact absurd rfl (htoken _) |
      simp [sortedVarStep, Parser.Category.Token.Internal.expectSymbol, Parser.Internal.syntaxError])

/-- The sorted variable parser on `(`, a symbol and a token that starts no sort: neither a
symbol nor `(`. -/
theorem sortedVar_rejects_sort {version : Token.Version} (symbol : Nodes.Symbol)
    {token : Parser.Internal.Input} (hsymbol : ∀ symbol, token ≠ .symbol symbol)
    (hopen : token ≠ .parenOpen) :
    Rejects version (SortedVarParser.new (H := H)) [.parenOpen, .symbol symbol, token]
      (pure () : PM H Unit) .expectedSort :=
  sortedVar_rejects (tokens := [.parenOpen, .symbol symbol])
    (.cons (middle := .opened) (by simp [sortedVarStep, Parser.Category.Token.Internal.expectOpen])
      (.cons (middle := .sort symbol .init)
        (by simp [sortedVarStep, Parser.Category.Token.Internal.expectSymbol]) (.nil _))) (by
    cases token <;> first | exact absurd rfl (hsymbol _) | exact absurd rfl hopen |
      simp [sortedVarStep, sortStep.eq_def, SortState.init, Parser.Internal.syntaxError])


/-- The sort parser's steps, within the sorted variable after its symbol. -/
private theorem sortedVar_sortRuns {version : Token.Version} (symbol : Nodes.Symbol)
    {tokens : List Parser.Internal.Input} {α : Type} {program : PM H α}
    {next : α → PM H (Parser.Internal.Step (SortState (Traits.Handler.«Sort» H))
      (Traits.Handler.«Sort» H))}
    (hsort : RunsS noPoints (sortStep version) SortState.init tokens program next) :
    RunsS noPoints (sortedVarStep (H := H) version) .start
      ([.parenOpen] ++ ([.symbol symbol] ++ tokens)) program
      fun a => next a >>= Parser.Internal.Step.wrap (fun state => SortedVarState.sort symbol state)
        fun sort => pure (.more (.close symbol sort)) := by
  have hsortRuns := RunsS.embed (outer := sortedVarStep (H := H) version)
    (fun state => SortedVarState.sort symbol state)
    (fun sort => pure (.more (.close symbol sort)))
    (fun state token => by
      simp only [sortedVarStep]
      congr 1
      funext step
      cases step <;> rfl) hsort
  refine (RunsS.append (middle := fun _ => SortedVarState.opened)
    (RunsS.token_more (by simp [sortedVarStep, Parser.Category.Token.Internal.expectOpen])) fun _ =>
      RunsS.append (middle := fun _ => SortedVarState.sort symbol .init)
        (RunsS.token_more (by simp [sortedVarStep, Parser.Category.Token.Internal.expectSymbol])) fun _ =>
          hsortRuns).congr ?_ rfl
  simp only [tick_noPoints, pure_bind]

/--
The sorted variable parser on `(`, a symbol and tokens on whose last token the sort parser fails
with a syntax error, having made the calls of a program: it rejects them with that error, having
made those calls.
-/
theorem sortedVar_rejects_sort_inner {version : Token.Version} (symbol : Nodes.Symbol)
    {tokens : List Parser.Internal.Input} {α : Type} {program : PM H α} {kind : SyntaxErrorKind}
    (hsort : RunsS noPoints (sortStep version) SortState.init tokens program
      fun _ => throw (.syntax kind)) :
    Rejects version (SortedVarParser.new (H := H))
      (.parenOpen :: .symbol symbol :: tokens) ((fun _ => ()) <$> program) kind := by
  have hruns := (sortedVar_sortRuns symbol hsort).congr
      (next' := fun _ => throw (Parser.ParseErrorCause.syntax kind)) rfl (by
    funext a
    apply ExceptT.ext
    simp [ExceptT.run_throw])
  have := rejects_of_runsS (state := SortedVarState.start) (@sortedVar_hparse H m _ _)
    (sortedVar_sim version) hruns
  exact this

/-- The sorted variable parser on `(`, a symbol, the tokens of a valid sort and a token that is
not `)`: it rejects that token with `expectedToken [)]`, having made the traversal's calls for
the sort. -/
theorem sortedVar_rejects_close {version : Token.Version}
    {h : Handler (StateT H m) (Traits.Handler.Error H) (valuesOf H)} (hA : TermAgrees h)
    (symbol : Nodes.Symbol) {sort : Tree.«Sort»} (hvalid : sort.Valid (Bridge.version version))
    {sortTokens : List Parser.Internal.Input} (hs : Stands sortTokens sort.tokens)
    {token : Parser.Internal.Input} (htoken : token ≠ .parenClose) :
    Rejects version (SortedVarParser.new (H := H))
      (.parenOpen :: .symbol symbol :: (sortTokens ++ [token]))
      ((fun _ => ()) <$> adaptRun (Traversal.sort noPoints h sort))
      (.expectedToken #[.parenClose]) := by
  have hsort := (BSmtLib.Facts.Proofs.Parser.Category.StepsSort.sort_runs (points := noPoints) hA
    sort hvalid hs [])
  have hfail : ∀ handled : Traits.Handler.«Sort» H,
      RunsS noPoints (sortedVarStep version) (.close symbol handled) [token]
        (do tick noPoints token; pure ())
        fun _ => throw (.syntax (.expectedToken #[.parenClose])) :=
    fun handled => RunsS.token (by
      cases token <;> first | exact absurd rfl htoken |
        simp [sortedVarStep, Parser.Category.Token.Internal.expectClose, Parser.Internal.syntaxError])
  have hruns := RunsS.append (middle := fun sort => SortedVarState.close symbol sort)
    ((sortedVar_sortRuns symbol hsort).congr rfl (by
      funext
      simp [BSmtLib.Facts.Proofs.Parser.«Sort».sortPush, Parser.Internal.Step.wrap])) hfail
  have := rejects_of_runsS (state := SortedVarState.start) (@sortedVar_hparse H m _ _)
    (sortedVar_sim version) hruns
  simp only [tick_noPoints, pure_bind, List.cons_append, List.nil_append,
    ] at this
  simp only [bind_pure_comp, Functor.map_map] at this
  exact this


/-! ## Sorts that fail -/

/-- The sort parser from its start on a token that starts no sort: neither a symbol nor `(`. -/
theorem sort_fails_first {version : Token.Version} {token : Parser.Internal.Input}
    (hsymbol : ∀ symbol, token ≠ .symbol symbol) (hopen : token ≠ .parenOpen) :
    RunsS noPoints (sortStep (H := H) version) SortState.init [token] (pure () : PM H Unit)
      fun _ => throw (.syntax .expectedSort) :=
  (RunsS.token (program := (pure () : PM H Unit)) (by
    cases token <;> first | exact absurd rfl (hsymbol _) | exact absurd rfl hopen |
      simp [sortStep.eq_def, SortState.init, Parser.Internal.syntaxError])
    (handlerOnly_pure ())).congr (by simp [tick_noPoints]) rfl

/-- The sort parser on `(` and a token that starts no head: neither a symbol, nor `(`, nor
`_`. -/
theorem sort_fails_inner {version : Token.Version} {token : Parser.Internal.Input}
    (hsymbol : ∀ symbol, token ≠ .symbol symbol) (hopen : token ≠ .parenOpen)
    (hunderscore : token ≠ .reserved (.general .underscore)) :
    RunsS noPoints (sortStep (H := H) version) SortState.init [.parenOpen, token]
      (pure () : PM H Unit) fun _ => throw (.syntax .expectedSortInner) := by
  have hu : token.isWord .underscore = false := by
    cases token with
    | reserved word =>
      cases word with
      | general w => cases w <;> first | exact absurd rfl hunderscore | rfl
      | _ => rfl
    | _ => rfl
  refine (RunsS.append (middle := fun _ => ({ mode := .opened, levels := [] } : SortState _))
    (RunsS.token_more (by simp [sortStep.eq_def, SortState.init])) fun _ =>
      RunsS.token (program := (pure () : PM H Unit)) (by
        cases token <;> first | exact absurd rfl (hsymbol _) | exact absurd rfl hopen |
          simp_all [sortStep.eq_def, Parser.Internal.syntaxError])
        (handlerOnly_pure ())).congr ?_ rfl
  simp [tick_noPoints]

/-- The sort parser on `(`, a symbol and `)`: an application without arguments. -/
theorem sort_fails_empty {version : Token.Version} (symbol : Nodes.Symbol) :
    RunsS noPoints (sortStep (H := H) version) SortState.init
      [.parenOpen, .symbol symbol, .parenClose] (pure () : PM H Unit)
      fun _ => throw (.syntax .emptySortApplication) := by
  refine (RunsS.append (middle := fun _ => ({ mode := .opened, levels := [] } : SortState _))
    (RunsS.token_more (by simp [sortStep.eq_def, SortState.init])) fun _ =>
      RunsS.append (middle := fun _ =>
        ({ mode := .start, levels := [⟨⟨symbol, #[]⟩, #[]⟩] } : SortState _))
        (RunsS.token_more (by simp [sortStep.eq_def])) fun _ =>
        RunsS.token (program := (pure () : PM H Unit)) (by
          simp [sortStep.eq_def, Parser.Internal.syntaxError]) (handlerOnly_pure ())).congr ?_ rfl
  simp [tick_noPoints]

/-- The sort parser on `(`, the tokens of a valid identifier, of valid sorts and a token that
neither starts another argument nor ends the application: it fails at that token, having made
the traversal's calls for the sorts. -/
theorem sort_fails_argument {version : Token.Version}
    {h : Handler (StateT H m) (Traits.Handler.Error H) (valuesOf H)} (hA : TermAgrees h)
    {head : Tree.Identifier} (hhead : head.Valid (Bridge.version version))
    {headTokens : List Parser.Internal.Input} (hsHead : Stands headTokens head.tokens)
    {sorts : List Tree.«Sort»} (hsorts : Tree.«Sort».ValidAll (Bridge.version version) sorts)
    {sortTokens : List Parser.Internal.Input}
    (hsSorts : Stands sortTokens (Tree.«Sort».tokensAll sorts))
    {token : Parser.Internal.Input} (hsymbol : ∀ symbol, token ≠ .symbol symbol)
    (hopen : token ≠ .parenOpen) (hclose : token ≠ .parenClose) :
    RunsS noPoints (sortStep (H := H) version) SortState.init
      (.parenOpen :: (headTokens ++ (sortTokens ++ [token])))
      ((fun _ => ()) <$> adaptRun (Traversal.sorts noPoints h sorts))
      fun _ => throw (.syntax .expectedSort) := by
  obtain ⟨node, _, hheadRuns⟩ := BSmtLib.Facts.Proofs.Parser.Category.StepsSort.head_runs
    (H := H) (points := noPoints) hhead hsHead []
  have hfail : ∀ handled : List (Traits.Handler.«Sort» H),
      RunsS noPoints (sortStep (H := H) version)
        { mode := .start, levels := [⟨node, #[] ++ handled.toArray⟩] } [token]
        (do tick noPoints token; (pure () : PM H Unit))
        fun _ => throw (.syntax .expectedSort) :=
    fun handled => RunsS.token (by
      cases token <;> first | exact absurd rfl (hsymbol _) | exact absurd rfl hopen |
        exact absurd rfl hclose | simp [sortStep.eq_def, Parser.Internal.syntaxError])
      (by handler_only)
  have hsortsRuns := BSmtLib.Facts.Proofs.Parser.Category.StepsSort.sorts_runs (H := H)
    (version := version) (points := noPoints) hA sorts hsorts hsSorts node #[] []
  have h₃ := RunsS.append (middle := fun (handled : List (Traits.Handler.«Sort» H)) =>
    ({ mode := .start, levels := [⟨node, #[] ++ handled.toArray⟩] } : SortState _))
    hsortsRuns hfail
  have h₂ := RunsS.append (middle := fun _ =>
    ({ mode := .start, levels := [⟨node, #[]⟩] } : SortState _)) hheadRuns fun _ => h₃
  have hopen' : RunsS noPoints (sortStep (H := H) version) SortState.init [.parenOpen]
      (tick noPoints .parenOpen) fun _ => pure (.more { mode := .opened, levels := [] }) :=
    RunsS.token_more (by simp [sortStep.eq_def, SortState.init])
  have h₁ := RunsS.append (middle := fun _ => ({ mode := .opened, levels := [] } : SortState _))
    hopen' fun _ => h₂
  refine h₁.congr ?_ rfl
  simp [tick_noPoints, ticks_noPoints, bind_pure_comp]


/-! ## The sorted variable parser on sorts that fail -/

/-- The sorted variable parser on `(`, a symbol, `(` and a token that starts no head of a
sort. -/
theorem sortedVar_rejects_sortInner {version : Token.Version} (symbol : Nodes.Symbol)
    {token : Parser.Internal.Input} (hsymbol : ∀ symbol, token ≠ .symbol symbol)
    (hopen : token ≠ .parenOpen) (hunderscore : token ≠ .reserved (.general .underscore)) :
    Rejects version (SortedVarParser.new (H := H))
      [.parenOpen, .symbol symbol, .parenOpen, token] (pure () : PM H Unit)
      .expectedSortInner := by
  have := sortedVar_rejects_sort_inner (H := H) (m := m) symbol
    (sort_fails_inner (version := version) hsymbol hopen hunderscore)
  simpa using this

/-- The sorted variable parser on `(`, a symbol, and `(`, a symbol and `)`: a sort application
without arguments. -/
theorem sortedVar_rejects_sortEmpty {version : Token.Version} (symbol head : Nodes.Symbol) :
    Rejects version (SortedVarParser.new (H := H))
      [.parenOpen, .symbol symbol, .parenOpen, .symbol head, .parenClose] (pure () : PM H Unit)
      .emptySortApplication := by
  have := sortedVar_rejects_sort_inner (H := H) (m := m) symbol
    (sort_fails_empty (version := version) head)
  simpa using this

/-- The sorted variable parser on `(`, a symbol, `(`, the tokens of a valid identifier and of
valid sorts and a token that neither starts another argument of the sort nor ends it: it rejects
that token with `expectedSort`, having made the traversal's calls for the sorts. -/
theorem sortedVar_rejects_sortArgument {version : Token.Version}
    {h : Handler (StateT H m) (Traits.Handler.Error H) (valuesOf H)} (hA : TermAgrees h)
    (symbol : Nodes.Symbol) {head : Tree.Identifier} (hhead : head.Valid (Bridge.version version))
    {headTokens : List Parser.Internal.Input} (hsHead : Stands headTokens head.tokens)
    {sorts : List Tree.«Sort»} (hsorts : Tree.«Sort».ValidAll (Bridge.version version) sorts)
    {sortTokens : List Parser.Internal.Input}
    (hsSorts : Stands sortTokens (Tree.«Sort».tokensAll sorts))
    {token : Parser.Internal.Input} (hsymbol : ∀ symbol, token ≠ .symbol symbol)
    (hopen : token ≠ .parenOpen) (hclose : token ≠ .parenClose) :
    Rejects version (SortedVarParser.new (H := H))
      (.parenOpen :: .symbol symbol :: .parenOpen :: (headTokens ++ (sortTokens ++ [token])))
      ((fun _ => ()) <$> adaptRun (Traversal.sorts noPoints h sorts)) .expectedSort := by
  have := sortedVar_rejects_sort_inner (H := H) (m := m) symbol
    (sort_fails_argument hA hhead hsHead hsorts hsSorts hsymbol hopen hclose)
  simpa [Functor.map_map] using this


/-! ## Sorts that fail inside open applications -/

/-- The tokens of open sort applications, outermost first: each a `(`, its head and its argument
sorts so far. -/
abbrev frameTokens (frames : List (Tree.Identifier × List Tree.«Sort»)) :
    List BSmtLibSpec.Grammar.SyntaxToken :=
  frames.flatMap fun frame => .parenOpen :: (frame.1.tokens ++ Tree.«Sort».tokensAll frame.2)

/-- From any stack, the sort parser reads the tokens of open applications with the traversal's
calls for their argument sorts, and is then before a sort, the applications open on the stack. -/
theorem sortFrames_runs {version : Token.Version}
    {h : Handler (StateT H m) (Traits.Handler.Error H) (valuesOf H)} (hA : TermAgrees h) :
    (frames : List (Tree.Identifier × List Tree.«Sort»)) →
    (∀ frame ∈ frames, frame.1.Valid (Bridge.version version) ∧
      Tree.«Sort».ValidAll (Bridge.version version) frame.2) →
    ∀ {tokens : List Parser.Internal.Input}, Stands tokens (frameTokens frames) →
    ∀ levels : List (SortLevel (Traits.Handler.«Sort» H)),
    ∃ build : List (List (Traits.Handler.«Sort» H)) → List (SortLevel (Traits.Handler.«Sort» H)),
      RunsS noPoints (sortStep (H := H) version) { mode := .start, levels } tokens
        (adaptRun (frames.mapM fun frame => Traversal.sorts noPoints h frame.2))
        fun handled => pure (.more { mode := .start, levels := build handled })
  | [], _, _, hs, levels => by
    have := Stands.eq_nil hs
    subst this
    exact ⟨fun _ => levels, (RunsS.nil [] rfl).congr (by simp) rfl⟩
  | frame :: frames, hvalid, _, hs, levels => by
    simp only [frameTokens, List.flatMap_cons] at hs
    obtain ⟨tokens₁, tokens₂, rfl, hs₁, hs₂⟩ := Stands.split hs
    obtain ⟨openToken, inner, rfl, hopen, hinner⟩ := Stands.split_cons hs₁
    rw [Parser.Internal.Input.received_parenOpen hopen]
    obtain ⟨headTokens, sortTokens, rfl, hsHead, hsSorts⟩ := Stands.split hinner
    obtain ⟨hhead, hsorts⟩ := hvalid frame (List.mem_cons_self ..)
    obtain ⟨node, _, hheadRuns⟩ := BSmtLib.Facts.Proofs.Parser.Category.StepsSort.head_runs
      (H := H) (points := noPoints) hhead hsHead levels
    have hsortsRuns := BSmtLib.Facts.Proofs.Parser.Category.StepsSort.sorts_runs (H := H)
      (version := version) (points := noPoints) hA frame.2 hsorts hsSorts node #[] levels
    have hrest := fun (handled : List (Traits.Handler.«Sort» H)) =>
      sortFrames_runs hA frames (fun f hf => hvalid f (List.mem_cons_of_mem _ hf)) hs₂
        (⟨node, #[] ++ handled.toArray⟩ :: levels)
    refine ⟨fun all => match all with
      | first :: others => Classical.choose (hrest first) others
      | [] => levels, ?_⟩
    have hopen' : RunsS noPoints (sortStep (H := H) version) { mode := .start, levels }
        [.parenOpen] (tick noPoints .parenOpen)
        fun _ => pure (.more { mode := .opened, levels }) :=
      RunsS.token_more (by simp [sortStep.eq_def])
    have h₃ := RunsS.append (middle := fun (handled : List (Traits.Handler.«Sort» H)) =>
      ({ mode := .start, levels := ⟨node, #[] ++ handled.toArray⟩ :: levels } : SortState _))
      (next := fun all => pure (.more { mode := .start, levels := match all with
        | first :: others => Classical.choose (hrest first) others
        | [] => levels }))
      hsortsRuns fun first =>
        (RunsS.map_program (f := (first :: ·)) (Classical.choose_spec (hrest first))).congr rfl rfl
    have h₂ := RunsS.append (middle := fun _ =>
      ({ mode := .start, levels := ⟨node, #[]⟩ :: levels } : SortState _)) hheadRuns fun _ => h₃
    have h₁ := RunsS.append (middle := fun _ => ({ mode := .opened, levels } : SortState _))
      hopen' fun _ => h₂
    simp only [List.cons_append, List.nil_append, List.append_assoc] at h₁ ⊢
    refine h₁.congr ?_ rfl
    simp [tick_noPoints, ticks_noPoints, List.mapM_cons, bind_pure_comp]


/-- Open applications, then a run from wherever they leave the stack to a syntax error: the sort
parser from its start fails there, having made the calls for the applications' argument sorts. -/
theorem sortFrames_fails {version : Token.Version}
    {h : Handler (StateT H m) (Traits.Handler.Error H) (valuesOf H)} (hA : TermAgrees h)
    {frames : List (Tree.Identifier × List Tree.«Sort»)}
    (hvalid : ∀ frame ∈ frames, frame.1.Valid (Bridge.version version) ∧
      Tree.«Sort».ValidAll (Bridge.version version) frame.2)
    {tokens : List Parser.Internal.Input} (hs : Stands tokens (frameTokens frames))
    {tokens' : List Parser.Internal.Input} {kind : SyntaxErrorKind}
    (hfail : ∀ levels : List (SortLevel (Traits.Handler.«Sort» H)),
      RunsS noPoints (sortStep (H := H) version) { mode := .start, levels } tokens'
        (pure () : PM H Unit) fun _ => throw (.syntax kind)) :
    RunsS noPoints (sortStep (H := H) version) SortState.init (tokens ++ tokens')
      ((fun _ => ()) <$> adaptRun (frames.mapM fun frame => Traversal.sorts noPoints h frame.2))
      fun _ => throw (.syntax kind) := by
  obtain ⟨build, hruns⟩ := sortFrames_runs hA frames hvalid hs []
  exact (RunsS.append (middle := fun handled =>
    ({ mode := .start, levels := build handled } : SortState _)) hruns
      fun handled => hfail (build handled)).congr (by simp [bind_pure_comp]) rfl

/-- Before a sort, on any stack, a token that neither starts a sort nor ends an application. -/
theorem sortLevels_fails_argument {version : Token.Version} {token : Parser.Internal.Input}
    (hsymbol : ∀ symbol, token ≠ .symbol symbol) (hopen : token ≠ .parenOpen)
    (hclose : token ≠ .parenClose) (levels : List (SortLevel (Traits.Handler.«Sort» H))) :
    RunsS noPoints (sortStep (H := H) version) { mode := .start, levels } [token]
      (pure () : PM H Unit) fun _ => throw (.syntax .expectedSort) :=
  (RunsS.token (program := (pure () : PM H Unit)) (by
    cases token <;> first | exact absurd rfl (hsymbol _) | exact absurd rfl hopen |
      exact absurd rfl hclose | simp [sortStep.eq_def, Parser.Internal.syntaxError])
    (handlerOnly_pure ())).congr (by simp [tick_noPoints]) rfl

/-- Before a sort, on any stack, `(` and a token that starts no head. -/
theorem sortLevels_fails_inner {version : Token.Version} {token : Parser.Internal.Input}
    (hsymbol : ∀ symbol, token ≠ .symbol symbol) (hopen : token ≠ .parenOpen)
    (hunderscore : token ≠ .reserved (.general .underscore))
    (levels : List (SortLevel (Traits.Handler.«Sort» H))) :
    RunsS noPoints (sortStep (H := H) version) { mode := .start, levels } [.parenOpen, token]
      (pure () : PM H Unit) fun _ => throw (.syntax .expectedSortInner) := by
  have hu : token.isWord .underscore = false := by
    cases token with
    | reserved word =>
      cases word with
      | general w => cases w <;> first | exact absurd rfl hunderscore | rfl
      | _ => rfl
    | _ => rfl
  refine (RunsS.append (middle := fun _ => ({ mode := .opened, levels } : SortState _))
    (RunsS.token_more (by simp [sortStep.eq_def])) fun _ =>
      RunsS.token (program := (pure () : PM H Unit)) (by
        cases token <;> first | exact absurd rfl (hsymbol _) | exact absurd rfl hopen |
          simp_all [sortStep.eq_def, Parser.Internal.syntaxError])
        (handlerOnly_pure ())).congr ?_ rfl
  simp [tick_noPoints]

/-- Before a sort, on any stack, `(`, a symbol and `)`. -/
theorem sortLevels_fails_empty {version : Token.Version} (symbol : Nodes.Symbol)
    (levels : List (SortLevel (Traits.Handler.«Sort» H))) :
    RunsS noPoints (sortStep (H := H) version) { mode := .start, levels }
      [.parenOpen, .symbol symbol, .parenClose] (pure () : PM H Unit)
      fun _ => throw (.syntax .emptySortApplication) := by
  refine (RunsS.append (middle := fun _ => ({ mode := .opened, levels } : SortState _))
    (RunsS.token_more (by simp [sortStep.eq_def])) fun _ =>
      RunsS.append (middle := fun _ =>
        ({ mode := .start, levels := ⟨⟨symbol, #[]⟩, #[]⟩ :: levels } : SortState _))
        (RunsS.token_more (by simp [sortStep.eq_def])) fun _ =>
        RunsS.token (program := (pure () : PM H Unit)) (by
          simp [sortStep.eq_def, Parser.Internal.syntaxError]) (handlerOnly_pure ())).congr ?_ rfl
  simp [tick_noPoints]

/-- The sorted variable parser on `(`, a symbol, the tokens of open sort applications and a
token that neither starts another argument nor ends an application: it rejects that token with
`expectedSort`, having made the traversal's calls for the applications' argument sorts. -/
theorem sortedVar_rejects_sortDeepArgument {version : Token.Version}
    {h : Handler (StateT H m) (Traits.Handler.Error H) (valuesOf H)} (hA : TermAgrees h)
    (symbol : Nodes.Symbol) {frames : List (Tree.Identifier × List Tree.«Sort»)}
    (hvalid : ∀ frame ∈ frames, frame.1.Valid (Bridge.version version) ∧
      Tree.«Sort».ValidAll (Bridge.version version) frame.2)
    {tokens : List Parser.Internal.Input} (hs : Stands tokens (frameTokens frames))
    {token : Parser.Internal.Input} (hsymbol : ∀ symbol, token ≠ .symbol symbol)
    (hopen : token ≠ .parenOpen) (hclose : token ≠ .parenClose) :
    Rejects version (SortedVarParser.new (H := H))
      (.parenOpen :: .symbol symbol :: (tokens ++ [token]))
      ((fun _ => ()) <$> adaptRun (frames.mapM fun frame => Traversal.sorts noPoints h frame.2))
      .expectedSort := by
  have := sortedVar_rejects_sort_inner (H := H) (m := m) symbol
    (sortFrames_fails hA hvalid hs (sortLevels_fails_argument hsymbol hopen hclose))
  simpa [Functor.map_map] using this

/-- The sorted variable parser on `(`, a symbol, the tokens of open sort applications, `(` and
a token that starts no head: it rejects that token with `expectedSortInner`, having made the
traversal's calls for the applications' argument sorts. -/
theorem sortedVar_rejects_sortDeepInner {version : Token.Version}
    {h : Handler (StateT H m) (Traits.Handler.Error H) (valuesOf H)} (hA : TermAgrees h)
    (symbol : Nodes.Symbol) {frames : List (Tree.Identifier × List Tree.«Sort»)}
    (hvalid : ∀ frame ∈ frames, frame.1.Valid (Bridge.version version) ∧
      Tree.«Sort».ValidAll (Bridge.version version) frame.2)
    {tokens : List Parser.Internal.Input} (hs : Stands tokens (frameTokens frames))
    {token : Parser.Internal.Input} (hsymbol : ∀ symbol, token ≠ .symbol symbol)
    (hopen : token ≠ .parenOpen) (hunderscore : token ≠ .reserved (.general .underscore)) :
    Rejects version (SortedVarParser.new (H := H))
      (.parenOpen :: .symbol symbol :: (tokens ++ [.parenOpen, token]))
      ((fun _ => ()) <$> adaptRun (frames.mapM fun frame => Traversal.sorts noPoints h frame.2))
      .expectedSortInner := by
  have := sortedVar_rejects_sort_inner (H := H) (m := m) symbol
    (sortFrames_fails hA hvalid hs (sortLevels_fails_inner hsymbol hopen hunderscore))
  simpa [Functor.map_map] using this

/-- The sorted variable parser on `(`, a symbol, the tokens of open sort applications, and `(`,
a symbol and `)`: it rejects the `)` with `emptySortApplication`, having made the traversal's
calls for the applications' argument sorts. -/
theorem sortedVar_rejects_sortDeepEmpty {version : Token.Version}
    {h : Handler (StateT H m) (Traits.Handler.Error H) (valuesOf H)} (hA : TermAgrees h)
    (symbol : Nodes.Symbol) {frames : List (Tree.Identifier × List Tree.«Sort»)}
    (hvalid : ∀ frame ∈ frames, frame.1.Valid (Bridge.version version) ∧
      Tree.«Sort».ValidAll (Bridge.version version) frame.2)
    {tokens : List Parser.Internal.Input} (hs : Stands tokens (frameTokens frames))
    (head : Nodes.Symbol) :
    Rejects version (SortedVarParser.new (H := H))
      (.parenOpen :: .symbol symbol :: (tokens ++ [.parenOpen, .symbol head, .parenClose]))
      ((fun _ => ()) <$> adaptRun (frames.mapM fun frame => Traversal.sorts noPoints h frame.2))
      .emptySortApplication := by
  have := sortedVar_rejects_sort_inner (H := H) (m := m) symbol
    (sortFrames_fails hA hvalid hs (sortLevels_fails_empty head))
  simpa [Functor.map_map] using this

end

end BSmtLib.Facts.Proofs.Parser.Category.SortedVar
