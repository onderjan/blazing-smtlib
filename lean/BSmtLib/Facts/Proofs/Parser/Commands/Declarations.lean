module

public import BSmtLib.Facts.Proofs.Parser.Commands.Literals
import all BSmtLib.Parser.Category.Combinator
import all BSmtLib.Parser.Command.Internal.Standard
import all BSmtLib.Parser.Category.Token

@[expose] public section

/-!
# Datatype commands against the traversal

`declare-datatype` runs the datatype parser with the start of its symbol; `declare-datatypes`
reads its sort declarations, makes its start, then reads as many datatype declarations as it
declared sorts, each ended by its own end, which the parser of an element of the list makes.
-/

namespace BSmtLib.Facts.Proofs.Parser.Commands.Declarations

open BSmtLibSpec.Grammar
open BSmtLib.Parser.Internal (PM)
open BSmtLib.Parser.Command.Internal.Standard (Payload FinalCall payloadStep finalCall)
open BSmtLib.Parser.Command (CommandOutcome)
open BSmtLib.Parser.Category.Combinator.Internal (ListState)
open BSmtLib.Parser.Command.Internal.Datatype (DatatypeState datatypeStep SortDecState)
open BSmtLib.Facts.Parser.Adapters.Bridge BSmtLib.Facts.Parser.Adapters.Run
open BSmtLib.Facts.Proofs.Parser.Commands.Datatypes BSmtLib.Facts.Proofs.Parser.Commands.Elements
open BSmtLib.Facts.Proofs.Parser.Commands.Elements.Runs BSmtLib.Facts.Proofs.Parser.Commands.Frame
open BSmtLib.Facts.Proofs.Parser.Commands.Simple BSmtLib.Facts.Proofs.Parser.Commands.Terms
open BSmtLib.Facts.Proofs.Parser.Drive BSmtLib.Facts.Proofs.Parser.Lemmas
open BSmtLib.Facts.Proofs.Parser.List BSmtLib.Facts.Proofs.Parser.Tokens

open BSmtLibSpec.Parser
open BSmtLibSpec.Parser.Traversal
open BSmtLibSpec.Facts.Proofs.Parser (Program.callUnit)

section

variable {H : Type} {m : Type → Type} [Monad m] [LawfulMonad m] [Traits.CommandHandler H m]
variable {points : Points (StateT H m)} {version : Token.Version}
variable {h : Traversal.Handler (StateT H m) (Traits.Handler.Error H) (valuesOf H)}

/-- The sort of the handler. -/
local notation "S" => Traits.Handler.«Sort» H

theorem adaptRun_forM {X : Type} (f : X → Run (StateT H m) (Traits.Handler.Error H) Unit)
    (items : List X) : adaptRun (items.forM f) = items.forM fun item => adaptRun (f item) := by
  induction items with
  | nil => simp [List.forM]
  | cons item items ih =>
    simp only [List.forM, adaptRun_bind]
    congr 1
    funext _
    exact ih

theorem mapM_bind_eq_forM {X β : Type} (f : X → PM H Unit) (items : List X) (k : PM H β) :
    (items.mapM f >>= fun _ => k) = (items.forM f >>= fun _ => k) := by
  induction items with
  | nil => simp
  | cons item items ih =>
    simp only [List.mapM_cons, List.forM, bind_assoc, pure_bind]
    congr 1
    funext _
    exact ih

variable (hA : Agrees h)
include hA

theorem declareDatatype_payload (name : Tree.Symbol) (declaration : Tree.DatatypeDec)
    (hvalid : declaration.Valid (Bridge.version version)) {payload : List Parser.Internal.Input}
    (hs : Stands payload (.symbol name :: declaration.tokens)) :
    PayloadRuns points version (Payload.init .declareDatatype version)
      (payload ++ [.parenClose])
      (adaptRun (do
        take points (.symbol name)
        let handled ← Traversal.datatype points h
          (fun parameters => Program.callUnit h (.startDeclareDatatype name parameters))
          declaration
        take points .parenClose
        Program.callUnit h (.endDeclareDatatype handled)))
      fun _ => pure (.done .command) := by
  obtain ⟨symbolToken, datatypeTokens, rfl, hsymbolToken, hdatatype⟩ := Stands.split_cons hs
  obtain ⟨symbol, rfl, rfl⟩ := Parser.Internal.Input.received_symbol hsymbolToken
  obtain ⟨-, program, hprogram, hruns⟩ := datatype_runs (points := points) (version := version)
    (fun parameters => Parser.Internal.call (Traits.CommandHandler.startDeclareDatatype (H := H) symbol
      (Multiple.Symbols.Internal.new parameters)))
    (start' := fun parameters =>
      Program.callUnit h (.startDeclareDatatype (Bridge.symbol symbol) parameters))
    hA.toTermAgrees (fun parameters => by simp [hA.startDeclareDatatype]) declaration hvalid
    hdatatype
  refine (Runs.append (first := [.symbol symbol])
    (middle := fun _ => .declareDatatype symbol .start)
    (Runs.token_moreA (arrival := Parser.Command.Internal.Standard.payloadArrive)
    (by simp [payloadStep, Payload.init, Parser.Category.Token.Internal.expectSymbol])) fun _ =>
    part_then_close (h := h) (wrap := Payload.declareDatatype symbol)
      (final := fun constructors => .endDeclareDatatype constructors)
      (request := fun constructors =>
        .endDeclareDatatype (constructors.toList.map Bridge.constructor))
      (by payload_step) hruns
      (fun _ => by simp [finalCall, hA.endDeclareDatatype]) (fun _ => rfl)).congr ?_ rfl
  simp [adaptRun_take hsymbolToken, ← hprogram]

omit hA in
/-- The parser of a datatype declaration in `declare-datatypes`, which ends it with its end. -/
abbrev datatypeElementStep (version : Token.Version) :
    DatatypeState S → Parser.Internal.Input → PM H (Parser.Internal.Step (DatatypeState S) Unit) :=
  let start parameters := Parser.Internal.call
    (Traits.CommandHandler.startDatatypeDeclaration (H := H)
      (Multiple.Symbols.Internal.new parameters))
  fun state token => do
    match ← datatypeStep start version state token with
    | .more state => return Parser.Internal.Step.more state
    | .done constructors =>
      Parser.Internal.call (Traits.CommandHandler.endDatatypeDeclaration
        (Multiple.Constructors.Internal.new constructors))
      return .done ()

/-- The datatype element parser reads a datatype declaration, then makes its end. -/
theorem datatypeElement_element :
    ElementRuns points (datatypeElementStep version) .start Tree.DatatypeDec.tokens
      (Tree.DatatypeDec.Valid (Bridge.version version))
      (fun declaration => adaptRun (do
        let handled ← Traversal.datatype points h
          (fun parameters => Program.callUnit h (.startDatatypeDeclaration parameters))
          declaration
        Program.callUnit h (.endDatatypeDeclaration handled)))
      id := by
  intro declaration hvalid tokens hs
  obtain ⟨⟨rest, rfl⟩, program, hprogram, hruns⟩ := datatype_runs (points := points)
    (version := version)
    (fun parameters => Parser.Internal.call (Traits.CommandHandler.startDatatypeDeclaration (H := H)
      (Multiple.Symbols.Internal.new parameters)))
    (start' := fun parameters => Program.callUnit h (.startDatatypeDeclaration parameters))
    hA.toTermAgrees (fun parameters => by simp [hA.startDatatypeDeclaration]) declaration
    hvalid hs
  refine ⟨⟨_, _, rfl, by simp⟩, program >>= fun constructors =>
    Parser.Internal.call (Traits.CommandHandler.endDatatypeDeclaration
      (Multiple.Constructors.Internal.new constructors)), ?_, ?_⟩
  · simp [← hprogram, hA.endDatatypeDeclaration]
  · refine Runs.bind_next ((Runs.embed (outer := datatypeElementStep version) id
      (fun constructors => Parser.Internal.call (Traits.CommandHandler.endDatatypeDeclaration
        (Multiple.Constructors.Internal.new constructors)) >>= fun _ => pure (.done ()))
      (fun state token => by
        simp only [datatypeElementStep]
        congr 1
        funext step
        cases step <;> rfl) hruns).congr rfl (by funext; simp [Parser.Internal.Step.wrap]))

theorem declareDatatypes_payload (sortDecs : List Tree.SortDec)
    (declarations : List Tree.DatatypeDec) (hne : sortDecs ≠ [])
    (hlength : sortDecs.length = declarations.length)
    (hvalid : ∀ declaration ∈ declarations, declaration.Valid (Bridge.version version))
    {payload : List Parser.Internal.Input}
    (hs : Stands payload (paren (sortDecs.flatMap Tree.SortDec.tokens) ++
      paren (declarations.flatMap Tree.DatatypeDec.tokens))) :
    PayloadRuns points version (Payload.init .declareDatatypes version)
      (payload ++ [.parenClose])
      (adaptRun (do
        take points .parenOpen
        takeAll points (sortDecs.flatMap Tree.SortDec.tokens)
        take points .parenClose
        Program.callUnit h
          (.startDeclareDatatypes (sortDecs.map fun sortDec => (sortDec.symbol, sortDec.arity)))
        take points .parenOpen
        declarations.forM fun declaration => do
          let handled ← Traversal.datatype points h
            (fun parameters => Program.callUnit h (.startDatatypeDeclaration parameters))
            declaration
          Program.callUnit h (.endDatatypeDeclaration handled)
        takeAll points [.parenClose, .parenClose]
        Program.callUnit h .endDeclareDatatypes))
      fun _ => pure (.done .command) := by
  obtain ⟨sortList, datatypeList, rfl, hsortList, hdatatypeList⟩ := Stands.split hs
  obtain ⟨sortInner, rfl, hsortInner⟩ := Stands.split_paren hsortList
  obtain ⟨datatypeInner, rfl, hdatatypeInner⟩ := Stands.split_paren hdatatypeList
  obtain ⟨views, hviews, hviewsLength, hviewsRuns⟩ := sortDecs_runs (H := H) (points := points)
    sortDecs hsortInner
  obtain ⟨view, views, rfl⟩ : ∃ view rest, views = view :: rest := by
    cases views with
    | nil => exact absurd (List.length_eq_zero_iff.mp hviewsLength.symm) hne
    | cons view rest => exact ⟨view, rest, rfl⟩
  let count := sortDecs.length
  have hsortsRuns : Runs points (ListState.step .start SortDecState.step none)
      (ListState.paren .start) (.parenOpen :: (sortInner ++ [.parenClose]))
      (ticks points (.parenOpen :: (sortInner ++ [.parenClose])))
      fun _ => pure (.done (#[] ++ (view :: views).toArray)) := by
    refine (Runs.append (first := [.parenOpen]) ListState.open_runs fun _ =>
      Runs.append (hviewsRuns #[]) fun _ =>
        Runs.token (program := pure ())
          (next := fun _ => pure (.done (#[] ++ (view :: views).toArray)))
          (by simp [ListState.step, ListState.between])).congr ?_ rfl
    simp [ticks_append]
  have hsortsPayload := Runs.bind_next
    (following := fun _ => Parser.Internal.call (Traits.CommandHandler.startDeclareDatatypes (H := H)
      (Multiple.SortArities.Internal.new (#[] ++ (view :: views).toArray))))
    (next := fun _ => pure (.more (Payload.declareDatatypesDatatypes count
      (ListState.paren .start))))
    ((Runs.embedA (outer := payloadStep version)
        (outerArrival :=
            Parser.Command.Internal.Standard.payloadArrive) Payload.declareDatatypesSorts
      (fun sorts => do
        if sorts.isEmpty then Parser.Internal.syntaxError (.empty .datatypeIntroductions)
        Parser.Internal.call (Traits.CommandHandler.startDeclareDatatypes (H := H)
          (Multiple.SortArities.Internal.new sorts))
        return .more (.declareDatatypesDatatypes sorts.size (ListState.paren .start)))
      (by payload_step) hsortsRuns).congr rfl
      (by funext; simp [Parser.Internal.Step.wrap, count, ← hviewsLength]))
  obtain ⟨found, hfound, hfoundLength, hfoundRuns⟩ := parenList_runs (maximum := some count)
    (datatypeElement_element (points := points) (version := version) hA) declarations hvalid
    hdatatypeInner (by intro limit hlimit; cases hlimit; simp [count, hlength])
  have hdatatypesPayload := Runs.congr_length (Runs.embedA (outer := payloadStep version)
      (outerArrival := Parser.Command.Internal.Standard.payloadArrive)
    (Payload.declareDatatypesDatatypes count)
    (fun datatypes => do
      if (datatypes.size != count) = true then (do
        Parser.Internal.syntaxError (.missing .datatype)
        pure (.more (.closing .endDeclareDatatypes)))
      else
        pure (.more (.closing .endDeclareDatatypes)))
    (by
      intro state token
      simp only [payloadStep]
      congr 1
      funext step
      cases step <;> simp [Parser.Internal.Step.wrap]) hfoundRuns)
      (HasLength.after (HasLength.bind_pure hfoundLength _) _)
      (next' := fun _ => pure (.more (.closing .endDeclareDatatypes)))
      (fun l hl => by simp [Parser.Internal.Step.wrap, hl, count, hlength])
  rw [show Parser.Internal.Input.parenOpen :: (sortInner ++ [.parenClose]) ++
      Parser.Internal.Input.parenOpen :: (datatypeInner ++ [.parenClose]) ++ [.parenClose] =
    (Parser.Internal.Input.parenOpen :: (sortInner ++ [.parenClose])) ++
      ((Parser.Internal.Input.parenOpen ::
          (datatypeInner ++ [.parenClose])) ++ [.parenClose]) by simp]
  refine (Runs.append (middle := fun _ => .declareDatatypesDatatypes count
      (ListState.paren .start)) hsortsPayload fun _ =>
    Runs.append (middle := fun _ => .closing .endDeclareDatatypes) hdatatypesPayload fun _ =>
      closing_runs (h := h) (request := .endDeclareDatatypes) .endDeclareDatatypes
        (by simp [finalCall, hA.endDeclareDatatypes]) rfl).congr ?_ rfl
  simp only [List.map_id_fun, id_map] at hfound
  simp only [adaptRun_bind]
  rw [adaptRun_takeAll hsortInner, adaptRun_forM]
  simp only [← hviews, hfound]
  simp [takeAll, mapM_bind_eq_forM, ticks_append, hA.startDeclareDatatypes,
    adaptRun_take (token := .parenOpen) rfl, adaptRun_take (token := .parenClose) rfl]

end

end BSmtLib.Facts.Proofs.Parser.Commands.Declarations
