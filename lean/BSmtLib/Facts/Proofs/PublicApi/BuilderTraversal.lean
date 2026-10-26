module

public import BSmtLib.Facts.Proofs.PublicApi.Builder
public import BSmtLibSpec.Facts.Proofs.Parser.Equations

@[expose] public section

/-!
# The traversal with the builder

The traversal, as the specification formalism (`BSmtLibSpec`) defines it, with the builder
(`specBuilder`) and with token points and a producer that do nothing:
- returns the tree itself and leaves the state as it is, for sorts, s-expressions, attributes and
  terms;
- adds a valid command to the commands built so far;
- from a state with any version and no commands, builds the commands of a valid script, newest
  first (`script_builds`).
-/

namespace BSmtLib.Facts.Proofs.PublicApi.BuilderTraversal

open BSmtLibSpec BSmtLibSpec.Grammar BSmtLibSpec.Lexicon
open BSmtLibSpec.Parser
open BSmtLibSpec.Parser.Traversal (Run take takeAll receive takeAllArriving)
open BSmtLibSpec.Facts.Proofs.Parser.Equations
open BSmtLib.Facts.Proofs.PublicApi.Builder
open BSmtLib.Facts.Proofs.Reader.Handler.Drive (nullPoints nullProducer)

/-- The token points of the builder's traversal, which do nothing. -/
abbrev P : Traversal.Points (StateT State Id) := nullPoints

/-- The run from the state ends in the state with the result. -/
def Yields {α : Type} (x : Run (StateT State Id) Unit α) (s : State) (a : α) (s' : State) :
    Prop :=
  x.run.run s = (.ok a, s')

theorem yields_bind {α β : Type} {x : Run (StateT State Id) Unit α}
    {f : α → Run (StateT State Id) Unit β} {s s' s'' : State} {a : α} {b : β}
    (hx : Yields x s a s') (hf : Yields (f a) s' b s'') : Yields (x >>= f) s b s'' := by
  simp only [Yields, ExceptT.run_bind, StateT.run_bind] at hx hf ⊢
  rw [hx]
  exact hf

theorem yields_pure {α : Type} (a : α) (s : State) :
    Yields (pure a : Run (StateT State Id) Unit α) s a s := rfl

theorem yields_take (token : Grammar.SyntaxToken) (s : State) : Yields (take P token) s () s := rfl

theorem yields_takeAll (tokens : List Grammar.SyntaxToken) (s : State) :
    Yields (takeAll P tokens) s () s := by
  induction tokens with
  | nil => rfl
  | cons token tokens ih =>
    simp only [takeAll] at ih ⊢
    exact yields_bind (yields_take token s) ih

theorem yields_receive (item : Traversal.Received) {atArrival : Run (StateT State Id) Unit Unit}
    {s s' : State} (h : Yields atArrival s () s') : Yields (receive P item atArrival) s () s' := by
  unfold receive
  exact yields_bind (yields_pure () s) (yields_bind h (yields_pure () s'))

theorem yields_takeAllArriving {atArrival : Run (StateT State Id) Unit Unit} {s : State}
    (h : Yields atArrival s () s) (tokens : List Grammar.SyntaxToken) :
    Yields (takeAllArriving P atArrival tokens) s () s := by
  cases tokens with
  | nil => rfl
  | cons first rest =>
    exact yields_bind (yields_receive _ h) (yields_takeAll rest s)

theorem yields_call {returns : Traversal.Returns} (request : Traversal.Call treeValues returns)
    {s s' : State} {a : treeValues.of returns} (h : (answer request).run s = (a, s')) :
    Yields (Traversal.call specBuilder request) s a s' := by
  show ((ExceptT.adapt Traversal.Cause.handler (ExceptT.lift (answer request) :
    ExceptT Unit (StateT State Id) _)).run.run s) = _
  simp only [ExceptT.adapt, ExceptT.run_mk, StateT.run_map]
  show (fun p => (Except.mapError Traversal.Cause.handler p.fst, p.snd)) <$>
    ((Except.ok <$> answer request).run s) = _
  rw [StateT.run_map, h]
  rfl

/-! ## Sorts, s-expressions and attributes -/

/-- The builder as the formalism's handler. -/
abbrev B : Traversal.Handler (StateT State Id) Unit treeValues := specBuilder

theorem sort_yields : ∀ n (t : Tree.Sort) (s : State), sizeOf t < n →
    Yields (Traversal.sort P B t) s t s
  | 0, _, _, h => absurd h (Nat.not_lt_zero _)
  | n + 1, ⟨identifier, arguments⟩, s, h => by
    simp only [Tree.«Sort».mk.sizeOf_spec] at h
    cases arguments with
    | nil =>
      rw [sort_nil]
      exact yields_bind (yields_takeAll _ s) (yields_call _ rfl)
    | cons first others =>
      have hargs : ∀ (list : List Tree.Sort) (s : State), sizeOf list < n →
          Yields (Traversal.sorts P B list) s list s := by
        intro list
        induction list with
        | nil => intro s _; rfl
        | cons a list ih =>
          intro s hl
          simp only [List.cons.sizeOf_spec] at hl
          simp only [Traversal.sorts]
          exact yields_bind (sort_yields n a s (by omega))
            (yields_bind (ih s (by omega)) (yields_pure _ _))
      rw [sort_cons]
      exact yields_bind (yields_take _ s) (yields_bind (yields_takeAll _ s)
        (yields_bind (hargs (first :: others) s (by omega)) (yields_bind (yields_take _ s)
          (yields_call _ rfl))))

theorem sort_yields' (t : Tree.Sort) (s : State) : Yields (Traversal.sort P B t) s t s :=
  sort_yields _ t s (Nat.lt_succ_self _)

theorem sorts_yields (list : List Tree.Sort) (s : State) :
    Yields (Traversal.sorts P B list) s list s := by
  induction list with
  | nil => rfl
  | cons a list ih =>
    simp only [Traversal.sorts]
    exact yields_bind (sort_yields _ a s (Nat.lt_succ_self _)) (yields_bind ih (yields_pure _ _))

theorem sExpr_yields : ∀ n (t : Tree.SExpr) (s : State), sizeOf t < n →
    Yields (Traversal.sExpr P B t) s t s
  | 0, _, _, h => absurd h (Nat.not_lt_zero _)
  | n + 1, t, s, h => by
    cases t with
    | constant c => rw [sExpr_constant]; exact yields_bind (yields_take _ s) (yields_call _ rfl)
    | symbol c => rw [sExpr_symbol]; exact yields_bind (yields_take _ s) (yields_call _ rfl)
    | reserved c => rw [sExpr_reserved]; exact yields_bind (yields_take _ s) (yields_call _ rfl)
    | keyword c => rw [sExpr_keyword]; exact yields_bind (yields_take _ s) (yields_call _ rfl)
    | list items =>
      simp only [Tree.SExpr.list.sizeOf_spec] at h
      have hitems : ∀ (list : List Tree.SExpr) (s : State), sizeOf list < n →
          Yields (Traversal.sExprs P B list) s list s := by
        intro list
        induction list with
        | nil => intro s _; rfl
        | cons a list ih =>
          intro s hl
          simp only [List.cons.sizeOf_spec] at hl
          simp only [Traversal.sExprs]
          exact yields_bind (sExpr_yields n a s (by omega))
            (yields_bind (ih s (by omega)) (yields_pure _ _))
      rw [sExpr_list]
      exact yields_bind (yields_take _ s) (yields_bind (hitems items s (by omega))
        (yields_bind (yields_take _ s) (yields_call _ rfl)))

theorem sExprs_yields (list : List Tree.SExpr) (s : State) :
    Yields (Traversal.sExprs P B list) s list s := by
  induction list with
  | nil => rfl
  | cons a list ih =>
    simp only [Traversal.sExprs]
    exact yields_bind (sExpr_yields _ a s (Nat.lt_succ_self _)) (yields_bind ih (yields_pure _ _))

theorem attributeValue_yields (value : Tree.AttributeValue) (s : State) :
    ∃ node, Yields (Traversal.attributeValue P B value) s node s ∧ valueOf node = value := by
  cases value with
  | constant c => exact ⟨_, yields_bind (yields_take _ s) (yields_pure _ _), rfl⟩
  | symbol c => exact ⟨_, yields_bind (yields_take _ s) (yields_pure _ _), rfl⟩
  | list items =>
    exact ⟨_, yields_bind (yields_take _ s) (yields_bind (sExprs_yields items s)
      (yields_bind (yields_take _ s) (yields_pure _ _))), rfl⟩

theorem attributeThen_yields (keyword : Regex.Chars) (following : Grammar.SyntaxToken)
    (value : Option Tree.AttributeValue) (s : State) :
    Yields (Traversal.attributeThen P B keyword following value) s ⟨keyword, value⟩ s := by
  cases value with
  | none =>
    rw [attributeThen_none]
    exact yields_bind (yields_take _ s) (yields_call _ rfl)
  | some value =>
    rw [attributeThen_some]
    obtain ⟨node, hn, hv⟩ := attributeValue_yields value s
    refine yields_bind hn (yields_bind (yields_call _ rfl) (yields_bind (yields_take _ s) ?_))
    rw [show (⟨keyword, (some node).map valueOf⟩ : Tree.Attribute) = ⟨keyword, some value⟩ by
      simp [hv]]
    exact yields_pure _ _

theorem attributesThen_yields : ∀ (keyword : Regex.Chars) (value : Option Tree.AttributeValue)
    (rest : List Tree.Attribute) (s : State),
    Yields (Traversal.attributesThen P B keyword value rest) s (⟨keyword, value⟩ :: rest) s
  | keyword, value, [], s => by
    simp only [Traversal.attributesThen]
    exact yields_bind (attributeThen_yields _ _ _ s) (yields_pure _ _)
  | keyword, value, ⟨nextKeyword, nextValue⟩ :: rest, s => by
    simp only [Traversal.attributesThen]
    exact yields_bind (attributeThen_yields _ _ _ s)
      (yields_bind (attributesThen_yields nextKeyword nextValue rest s) (yields_pure _ _))

/-! ## Terms -/

theorem qualIdentifier_yields (q : Tree.QualIdentifier)
    {atArrival : Run (StateT State Id) Unit Unit}
    {s : State} (ha : Yields atArrival s () s) :
    ∃ name so, Yields (Traversal.qualIdentifier P B q atArrival) s (name, so) s ∧
      qualified name so = q := by
  cases q with
  | plain identifier =>
    exact ⟨_, _, yields_bind (yields_takeAllArriving ha _) (yields_pure _ _), rfl⟩
  | as identifier qualification =>
    exact ⟨_, _, yields_bind (yields_takeAllArriving ha _) (yields_bind (yields_takeAll _ s)
      (yields_bind (sort_yields _ qualification s (Nat.lt_succ_self _))
        (yields_bind (yields_take _ s) (yields_pure _ _)))), rfl⟩

theorem sortedVars_yields : ∀ (vs : List Tree.SortedVar) (s : State),
    ∃ pairs, Yields (Traversal.sortedVars P B vs) s pairs s ∧ sortedVarsOf pairs = vs
  | [], s => ⟨[], rfl, rfl⟩
  | ⟨symbol, sort⟩ :: rest, s => by
    obtain ⟨pairs, hp, he⟩ := sortedVars_yields rest s
    refine ⟨(symbol, sort) :: pairs, ?_, by simp [sortedVarsOf] at he ⊢; exact he⟩
    simp only [Traversal.sortedVars]
    exact yields_bind (yields_takeAll _ s) (yields_bind (sort_yields _ sort s (Nat.lt_succ_self _))
      (yields_bind (yields_take _ s) (yields_bind hp (yields_pure _ _))))

/-- What `term_yields` proves for terms smaller than `n`. -/
def TermsYield (n : Nat) : Prop :=
  ∀ (t : Tree.Term) (atArrival : Run (StateT State Id) Unit Unit) (s : State), sizeOf t < n →
    Yields atArrival s () s → Yields (Traversal.term P B t atArrival) s t s

theorem terms_yields {n : Nat} (ih : TermsYield n) :
    ∀ (list : List Tree.Term) (s : State), sizeOf list < n →
      Yields (Traversal.terms P B list) s list s
  | [], _, _ => rfl
  | t :: list, s, h => by
    simp only [List.cons.sizeOf_spec] at h
    simp only [Traversal.terms]
    exact yields_bind (ih t _ s (by omega) (yields_pure () s))
      (yields_bind (terms_yields ih list s (by omega)) (yields_pure _ _))

theorem bindings_yields {n : Nat} (ih : TermsYield n) :
    ∀ (list : List (Tree.Symbol × Tree.Term)) (s : State), sizeOf list < n →
      Yields (Traversal.bindings P B list) s list s
  | [], _, _ => rfl
  | (symbol, t) :: list, s, h => by
    simp only [List.cons.sizeOf_spec, Prod.mk.sizeOf_spec] at h
    simp only [Traversal.bindings]
    exact yields_bind (yields_takeAll _ s) (yields_bind (ih t _ s (by omega) (yields_pure () s))
      (yields_bind (yields_take _ s) (yields_bind (bindings_yields ih list s (by omega))
        (yields_pure _ _))))

theorem cases_yields {n : Nat} (ih : TermsYield n) (scrutinee : Tree.Term) :
    ∀ (list : List (Tree.Pattern × Tree.Term)) (s : State), sizeOf list < n →
      Yields (Traversal.cases P B scrutinee list) s list s
  | [], _, _ => rfl
  | (pattern, body) :: list, s, h => by
    simp only [List.cons.sizeOf_spec, Prod.mk.sizeOf_spec] at h
    rw [cases_cons]
    exact yields_bind (yields_take _ s) (yields_bind (yields_takeAll _ s)
      (yields_bind (yields_call _ rfl) (yields_bind (ih body _ s (by omega) (yields_pure () s))
        (yields_bind (yields_take _ s) (yields_bind (yields_call _ rfl)
          (yields_bind (cases_yields ih scrutinee list s (by omega)) (yields_pure _ _)))))))

theorem term_yields : ∀ n, TermsYield n
  | 0 => fun _ _ _ h => absurd h (Nat.not_lt_zero _)
  | n + 1 => by
    have ih := term_yields n
    intro t a s h ha
    cases t with
    | constant c =>
      rw [term_constant]
      exact yields_bind (yields_receive _ ha) (yields_call _ rfl)
    | identifier q =>
      rw [term_identifier]
      obtain ⟨name, so, hq, he⟩ := qualIdentifier_yields q ha
      refine yields_bind hq ?_
      rw [← he]
      exact yields_call _ rfl
    | application function arguments =>
      simp only [Tree.Term.application.sizeOf_spec] at h
      rw [term_application]
      obtain ⟨name, so, hq, he⟩ := qualIdentifier_yields function (yields_pure () s)
      refine yields_bind (yields_receive _ ha) (yields_bind hq (yields_bind
        (terms_yields ih arguments s (by omega)) (yields_bind (yields_take _ s) ?_)))
      rw [← he]
      exact yields_call _ rfl
    | «let» bs body =>
      simp only [Tree.Term.let.sizeOf_spec] at h
      rw [term_let]
      exact yields_bind (yields_takeAllArriving ha _) (yields_bind
        (bindings_yields ih bs s (by omega)) (yields_bind (yields_take _ s)
          (yields_bind (yields_call _ rfl) (yields_bind (ih body _ s (by omega) (yields_pure () s))
            (yields_bind (yields_take _ s) (yields_call _ rfl))))))
    | lambda vs body =>
      simp only [Tree.Term.lambda.sizeOf_spec] at h
      rw [term_lambda]
      obtain ⟨pairs, hp, he⟩ := sortedVars_yields vs s
      refine yields_bind (yields_takeAllArriving ha _) (yields_bind hp (yields_bind
        (yields_take _ s) (yields_bind (yields_call _ rfl)
          (yields_bind (ih body _ s (by omega) (yields_pure () s))
            (yields_bind (yields_take _ s) ?_)))))
      rw [← he]
      exact yields_call _ rfl
    | quantified q vs body =>
      simp only [Tree.Term.quantified.sizeOf_spec] at h
      rw [term_quantified]
      obtain ⟨pairs, hp, he⟩ := sortedVars_yields vs s
      refine yields_bind (yields_takeAllArriving ha _) (yields_bind hp (yields_bind
        (yields_take _ s) (yields_bind (yields_call _ rfl)
          (yields_bind (ih body _ s (by omega) (yields_pure () s))
            (yields_bind (yields_take _ s) ?_)))))
      rw [← he]
      exact yields_call _ rfl
    | «match» scrutinee cs =>
      simp only [Tree.Term.match.sizeOf_spec] at h
      rw [term_match]
      exact yields_bind (yields_takeAllArriving ha _) (yields_bind
        (ih scrutinee _ s (by omega) (yields_pure () s)) (yields_bind (yields_call _ rfl)
          (yields_bind (yields_take _ s) (yields_bind (cases_yields ih scrutinee cs s (by omega))
            (yields_bind (yields_takeAll _ s) (yields_call _ rfl))))))
    | annotated t attrs =>
      simp only [Tree.Term.annotated.sizeOf_spec] at h
      rw [term_annotated]
      refine yields_bind (yields_takeAllArriving ha _) (yields_bind
        (ih t _ s (by omega) (yields_pure () s)) ?_)
      cases attrs with
      | nil =>
        exact yields_bind (yields_take _ s) (yields_bind (yields_pure _ _) (yields_call _ rfl))
      | cons a rest =>
        obtain ⟨k, v⟩ := a
        exact yields_bind (yields_take _ s) (yields_bind (attributesThen_yields k v rest s)
          (yields_call _ rfl))

theorem term_yields' (t : Tree.Term) (s : State) :
    Yields (Traversal.term P B t) s t s :=
  term_yields _ t _ s (Nat.lt_succ_self _) (yields_pure () s)

theorem terms_yields' (list : List Tree.Term) (s : State) :
    Yields (Traversal.terms P B list) s list s :=
  terms_yields (term_yields _) list s (Nat.lt_succ_self _)

/-! ## The parts of commands -/

theorem yields_opening (name : String) (s : State) :
    Yields (Traversal.opening P name) s () s :=
  yields_bind (yields_take _ s) (yields_take _ s)

theorem signature_yields (symbol : Tree.Symbol) (parameters : List Tree.SortedVar)
    (result : Tree.Sort) (s : State) :
    ∃ sig, Yields (Traversal.signature P B symbol parameters result) s sig s ∧
      declarationOf sig = ⟨symbol, parameters, result⟩ ∧ sig.symbol = symbol ∧
      sortedVarsOf sig.parameters = parameters ∧ sig.result = result := by
  obtain ⟨pairs, hp, he⟩ := sortedVars_yields parameters s
  refine ⟨⟨symbol, pairs, result⟩, ?_, by simp [declarationOf, he], rfl, he, rfl⟩
  exact yields_bind (yields_takeAll _ s) (yields_bind hp (yields_bind (yields_take _ s)
    (yields_bind (sort_yields _ result s (Nat.lt_succ_self _)) (yields_pure _ _))))

theorem selectors_yields : ∀ (list : List Tree.SelectorDec) (s : State),
    ∃ pairs, Yields (Traversal.selectors P B list) s pairs s ∧
      pairs.map (fun (p : Tree.Symbol × Tree.Sort) => (⟨p.1, p.2⟩ : Tree.SelectorDec)) = list
  | [], s => ⟨[], rfl, rfl⟩
  | ⟨symbol, sort⟩ :: rest, s => by
    obtain ⟨pairs, hp, he⟩ := selectors_yields rest s
    refine ⟨(symbol, sort) :: pairs, ?_, by simp [he]⟩
    simp only [Traversal.selectors]
    exact yields_bind (yields_takeAll _ s) (yields_bind (sort_yields _ sort s (Nat.lt_succ_self _))
      (yields_bind (yields_take _ s) (yields_bind hp (yields_pure _ _))))

theorem constructorAfterOpen_yields (c : Tree.ConstructorDec) (s : State) :
    ∃ k, Yields (Traversal.constructorAfterOpen P B c) s k s ∧ constructorOf k = c := by
  obtain ⟨pairs, hp, he⟩ := selectors_yields c.selectors s
  refine ⟨⟨c.symbol, pairs⟩, ?_, ?_⟩
  · exact yields_bind (yields_take _ s) (yields_bind hp (yields_bind (yields_take _ s)
      (yields_pure _ _)))
  · obtain ⟨sym, sel⟩ := c
    simp only [constructorOf] at he ⊢
    rw [show (pairs.map fun (p : Tree.Symbol × Tree.Sort) => (⟨p.1, p.2⟩ : Tree.SelectorDec)) =
      pairs.map (fun x => match x with | (symbol, sort) => ⟨symbol, sort⟩) from rfl] at he
    rw [he]

theorem constructors_yields : ∀ (list : List Tree.ConstructorDec) (s : State),
    ∃ ks, Yields (Traversal.constructors P B list) s ks s ∧ ks.map constructorOf = list
  | [], s => ⟨[], rfl, rfl⟩
  | c :: rest, s => by
    obtain ⟨k, hk, hc⟩ := constructorAfterOpen_yields c s
    obtain ⟨ks, hks, hcs⟩ := constructors_yields rest s
    refine ⟨k :: ks, ?_, by simp [hc, hcs]⟩
    simp only [Traversal.constructors, List.mapM_cons] at hks ⊢
    exact yields_bind (yields_bind (yields_take _ s) hk) (yields_bind hks (yields_pure _ _))

theorem datatype_yields (start : List Tree.Symbol → Run (StateT State Id) Unit Unit)
    (s : State) (g : List Tree.Symbol → State) (hstart : ∀ ps, Yields (start ps) s () (g ps))
    (decl : Tree.DatatypeDec) :
    ∃ ks, Yields (Traversal.datatype P B start decl) s ks (g decl.parameters) ∧
      ks.map constructorOf = decl.constructors := by
  obtain ⟨ps, cs⟩ := decl
  cases ps with
  | nil =>
    cases cs with
    | nil =>
      rw [datatype_empty]
      exact ⟨[], yields_bind (yields_takeAll _ s) (yields_bind (hstart []) (yields_pure _ _)),
        rfl⟩
    | cons first rest =>
      rw [datatype_plain]
      obtain ⟨k, hk, hc⟩ := constructorAfterOpen_yields first (g [])
      obtain ⟨ks, hks, hcs⟩ := constructors_yields rest (g [])
      exact ⟨k :: ks, yields_bind (yields_takeAll _ s) (yields_bind (hstart [])
        (yields_bind hk (yields_bind hks (yields_bind (yields_take _ _) (yields_pure _ _))))),
        by simp [hc, hcs]⟩
  | cons p ps =>
    rw [datatype_par]
    obtain ⟨ks, hks, hcs⟩ := constructors_yields cs (g (p :: ps))
    exact ⟨ks, yields_bind (yields_takeAll _ s) (yields_bind (yields_takeAll _ s)
      (yields_bind (yields_take _ s) (yields_bind (hstart _) (yields_bind (yields_take _ _)
        (yields_bind hks (yields_bind (yields_takeAll _ _) (yields_pure _ _))))))), hcs⟩

theorem yields_callUnit (request : Traversal.Call treeValues .nothing) (s : State) :
    Yields (Facts.Proofs.Parser.Program.callUnit B request) s ()
      (s.1, command s.1 s.2 request) := yields_call request rfl

theorem withConstructors_snoc (cs : List Tree.ConstructorDec) (ps : List Tree.Symbol) :
    ∀ done : List Tree.DatatypeDec,
      withConstructors cs (done ++ [⟨ps, []⟩]) = done ++ [⟨ps, cs⟩]
  | [] => rfl
  | [d] => rfl
  | d :: e :: rest => by
    show d :: withConstructors cs ((e :: rest) ++ [⟨ps, []⟩]) = _
    rw [withConstructors_snoc cs ps (e :: rest)]
    rfl

theorem datatypes_yields (version : Lexicon.Version) (built : List Tree.Command)
    (sorts : List Tree.SortDec) :
    ∀ (decls done : List Tree.DatatypeDec),
      Yields (decls.forM fun declaration => do
          let handled ← Traversal.datatype P B
            (fun parameters => Facts.Proofs.Parser.Program.callUnit B
              (.startDatatypeDeclaration parameters)) declaration
          Facts.Proofs.Parser.Program.callUnit B (.endDatatypeDeclaration handled))
        (version, .declareDatatypes sorts done :: built) ()
        (version, .declareDatatypes sorts (done ++ decls) :: built)
  | [], done => by simp only [List.append_nil, List.forM]; rfl
  | decl :: rest, done => by
    simp only [List.forM]
    obtain ⟨ks, hks, hcs⟩ := datatype_yields (fun parameters =>
      Facts.Proofs.Parser.Program.callUnit B (.startDatatypeDeclaration parameters))
      (version, .declareDatatypes sorts done :: built)
      (fun ps => (version, .declareDatatypes sorts (done ++ [⟨ps, []⟩]) :: built))
      (fun ps => yields_callUnit _ _) decl
    refine yields_bind (yields_bind hks (yields_callUnit _ _)) ?_
    show Yields _ (version, .declareDatatypes sorts
      (withConstructors (ks.map constructorOf) (done ++ [⟨decl.parameters, []⟩])) :: built) () _
    rw [withConstructors_snoc, hcs, show (⟨decl.parameters, decl.constructors⟩ :
      Tree.DatatypeDec) = decl from rfl]
    have := datatypes_yields version built sorts rest (done ++ [decl])
    simpa using this

theorem recursiveBodies_yields (version : Lexicon.Version) (built : List Tree.Command)
    (ds : List Tree.FunctionDec) :
    ∀ (sigs : List (Traversal.Signature treeValues)) (bodies done : List Tree.Term),
      sigs.length = bodies.length →
      Yields (Traversal.recursiveBodies P B (sigs.zip bodies))
        (version, .defineFunsRec ds done :: built) ()
        (version, .defineFunsRec ds (done ++ bodies) :: built)
  | [], [], done, _ => by simp only [List.append_nil]; rfl
  | sig :: sigs, body :: bodies, done, h => by
    simp only [List.length_cons, Nat.add_right_cancel_iff] at h
    simp only [List.zip_cons_cons]
    rw [recursiveBodies_cons]
    refine yields_bind (term_yields _ body _ _ (Nat.lt_succ_self _) (yields_call _ rfl))
      (yields_bind (yields_call _ rfl) ?_)
    have := recursiveBodies_yields version built ds sigs bodies (done ++ [body]) h
    show Yields _ (version, Tree.Command.defineFunsRec ds (done ++ [body]) :: built) () _
    simpa using this
  | [], _ :: _, _, h => by simp at h
  | _ :: _, [], _, h => by simp at h

theorem literalOf_asTerm (literal : Tree.PropLiteral) :
    literalOf literal.asTerm = some literal := by
  cases literal <;> rfl

theorem filterMap_literalOf' (literals : List Tree.PropLiteral) :
    literals.filterMap (literalOf ∘ Tree.PropLiteral.asTerm) = literals := by
  induction literals with
  | nil => rfl
  | cons l ls ih => simp [literalOf_asTerm, ih]

theorem filterMap_literalOf (literals : List Tree.PropLiteral) :
    (literals.map Tree.PropLiteral.asTerm).filterMap literalOf = literals := by
  induction literals with
  | nil => rfl
  | cons l ls ih => simp [literalOf_asTerm, ih]

/-! ## Commands -/

theorem signatures_yields : ∀ (ds : List Tree.FunctionDec) (s : State),
    ∃ sigs, Yields (ds.mapM fun declaration => do
        take P .parenOpen
        let handled ← Traversal.signature P B declaration.symbol declaration.parameters
          declaration.result
        take P .parenClose
        pure handled) s sigs s ∧ sigs.map declarationOf = ds
  | [], s => ⟨[], rfl, rfl⟩
  | d :: ds, s => by
    obtain ⟨sig, hsig, hd, -⟩ := signature_yields d.symbol d.parameters d.result s
    obtain ⟨sigs, hs, he⟩ := signatures_yields ds s
    refine ⟨sig :: sigs, ?_, by simp [hd, he]⟩
    simp only [List.mapM_cons]
    exact yields_bind (yields_bind (yields_take _ s) (yields_bind hsig (yields_bind
      (yields_take _ s) (yields_pure _ _)))) (yields_bind hs (yields_pure _ _))

theorem sortDecs_eq : ∀ sorts : List Tree.SortDec,
    (sorts.map fun sortDec => (sortDec.symbol, sortDec.arity)).map
      (fun (p : Tree.Symbol × Regex.Chars) => (⟨p.1, p.2⟩ : Tree.SortDec)) = sorts
  | [] => rfl
  | a :: l => by simp only [List.map_cons, sortDecs_eq l]

/-- The traversal of a command valid in the version, from the version in force, adds it to the
commands built so far. -/
theorem command_yields (version : Lexicon.Version) (built : List Tree.Command)
    (c : Tree.Command) (hv : c.Valid version) :
    Yields (Traversal.command P B c) (version, built) () (version, c :: built) := by
  have op := fun n => yields_opening n (version, built)
  have tk := fun t => yields_take t (version, built)
  have ta := fun ts => yields_takeAll ts (version, built)
  have cu := fun r => yields_callUnit r (version, built)
  cases c with
  | assert t =>
    rw [command_assert]
    exact yields_bind (op _) (yields_bind (term_yields' t _) (yields_bind (tk _) (cu _)))
  | checkSat => rw [command_checkSat]; exact yields_bind (op _) (yields_bind (tk _) (cu _))
  | checkSatAssuming ts =>
    rw [command_checkSatAssuming]
    refine yields_bind (op _) (yields_bind (tk _) (yields_bind (terms_yields' ts _)
      (yields_bind (ta _) ?_)))
    have h27 : version = .v2_7 := by
      have := hv.1
      cases version <;> simp_all [versionAtLeast, Version.upTo]
    subst h27
    exact cu _
  | checkSatAssumingLiterals ls =>
    rw [command_checkSatAssumingLiterals]
    refine yields_bind (op _) (yields_bind (tk _) (yields_bind (terms_yields' _ _)
      (yields_bind (ta _) ?_)))
    have hn : version ≠ .v2_7 := by
      have := hv.2.1
      rintro rfl
      exact this (by simp [versionAtLeast, Version.upTo])
    have e := cu (.commandCheckSatAssuming (ls.map Tree.PropLiteral.asTerm))
    revert e
    cases version <;> first | exact absurd rfl hn | (intro e; simpa [command,
      filterMap_literalOf, filterMap_literalOf'] using e)
  | declareConst s t =>
    rw [command_declareConst]
    exact yields_bind (op _) (yields_bind (tk _) (yields_bind (sort_yields' t _)
      (yields_bind (tk _) (cu _))))
  | declareDatatype s decl =>
    rw [command_declareDatatype]
    obtain ⟨ks, hks, hcs⟩ := datatype_yields (fun parameters =>
      Facts.Proofs.Parser.Program.callUnit B (.startDeclareDatatype s parameters))
      (version, built) (fun ps => (version, .declareDatatype s ⟨ps, []⟩ :: built))
      (fun ps => yields_callUnit _ _) decl
    refine yields_bind (op _) (yields_bind (tk _) (yields_bind hks
      (yields_bind (yields_take _ _) ?_)))
    have e := yields_callUnit (.endDeclareDatatype ks)
      (version, .declareDatatype s ⟨decl.parameters, []⟩ :: built)
    simp only [command, hcs] at e
    exact e
  | declareDatatypes sorts decls =>
    rw [command_declareDatatypes]
    have hs : (sorts.map fun sortDec => (sortDec.symbol, sortDec.arity)).map
        (fun (p : Tree.Symbol × Regex.Chars) => (⟨p.1, p.2⟩ : Tree.SortDec)) = sorts := by
      exact sortDecs_eq sorts
    refine yields_bind (op _) (yields_bind (tk _) (yields_bind (ta _) (yields_bind (tk _)
      (yields_bind (cu _) (yields_bind (yields_take _ _) ?_)))))
    show Yields _ (version, .declareDatatypes ((sorts.map fun sortDec =>
      (sortDec.symbol, sortDec.arity)).map
        (fun (p : Tree.Symbol × Regex.Chars) => (⟨p.1, p.2⟩ : Tree.SortDec))) [] :: built) () _
    rw [hs]
    have hd := datatypes_yields version built sorts decls []
    simp only [List.nil_append] at hd
    exact yields_bind hd (yields_bind (yields_takeAll _ _) (yields_callUnit _ _))
  | declareFun s ps r =>
    rw [command_declareFun]
    exact yields_bind (op _) (yields_bind (ta _) (yields_bind (sorts_yields ps _)
      (yields_bind (tk _) (yields_bind (sort_yields' r _) (yields_bind (tk _) (cu _))))))
  | declareSort s n =>
    rw [command_declareSort]; exact yields_bind (op _) (yields_bind (ta _) (cu _))
  | declareSortParameter s =>
    rw [command_declareSortParameter]; exact yields_bind (op _) (yields_bind (ta _) (cu _))
  | defineConst s t b =>
    rw [command_defineConst]
    exact yields_bind (op _) (yields_bind (tk _) (yields_bind (sort_yields' t _)
      (yields_bind (term_yields' b _) (yields_bind (tk _) (cu _)))))
  | defineFun d =>
    obtain ⟨s, ps, r, body⟩ := d
    rw [command_defineFun]
    obtain ⟨⟨sym, pairs, res⟩, hsig, -, hsym, hps, hr⟩ := signature_yields s ps r (version, built)
    dsimp only at hsym hr hps
    subst hsym hr
    refine yields_bind (op _) (yields_bind hsig (yields_bind (cu _)
      (yields_bind (term_yields' body _) (yields_bind (yields_take _ _) ?_))))
    rw [← hps]
    exact yields_callUnit (.endDefineFun body)
      (version, .defineFun ⟨sym, sortedVarsOf pairs, res, placeTerm⟩ :: built)
  | defineFunRec d =>
    obtain ⟨s, ps, r, body⟩ := d
    rw [command_defineFunRec]
    obtain ⟨⟨sym, pairs, res⟩, hsig, -, hsym, hps, hr⟩ := signature_yields s ps r (version, built)
    dsimp only at hsym hr hps
    subst hsym hr
    refine yields_bind (op _) (yields_bind hsig (yields_bind (cu _)
      (yields_bind (term_yields' body _) (yields_bind (yields_take _ _) ?_))))
    rw [← hps]
    exact yields_callUnit (.endDefineFunRec body)
      (version, .defineFunRec ⟨sym, sortedVarsOf pairs, res, placeTerm⟩ :: built)
  | defineFunsRec ds bodies =>
    rw [command_defineFunsRec]
    obtain ⟨sigs, hs, he⟩ := signatures_yields ds (version, built)
    have hlen : sigs.length = bodies.length := by
      rw [← hv.2.2.1, ← he, List.length_map]
    refine yields_bind (op _) (yields_bind (tk _) (yields_bind hs (yields_bind (tk _)
      (yields_bind (cu _) (yields_bind (yields_take _ _) ?_)))))
    have hb := recursiveBodies_yields version built (sigs.map declarationOf) sigs bodies [] hlen
    simp only [List.nil_append] at hb
    rw [← he]
    exact yields_bind hb (yields_bind (yields_takeAll _ _) (yields_callUnit _ _))
  | defineSort s ps t =>
    rw [command_defineSort]
    refine yields_bind (op _) (yields_bind (ta _) (yields_bind (ta _) (yields_bind (tk _)
      (yields_bind (cu _) (yields_bind (sort_yields' t _) (yields_bind (yields_take _ _) ?_))))))
    exact yields_callUnit _ _
  | echo c => rw [command_echo]; exact yields_bind (op _) (yields_bind (ta _) (cu _))
  | exit => rw [command_exit]; exact yields_bind (op _) (yields_bind (tk _) (cu _))
  | getAssertions =>
    rw [command_getAssertions]; exact yields_bind (op _) (yields_bind (tk _) (cu _))
  | getAssignment =>
    rw [command_getAssignment]; exact yields_bind (op _) (yields_bind (tk _) (cu _))
  | getInfo k => rw [command_getInfo]; exact yields_bind (op _) (yields_bind (ta _) (cu _))
  | getModel => rw [command_getModel]; exact yields_bind (op _) (yields_bind (tk _) (cu _))
  | getOption k => rw [command_getOption]; exact yields_bind (op _) (yields_bind (ta _) (cu _))
  | getProof => rw [command_getProof]; exact yields_bind (op _) (yields_bind (tk _) (cu _))
  | getUnsatAssumptions =>
    rw [command_getUnsatAssumptions]; exact yields_bind (op _) (yields_bind (tk _) (cu _))
  | getUnsatCore => rw [command_getUnsatCore]; exact yields_bind (op _) (yields_bind (tk _) (cu _))
  | getValue ts =>
    rw [command_getValue]
    exact yields_bind (op _) (yields_bind (tk _) (yields_bind (terms_yields' ts _)
      (yields_bind (ta _) (cu _))))
  | pop n => rw [command_pop]; exact yields_bind (op _) (yields_bind (ta _) (cu _))
  | push n => rw [command_push]; exact yields_bind (op _) (yields_bind (ta _) (cu _))
  | reset => rw [command_reset]; exact yields_bind (op _) (yields_bind (tk _) (cu _))
  | resetAssertions =>
    rw [command_resetAssertions]; exact yields_bind (op _) (yields_bind (tk _) (cu _))
  | setInfo a =>
    obtain ⟨k, v⟩ := a
    rw [command_setInfo]
    exact yields_bind (op _) (yields_bind (tk _) (yields_bind (attributeThen_yields _ _ _ _)
      (cu _)))
  | setLogic s => rw [command_setLogic]; exact yields_bind (op _) (yields_bind (ta _) (cu _))
  | setOption a =>
    obtain ⟨k, v⟩ := a
    rw [command_setOption]
    exact yields_bind (op _) (yields_bind (tk _) (yields_bind (attributeThen_yields _ _ _ _)
      (cu _)))

/-! ## Scripts -/

open BSmtLibSpec.Facts.Proofs.Parser.Rebuild (modeAfter_read unrestricted_ok)
open BSmtLibSpec.Facts.Proofs.Parser.Simulation (modeAfter_unparsed namesNoVersion_eq_false)

/-- The producer of the builder's traversal, which does nothing. -/
abbrev N : Traversal.Producer (StateT State Id) := nullProducer

theorem yields_switch (declarations : Nat) (version : Lexicon.Version) (s : State) :
    Yields (Traversal.switchVersion B N VersionPolicy.unrestricted declarations version) s ()
      (version, s.2) := by
  simp only [Traversal.switchVersion, unrestricted_ok]
  rfl

theorem commands_cons_none {command : Tree.Command} (hne : command ≠ .exit)
    (hd : command.declaredVersion = none) (hn : command.namesNoVersion = false)
    (declarations : Nat) (commands : List Tree.Command) :
    Traversal.commands P B N VersionPolicy.unrestricted declarations (command :: commands) =
      (Traversal.command P B command >>= fun _ =>
        Traversal.commands P B N VersionPolicy.unrestricted declarations commands) := by
  cases command <;> first | exact absurd rfl hne | simp [Traversal.commands, hd, hn]

theorem commands_cons_some {command : Tree.Command} (hne : command ≠ .exit)
    {version : Lexicon.Version}
    (hd : command.declaredVersion = some version) (declarations : Nat)
    (commands : List Tree.Command) :
    Traversal.commands P B N VersionPolicy.unrestricted declarations (command :: commands) =
      (Traversal.command P B command >>= fun _ =>
        Traversal.switchVersion B N VersionPolicy.unrestricted declarations version >>= fun _ =>
        Traversal.commands P B N VersionPolicy.unrestricted (declarations + 1) commands) := by
  cases command <;> first | exact absurd rfl hne | simp [Traversal.commands, hd]

theorem commands_yields : ∀ (commands : List Tree.Command) (version : Lexicon.Version)
    (built : List Tree.Command) (declarations : Nat), Script version commands →
    ∃ version', Yields (Traversal.commands P B N VersionPolicy.unrestricted declarations commands)
      (version, built) () (version', commands.reverse ++ built)
  | [], version, built, _, _ => ⟨version, by
      simp only [Traversal.commands, List.reverse_nil, List.nil_append]
      exact yields_receive _ (yields_pure () _)⟩
  | command :: commands, version, built, declarations, hs => by
    cases hs with
    | stop hv hm =>
      obtain rfl := modeAfter_unparsed hm
      refine ⟨version, ?_⟩
      simp only [Traversal.commands, List.reverse_cons, List.reverse_nil, List.nil_append,
        List.singleton_append]
      exact yields_bind (command_yields _ built .exit hv) (yields_bind (yields_pure () _)
        (yields_receive _ (yields_pure () _)))
    | command hv hm hrest =>
      rename_i next
      have hne : command ≠ .exit := by
        rintro rfl
        simp [Tree.Command.modeAfter] at hm
      have hc := command_yields version built command hv
      rcases modeAfter_read hm with ⟨hd, hn⟩ | hd
      · rw [hn] at hrest
        obtain ⟨v', h'⟩ := commands_yields commands version (command :: built) declarations hrest
        refine ⟨v', ?_⟩
        rw [commands_cons_none hne hd (namesNoVersion_eq_false hm)]
        simpa using yields_bind hc h'
      · obtain ⟨v', h'⟩ := commands_yields commands next (command :: built) (declarations + 1)
          hrest
        refine ⟨v', ?_⟩
        rw [commands_cons_some hne hd]
        simpa using yields_bind hc (yields_bind (yields_switch declarations next _) h')

/-- The traversal of a valid script with the builder, from any version and no commands, does not
fail and leaves the script's commands, newest first. -/
theorem script_builds (start version : Lexicon.Version) (commands : List Tree.Command)
    (h : Script version commands) :
    ∃ version', (Traversal.script P B N VersionPolicy.unrestricted version commands).run.run
      (start, []) = (.ok (), (version', commands.reverse)) := by
  obtain ⟨v', h'⟩ := commands_yields commands version [] 0 h
  refine ⟨v', ?_⟩
  have hs : Yields (Traversal.script P B N VersionPolicy.unrestricted version commands)
      (start, []) () (v', commands.reverse ++ []) :=
    yields_bind (x := ExceptT.lift (B.setVersion version)) (s' := (version, [])) rfl h'
  simpa [Yields] using hs

end BSmtLib.Facts.Proofs.PublicApi.BuilderTraversal
