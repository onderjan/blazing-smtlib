module

public import BSmtLib.Facts.Proofs.Parser.Category.Combinator
import all BSmtLib.Parser
import all BSmtLib.Parser.Category.Token
import all BSmtLib.Parser.Category.Combinator

@[expose] public section

/-!
# The list combinators on a cursor

A list of values of an inner parser up to a `)` is read value by value: between values, a `)`
ends the list, and any other token starts the next value, which the inner parser parses from the
cursor that has that token. The lemmas go by induction over the values, each value known by
`Parses` of the inner parser.
-/

namespace BSmtLib.Facts.Proofs.Parser.Category.Multiple

open BSmtLib.Token (Cursor)
open BSmtLib.Parser (Parse ParseError ParseErrorCause ParseState SyntaxErrorKind VersionErrorKind)
open BSmtLib.Parser.Internal (PM)
open BSmtLib.Parser.Category.Token BSmtLib.Parser.Category.Combinator
open BSmtLib.Parser.Category.Token.Internal
open BSmtLib.Parser.Category.Combinator.Internal
open BSmtLib.Facts.Parser.Adapters
open BSmtLib.Facts.Parser.Adapters.Cursor (Takes Reads noPoints)
open BSmtLib.Facts.Parser.Adapters.Outcome (Outcome outcome answer HandlerOnly)
open BSmtLib.Facts.Proofs.Parser.Category.Cursor BSmtLib.Facts.Proofs.Parser.Category.Token
open BSmtLib.Facts.Proofs.Parser.Category.Combinator BSmtLib.Facts.Proofs.Parser.Category.Steps

section

variable {Z : Type} [Cursor Z]

theorem firstToken_eq {cursor after : Z} {raw : Cursor.Token Z}
    {consumed : Cursor.Consumed after cursor}
    (hnext : Cursor.next? cursor = some (raw, ⟨after, consumed⟩)) (h : Cursor.HasNext cursor) :
    Internal.firstToken cursor h = (raw, ⟨after, consumed⟩) := by
  unfold Internal.firstToken
  split
  · rename_i heq
    rw [hnext] at heq
    cases heq
    rfl
  · rename_i heq
    rw [hnext] at heq
    cases heq

theorem ofSyntax_parenClose {token : Token}
    (h : Parser.Internal.Input.ofSyntax token = .parenClose) : token = .parenClose := by
  cases token <;> first | rfl | cases h

end

/-- What a loop gave, as an `Outcome`. -/
def outcomeAny {H E R S : Type} {Z : Type} {q : Z → Prop} :
    Except (ParseError E) (ControlFlow R) × S × ParseState H × { z : Z // q z } →
    Outcome R S Z E
  | (.ok (.break result), parser, _, next) => .finished result parser next.val
  | (.ok .continue, parser, _, _) => .waits parser
  | (.error error, _, _, next) =>
    match error.cause with
    | .syntax kind => .rejected kind next.val
    | .version kind => .rejectedVersion kind next.val
    | .handler error => .failed error

/-- The tokens of the values, one after another. -/
abbrev valuesTokens {α : Type} (values : List (List Parser.Internal.Input × α)) :
    List Parser.Internal.Input :=
  values.flatMap (·.1)

/-- The values finish with the inner parser, back as it was, and none starts with a `)`. -/
def ValuesParse {H P R E : Type} {m : Type → Type} [Monad m] [Parse P H m E R]
    (version : Version) (parser : P)
    (values : List (List Parser.Internal.Input × ExceptT (ParseErrorCause E) (StateT H m) R)) :
    Prop :=
  ∀ value ∈ values, Outcome.Finishes version parser value.1 value.2 parser ∧
    ∃ token tokens, value.1 = token :: tokens ∧ token ≠ .parenClose

section

variable {H P R : Type} {m : Type → Type} [Monad m] [LawfulMonad m] [Handler H m]
  [Parse P H m (Handler.Error H) R]

theorem values_handlerOnly {version : Version} {p : P}
    {values : List (List Parser.Internal.Input × PM H R)} (hvalues : ValuesParse version p values) :
    HandlerOnly (values.mapM fun (value : List Parser.Internal.Input × PM H R) => value.2) := by
  induction values with
  | nil => exact handlerOnly_pure _
  | cons value values ih =>
    rw [List.mapM_cons]
    exact handlerOnly_bind (hvalues value (List.mem_cons_self ..)).1.1 fun _ =>
      handlerOnly_bind (ih fun v hv => hvalues v (List.mem_cons_of_mem _ hv)) fun _ =>
        handlerOnly_pure _


set_option hygiene false in
/-- The proof that a loop's continuation after the inner parser depends on no more than what
`outcome` reads. -/
macro "loop_resp" : tactic => `(tactic| (
  intro x
  obtain ⟨a, p', s, ⟨z, hz⟩⟩ := x
  answer_cases a
  · rw [show outcome (.error (ParseError.Internal.new (.syntax kind)), p', s, ⟨z, hz⟩) =
      .rejected kind z from rfl, onOutcome_rejected _ _ _ hz]
    simp only [pure_bind, map_pure]
    try rfl
  · rw [show outcome (.error (ParseError.Internal.new (.version kind)), p', s, ⟨z, hz⟩) =
      .rejectedVersion kind z from rfl, onOutcome_rejectedVersion _ _ _ hz]
    simp only [pure_bind, map_pure]
    try rfl
  · simp only [onOutcome, outcome, pure_bind, map_pure, ParseError.Internal.cause_new]
    try rfl
  · simp only [onOutcome, outcome, pure_bind, map_pure]
    try rfl
  · rw [show outcome (.ok (.break result), p', s, ⟨z, hz⟩) = .finished result p' z from rfl,
      onOutcome_finished _ _ _ _ hz, parseState_eq s .new]))

/-- The values, then what the loop does at the cursor after them, with the items it has. -/
private theorem multiple_loop {version : Version} {p : P} {Z : Type} [Cursor Z]
    {origin last : Z}
    (finale : Array R →
      StateT H m (Outcome (Array R) (ClosedMultipleParser H P) Z (Handler.Error H)))
    (hfinale : ∀ (items : Array R) (state : ParseState H) (hc : Cursor.Consumed last origin),
      outcomeAny <$> Internal.repeatTurns ClosedMultipleParser.turn origin
          ({ inner := p, outside := true, items } : ClosedMultipleParser H P) state last hc =
        finale items) :
    (values : List (List Parser.Internal.Input × PM H R)) → ValuesParse version p values →
    (items : Array R) → (state : ParseState H) → (cursor : Z) →
    (hc : Cursor.Consumed cursor origin) → (rest : List Parser.Internal.Input) →
    Takes version cursor (valuesTokens values) last → Reads version last rest →
    outcomeAny <$> Internal.repeatTurns ClosedMultipleParser.turn origin
        ({ inner := p, outside := true, items } : ClosedMultipleParser H P) state cursor hc =
      (values.mapM fun (value : List Parser.Internal.Input × PM H R) => value.2).run >>= fun e =>
        match e with
        | .ok found => finale (items ++ found.toArray)
        | .error (.handler error) => pure (.failed error)
        | .error (.syntax kind) => pure (.rejected kind last)
        | .error (.version kind) => pure (.rejectedVersion kind last)
  | [], _, items, state, cursor, hc, rest, htakes, hreads => by
    have e := Takes.nil_inv htakes
    subst e
    rw [hfinale items state hc]
    simp
  | value :: values, hvalues, items, state, cursor, hc, rest, htakes, hreads => by
    obtain ⟨hparses, token, tokens, hvalue, htok⟩ := hvalues value (List.mem_cons_self ..)
    obtain ⟨calls, hcalls⟩ := handler_run hparses.1
    simp only [valuesTokens, List.flatMap_cons] at htakes
    obtain ⟨middle, ht₁, ht₂⟩ := Takes.split htakes
    have ht₁' := ht₁
    rw [hvalue] at ht₁'
    obtain ⟨after, raw, consumed, hn, hnext, hver, htoken, htail⟩ := Takes.cons_inv ht₁'
    have hc₁ := Takes.consumed_of_ne ht₁ (by simp [hvalue])
    rw [Internal.repeatTurns]
    split
    · rename_i hn' _
      exact absurd hn hn'
    · rename_i h _
      simp only [ClosedMultipleParser.turn, ite_true, firstToken_eq hnext h]
      split
      · rename_i heq
        rw [heq] at htoken
        exact absurd htoken.symm htok
      · simp only [bind_assoc, map_bind]
        rw [bind_outcome_eq _ _ (.ok .continue, p, .new, ⟨middle, hc₁⟩) (by loop_resp),
          hparses.2 state cursor middle _ ht₁ (Reads.of_takes ht₂ hreads),
          answer_bind hcalls, List.mapM_cons, ExceptT.run_bind, hcalls, bind_map_left,
          bind_assoc]
        refine bind_congr fun e => ?_
        rcases e with error | result
        · simp [onOutcome, outcomeAny]
        · dsimp only
          rw [onOutcome_finished _ _ _ _ hc₁]
          simp only [pure_bind]
          rw [multiple_loop finale hfinale values
            (fun v hv => hvalues v (List.mem_cons_of_mem _ hv)) (items.push result)
            ParseState.new middle _ rest ht₂ hreads]
          simp only [ExceptT.run_bind, ExceptT.run_pure, bind_assoc]
          refine bind_congr fun e => ?_
          rcases e with (kind | kind | error) | found <;> simp


omit [LawfulMonad m] in
/-- The list parser's parse from a state between values with the items so far: its first turn,
then the loop. -/
private theorem multiple_parse_eq (p : P) (items : Array R) {Z : Type} [Cursor Z]
    (state : ParseState H) (cursor : Z) :
    Parse.parse ({ inner := p, outside := true, items } : ClosedMultipleParser H P) state cursor =
      Internal.parseByTurns ClosedMultipleParser.turn
        ({ inner := p, outside := true, items } : ClosedMultipleParser H P) state cursor := rfl

/-- The parse of a list with a first value: the values, then what the loop does at the cursor
after them. -/
private theorem multiple_first {version : Version} {p : P} {Z : Type} [Cursor Z]
    {cursor last : Z}
    (finale : Array R →
      StateT H m (Outcome (Array R) (ClosedMultipleParser H P) Z (Handler.Error H)))
    (hfinale : ∀ (items : Array R) (state : ParseState H) (hc : Cursor.Consumed last cursor),
      outcomeAny <$> Internal.repeatTurns ClosedMultipleParser.turn cursor
          ({ inner := p, outside := true, items } : ClosedMultipleParser H P) state last hc =
        finale items)
    (value : List Parser.Internal.Input × PM H R)
    (values : List (List Parser.Internal.Input × PM H R))
    (hvalues : ValuesParse version p (value :: values)) (items : Array R) (state : ParseState H)
    (rest : List Parser.Internal.Input)
    (htakes : Takes version cursor (valuesTokens (value :: values)) last)
    (hreads : Reads version last rest) :
    outcome <$> Parse.parse ({ inner := p, outside := true, items } : ClosedMultipleParser H P)
        state cursor =
      ((value :: values).mapM fun (value : List Parser.Internal.Input × PM H R) => value.2).run >>=
        fun e => match e with
        | .ok found => finale (items ++ found.toArray)
        | .error (.handler error) => pure (.failed error)
        | .error (.syntax kind) => pure (.rejected kind last)
        | .error (.version kind) => pure (.rejectedVersion kind last) := by
  obtain ⟨hparses, token, tokens, hvalue, htok⟩ := hvalues value (List.mem_cons_self ..)
  obtain ⟨calls, hcalls⟩ := handler_run hparses.1
  simp only [valuesTokens, List.flatMap_cons] at htakes
  obtain ⟨middle, ht₁, ht₂⟩ := Takes.split htakes
  have ht₁' := ht₁
  rw [hvalue] at ht₁'
  obtain ⟨after, raw, consumed, hn, hnext, hver, htoken, htail⟩ := Takes.cons_inv ht₁'
  have hc₁ := Takes.consumed_of_ne ht₁ (by simp [hvalue])
  rw [multiple_parse_eq]
  simp only [Internal.parseByTurns]
  split
  · rename_i hn' _
    exact absurd hn hn'
  · rename_i h _
    simp only [ClosedMultipleParser.turn, ite_true, firstToken_eq hnext h]
    split
    · rename_i heq
      rw [heq] at htoken
      exact absurd htoken.symm htok
    · simp only [bind_assoc, map_bind]
      rw [bind_outcome_eq _ _ (.ok .continue, p, .new, ⟨middle, hc₁⟩) (by loop_resp),
        hparses.2 state cursor middle _ ht₁ (Reads.of_takes ht₂ hreads),
        answer_bind hcalls, List.mapM_cons, ExceptT.run_bind, hcalls, bind_map_left,
        bind_assoc]
      refine bind_congr fun e => ?_
      rcases e with error | result
      · simp [onOutcome, outcome]
      · dsimp only
        rw [onOutcome_finished _ _ _ _ hc₁]
        simp only [pure_bind]
        rw [show ∀ X : StateT H m (Except (ParseError (Handler.Error H))
              (ControlFlow (Array R)) × ClosedMultipleParser H P × ParseState H ×
              { z : Z // Cursor.Consumed z cursor }),
            (outcome <$> (X >>= fun x => match x with
              | (answer, self, state, ⟨done, consumed⟩) =>
                pure (answer, self, state, (⟨done, fun _ => consumed⟩ :
                  { z : Z // Cursor.HasNext cursor → Cursor.Consumed z cursor })))) =
              outcomeAny <$> X from fun X => by
          rw [map_bind]
          conv => rhs; rw [← bind_pure X, map_bind]
          refine bind_congr fun x => ?_
          obtain ⟨a, s', st', ⟨z, hz⟩⟩ := x
          rcases a with (_ | _) | (_ | _) <;> simp only [map_pure] <;> rfl]
        rw [multiple_loop finale hfinale values
          (fun v hv => hvalues v (List.mem_cons_of_mem _ hv)) (items.push result)
          ParseState.new middle _ rest ht₂ hreads]
        simp only [ExceptT.run_bind, ExceptT.run_pure, bind_assoc]
        refine bind_congr fun e => ?_
        rcases e with (kind | kind | error) | found <;> simp


/-- Between values, a `)` ends the list with its items. -/
private theorem loop_close {version : Version} {p : P} {Z : Type} [Cursor Z]
    {origin last next : Z} (items : Array R) (state : ParseState H)
    (hc : Cursor.Consumed last origin) (htakes : Takes version last [.parenClose] next) :
    outcomeAny <$> Internal.repeatTurns ClosedMultipleParser.turn origin
        ({ inner := p, outside := true, items } : ClosedMultipleParser H P) state last hc =
      pure (.finished items (ClosedMultipleParser.new (H := H) p) next) := by
  obtain ⟨after, raw, consumed, hn, hnext, hver, htoken, htail⟩ := Takes.cons_inv htakes
  rw [Takes.nil_inv htail, Internal.repeatTurns]
  split
  · rename_i hn' _
    exact absurd hn hn'
  · rename_i h _
    simp only [ClosedMultipleParser.turn, ite_true, firstToken_eq hnext h,
      ofSyntax_parenClose htoken]
    simp [outcomeAny, ClosedMultipleParser.new]

private theorem first_close {version : Version} {p : P} {Z : Type} [Cursor Z]
    {cursor next : Z} (items : Array R) (state : ParseState H)
    (htakes : Takes version cursor [.parenClose] next) :
    outcome <$> Parse.parse ({ inner := p, outside := true, items } : ClosedMultipleParser H P)
        state cursor = pure (.finished items (ClosedMultipleParser.new (H := H) p) next) := by
  obtain ⟨after, raw, consumed, hn, hnext, hver, htoken, htail⟩ := Takes.cons_inv htakes
  rw [Takes.nil_inv htail, multiple_parse_eq]
  simp only [Internal.parseByTurns]
  split
  · rename_i hn' _
    exact absurd hn hn'
  · rename_i h _
    simp only [ClosedMultipleParser.turn, ite_true, firstToken_eq hnext h,
      ofSyntax_parenClose htoken]
    simp [outcome, ClosedMultipleParser.new]

/-- Between values, the end of the cursor: the loop continues, as it is. -/
private theorem loop_end {p : P} {Z : Type} [Cursor Z] {origin last : Z} (items : Array R)
    (state : ParseState H) (hc : Cursor.Consumed last origin)
    (hnone : Cursor.next? last = none) :
    outcomeAny <$> Internal.repeatTurns ClosedMultipleParser.turn origin
        ({ inner := p, outside := true, items } : ClosedMultipleParser H P) state last hc =
      pure (.waits { inner := p, outside := true, items }) := by
  rw [Internal.repeatTurns]
  split
  · simp [outcomeAny]
  · rename_i h _
    exact absurd h (Parser.Internal.not_hasNext hnone)

/-- Between values, the inner parser rejects tokens that do not start with `)`: the loop
rejects them. -/
private theorem loop_rejects {version : Version} {p : P} {Z : Type} [Cursor Z]
    {origin last next : Z} {tokens : List Parser.Internal.Input} {program : PM H Unit}
    {kind : SyntaxErrorKind} (h : Outcome.Rejects version p tokens program kind)
    (hfirst : ∃ token tokens', tokens = token :: tokens' ∧ token ≠ .parenClose)
    (rest : List Parser.Internal.Input) (htakes : Takes version last tokens next)
    (hreads : Reads version next rest) (items : Array R) (state : ParseState H)
    (hc : Cursor.Consumed last origin) :
    outcomeAny <$> Internal.repeatTurns ClosedMultipleParser.turn origin
        ({ inner := p, outside := true, items } : ClosedMultipleParser H P) state last hc =
      answer (fun () => .rejected kind next) next <$> program.run := by
  obtain ⟨calls, hcalls⟩ := handler_run h.1
  obtain ⟨token, tokens', rfl, htok⟩ := hfirst
  obtain ⟨after, raw, consumed, hn, hnext, hver, htoken, htail⟩ := Takes.cons_inv htakes
  have hcf := Takes.consumed htakes
  rw [Internal.repeatTurns]
  split
  · rename_i hn' _
    exact absurd hn hn'
  · rename_i hh _
    simp only [ClosedMultipleParser.turn, ite_true, firstToken_eq hnext hh]
    split
    · rename_i heq
      rw [heq] at htoken
      exact absurd htoken.symm htok
    · simp only [bind_assoc, map_bind]
      rw [bind_outcome_eq _ _ (.ok .continue, p, .new, ⟨next, fun _ => hcf⟩) (by loop_resp),
        h.2 state last next rest htakes hreads, answer_bind hcalls, hcalls, Functor.map_map]
      conv => rhs; rw [map_eq_pure_bind]
      refine bind_congr fun e => ?_
      rcases e with error | ⟨⟩
      · simp [onOutcome, outcomeAny, answer]
      · dsimp only
        rw [onOutcome_rejected _ _ _ (fun _ => hcf)]
        simp [outcomeAny, answer]

/-- Between values, when the tokens do not start with `)` and the inner parser continues on them,
the loop continues, as the inner parser, within a value. -/
private theorem loop_waits {version : Version} {p : P} {Z : Type} [Cursor Z]
    {origin last final : Z} {tokens : List Parser.Internal.Input} {α : Type}
    {program : PM H α} {after : α → P} (h : Outcome.Waits version p tokens program after)
    (hfirst : ∃ token tokens', tokens = token :: tokens' ∧ token ≠ .parenClose)
    (htakes : Takes version last tokens final) (hnone : Cursor.next? final = none)
    (items : Array R) (state : ParseState H) (hc : Cursor.Consumed last origin) :
    outcomeAny <$> Internal.repeatTurns ClosedMultipleParser.turn origin
        ({ inner := p, outside := true, items } : ClosedMultipleParser H P) state last hc =
      answer (fun a => .waits { inner := after a, outside := false, items }) final <$>
        program.run := by
  obtain ⟨calls, hcalls⟩ := handler_run h.1
  obtain ⟨token, tokens', rfl, htok⟩ := hfirst
  obtain ⟨after', raw, consumed, hn, hnext, hver, htoken, htail⟩ := Takes.cons_inv htakes
  have hcf := Takes.consumed htakes
  rw [Internal.repeatTurns]
  split
  · rename_i hn' _
    exact absurd hn hn'
  · rename_i hh _
    simp only [ClosedMultipleParser.turn, ite_true, firstToken_eq hnext hh]
    split
    · rename_i heq
      rw [heq] at htoken
      exact absurd htoken.symm htok
    · simp only [bind_assoc, map_bind]
      rw [bind_outcome_eq _ _ (.ok .continue, p, .new, ⟨final, fun _ => hcf⟩) (by loop_resp),
        h.2 state last final htakes hnone, answer_bind hcalls, hcalls, Functor.map_map]
      conv => rhs; rw [map_eq_pure_bind]
      refine bind_congr fun e => ?_
      rcases e with error | a
      · simp [onOutcome, outcomeAny, answer]
      · simp [onOutcome, outcomeAny, answer]


private theorem first_rejects {version : Version} {p : P} {Z : Type} [Cursor Z]
    {cursor next : Z} {tokens : List Parser.Internal.Input} {program : PM H Unit}
    {kind : SyntaxErrorKind} (h : Outcome.Rejects version p tokens program kind)
    (hfirst : ∃ token tokens', tokens = token :: tokens' ∧ token ≠ .parenClose)
    (rest : List Parser.Internal.Input) (htakes : Takes version cursor tokens next)
    (hreads : Reads version next rest) (items : Array R) (state : ParseState H) :
    outcome <$> Parse.parse ({ inner := p, outside := true, items } : ClosedMultipleParser H P)
        state cursor = answer (fun () => .rejected kind next) next <$> program.run := by
  obtain ⟨calls, hcalls⟩ := handler_run h.1
  obtain ⟨token, tokens', rfl, htok⟩ := hfirst
  obtain ⟨after, raw, consumed, hn, hnext, hver, htoken, htail⟩ := Takes.cons_inv htakes
  have hcf := Takes.consumed htakes
  rw [multiple_parse_eq]
  simp only [Internal.parseByTurns]
  split
  · rename_i hn' _
    exact absurd hn hn'
  · rename_i hh _
    simp only [ClosedMultipleParser.turn, ite_true, firstToken_eq hnext hh]
    split
    · rename_i heq
      rw [heq] at htoken
      exact absurd htoken.symm htok
    · simp only [bind_assoc, map_bind]
      rw [bind_outcome_eq _ _ (.ok .continue, p, .new, ⟨next, fun _ => hcf⟩) (by loop_resp),
        h.2 state cursor next rest htakes hreads, answer_bind hcalls, hcalls, Functor.map_map]
      conv => rhs; rw [map_eq_pure_bind]
      refine bind_congr fun e => ?_
      rcases e with error | ⟨⟩
      · simp [onOutcome, outcome, answer]
      · dsimp only
        rw [onOutcome_rejected _ _ _ (fun _ => hcf)]
        simp [outcome, answer]

private theorem first_waits {version : Version} {p : P} {Z : Type} [Cursor Z]
    {cursor final : Z} {tokens : List Parser.Internal.Input} {α : Type}
    {program : PM H α} {after : α → P} (h : Outcome.Waits version p tokens program after)
    (hfirst : ∃ token tokens', tokens = token :: tokens' ∧ token ≠ .parenClose)
    (htakes : Takes version cursor tokens final) (hnone : Cursor.next? final = none)
    (items : Array R) (state : ParseState H) :
    outcome <$> Parse.parse ({ inner := p, outside := true, items } : ClosedMultipleParser H P)
        state cursor =
      answer (fun a => .waits { inner := after a, outside := false, items }) final <$>
        program.run := by
  obtain ⟨calls, hcalls⟩ := handler_run h.1
  obtain ⟨token, tokens', rfl, htok⟩ := hfirst
  obtain ⟨after', raw, consumed, hn, hnext, hver, htoken, htail⟩ := Takes.cons_inv htakes
  have hcf := Takes.consumed htakes
  rw [multiple_parse_eq]
  simp only [Internal.parseByTurns]
  split
  · rename_i hn' _
    exact absurd hn hn'
  · rename_i hh _
    simp only [ClosedMultipleParser.turn, ite_true, firstToken_eq hnext hh]
    split
    · rename_i heq
      rw [heq] at htoken
      exact absurd htoken.symm htok
    · simp only [bind_assoc, map_bind]
      rw [bind_outcome_eq _ _ (.ok .continue, p, .new, ⟨final, fun _ => hcf⟩) (by loop_resp),
        h.2 state cursor final htakes hnone, answer_bind hcalls, hcalls, Functor.map_map]
      conv => rhs; rw [map_eq_pure_bind]
      refine bind_congr fun e => ?_
      rcases e with error | a
      · simp [onOutcome, outcome, answer]
      · simp [onOutcome, outcome, answer]


/-- A handler-only program's run, bound to a continuation that answers handler failures as
failures: the continuation on the program's calls. -/
private theorem run_bind_calls {β γ : Type} {x : PM H β}
    {calls : ExceptT (Handler.Error H) (StateT H m) β}
    (hcalls : x.run = (fun e => match e with
        | .ok a => .ok a
        | .error error => .error (.handler error)) <$> calls.run)
    (F : β → StateT H m γ) (G : Handler.Error H → StateT H m γ)
    (S : SyntaxErrorKind → StateT H m γ) (V : VersionErrorKind → StateT H m γ) :
    (x.run >>= fun e => match e with
      | .ok found => F found
      | .error (.handler error) => G error
      | .error (.syntax kind) => S kind
      | .error (.version kind) => V kind) =
      calls.run >>= fun e => match e with
        | .ok found => F found
        | .error error => G error := by
  rw [hcalls, bind_map_left]
  refine bind_congr fun e => ?_
  rcases e with error | a <;> rfl

private theorem items_finishes {version : Version} {p : P}
    {values : List (List Parser.Internal.Input × PM H R)} (hvalues : ValuesParse version p values)
    (items : Array R) :
    Outcome.Finishes version ({ inner := p, outside := true, items } : ClosedMultipleParser H P)
      (valuesTokens values ++ [.parenClose])
      ((fun found => items ++ found.toArray) <$> values.mapM fun value => value.2)
      (ClosedMultipleParser.new (H := H) p) := by
  have hho := values_handlerOnly hvalues
  refine ⟨handlerOnly_map _ hho, fun state cursor next rest htakes hreads => ?_⟩
  obtain ⟨calls, hcalls⟩ := handler_run hho
  obtain ⟨last, ht₁, ht₂⟩ := Takes.split htakes
  cases values with
  | nil =>
    rw [Takes.nil_inv ht₁] at ht₂
    rw [first_close items state ht₂]
    simp [answer]
  | cons value values =>
    rw [multiple_first (fun items => pure (.finished items (ClosedMultipleParser.new p) next))
      (fun items state hc => loop_close items state hc ht₂) value values hvalues items state
      ([.parenClose] ++ rest) ht₁ (Reads.of_takes ht₂ hreads),
      ExceptT.run_map, hcalls, bind_map_left, Functor.map_map, Functor.map_map]
    conv => rhs; rw [map_eq_pure_bind]
    refine bind_congr fun e => ?_
    rcases e with error | found <;> rfl

private theorem items_rejects {version : Version} {p : P}
    {values : List (List Parser.Internal.Input × PM H R)} (hvalues : ValuesParse version p values)
    {tokens : List Parser.Internal.Input} {program : PM H Unit} {kind : SyntaxErrorKind}
    (h : Outcome.Rejects version p tokens program kind)
    (hfirst : ∃ token tokens', tokens = token :: tokens' ∧ token ≠ .parenClose)
    (items : Array R) :
    Outcome.Rejects version ({ inner := p, outside := true, items } : ClosedMultipleParser H P)
      (valuesTokens values ++ tokens)
      (do let _ ← values.mapM fun value => value.2; program) kind := by
  have hho := values_handlerOnly hvalues
  refine ⟨handlerOnly_bind hho fun _ => h.1, fun state cursor next rest htakes hreads => ?_⟩
  obtain ⟨calls, hcalls⟩ := handler_run hho
  obtain ⟨calls₂, hcalls₂⟩ := handler_run h.1
  obtain ⟨last, ht₁, ht₂⟩ := Takes.split htakes
  cases values with
  | nil =>
    rw [Takes.nil_inv ht₁] at ht₂
    rw [first_rejects h hfirst rest ht₂ hreads items state]
    simp
  | cons value values =>
    rw [multiple_first (fun _ => answer (fun () => .rejected kind next) next <$> program.run)
      (fun items state hc => loop_rejects h hfirst rest ht₂ hreads items state hc) value values
      hvalues items state (tokens ++ rest) ht₁ (Reads.of_takes ht₂ hreads),
      hcalls, bind_map_left, answer_run_bind hcalls]
    refine bind_congr fun e => ?_
    rcases e with error | found <;> rfl

private theorem items_waits_end {version : Version} {p : P}
    {values : List (List Parser.Internal.Input × PM H R)} (hvalues : ValuesParse version p values)
    (items : Array R) :
    Outcome.Waits version ({ inner := p, outside := true, items } : ClosedMultipleParser H P)
      (valuesTokens values) (values.mapM fun value => value.2)
      fun found => { inner := p, outside := true, items := items ++ found.toArray } := by
  have hho := values_handlerOnly hvalues
  refine ⟨hho, fun state cursor last htakes hnone => ?_⟩
  obtain ⟨calls, hcalls⟩ := handler_run hho
  cases values with
  | nil =>
    rw [Takes.nil_inv htakes] at hnone
    rw [multiple_parse_eq]
    simp only [Internal.parseByTurns]
    split
    · simp [outcome, answer]
    · rename_i hh _
      exact absurd hh (Parser.Internal.not_hasNext hnone)
  | cons value values =>
    rw [multiple_first (fun items => pure (.waits { inner := p, outside := true, items }))
      (fun items state hc => loop_end items state hc hnone) value values hvalues items state []
      htakes ⟨last, .nil last, hnone⟩, hcalls, bind_map_left, Functor.map_map]
    conv => rhs; rw [map_eq_pure_bind]
    refine bind_congr fun e => ?_
    rcases e with error | found <;> rfl

private theorem items_waits_inner {version : Version} {p : P}
    {values : List (List Parser.Internal.Input × PM H R)} (hvalues : ValuesParse version p values)
    {tokens : List Parser.Internal.Input} {α : Type} {program : PM H α} {after : α → P}
    (h : Outcome.Waits version p tokens program after)
    (hfirst : ∃ token tokens', tokens = token :: tokens' ∧ token ≠ .parenClose)
    (items : Array R) :
    Outcome.Waits version ({ inner := p, outside := true, items } : ClosedMultipleParser H P)
      (valuesTokens values ++ tokens)
      (do let found ← values.mapM fun value => value.2; let a ← program; pure (found, a))
      fun x => { inner := after x.2, outside := false, items := items ++ x.1.toArray } := by
  have hho := values_handlerOnly hvalues
  refine ⟨handlerOnly_bind hho fun _ => handlerOnly_bind h.1 fun _ => handlerOnly_pure _,
    fun state cursor final htakes hnone => ?_⟩
  obtain ⟨calls, hcalls⟩ := handler_run hho
  obtain ⟨calls₂, hcalls₂⟩ := handler_run h.1
  obtain ⟨last, ht₁, ht₂⟩ := Takes.split htakes
  cases values with
  | nil =>
    rw [Takes.nil_inv ht₁] at ht₂
    rw [first_waits h hfirst ht₂ hnone items state]
    simp only [List.mapM_nil, pure_bind, ExceptT.run_bind, ExceptT.run_pure]
    rw [hcalls₂]
    simp only [pure_bind, map_eq_pure_bind,
      bind_assoc]
    refine bind_congr fun e => ?_
    rcases e with error | a <;> simp [answer]
  | cons value values =>
    rw [multiple_first (fun items => answer (fun a => Outcome.waits
        ({ inner := after a, outside := false, items } : ClosedMultipleParser H P)) final <$>
        program.run)
      (fun items state hc => loop_waits h hfirst ht₂ hnone items state hc) value values hvalues
      items state tokens ht₁ (by simpa using Reads.of_takes ht₂ ⟨final, .nil final, hnone⟩),
      hcalls, bind_map_left, answer_run_bind hcalls]
    refine bind_congr fun e => ?_
    rcases e with error | found
    · rfl
    · simp only [map_eq_pure_bind, bind_assoc, ExceptT.run_bind,
        ExceptT.run_pure]
      rw [hcalls₂]
      simp only [bind_map_left]
      refine bind_congr fun e => ?_
      rcases e with error | a <;> simp [answer]


/-- The list parser within a value: the inner parser finishes it, then the values, then what
the loop does at the cursor after them. -/
private theorem resume_first {version : Version} {p q : P} {Z : Type} [Cursor Z]
    {cursor last : Z}
    (finale : Array R →
      StateT H m (Outcome (Array R) (ClosedMultipleParser H P) Z (Handler.Error H)))
    (hfinale : ∀ (items : Array R) (state : ParseState H) (hc : Cursor.Consumed last cursor),
      outcomeAny <$> Internal.repeatTurns ClosedMultipleParser.turn cursor
          ({ inner := p, outside := true, items } : ClosedMultipleParser H P) state last hc =
        finale items)
    {tokens : List Parser.Internal.Input} {program : PM H R}
    (hq : Outcome.Finishes version q tokens program p) (hne : tokens ≠ [])
    (values : List (List Parser.Internal.Input × PM H R))
    (hvalues : ValuesParse version p values) (items : Array R) (state : ParseState H)
    (rest : List Parser.Internal.Input)
    (htakes : Takes version cursor (tokens ++ valuesTokens values) last)
    (hreads : Reads version last rest) :
    outcome <$> Parse.parse ({ inner := q, outside := false, items } : ClosedMultipleParser H P)
        state cursor =
      (program >>= fun first => (values.mapM fun (value : List Parser.Internal.Input × PM H R) =>
          value.2) >>= fun found => pure (first :: found)).run >>=
        fun e => match e with
        | .ok found => finale (items ++ found.toArray)
        | .error (.handler error) => pure (.failed error)
        | .error (.syntax kind) => pure (.rejected kind last)
        | .error (.version kind) => pure (.rejectedVersion kind last) := by
  obtain ⟨calls, hcalls⟩ := handler_run hq.1
  obtain ⟨middle, ht₁, ht₂⟩ := Takes.split htakes
  have hc₁ := Takes.consumed_of_ne ht₁ hne
  have hn := Takes.hasNext_of_ne ht₁ hne
  rw [show Parse.parse ({ inner := q, outside := false, items } : ClosedMultipleParser H P) state
      cursor = Internal.parseByTurns ClosedMultipleParser.turn
        ({ inner := q, outside := false, items } : ClosedMultipleParser H P) state cursor from rfl]
  simp only [Internal.parseByTurns]
  split
  · rename_i hn' _
    exact absurd hn hn'
  · rename_i h _
    simp only [ClosedMultipleParser.turn, Bool.false_eq_true, ite_false]
    simp only [bind_assoc, map_bind]
    rw [bind_outcome_eq _ _ (.ok .continue, q, .new, ⟨middle, hc₁⟩) (by loop_resp),
      hq.2 state cursor middle _ ht₁ (Reads.of_takes ht₂ hreads),
      answer_bind hcalls, ExceptT.run_bind, hcalls, bind_map_left, bind_assoc]
    refine bind_congr fun e => ?_
    rcases e with error | result
    · simp [onOutcome, outcome]
    · dsimp only
      rw [onOutcome_finished _ _ _ _ hc₁]
      simp only [pure_bind]
      rw [show ∀ X : StateT H m (Except (ParseError (Handler.Error H))
            (ControlFlow (Array R)) × ClosedMultipleParser H P × ParseState H ×
            { z : Z // Cursor.Consumed z cursor }),
          (outcome <$> (X >>= fun x => match x with
            | (answer, self, state, ⟨done, consumed⟩) =>
              pure (answer, self, state, (⟨done, fun _ => consumed⟩ :
                { z : Z // Cursor.HasNext cursor → Cursor.Consumed z cursor })))) =
            outcomeAny <$> X from fun X => by
        rw [map_bind]
        conv => rhs; rw [← bind_pure X, map_bind]
        refine bind_congr fun x => ?_
        obtain ⟨a, s', st', ⟨z, hz⟩⟩ := x
        rcases a with (_ | _) | (_ | _) <;> simp only [map_pure] <;> rfl]
      rw [multiple_loop finale hfinale values hvalues (items.push result) ParseState.new middle _
        rest ht₂ hreads]
      simp only [ExceptT.run_bind, ExceptT.run_pure, bind_assoc]
      refine bind_congr fun e => ?_
      rcases e with (kind | kind | error) | found <;> simp

/-- The closed list parser on its values and the `)` after them. -/
theorem closedMultiple_parses {version : Version} {p : P}
    {values : List (List Parser.Internal.Input × PM H R)} (hvalues : ValuesParse version p values) :
    Outcome.Finishes version (ClosedMultipleParser.new (H := H) p)
      (valuesTokens values ++ [.parenClose])
      ((fun results => results.toArray) <$> values.mapM fun value => value.2)
      (ClosedMultipleParser.new p) := by
  have := items_finishes hvalues #[]
  simpa [ClosedMultipleParser.new] using this

/-- The closed list parser on its values and then tokens that its inner parser rejects, not
starting with `)`. -/
theorem closedMultiple_rejects_inner {version : Version} {p : P}
    {values : List (List Parser.Internal.Input × PM H R)} (hvalues : ValuesParse version p values)
    {tokens : List Parser.Internal.Input} {program : PM H Unit} {kind : SyntaxErrorKind}
    (h : Outcome.Rejects version p tokens program kind)
    (hfirst : ∃ token tokens', tokens = token :: tokens' ∧ token ≠ .parenClose) :
    Outcome.Rejects version (ClosedMultipleParser.new (H := H) p) (valuesTokens values ++ tokens)
      (do let _ ← values.mapM fun value => value.2; program) kind :=
  items_rejects hvalues h hfirst #[]

/--
When the cursor holds exactly the tokens of its values, the closed list parser continues, as a
parser that finishes on further values and the `)`, and rejects further values and tokens that
its inner parser rejects.
-/
theorem closedMultiple_waits_between {version : Version} {p : P}
    {values : List (List Parser.Internal.Input × PM H R)} (hvalues : ValuesParse version p values) :
    ∃ after : List R → ClosedMultipleParser H P,
      Outcome.Waits version (ClosedMultipleParser.new (H := H) p) (valuesTokens values)
        (values.mapM fun value => value.2) after ∧
      (∀ found {values' : List (List Parser.Internal.Input × PM H R)},
        ValuesParse version p values' →
        Outcome.Finishes version (after found) (valuesTokens values' ++ [.parenClose])
          ((fun results => (found ++ results).toArray) <$> values'.mapM fun value => value.2)
          (ClosedMultipleParser.new p)) ∧
      (∀ found {values' : List (List Parser.Internal.Input × PM H R)}
        {tokens : List Parser.Internal.Input} {program : PM H Unit} {kind : SyntaxErrorKind},
        ValuesParse version p values' → Outcome.Rejects version p tokens program kind →
        (∃ token tokens', tokens = token :: tokens' ∧ token ≠ .parenClose) →
        Outcome.Rejects version (after found) (valuesTokens values' ++ tokens)
          (do let _ ← values'.mapM fun value => value.2; program) kind) := by
  refine ⟨fun found => { inner := p, outside := true, items := found.toArray }, ?_,
    fun found _ hv => ?_, fun found _ _ _ _ hv h hf => items_rejects hv h hf _⟩
  · have := items_waits_end hvalues #[]
    simpa [ClosedMultipleParser.new] using this
  · have := items_finishes hv found.toArray
    simpa using this

/--
When the cursor holds its values and then tokens that do not start with `)`, and its inner parser
continues on those tokens, the closed list parser continues, as a parser that finishes once the
inner parser finishes its value and further values and the `)` follow.
-/
theorem closedMultiple_waits_inner {version : Version} {p : P}
    {values : List (List Parser.Internal.Input × PM H R)} (hvalues : ValuesParse version p values)
    {tokens : List Parser.Internal.Input} {α : Type} {program : PM H α} {after : α → P}
    (h : Outcome.Waits version p tokens program after)
    (hfirst : ∃ token tokens', tokens = token :: tokens' ∧ token ≠ .parenClose) :
    ∃ after' : List R × α → ClosedMultipleParser H P,
      Outcome.Waits version (ClosedMultipleParser.new (H := H) p) (valuesTokens values ++ tokens)
        (do let found ← values.mapM fun value => value.2; let a ← program; pure (found, a))
        after' ∧
      ∀ found a {tokens' : List Parser.Internal.Input} {program' : PM H R}
        {values' : List (List Parser.Internal.Input × PM H R)},
        Outcome.Finishes version (after a) tokens' program' p → tokens' ≠ [] →
        ValuesParse version p values' →
        Outcome.Finishes version (after' (found, a)) (tokens' ++ valuesTokens values' ++
          [.parenClose])
          ((fun results => (found ++ results).toArray) <$> (program' >>= fun first =>
            (values'.mapM fun value => value.2) >>= fun others => pure (first :: others)))
          (ClosedMultipleParser.new p) := by
  refine ⟨fun x => { inner := after x.2, outside := false, items := x.1.toArray }, ?_,
    fun found a _ _ values' hq hne hv => ?_⟩
  · have := items_waits_inner hvalues h hfirst #[]
    simpa [ClosedMultipleParser.new] using this
  · obtain ⟨calls, hcalls⟩ := handler_run hq.1
    have hho := values_handlerOnly hv
    refine ⟨handlerOnly_map _ (handlerOnly_bind hq.1 fun _ =>
      handlerOnly_bind hho fun _ => handlerOnly_pure _), fun state cursor next rest htakes
        hreads => ?_⟩
    obtain ⟨last, ht₁, ht₂⟩ := Takes.split htakes
    rw [resume_first (fun items => pure (.finished items (ClosedMultipleParser.new p) next))
      (fun items state hc => loop_close items state hc ht₂) hq hne values' hv found.toArray
      state ([.parenClose] ++ rest) ht₁ (Reads.of_takes ht₂ hreads)]
    obtain ⟨calls₂, hcalls₂⟩ := handler_run (handlerOnly_bind hq.1 fun first =>
      handlerOnly_bind hho fun others => handlerOnly_pure (first :: others))
    rw [hcalls₂, bind_map_left, ExceptT.run_map, hcalls₂, Functor.map_map, Functor.map_map]
    conv => rhs; rw [map_eq_pure_bind]
    refine bind_congr fun e => ?_
    rcases e with error | results <;> simp [answer, Except.map]


/-- The list parser enclosed in `(` and `)` answers as the opened parser it wraps. -/
private theorem parenMultiple_wraps :
    Wraps (H := H) fun inner : OpenedParser H (ClosedMultipleParser H P) =>
      (⟨inner⟩ : ParenMultipleParser H P) := by
  intro inner Z _ state cursor
  rw [show Parse.parse (⟨inner⟩ : ParenMultipleParser H P) state cursor =
      Parse.parse inner state cursor >>= fun x =>
        pure (x.1, (⟨x.2.1⟩ : ParenMultipleParser H P), x.2.2.1, x.2.2.2) from rfl, map_bind,
    Functor.map_map, map_eq_pure_bind]
  refine bind_congr fun x => ?_
  obtain ⟨a, p, s, ⟨z, hz⟩⟩ := x
  rcases a with (_ | _) | (_ | _) <;> simp only [map_pure] <;> rfl

/-- The list parser enclosed in `(` and `)` on a `(`, its values and the `)`. -/
theorem parenMultiple_parses {version : Version} {p : P}
    {values : List (List Parser.Internal.Input × PM H R)} (hvalues : ValuesParse version p values) :
    Outcome.Finishes version (ParenMultipleParser.new (H := H) p)
      (.parenOpen :: (valuesTokens values ++ [.parenClose]))
      ((fun results => results.toArray) <$> values.mapM fun value => value.2)
      (ParenMultipleParser.new p) :=
  wraps_finishes parenMultiple_wraps (opened_parses (closedMultiple_parses hvalues) (by simp))

/-- The list parser enclosed in `(` and `)` on a first token that is not `(`. -/
theorem parenMultiple_rejects_open {version : Version} {p : P}
    {token : Parser.Internal.Input} (htoken : token ≠ .parenOpen) :
    Outcome.Rejects version (ParenMultipleParser.new (H := H) p)
      [token] (pure () : PM H Unit)
      (.expected #[.token .parenOpen]) :=
  wraps_rejects parenMultiple_wraps (opened_rejects_open htoken)

/-- The list parser enclosed in `(` and `)` on a `(`, values and then tokens that its inner
parser rejects, not starting with `)`. -/
theorem parenMultiple_rejects_inner {version : Version} {p : P}
    {values : List (List Parser.Internal.Input × PM H R)} (hvalues : ValuesParse version p values)
    {tokens : List Parser.Internal.Input} {program : PM H Unit} {kind : SyntaxErrorKind}
    (h : Outcome.Rejects version p tokens program kind)
    (hfirst : ∃ token tokens', tokens = token :: tokens' ∧ token ≠ .parenClose) :
    Outcome.Rejects version (ParenMultipleParser.new (H := H) p)
      (.parenOpen :: (valuesTokens values ++ tokens))
      (do let _ ← values.mapM fun value => value.2; program) kind := by
  refine wraps_rejects parenMultiple_wraps
    (opened_rejects_inner (closedMultiple_rejects_inner hvalues h hfirst) ?_)
  obtain ⟨token, tokens', rfl, _⟩ := hfirst
  simp

/-- When the cursor holds exactly its `(`, the list parser enclosed in `(` and `)` continues, as a
parser that finishes on values and the `)`. -/
theorem parenMultiple_waits_open {version : Version} {p : P} :
    ∃ after : Unit → ParenMultipleParser H P,
      Outcome.Waits version (ParenMultipleParser.new (H := H) p)
        [.parenOpen]
        (pure () : PM H Unit) after ∧
      ∀ {values : List (List Parser.Internal.Input × PM H R)}, ValuesParse version p values →
        Outcome.Finishes version (after ()) (valuesTokens values ++ [.parenClose])
          ((fun results => results.toArray) <$> values.mapM fun value => value.2)
          (ParenMultipleParser.new p) := by
  obtain ⟨after, hwaits, hfin, _⟩ := opened_waits_after_open (H := H) (version := version)
    (p := ClosedMultipleParser.new (H := H) p)
  exact ⟨fun a => ⟨after a⟩, wraps_waits parenMultiple_wraps hwaits,
    fun hv => wraps_finishes parenMultiple_wraps (hfin (closedMultiple_parses hv))⟩

/-- When the cursor holds exactly its `(` and its values, at least one, the list parser enclosed
in `(` and `)` continues, as a parser that finishes on further values and the `)`. -/
theorem parenMultiple_waits_between {version : Version} {p : P}
    {values : List (List Parser.Internal.Input × PM H R)} (hvalues : ValuesParse version p values)
    (hne : values ≠ []) :
    ∃ after : List R → ParenMultipleParser H P,
      Outcome.Waits version (ParenMultipleParser.new (H := H) p)
        (.parenOpen :: valuesTokens values) (values.mapM fun value => value.2) after ∧
      ∀ found {values' : List (List Parser.Internal.Input × PM H R)},
        ValuesParse version p values' →
        Outcome.Finishes version (after found) (valuesTokens values' ++ [.parenClose])
          ((fun results => (found ++ results).toArray) <$> values'.mapM fun value => value.2)
          (ParenMultipleParser.new p) := by
  obtain ⟨after, hwaits, hfin, _⟩ := closedMultiple_waits_between hvalues
  have htok : valuesTokens values ≠ [] := by
    obtain ⟨value, values', rfl⟩ := List.exists_cons_of_ne_nil hne
    obtain ⟨_, token, tokens, hvalue, _⟩ := hvalues value (List.mem_cons_self ..)
    simp [valuesTokens, hvalue]
  obtain ⟨after', hwaits', hfin', _⟩ := opened_waits_inner hwaits htok
  exact ⟨fun a => ⟨after' a⟩, wraps_waits parenMultiple_wraps hwaits',
    fun found _ hv => wraps_finishes parenMultiple_wraps (hfin' found (hfin found hv))⟩

end

end BSmtLib.Facts.Proofs.Parser.Category.Multiple
