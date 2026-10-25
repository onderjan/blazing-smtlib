module

public import BSmtLib.Facts.Proofs.Parser.Category.Multiple
import all BSmtLib.Parser
import all BSmtLib.Parser.Category.Token
import all BSmtLib.Parser.Category.Combinator

@[expose] public section

/-!
# The list combinators with a maximum on a cursor

As the list combinators without a maximum (`Category.Multiple`), value by value; below the
maximum a token that is not a `)` starts the next value, and at the maximum it is an error.

A loop's turn is read through `turnThen`: what the turn answers when it stops, and a
continuation when it goes on. Both the first turn and the later ones are read so.
-/

namespace BSmtLib.Facts.Proofs.Parser.Category.Maximum

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
open BSmtLib.Facts.Proofs.Parser.Category.Multiple

/-! ## Turns -/

section

variable {H S R E : Type} {m : Type → Type} [Monad m] [LawfulMonad m] {Z : Type} [Cursor Z]

/-- A turn, read as `outcomeAny` reads its answer when it stops, and as `k` says when it goes
on. -/
def turnThen (turn : Internal.Turn H S R E Z m) (self : S) (state : ParseState H) (cursor : Z)
    (h : Cursor.HasNext cursor)
    (k : S → ParseState H → (next : Z) → Cursor.Consumed next cursor →
      StateT H m (Outcome R S Z E)) : StateT H m (Outcome R S Z E) :=
  turn self state cursor h >>= fun r => match r with
  | (some a, s, st, next) => pure (outcomeAny (a, s, st, next))
  | (none, s, st, ⟨next, taken⟩) => k s st next taken

/-- A loop's first turn, on a cursor with a token. -/
theorem parseByTurns_turnThen (turn : Internal.Turn H S R E Z m) (self : S)
    (state : ParseState H) (cursor : Z) (h : Cursor.HasNext cursor) :
    outcome <$> Internal.parseByTurns turn self state cursor =
      turnThen turn self state cursor h fun s st next taken =>
        outcomeAny <$> Internal.repeatTurns turn cursor s st next taken := by
  simp only [Internal.parseByTurns]
  split
  · rename_i hn _
    exact absurd h hn
  · rename_i h' _
    rw [map_bind, turnThen]
    refine bind_congr fun r => ?_
    obtain ⟨a, s, st, ⟨n, t⟩⟩ := r
    rcases a with _ | a
    · dsimp only
      rw [map_bind]
      conv => rhs; rw [← bind_pure (Internal.repeatTurns turn cursor s st n t), map_bind]
      refine bind_congr fun x => ?_
      obtain ⟨a, s', st', ⟨z, hz⟩⟩ := x
      rcases a with (_ | _) | (_ | _) <;> simp only [map_pure] <;> rfl
    · simp only [map_pure]
      rcases a with (_ | _) | (_ | _) <;> rfl

/-- A loop's later turn, on a cursor with a token. -/
theorem repeatTurns_turnThen (turn : Internal.Turn H S R E Z m) (origin : Z) (self : S)
    (state : ParseState H) (cursor : Z) (hc : Cursor.Consumed cursor origin)
    (h : Cursor.HasNext cursor) :
    outcomeAny <$> Internal.repeatTurns turn origin self state cursor hc =
      turnThen turn self state cursor h fun s st next taken =>
        outcomeAny <$> Internal.repeatTurns turn origin s st next
          (Cursor.consumed_trans taken hc) := by
  rw [Internal.repeatTurns]
  split
  · rename_i hn _
    exact absurd h hn
  · rename_i h' _
    rw [map_bind, turnThen]
    refine bind_congr fun r => ?_
    obtain ⟨a, s, st, ⟨n, t⟩⟩ := r
    rcases a with _ | a
    · rfl
    · simp only [map_pure]
      rcases a with (_ | _) | (_ | _) <;> rfl

/-- A loop's first turn on a cursor without a token: it wants more, as it is. -/
theorem parseByTurns_end (turn : Internal.Turn H S R E Z m) (self : S) (state : ParseState H)
    {cursor : Z} (hnone : Cursor.next? cursor = none) :
    outcome <$> Internal.parseByTurns turn self state cursor = pure (.waits self) := by
  simp only [Internal.parseByTurns]
  split
  · simp only [map_pure]
    rfl
  · rename_i h _
    exact absurd h (Parser.Internal.not_hasNext hnone)

/-- A loop's later turn on a cursor without a token: it wants more, as it is. -/
theorem repeatTurns_end (turn : Internal.Turn H S R E Z m) (origin : Z) (self : S)
    (state : ParseState H) {cursor : Z} (hc : Cursor.Consumed cursor origin)
    (hnone : Cursor.next? cursor = none) :
    outcomeAny <$> Internal.repeatTurns turn origin self state cursor hc =
      pure (.waits self) := by
  rw [Internal.repeatTurns]
  split
  · simp only [map_pure]
    rfl
  · rename_i h _
    exact absurd h (Parser.Internal.not_hasNext hnone)

end

/-! ## The turns of the list with a maximum -/

section

variable {H P R : Type} {m : Type → Type} [Monad m] [LawfulMonad m] [Handler H m]
  [Parse P H m (Handler.Error H) R]

/-- The list parser with a maximum between values, with the results so far. -/
private abbrev between (p : P) (maximum : Nat) (results : Array R) : ClosedMaximumParser H P :=
  { maximum, outside := true, results, inner := p }

/-- The first token of the cursor, taken by the tokens. -/
private theorem first_of_takes {version : Version} {Z : Type} [Cursor Z] {cursor next : Z}
    {token : Parser.Internal.Input} {tokens : List Parser.Internal.Input}
    (htakes : Takes version cursor (token :: tokens) next) :
    ∃ (h : Cursor.HasNext cursor) (raw : Cursor.Token Z) (after : Z)
      (consumed : Cursor.Consumed after cursor),
      Internal.firstToken cursor h = (raw, ⟨after, consumed⟩) ∧
      Parser.Internal.Input.ofSyntax (Cursor.syntax after raw) = token ∧
      Takes version after tokens next := by
  obtain ⟨after, raw, consumed, hn, hnext, hver, htoken, htail⟩ := Takes.cons_inv htakes
  have h := Takes.hasNext htakes
  exact ⟨h, raw, after, consumed, firstToken_eq hnext h, htoken, htail⟩

/-- A turn between values on a `)`: the list finishes with its results. -/
private theorem turn_close {version : Version} {p : P} {maximum : Nat} {Z : Type} [Cursor Z]
    {cursor next : Z} (results : Array R) (state : ParseState H)
    (htakes : Takes version cursor [.parenClose] next) (h : Cursor.HasNext cursor) (k) :
    turnThen ClosedMaximumParser.turn (between (H := H) p maximum results) state cursor h k =
      pure (.finished results (ClosedMaximumParser.new (H := H) p maximum) next) := by
  obtain ⟨h', raw, after, consumed, hfirst, htoken, htail⟩ := first_of_takes htakes
  rw [Takes.nil_inv htail]
  simp only [turnThen, ClosedMaximumParser.turn, ite_true, hfirst,
    ofSyntax_parenClose htoken]
  simp [outcomeAny, ClosedMaximumParser.new]

/-- A turn between values at the maximum on a token that is not `)`: the list rejects it. -/
private theorem turn_beyond {version : Version} {p : P} {maximum : Nat} {Z : Type} [Cursor Z]
    {cursor next : Z} {token : Parser.Internal.Input} (results : Array R)
    (hsize : maximum ≤ results.size) (htoken : token ≠ .parenClose) (state : ParseState H)
    (htakes : Takes version cursor [token] next) (h : Cursor.HasNext cursor) (k) :
    turnThen ClosedMaximumParser.turn (between (H := H) p maximum results) state cursor h k =
      pure (.rejected (.expected #[.token .parenClose]) next) := by
  obtain ⟨h', raw, after, consumed, hfirst, htoken', htail⟩ := first_of_takes htakes
  rw [Takes.nil_inv htail]
  simp only [turnThen, ClosedMaximumParser.turn, between, ite_true, hfirst, hsize]
  split
  · rename_i heq
    rw [heq] at htoken'
    exact absurd htoken'.symm htoken
  · simp only [pure_bind]
    rfl

/-- What a turn between values below the maximum does on tokens of the inner parser, which do
not start with `)`: it has the inner parser parse them. -/
private theorem turn_inner {p : P} {maximum : Nat} {Z : Type} [Cursor Z] {cursor : Z}
    {token : Parser.Internal.Input} {tokens : List Parser.Internal.Input} {version : Version}
    {last : Z} (htakes : Takes version cursor (token :: tokens) last)
    (htok : token ≠ .parenClose) (results : Array R) (hsize : results.size < maximum)
    (state : ParseState H) (h : Cursor.HasNext cursor) (k) :
    turnThen ClosedMaximumParser.turn (between (H := H) p maximum results) state cursor h k =
      Parse.parse p state cursor >>= fun x => match x with
        | (.error error, inner, state, ⟨later, taken⟩) =>
          pure (outcomeAny (.error error, ({ maximum, outside := false, results, inner } :
            ClosedMaximumParser H P), state, (⟨later, taken h⟩ :
              { z : Z // Cursor.Consumed z cursor })))
        | (.ok .continue, inner, state, ⟨later, taken⟩) =>
          pure (outcomeAny (.ok .continue, ({ maximum, outside := false, results, inner } :
            ClosedMaximumParser H P), state, (⟨later, taken h⟩ :
              { z : Z // Cursor.Consumed z cursor })))
        | (.ok (.break item), inner, state, ⟨later, taken⟩) =>
          k { maximum, outside := true, results := results.push item, inner } state later
            (taken h) := by
  obtain ⟨h', raw, after, consumed, hfirst, htoken, htail⟩ := first_of_takes htakes
  have hlt : ¬ maximum ≤ results.size := by omega
  simp only [turnThen, ClosedMaximumParser.turn, between, ite_true, hfirst, hlt, ite_false]
  split
  · rename_i heq
    rw [heq] at htoken
    exact absurd htoken.symm htok
  · simp only [bind_assoc]
    refine bind_congr fun x => ?_
    obtain ⟨a, inner, st, ⟨later, taken⟩⟩ := x
    rcases a with error | (_ | item) <;> simp

/-- A turn between values below the maximum on a value that does not start with `)`: the inner
parser's program, then the continuation with the result added. -/
private theorem turn_value {version : Version} {p : P} {maximum : Nat} {Z : Type} [Cursor Z]
    {cursor last : Z} {tokens : List Parser.Internal.Input} {program : PM H R}
    (hp : Outcome.Finishes version p tokens program p)
    (hfirst : ∃ token tokens', tokens = token :: tokens' ∧ token ≠ .parenClose)
    (rest : List Parser.Internal.Input) (htakes : Takes version cursor tokens last)
    (hreads : Reads version last rest) (results : Array R) (hsize : results.size < maximum)
    (state : ParseState H) (h : Cursor.HasNext cursor) (k) :
    turnThen ClosedMaximumParser.turn (between (H := H) p maximum results) state cursor h k =
      program.run >>= fun e => match e with
        | .ok item => k (between p maximum (results.push item)) .new last (Takes.consumed_of_ne
            htakes (by obtain ⟨_, _, rfl, _⟩ := hfirst; simp) h)
        | .error (.handler error) => pure (.failed error)
        | .error (.syntax kind) => pure (.rejected kind last)
        | .error (.version kind) => pure (.rejectedVersion kind last) := by
  obtain ⟨token, tokens', rfl, htok⟩ := hfirst
  obtain ⟨calls, hcalls⟩ := handler_run hp.1
  have hc := Takes.consumed htakes
  rw [turn_inner htakes htok results hsize state h k,
    bind_outcome_eq _ _ (.ok .continue, p, .new, ⟨last, fun _ => hc⟩) (by
      intro x
      obtain ⟨a, p', s, ⟨z, hz⟩⟩ := x
      answer_cases a
      · rw [show outcome (.error (ParseError.Internal.new (.syntax kind)), p', s, ⟨z, hz⟩) =
            .rejected kind z from rfl, onOutcome_rejected _ _ _ hz]
        rfl
      · rw [show outcome (.error (ParseError.Internal.new (.version kind)), p', s, ⟨z, hz⟩) =
            .rejectedVersion kind z from rfl, onOutcome_rejectedVersion _ _ _ hz]
        rfl
      · rfl
      · rfl
      · rw [show outcome (.ok (.break result), p', s, ⟨z, hz⟩) = .finished result p' z from rfl,
          onOutcome_finished _ _ _ _ hz, parseState_eq s .new]),
    hp.2 state cursor last rest htakes hreads, hcalls, Functor.map_map, bind_map_left]
  rw [bind_map_left]
  refine bind_congr fun e => ?_
  rcases e with error | item
  · simp [answer, onOutcome, outcomeAny]
  · simp only [answer]
    rw [onOutcome_finished _ _ _ _ (fun _ => hc)]

/-- A turn between values below the maximum on tokens that the inner parser rejects, not
starting with `)`: the list rejects them. -/
private theorem turn_rejects {version : Version} {p : P} {maximum : Nat} {Z : Type}
    [Cursor Z]
    {cursor next : Z} {tokens : List Parser.Internal.Input} {program : PM H Unit}
    {kind : SyntaxErrorKind} (hp : Outcome.Rejects version p tokens program kind)
    (hfirst : ∃ token tokens', tokens = token :: tokens' ∧ token ≠ .parenClose)
    (rest : List Parser.Internal.Input) (htakes : Takes version cursor tokens next)
    (hreads : Reads version next rest) (results : Array R) (hsize : results.size < maximum)
    (state : ParseState H) (h : Cursor.HasNext cursor) (k) :
    turnThen ClosedMaximumParser.turn (between (H := H) p maximum results) state cursor h k =
      answer (fun () => .rejected kind next) next <$> program.run := by
  obtain ⟨token, tokens', rfl, htok⟩ := hfirst
  obtain ⟨calls, hcalls⟩ := handler_run hp.1
  have hc := Takes.consumed htakes
  rw [turn_inner htakes htok results hsize state h k,
    bind_outcome_eq _ _ (.ok .continue, p, .new, ⟨next, fun _ => hc⟩) (by
      intro x
      obtain ⟨a, p', s, ⟨z, hz⟩⟩ := x
      answer_cases a
      · rw [show outcome (.error (ParseError.Internal.new (.syntax kind)), p', s, ⟨z, hz⟩) =
            .rejected kind z from rfl, onOutcome_rejected _ _ _ hz]
        rfl
      · rw [show outcome (.error (ParseError.Internal.new (.version kind)), p', s, ⟨z, hz⟩) =
            .rejectedVersion kind z from rfl, onOutcome_rejectedVersion _ _ _ hz]
        rfl
      · rfl
      · rfl
      · rw [show outcome (.ok (.break result), p', s, ⟨z, hz⟩) = .finished result p' z from rfl,
          onOutcome_finished _ _ _ _ hz, parseState_eq s .new]),
    hp.2 state cursor next rest htakes hreads, hcalls, Functor.map_map, bind_map_left]
  conv => rhs; rw [Functor.map_map, map_eq_pure_bind]
  refine bind_congr fun e => ?_
  rcases e with error | ⟨⟩
  · simp [answer, onOutcome, outcomeAny]
  · simp only [answer]
    rw [onOutcome_rejected _ _ _ (fun _ => hc)]
    rfl

/-- A turn between values below the maximum on tokens on which the inner parser wants more, not
starting with `)`: the list wants more, within a value. -/
private theorem turn_waits {version : Version} {p : P} {maximum : Nat} {Z : Type} [Cursor Z]
    {cursor final : Z} {tokens : List Parser.Internal.Input} {α : Type} {program : PM H α}
    {after : α → P} (hp : Outcome.Waits version p tokens program after)
    (hfirst : ∃ token tokens', tokens = token :: tokens' ∧ token ≠ .parenClose)
    (htakes : Takes version cursor tokens final) (hnone : Cursor.next? final = none)
    (results : Array R) (hsize : results.size < maximum) (state : ParseState H)
    (h : Cursor.HasNext cursor) (k) :
    turnThen ClosedMaximumParser.turn (between (H := H) p maximum results) state cursor h k =
      answer (fun a => .waits ({ maximum, outside := false, results, inner := after a } :
        ClosedMaximumParser H P)) final <$> program.run := by
  obtain ⟨token, tokens', rfl, htok⟩ := hfirst
  obtain ⟨calls, hcalls⟩ := handler_run hp.1
  have hc := Takes.consumed htakes
  rw [turn_inner htakes htok results hsize state h k,
    bind_outcome_eq _ _ (.ok .continue, p, .new, ⟨final, fun _ => hc⟩) (by
      intro x
      obtain ⟨a, p', s, ⟨z, hz⟩⟩ := x
      answer_cases a
      · rw [show outcome (.error (ParseError.Internal.new (.syntax kind)), p', s, ⟨z, hz⟩) =
            .rejected kind z from rfl, onOutcome_rejected _ _ _ hz]
        rfl
      · rw [show outcome (.error (ParseError.Internal.new (.version kind)), p', s, ⟨z, hz⟩) =
            .rejectedVersion kind z from rfl, onOutcome_rejectedVersion _ _ _ hz]
        rfl
      · rfl
      · rfl
      · rw [show outcome (.ok (.break result), p', s, ⟨z, hz⟩) = .finished result p' z from rfl,
          onOutcome_finished _ _ _ _ hz, parseState_eq s .new]),
    hp.2 state cursor final htakes hnone, hcalls, Functor.map_map, bind_map_left]
  conv => rhs; rw [Functor.map_map, map_eq_pure_bind]
  refine bind_congr fun e => ?_
  rcases e with error | a <;> simp [answer, onOutcome, outcomeAny]


/-! ## The loop -/

omit [Monad m] [LawfulMonad m] in
private theorem value_ne {value : List Parser.Internal.Input × PM H R}
    (hfirst : ∃ token tokens, value.1 = token :: tokens ∧ token ≠ .parenClose) :
    value.1 ≠ [] := by
  obtain ⟨_, _, h, _⟩ := hfirst
  simp [h]

/-- The values, then what the loop does at the cursor after them, with the results it has. -/
private theorem maximum_loop {version : Version} {p : P} {maximum target : Nat}
    {Z : Type} [Cursor Z] {origin last : Z}
    (finale : Array R →
      StateT H m (Outcome (Array R) (ClosedMaximumParser H P) Z (Handler.Error H)))
    (hfinale : ∀ (results : Array R) (state : ParseState H) (hc : Cursor.Consumed last origin),
      results.size = target →
      outcomeAny <$> Internal.repeatTurns ClosedMaximumParser.turn origin
          (between (H := H) p maximum results) state last hc = finale results) :
    (values : List (List Parser.Internal.Input × PM H R)) → ValuesParse version p values →
    (results : Array R) → results.size + values.length = target → target ≤ maximum →
    (state : ParseState H) → (cursor : Z) → (hc : Cursor.Consumed cursor origin) →
    (rest : List Parser.Internal.Input) →
    Takes version cursor (valuesTokens values) last → Reads version last rest →
    outcomeAny <$> Internal.repeatTurns ClosedMaximumParser.turn origin
        (between (H := H) p maximum results) state cursor hc =
      (values.mapM fun (value : List Parser.Internal.Input × PM H R) => value.2).run >>= fun e =>
        match e with
        | .ok found => finale (results ++ found.toArray)
        | .error (.handler error) => pure (.failed error)
        | .error (.syntax kind) => pure (.rejected kind last)
        | .error (.version kind) => pure (.rejectedVersion kind last)
  | [], _, results, hsize, _, state, cursor, hc, rest, htakes, hreads => by
    have e := Takes.nil_inv htakes
    subst e
    rw [hfinale results state hc (by simpa using hsize)]
    simp
  | value :: values, hvalues, results, hsize, hmax, state, cursor, hc, rest, htakes, hreads => by
    obtain ⟨hparses, hfirst⟩ := hvalues value (List.mem_cons_self ..)
    obtain ⟨calls, hcalls⟩ := handler_run hparses.1
    simp only [valuesTokens, List.flatMap_cons] at htakes
    obtain ⟨middle, ht₁, ht₂⟩ := Takes.split htakes
    rw [repeatTurns_turnThen _ _ _ _ _ hc (Takes.hasNext_of_ne ht₁ (value_ne hfirst)),
      turn_value hparses hfirst _ ht₁ (Reads.of_takes ht₂ hreads) results
        (by simp only [List.length_cons] at hsize; omega) state _ _,
      List.mapM_cons, ExceptT.run_bind, hcalls, bind_map_left, bind_map_left, bind_assoc]
    refine bind_congr fun e => ?_
    rcases e with error | result
    · simp
    · dsimp only
      rw [maximum_loop finale hfinale values
        (fun v hv => hvalues v (List.mem_cons_of_mem _ hv)) (results.push result)
        (by simp only [List.length_cons, Array.size_push] at hsize ⊢; omega) hmax
        ParseState.new middle _ rest ht₂ hreads]
      simp only [ExceptT.run_bind, ExceptT.run_pure, bind_assoc]
      refine bind_congr fun e => ?_
      rcases e with (kind | kind | error) | found <;> simp

/-- The parse of a list with a maximum that has a first value: the values, then what the loop
does at the cursor after them. -/
private theorem maximum_first {version : Version} {p : P} {maximum target : Nat}
    {Z : Type} [Cursor Z] {cursor last : Z}
    (finale : Array R →
      StateT H m (Outcome (Array R) (ClosedMaximumParser H P) Z (Handler.Error H)))
    (hfinale : ∀ (results : Array R) (state : ParseState H) (hc : Cursor.Consumed last cursor),
      results.size = target →
      outcomeAny <$> Internal.repeatTurns ClosedMaximumParser.turn cursor
          (between (H := H) p maximum results) state last hc = finale results)
    (value : List Parser.Internal.Input × PM H R)
    (values : List (List Parser.Internal.Input × PM H R))
    (hvalues : ValuesParse version p (value :: values)) (results : Array R)
    (hsize : results.size + values.length + 1 = target) (hmax : target ≤ maximum)
    (state : ParseState H) (rest : List Parser.Internal.Input)
    (htakes : Takes version cursor (valuesTokens (value :: values)) last)
    (hreads : Reads version last rest) :
    outcome <$> Parse.parse (between (H := H) p maximum results) state cursor =
      ((value :: values).mapM fun (value : List Parser.Internal.Input × PM H R) => value.2).run >>=
        fun e => match e with
        | .ok found => finale (results ++ found.toArray)
        | .error (.handler error) => pure (.failed error)
        | .error (.syntax kind) => pure (.rejected kind last)
        | .error (.version kind) => pure (.rejectedVersion kind last) := by
  obtain ⟨hparses, hfirst⟩ := hvalues value (List.mem_cons_self ..)
  obtain ⟨calls, hcalls⟩ := handler_run hparses.1
  simp only [valuesTokens, List.flatMap_cons] at htakes
  obtain ⟨middle, ht₁, ht₂⟩ := Takes.split htakes
  rw [show Parse.parse (between (H := H) p maximum results) state cursor =
      Internal.parseByTurns ClosedMaximumParser.turn (between (H := H) p maximum results) state
        cursor from rfl,
    parseByTurns_turnThen _ _ _ _ (Takes.hasNext_of_ne ht₁ (value_ne hfirst)),
    turn_value hparses hfirst _ ht₁ (Reads.of_takes ht₂ hreads) results (by omega) state _ _,
    List.mapM_cons, ExceptT.run_bind, hcalls, bind_map_left, bind_map_left, bind_assoc]
  refine bind_congr fun e => ?_
  rcases e with error | result
  · simp
  · dsimp only
    rw [maximum_loop finale hfinale values
      (fun v hv => hvalues v (List.mem_cons_of_mem _ hv)) (results.push result)
      (by simp only [Array.size_push]; omega) hmax ParseState.new middle _ rest ht₂ hreads]
    simp only [ExceptT.run_bind, ExceptT.run_pure, bind_assoc]
    refine bind_congr fun e => ?_
    rcases e with (kind | kind | error) | found <;> simp

omit [LawfulMonad m] in
private theorem between_parse_eq (p : P) (maximum : Nat) (results : Array R) {Z : Type}
    [Cursor Z] (state : ParseState H) (cursor : Z) :
    Parse.parse (between (H := H) p maximum results) state cursor =
      Internal.parseByTurns ClosedMaximumParser.turn (between (H := H) p maximum results) state
        cursor := rfl


/-! ## From a state between values -/

private theorem results_finishes {version : Version} {p : P} {maximum : Nat}
    {values : List (List Parser.Internal.Input × PM H R)} (hvalues : ValuesParse version p values)
    (results : Array R) (hlength : results.size + values.length ≤ maximum) :
    Outcome.Finishes version (between (H := H) p maximum results)
      (valuesTokens values ++ [.parenClose])
      ((fun found => results ++ found.toArray) <$> values.mapM fun value => value.2)
      (ClosedMaximumParser.new (H := H) p maximum) := by
  have hho := values_handlerOnly hvalues
  refine ⟨handlerOnly_map _ hho, fun state cursor next rest htakes hreads => ?_⟩
  obtain ⟨calls, hcalls⟩ := handler_run hho
  obtain ⟨last, ht₁, ht₂⟩ := Takes.split htakes
  cases values with
  | nil =>
    rw [Takes.nil_inv ht₁] at ht₂
    rw [between_parse_eq, parseByTurns_turnThen _ _ _ _ (Takes.hasNext ht₂),
      turn_close results state ht₂]
    simp [answer]
  | cons value values =>
    rw [maximum_first (fun results => pure (.finished results (ClosedMaximumParser.new p maximum)
        next))
      (fun results state hc _ => by
        rw [repeatTurns_turnThen _ _ _ _ _ hc (Takes.hasNext ht₂), turn_close results state ht₂])
      value values hvalues results rfl (by simpa [Nat.add_assoc] using hlength) state
      ([.parenClose] ++ rest) ht₁ (Reads.of_takes ht₂ hreads),
      ExceptT.run_map, hcalls, bind_map_left, Functor.map_map, Functor.map_map]
    conv => rhs; rw [map_eq_pure_bind]
    refine bind_congr fun e => ?_
    rcases e with error | found <;> rfl

private theorem results_rejects_beyond {version : Version} {p : P} {maximum : Nat}
    {values : List (List Parser.Internal.Input × PM H R)} (hvalues : ValuesParse version p values)
    (results : Array R) (hlength : results.size + values.length = maximum)
    {token : Parser.Internal.Input} (htoken : token ≠ .parenClose) :
    Outcome.Rejects version (between (H := H) p maximum results) (valuesTokens values ++ [token])
      (do let _ ← values.mapM fun value => value.2; pure ()) (.expected #[.token .parenClose]) := by
  have hho := values_handlerOnly hvalues
  refine ⟨handlerOnly_bind hho fun _ => by handler_only,
    fun state cursor next rest htakes hreads => ?_⟩
  obtain ⟨calls, hcalls⟩ := handler_run hho
  obtain ⟨last, ht₁, ht₂⟩ := Takes.split htakes
  cases values with
  | nil =>
    rw [Takes.nil_inv ht₁] at ht₂
    rw [between_parse_eq, parseByTurns_turnThen _ _ _ _ (Takes.hasNext ht₂),
      turn_beyond results (by simp at hlength; omega) htoken state ht₂]
    simp [answer]
  | cons value values =>
    rw [maximum_first (fun _ => pure (.rejected (.expected #[.token .parenClose]) next))
      (fun results' state hc hsize => by
        rw [repeatTurns_turnThen _ _ _ _ _ hc (Takes.hasNext ht₂),
          turn_beyond results' (by simp only [List.length_cons] at hlength; omega) htoken
            state ht₂])
      value values hvalues results rfl (by simp at hlength; omega) state
      ([token] ++ rest) ht₁ (Reads.of_takes ht₂ hreads),
      ExceptT.run_bind, hcalls]
    simp only [bind_map_left, map_bind]
    refine bind_congr fun e => ?_
    rcases e with error | found <;> simp [answer]

private theorem results_rejects_inner {version : Version} {p : P} {maximum : Nat}
    {values : List (List Parser.Internal.Input × PM H R)} (hvalues : ValuesParse version p values)
    (results : Array R) (hlength : results.size + values.length < maximum)
    {tokens : List Parser.Internal.Input} {program : PM H Unit} {kind : SyntaxErrorKind}
    (h : Outcome.Rejects version p tokens program kind)
    (hfirst : ∃ token tokens', tokens = token :: tokens' ∧ token ≠ .parenClose) :
    Outcome.Rejects version (between (H := H) p maximum results) (valuesTokens values ++ tokens)
      (do let _ ← values.mapM fun value => value.2; program) kind := by
  have hho := values_handlerOnly hvalues
  have hne : tokens ≠ [] := by
    obtain ⟨_, _, rfl, _⟩ := hfirst
    simp
  refine ⟨handlerOnly_bind hho fun _ => h.1, fun state cursor next rest htakes hreads => ?_⟩
  obtain ⟨calls, hcalls⟩ := handler_run hho
  obtain ⟨last, ht₁, ht₂⟩ := Takes.split htakes
  cases values with
  | nil =>
    rw [Takes.nil_inv ht₁] at ht₂
    rw [between_parse_eq, parseByTurns_turnThen _ _ _ _ (Takes.hasNext_of_ne ht₂ hne),
      turn_rejects h hfirst rest ht₂ hreads results (by simpa using hlength) state]
    simp
  | cons value values =>
    rw [maximum_first (fun _ => answer (fun () => .rejected kind next) next <$> program.run)
      (fun results' state hc hsize => by
        rw [repeatTurns_turnThen _ _ _ _ _ hc (Takes.hasNext_of_ne ht₂ hne),
          turn_rejects h hfirst rest ht₂ hreads results'
            (by simp only [List.length_cons] at hlength; omega) state])
      value values hvalues results rfl (by simp at hlength; omega) state
      (tokens ++ rest) ht₁ (Reads.of_takes ht₂ hreads),
      hcalls, bind_map_left, answer_run_bind hcalls]
    refine bind_congr fun e => ?_
    rcases e with error | found <;> rfl

private theorem results_waits_end {version : Version} {p : P} {maximum : Nat}
    {values : List (List Parser.Internal.Input × PM H R)} (hvalues : ValuesParse version p values)
    (results : Array R) (hlength : results.size + values.length ≤ maximum) :
    Outcome.Waits version (between (H := H) p maximum results) (valuesTokens values)
      (values.mapM fun value => value.2)
      fun found => between p maximum (results ++ found.toArray) := by
  have hho := values_handlerOnly hvalues
  refine ⟨hho, fun state cursor last htakes hnone => ?_⟩
  obtain ⟨calls, hcalls⟩ := handler_run hho
  cases values with
  | nil =>
    rw [Takes.nil_inv htakes] at hnone
    rw [between_parse_eq, parseByTurns_end _ _ _ hnone]
    simp [answer]
  | cons value values =>
    rw [maximum_first (fun results => pure (.waits (between p maximum results)))
      (fun results' state hc _ => repeatTurns_end _ _ _ state hc hnone)
      value values hvalues results rfl (by simpa [Nat.add_assoc] using hlength) state []
      htakes ⟨last, .nil last, hnone⟩, hcalls, bind_map_left, Functor.map_map]
    conv => rhs; rw [map_eq_pure_bind]
    refine bind_congr fun e => ?_
    rcases e with error | found <;> rfl


/-! ## The list closed by `)` -/

/-- The closed list parser with a maximum on at most the maximum of values and the `)` after
them. -/
theorem closedMaximum_parses {version : Version} {p : P} {maximum : Nat}
    {values : List (List Parser.Internal.Input × PM H R)} (hvalues : ValuesParse version p values)
    (hlength : values.length ≤ maximum) :
    Outcome.Finishes version (ClosedMaximumParser.new (H := H) p maximum)
      (valuesTokens values ++ [.parenClose])
      ((fun results => results.toArray) <$> values.mapM fun value => value.2)
      (ClosedMaximumParser.new p maximum) := by
  have := results_finishes hvalues #[] (by simpa using hlength)
  simpa [between, ClosedMaximumParser.new] using this

/-- The closed list parser with a maximum on the maximum of values and a token after them that
is not `)`: it rejects that token. -/
theorem closedMaximum_rejects_beyond {version : Version} {p : P} {maximum : Nat}
    {values : List (List Parser.Internal.Input × PM H R)} (hvalues : ValuesParse version p values)
    (hlength : values.length = maximum) {token : Parser.Internal.Input}
    (htoken : token ≠ .parenClose) :
    Outcome.Rejects version (ClosedMaximumParser.new (H := H) p maximum)
      (valuesTokens values ++ [token])
      (do let _ ← values.mapM fun value => value.2; pure ()) (.expected #[.token .parenClose]) :=
  results_rejects_beyond hvalues #[] (by simpa using hlength) htoken

/-- The closed list parser with a maximum on fewer values than the maximum and then tokens that
its inner parser rejects, not starting with `)`. -/
theorem closedMaximum_rejects_inner {version : Version} {p : P} {maximum : Nat}
    {values : List (List Parser.Internal.Input × PM H R)} (hvalues : ValuesParse version p values)
    (hlength : values.length < maximum) {tokens : List Parser.Internal.Input}
    {program : PM H Unit} {kind : SyntaxErrorKind}
    (h : Outcome.Rejects version p tokens program kind)
    (hfirst : ∃ token tokens', tokens = token :: tokens' ∧ token ≠ .parenClose) :
    Outcome.Rejects version (ClosedMaximumParser.new (H := H) p maximum)
      (valuesTokens values ++ tokens)
      (do let _ ← values.mapM fun value => value.2; program) kind :=
  results_rejects_inner hvalues #[] (by simpa using hlength) h hfirst

/--
The closed list parser with a maximum on at most the maximum of values and no more: it wants
more, as a parser that holds the maximum and the results so far. A maximum set on it applies to
the values after them: it finishes on as many further values as the maximum leaves and the `)`,
and rejects a token not `)` after values that reach the maximum.
-/
theorem closedMaximum_waits_between {version : Version} {p : P}
    {values : List (List Parser.Internal.Input × PM H R)} (hvalues : ValuesParse version p values) :
    ∃ after : Nat → List R → ClosedMaximumParser H P,
      (∀ maximum found n, (after maximum found).setMaxElements n = after n found) ∧
      (∀ maximum, values.length ≤ maximum →
        Outcome.Waits version (ClosedMaximumParser.new (H := H) p maximum) (valuesTokens values)
          (values.mapM fun value => value.2) (after maximum)) ∧
      (∀ maximum found {values' : List (List Parser.Internal.Input × PM H R)},
        ValuesParse version p values' → found.length + values'.length ≤ maximum →
        Outcome.Finishes version (after maximum found) (valuesTokens values' ++ [.parenClose])
          ((fun results => (found ++ results).toArray) <$> values'.mapM fun value => value.2)
          (ClosedMaximumParser.new p maximum)) ∧
      (∀ maximum found {values' : List (List Parser.Internal.Input × PM H R)}
        {token : Parser.Internal.Input},
        ValuesParse version p values' → found.length + values'.length = maximum →
        token ≠ .parenClose →
        Outcome.Rejects version (after maximum found) (valuesTokens values' ++ [token])
          (do let _ ← values'.mapM fun value => value.2; pure ())
          (.expected #[.token .parenClose])) := by
  refine ⟨fun maximum found => between p maximum found.toArray, fun _ _ _ => rfl,
    fun maximum hlength => ?_, fun maximum found _ hv hlength => ?_,
    fun maximum found _ _ hv hlength htoken => ?_⟩
  · have := results_waits_end hvalues #[] (maximum := maximum) (by simpa using hlength)
    simpa [between, ClosedMaximumParser.new] using this
  · have := results_finishes hv found.toArray (by simpa using hlength)
    simpa using this
  · exact results_rejects_beyond hv found.toArray (by simpa using hlength) htoken

omit [Monad m] [LawfulMonad m] in
/-- Setting the maximum of a closed list parser with a maximum before its first value: the
parser with the new maximum. -/
theorem closedMaximum_setMaximum_new (p : P) (maximum n : Nat) :
    (ClosedMaximumParser.new (H := H) p maximum).setMaxElements n =
      ClosedMaximumParser.new (H := H) p n := by rfl

omit [Monad m] [LawfulMonad m] in
/-- The maximum of a closed list parser with a maximum. -/
theorem closedMaximum_maxElements_new (p : P) (maximum : Nat) :
    (ClosedMaximumParser.new (H := H) p maximum).maxElements = maximum := by rfl

/-! ## Within a value -/

/-- The list parser with a maximum within a value, with the results so far. -/
private abbrev within (maximum : Nat) (results : Array R) (q : P) :
    ClosedMaximumParser H P :=
  { maximum, outside := false, results, inner := q }

private theorem results_waits_inner {version : Version} {p : P} {maximum : Nat}
    {values : List (List Parser.Internal.Input × PM H R)} (hvalues : ValuesParse version p values)
    (results : Array R) (hlength : results.size + values.length < maximum)
    {tokens : List Parser.Internal.Input} {α : Type} {program : PM H α} {after : α → P}
    (h : Outcome.Waits version p tokens program after)
    (hfirst : ∃ token tokens', tokens = token :: tokens' ∧ token ≠ .parenClose) :
    Outcome.Waits version (between (H := H) p maximum results) (valuesTokens values ++ tokens)
      (do let found ← values.mapM fun value => value.2; let a ← program; pure (found, a))
      fun x => within (H := H) maximum (results ++ x.1.toArray) (after x.2) := by
  have hho := values_handlerOnly hvalues
  have hne : tokens ≠ [] := by
    obtain ⟨_, _, rfl, _⟩ := hfirst
    simp
  refine ⟨handlerOnly_bind hho fun _ => handlerOnly_bind h.1 fun _ => handlerOnly_pure _,
    fun state cursor final htakes hnone => ?_⟩
  obtain ⟨calls, hcalls⟩ := handler_run hho
  obtain ⟨calls₂, hcalls₂⟩ := handler_run h.1
  obtain ⟨last, ht₁, ht₂⟩ := Takes.split htakes
  cases values with
  | nil =>
    rw [Takes.nil_inv ht₁] at ht₂
    rw [between_parse_eq, parseByTurns_turnThen _ _ _ _ (Takes.hasNext_of_ne ht₂ hne),
      turn_waits h hfirst ht₂ hnone results (by simpa using hlength) state]
    simp only [List.mapM_nil, pure_bind, ExceptT.run_bind, ExceptT.run_pure]
    rw [hcalls₂]
    simp only [pure_bind, map_eq_pure_bind, bind_assoc]
    refine bind_congr fun e => ?_
    rcases e with error | a <;> simp [answer]
  | cons value values =>
    rw [maximum_first (fun results => answer (fun a => Outcome.waits
        ({ maximum, outside := false, results, inner := after a } : ClosedMaximumParser H P))
        final <$> program.run)
      (fun results' state hc hsize => by
        rw [repeatTurns_turnThen _ _ _ _ _ hc (Takes.hasNext_of_ne ht₂ hne),
          turn_waits h hfirst ht₂ hnone results'
            (by simp only [List.length_cons] at hlength; omega) state])
      value values hvalues results rfl (by simp only [List.length_cons] at hlength; omega) state
      tokens ht₁ (by simpa using Reads.of_takes ht₂ ⟨final, .nil final, hnone⟩),
      hcalls, bind_map_left, answer_run_bind hcalls]
    refine bind_congr fun e => ?_
    rcases e with error | found
    · rfl
    · simp only [map_eq_pure_bind, bind_assoc, ExceptT.run_bind, ExceptT.run_pure]
      rw [hcalls₂]
      simp only [bind_map_left]
      refine bind_congr fun e => ?_
      rcases e with error | a <;> simp [answer]

/-- A turn within a value: the inner parser parses on. -/
private theorem turn_resume {q : P} {maximum : Nat} {Z : Type} [Cursor Z] {cursor : Z}
    (results : Array R) (state : ParseState H) (h : Cursor.HasNext cursor) (k) :
    turnThen ClosedMaximumParser.turn
        ({ maximum, outside := false, results, inner := q } : ClosedMaximumParser H P) state
        cursor h k =
      Parse.parse q state cursor >>= fun x => match x with
        | (.error error, inner, state, ⟨later, taken⟩) =>
          pure (outcomeAny (.error error, ({ maximum, outside := false, results, inner } :
            ClosedMaximumParser H P), state, (⟨later, taken h⟩ :
              { z : Z // Cursor.Consumed z cursor })))
        | (.ok .continue, inner, state, ⟨later, taken⟩) =>
          pure (outcomeAny (.ok .continue, ({ maximum, outside := false, results, inner } :
            ClosedMaximumParser H P), state, (⟨later, taken h⟩ :
              { z : Z // Cursor.Consumed z cursor })))
        | (.ok (.break item), inner, state, ⟨later, taken⟩) =>
          k { maximum, outside := true, results := results.push item, inner } state later
            (taken h) := by
  simp only [turnThen, ClosedMaximumParser.turn, Bool.false_eq_true, ite_false]
  simp only [bind_assoc]
  refine bind_congr fun x => ?_
  obtain ⟨a, inner, st, ⟨later, taken⟩⟩ := x
  rcases a with error | (_ | item) <;> simp

/-- A turn within a value that the inner parser finishes, back as `p`: the inner parser's
program, then the continuation with the result added. -/
private theorem turn_resume_value {version : Version} {p q : P} {maximum : Nat} {Z : Type}
    [Cursor Z] {cursor last : Z} {tokens : List Parser.Internal.Input} {program : PM H R}
    (hq : Outcome.Finishes version q tokens program p) (hne : tokens ≠ [])
    (rest : List Parser.Internal.Input) (htakes : Takes version cursor tokens last)
    (hreads : Reads version last rest) (results : Array R) (state : ParseState H)
    (h : Cursor.HasNext cursor) (k) :
    turnThen ClosedMaximumParser.turn
        ({ maximum, outside := false, results, inner := q } : ClosedMaximumParser H P) state
        cursor h k =
      program.run >>= fun e => match e with
        | .ok item => k (between p maximum (results.push item)) .new last
            (Takes.consumed_of_ne htakes hne h)
        | .error (.handler error) => pure (.failed error)
        | .error (.syntax kind) => pure (.rejected kind last)
        | .error (.version kind) => pure (.rejectedVersion kind last) := by
  obtain ⟨calls, hcalls⟩ := handler_run hq.1
  have hc := Takes.consumed_of_ne htakes hne
  rw [turn_resume results state h k,
    bind_outcome_eq _ _ (.ok .continue, q, .new, ⟨last, hc⟩) (by
      intro x
      obtain ⟨a, p', s, ⟨z, hz⟩⟩ := x
      answer_cases a
      · rw [show outcome (.error (ParseError.Internal.new (.syntax kind)), p', s, ⟨z, hz⟩) =
            .rejected kind z from rfl, onOutcome_rejected _ _ _ hz]
        rfl
      · rw [show outcome (.error (ParseError.Internal.new (.version kind)), p', s, ⟨z, hz⟩) =
            .rejectedVersion kind z from rfl, onOutcome_rejectedVersion _ _ _ hz]
        rfl
      · rfl
      · rfl
      · rw [show outcome (.ok (.break result), p', s, ⟨z, hz⟩) = .finished result p' z from rfl,
          onOutcome_finished _ _ _ _ hz, parseState_eq s .new]),
    hq.2 state cursor last rest htakes hreads, hcalls, Functor.map_map, bind_map_left]
  rw [bind_map_left]
  refine bind_congr fun e => ?_
  rcases e with error | item
  · simp [answer, onOutcome, outcomeAny]
  · simp only [answer]
    rw [onOutcome_finished _ _ _ _ hc]

/-- Within a value that the inner parser finishes, then further values and the `)`: the list
finishes with them. -/
private theorem results_resume_finishes {version : Version} {p q : P} {maximum : Nat}
    {tokens : List Parser.Internal.Input} {program : PM H R}
    (hq : Outcome.Finishes version q tokens program p) (hne : tokens ≠ [])
    {values : List (List Parser.Internal.Input × PM H R)} (hvalues : ValuesParse version p values)
    (results : Array R) (hlength : results.size + 1 + values.length ≤ maximum) :
    Outcome.Finishes version
      ({ maximum, outside := false, results, inner := q } : ClosedMaximumParser H P)
      (tokens ++ valuesTokens values ++ [.parenClose])
      ((fun found => results ++ found.toArray) <$> (program >>= fun first =>
        (values.mapM fun value => value.2) >>= fun others => pure (first :: others)))
      (ClosedMaximumParser.new (H := H) p maximum) := by
  have hho := values_handlerOnly hvalues
  refine ⟨handlerOnly_map _ (handlerOnly_bind hq.1 fun _ =>
    handlerOnly_bind hho fun _ => handlerOnly_pure _), fun state cursor next rest htakes
      hreads => ?_⟩
  obtain ⟨calls, hcalls⟩ := handler_run hq.1
  obtain ⟨calls₂, hcalls₂⟩ := handler_run hho
  obtain ⟨middle, ht₁, ht₂⟩ := Takes.split htakes
  obtain ⟨last, ht₃, ht₄⟩ := Takes.split ht₁
  rw [show Parse.parse ({ maximum, outside := false, results, inner := q } :
      ClosedMaximumParser H P) state cursor = Internal.parseByTurns ClosedMaximumParser.turn
        ({ maximum, outside := false, results, inner := q } : ClosedMaximumParser H P) state
        cursor from rfl,
    parseByTurns_turnThen _ _ _ _ (Takes.hasNext_of_ne ht₃ hne),
    turn_resume_value hq hne _ ht₃ (Reads.of_takes (Takes.append ht₄ ht₂) hreads) results
      state _ _]
  have hloop := fun (r : Array R) (hr : r.size = results.size + 1) =>
    maximum_loop (origin := cursor) (target := results.size + 1 + values.length)
      (fun results => pure (.finished results (ClosedMaximumParser.new p maximum) next))
      (fun results state hc _ => by
        rw [repeatTurns_turnThen _ _ _ _ _ hc (Takes.hasNext ht₂), turn_close results state ht₂])
      values hvalues r (by omega) hlength ParseState.new last
  rw [ExceptT.run_map, ExceptT.run_bind, hcalls]
  simp only [bind_map_left, map_bind]
  refine bind_congr fun e => ?_
  rcases e with error | first
  · simp [answer, Except.map]
  · dsimp only
    rw [hloop (results.push first) (by simp) _ ([.parenClose] ++ rest) ht₄
      (Reads.of_takes ht₂ hreads), ExceptT.run_bind, hcalls₂, bind_map_left, map_bind,
      bind_map_left]
    rw [map_bind]
    refine bind_congr fun e => ?_
    rcases e with error | others <;> simp [answer, Except.map]

/--
The closed list parser with a maximum on fewer values than the maximum and then tokens on which
its inner parser wants more, not starting with `)`: it wants more, as a parser that holds the
maximum, the results so far and the inner parser within its value. A maximum set on it applies
to the values after that value; it finishes once the inner parser finishes the value and as many
further values as the maximum leaves and the `)` follow.
-/
theorem closedMaximum_waits_inner {version : Version} {p : P}
    {values : List (List Parser.Internal.Input × PM H R)} (hvalues : ValuesParse version p values)
    {tokens : List Parser.Internal.Input} {α : Type} {program : PM H α} {after : α → P}
    (h : Outcome.Waits version p tokens program after)
    (hfirst : ∃ token tokens', tokens = token :: tokens' ∧ token ≠ .parenClose) :
    ∃ after' : Nat → List R × α → ClosedMaximumParser H P,
      (∀ maximum x n, (after' maximum x).setMaxElements n = after' n x) ∧
      (∀ maximum, values.length < maximum →
        Outcome.Waits version (ClosedMaximumParser.new (H := H) p maximum)
          (valuesTokens values ++ tokens)
          (do let found ← values.mapM fun value => value.2; let a ← program; pure (found, a))
          (after' maximum)) ∧
      ∀ maximum found a {tokens' : List Parser.Internal.Input} {program' : PM H R}
        {values' : List (List Parser.Internal.Input × PM H R)},
        Outcome.Finishes version (after a) tokens' program' p → tokens' ≠ [] →
        ValuesParse version p values' → found.length + 1 + values'.length ≤ maximum →
        Outcome.Finishes version (after' maximum (found, a))
          (tokens' ++ valuesTokens values' ++ [.parenClose])
          ((fun results => (found ++ results).toArray) <$> (program' >>= fun first =>
            (values'.mapM fun value => value.2) >>= fun others => pure (first :: others)))
          (ClosedMaximumParser.new p maximum) := by
  refine ⟨fun maximum x =>
    { maximum, outside := false, results := x.1.toArray, inner := after x.2 },
    fun _ _ _ => rfl, fun maximum hlength => ?_,
    fun maximum found a _ _ _ hq hne hv hlength => ?_⟩
  · have := results_waits_inner hvalues #[] (maximum := maximum) (by simpa using hlength) h
      hfirst
    simpa [between, ClosedMaximumParser.new] using this
  · have := results_resume_finishes hq hne hv found.toArray (by simpa using hlength)
    simpa [Functor.map_map] using this

/-! ## The list with its own `(` -/

private def parenF {Z : Type} :
    Outcome (Array R) (ClosedMaximumParser H P) Z (Handler.Error H) →
    Outcome (Array R) (ParenMaximumParser H P) Z (Handler.Error H)
  | .finished results q next => .finished results ⟨false, q⟩ next
  | .waits q => .waits ⟨true, q⟩
  | .rejected kind next => .rejected kind next
  | .rejectedVersion kind next => .rejectedVersion kind next
  | .failed error => .failed error

/-- The parse of a list with a maximum and its own `(`, the `(` taken, as the parse of the list
that the `(` opens. -/
private theorem parenMaximum_open (q : ClosedMaximumParser H P) {Z : Type} [Cursor Z]
    (state : ParseState H) {cursor after : Z} {raw : Cursor.Token Z}
    {consumed : Cursor.Consumed after cursor}
    (hnext : Cursor.next? cursor = some (raw, ⟨after, consumed⟩))
    (hopen : Parser.Internal.Input.ofSyntax (Cursor.syntax after raw) = .parenOpen)
    (hn : Cursor.HasNext after) :
    outcome <$> Parse.parse (⟨false, q⟩ : ParenMaximumParser H P) state cursor =
      parenF <$> (outcome <$> Parse.parse q state after) := by
  have hsyntax : Cursor.syntax after raw = .parenOpen := by
    cases h : Cursor.syntax after raw <;> rw [h] at hopen <;> first | rfl | cases hopen
  simp only [Parse.parse, Bool.false_eq_true, ite_false]
  split
  · rename_i heq
    rw [hnext] at heq
    cases heq
  · rename_i raw' after' consumed' heq
    rw [hnext] at heq
    cases heq
    simp only [hsyntax]
    split
    · rename_i hn' _
      exact absurd hn hn'
    · simp only [ParenMaximumParser.parseInner, map_bind, Functor.map_map]
      rw [bind_assoc, map_eq_pure_bind]
      refine bind_congr fun x => ?_
      obtain ⟨a, p', s, ⟨z, hz⟩⟩ := x
      rcases a with (_ | _) | (_ | _) <;> simp [outcome, parenF]

private theorem paren_finishes {version : Version} {q b : ClosedMaximumParser H P}
    {tokens : List Parser.Internal.Input} {program : PM H (Array R)}
    (h : Outcome.Finishes version q tokens program b) (hne : tokens ≠ []) :
    Outcome.Finishes version (⟨false, q⟩ : ParenMaximumParser H P) (.parenOpen :: tokens)
      program ⟨false, b⟩ := by
  refine ⟨h.1, fun state cursor next rest htakes hreads => ?_⟩
  obtain ⟨after, raw, consumed, hn, hnext, hver, hopen, htail⟩ := Takes.cons_inv htakes
  rw [parenMaximum_open q state hnext hopen (Takes.hasNext_of_ne htail hne),
    h.2 state after next rest htail hreads, Functor.map_map]
  congr 1
  funext e
  rcases e with (_ | _ | _) | _ <;> rfl

private theorem paren_rejects {version : Version} {q : ClosedMaximumParser H P}
    {tokens : List Parser.Internal.Input} {program : PM H Unit} {kind : SyntaxErrorKind}
    (h : Outcome.Rejects version q tokens program kind) (hne : tokens ≠ []) :
    Outcome.Rejects version (⟨false, q⟩ : ParenMaximumParser H P) (.parenOpen :: tokens)
      program kind := by
  refine ⟨h.1, fun state cursor next rest htakes hreads => ?_⟩
  obtain ⟨after, raw, consumed, hn, hnext, hver, hopen, htail⟩ := Takes.cons_inv htakes
  rw [parenMaximum_open q state hnext hopen (Takes.hasNext_of_ne htail hne),
    h.2 state after next rest htail hreads, Functor.map_map]
  congr 1
  funext e
  rcases e with (_ | _ | _) | _ <;> rfl

/-- The list parser with a maximum and its own `(` on the `(`, at most the maximum of values
and the `)`. -/
theorem parenMaximum_parses {version : Version} {p : P} {maximum : Nat}
    {values : List (List Parser.Internal.Input × PM H R)} (hvalues : ValuesParse version p values)
    (hlength : values.length ≤ maximum) :
    Outcome.Finishes version (ParenMaximumParser.new (H := H) p maximum)
      (.parenOpen :: (valuesTokens values ++ [.parenClose]))
      ((fun results => results.toArray) <$> values.mapM fun value => value.2)
      (ParenMaximumParser.new p maximum) :=
  paren_finishes (closedMaximum_parses hvalues hlength) (by simp)

/-- The list parser with a maximum and its own `(` on a first token that is not `(`. -/
theorem parenMaximum_rejects_open {version : Version} {p : P} {maximum : Nat}
    {token : Parser.Internal.Input} (htoken : token ≠ .parenOpen) :
    Outcome.Rejects version (ParenMaximumParser.new (H := H) p maximum) [token]
      (pure () : PM H Unit) (.expected #[.token .parenOpen]) := by
  refine ⟨handlerOnly_pure _, fun state cursor next rest htakes hreads => ?_⟩
  obtain ⟨after, raw, consumed, hn, hnext, hver, htoken', htail⟩ := Takes.cons_inv htakes
  rw [Takes.nil_inv htail]
  simp only [Parse.parse, ParenMaximumParser.new, Bool.false_eq_true, ite_false]
  split
  · rename_i heq
    rw [hnext] at heq
    cases heq
  · rename_i raw' after' consumed' heq
    rw [hnext] at heq
    cases heq
    split
    · rename_i heq
      rw [heq] at htoken'
      exact absurd htoken'.symm htoken
    · simp [outcome, answer]

/-- The list parser with a maximum and its own `(` on the `(`, the maximum of values and a token
after them that is not `)`: it rejects that token. -/
theorem parenMaximum_rejects_beyond {version : Version} {p : P} {maximum : Nat}
    {values : List (List Parser.Internal.Input × PM H R)} (hvalues : ValuesParse version p values)
    (hlength : values.length = maximum) {token : Parser.Internal.Input}
    (htoken : token ≠ .parenClose) :
    Outcome.Rejects version (ParenMaximumParser.new (H := H) p maximum)
      (.parenOpen :: (valuesTokens values ++ [token]))
      (do let _ ← values.mapM fun value => value.2; pure ()) (.expected #[.token .parenClose]) :=
  paren_rejects (closedMaximum_rejects_beyond hvalues hlength htoken) (by simp)

/-- The list parser with a maximum and its own `(` on the `(`, fewer values than the maximum and
then tokens that its inner parser rejects, not starting with `)`. -/
theorem parenMaximum_rejects_inner {version : Version} {p : P} {maximum : Nat}
    {values : List (List Parser.Internal.Input × PM H R)} (hvalues : ValuesParse version p values)
    (hlength : values.length < maximum) {tokens : List Parser.Internal.Input}
    {program : PM H Unit} {kind : SyntaxErrorKind}
    (h : Outcome.Rejects version p tokens program kind)
    (hfirst : ∃ token tokens', tokens = token :: tokens' ∧ token ≠ .parenClose) :
    Outcome.Rejects version (ParenMaximumParser.new (H := H) p maximum)
      (.parenOpen :: (valuesTokens values ++ tokens))
      (do let _ ← values.mapM fun value => value.2; program) kind := by
  refine paren_rejects (closedMaximum_rejects_inner hvalues hlength h hfirst) ?_
  obtain ⟨_, _, rfl, _⟩ := hfirst
  simp

omit [Monad m] [LawfulMonad m] in
/-- Setting the maximum of a list parser with a maximum and its own `(` before its `(`: the
parser with the new maximum. -/
theorem parenMaximum_setMaximum_new (p : P) (maximum n : Nat) :
    (ParenMaximumParser.new (H := H) p maximum).setMaxElements n =
      ParenMaximumParser.new (H := H) p n := by rfl

omit [Monad m] [LawfulMonad m] in
/-- The maximum of a list parser with a maximum and its own `(`. -/
theorem parenMaximum_maxElements_new (p : P) (maximum : Nat) :
    (ParenMaximumParser.new (H := H) p maximum).maxElements = maximum := by rfl


/-! ## Waiting with its own `(` -/

/-- The parse of a list with a maximum and its own `(`, the `(` taken before: the parse of the
list. -/
private theorem parenMaximum_opened (q : ClosedMaximumParser H P) {Z : Type} [Cursor Z]
    (state : ParseState H) (cursor : Z) :
    outcome <$> Parse.parse (⟨true, q⟩ : ParenMaximumParser H P) state cursor =
      parenF <$> (outcome <$> Parse.parse q state cursor) := by
  simp only [Parse.parse, ite_true, ParenMaximumParser.parseInner, map_bind, Functor.map_map]
  rw [map_eq_pure_bind]
  refine bind_congr fun x => ?_
  obtain ⟨a, p', s, ⟨z, hz⟩⟩ := x
  rcases a with (_ | _) | (_ | _) <;> simp [outcome, parenF]

private theorem opened_finishes {version : Version} {q b : ClosedMaximumParser H P}
    {tokens : List Parser.Internal.Input} {program : PM H (Array R)}
    (h : Outcome.Finishes version q tokens program b) :
    Outcome.Finishes version (⟨true, q⟩ : ParenMaximumParser H P) tokens program ⟨false, b⟩ := by
  refine ⟨h.1, fun state cursor next rest htakes hreads => ?_⟩
  rw [parenMaximum_opened q state cursor, h.2 state cursor next rest htakes hreads,
    Functor.map_map]
  congr 1
  funext e
  rcases e with (_ | _ | _) | _ <;> rfl

private theorem opened_rejects {version : Version} {q : ClosedMaximumParser H P}
    {tokens : List Parser.Internal.Input} {program : PM H Unit} {kind : SyntaxErrorKind}
    (h : Outcome.Rejects version q tokens program kind) :
    Outcome.Rejects version (⟨true, q⟩ : ParenMaximumParser H P) tokens program kind := by
  refine ⟨h.1, fun state cursor next rest htakes hreads => ?_⟩
  rw [parenMaximum_opened q state cursor, h.2 state cursor next rest htakes hreads,
    Functor.map_map]
  congr 1
  funext e
  rcases e with (_ | _ | _) | _ <;> rfl

private theorem paren_waits {version : Version} {q : ClosedMaximumParser H P}
    {tokens : List Parser.Internal.Input} {α : Type} {program : PM H α}
    {after : α → ClosedMaximumParser H P}
    (h : Outcome.Waits version q tokens program after) (hne : tokens ≠ []) :
    Outcome.Waits version (⟨false, q⟩ : ParenMaximumParser H P) (.parenOpen :: tokens) program
      fun a => ⟨true, after a⟩ := by
  refine ⟨h.1, fun state cursor last htakes hnone => ?_⟩
  obtain ⟨after', raw, consumed, hn, hnext, hver, hopen, htail⟩ := Takes.cons_inv htakes
  rw [parenMaximum_open q state hnext hopen (Takes.hasNext_of_ne htail hne),
    h.2 state after' last htail hnone, Functor.map_map]
  congr 1
  funext e
  rcases e with (_ | _ | _) | _ <;> rfl

/-- The list parser with a maximum and its own `(` on no token: it wants more, as it is. -/
theorem parenMaximum_waits_open {version : Version} {p : P} {maximum : Nat} :
    Outcome.Waits version (ParenMaximumParser.new (H := H) p maximum) [] (pure () : PM H Unit)
      fun _ => ParenMaximumParser.new p maximum := by
  refine ⟨handlerOnly_pure _, fun state cursor last htakes hnone => ?_⟩
  rw [Takes.nil_inv htakes] at hnone
  simp only [Parse.parse, ParenMaximumParser.new, Bool.false_eq_true, ite_false]
  split
  · simp [outcome, answer]
  · rename_i heq
    rw [hnone] at heq
    cases heq

/--
The list parser with a maximum and its own `(` on its `(` and no more: it wants more, as a parser
that holds the maximum, which a maximum set on it replaces. It finishes on at most the maximum
of values and the `)`, and rejects a token not `)` after the maximum of values.
-/
theorem parenMaximum_waits_after_open {version : Version} {p : P} :
    ∃ after : Nat → ParenMaximumParser H P,
      (∀ maximum n, (after maximum).setMaxElements n = after n) ∧
      (∀ maximum, Outcome.Waits version (ParenMaximumParser.new (H := H) p maximum) [.parenOpen]
        (pure () : PM H Unit) fun _ => after maximum) ∧
      (∀ maximum {values : List (List Parser.Internal.Input × PM H R)},
        ValuesParse version p values → values.length ≤ maximum →
        Outcome.Finishes version (after maximum) (valuesTokens values ++ [.parenClose])
          ((fun results => results.toArray) <$> values.mapM fun value => value.2)
          (ParenMaximumParser.new p maximum)) ∧
      (∀ maximum {values : List (List Parser.Internal.Input × PM H R)}
        {token : Parser.Internal.Input},
        ValuesParse version p values → values.length = maximum → token ≠ .parenClose →
        Outcome.Rejects version (after maximum) (valuesTokens values ++ [token])
          (do let _ ← values.mapM fun value => value.2; pure ())
          (.expected #[.token .parenClose])) := by
  refine ⟨fun maximum => ⟨true, ClosedMaximumParser.new p maximum⟩, fun _ _ => rfl,
    fun maximum => ⟨handlerOnly_pure _, fun state cursor last htakes hnone => ?_⟩,
    fun maximum _ hv hlength => opened_finishes (closedMaximum_parses hv hlength),
    fun maximum _ _ hv hlength htoken =>
      opened_rejects (closedMaximum_rejects_beyond hv hlength htoken)⟩
  obtain ⟨after, raw, consumed, hn, hnext, hver, hopen, htail⟩ := Takes.cons_inv htakes
  rw [Takes.nil_inv htail] at hnone
  have hsyntax : Cursor.syntax after raw = .parenOpen := by
    cases h : Cursor.syntax after raw <;> rw [h] at hopen <;> first | rfl | cases hopen
  simp only [Parse.parse, ParenMaximumParser.new, Bool.false_eq_true, ite_false]
  split
  · rename_i heq
    rw [hnext] at heq
    cases heq
  · rename_i raw' after' consumed' heq
    rw [hnext] at heq
    cases heq
    simp only [hsyntax]
    split
    · simp [outcome, answer]
    · rename_i h' _
      exact absurd h' (Parser.Internal.not_hasNext hnone)

/--
The list parser with a maximum and its own `(` on its `(` and at most the maximum of values, at
least one, and no more: it wants more, as a parser that holds the maximum and the results so
far. A maximum set on it applies to the values after them.
-/
theorem parenMaximum_waits_between {version : Version} {p : P}
    {values : List (List Parser.Internal.Input × PM H R)} (hvalues : ValuesParse version p values)
    (hne : values ≠ []) :
    ∃ after : Nat → List R → ParenMaximumParser H P,
      (∀ maximum found n, (after maximum found).setMaxElements n = after n found) ∧
      (∀ maximum, values.length ≤ maximum →
        Outcome.Waits version (ParenMaximumParser.new (H := H) p maximum)
          (.parenOpen :: valuesTokens values) (values.mapM fun value => value.2)
          (after maximum)) ∧
      (∀ maximum found {values' : List (List Parser.Internal.Input × PM H R)},
        ValuesParse version p values' → found.length + values'.length ≤ maximum →
        Outcome.Finishes version (after maximum found) (valuesTokens values' ++ [.parenClose])
          ((fun results => (found ++ results).toArray) <$> values'.mapM fun value => value.2)
          (ParenMaximumParser.new p maximum)) ∧
      (∀ maximum found {values' : List (List Parser.Internal.Input × PM H R)}
        {token : Parser.Internal.Input},
        ValuesParse version p values' → found.length + values'.length = maximum →
        token ≠ .parenClose →
        Outcome.Rejects version (after maximum found) (valuesTokens values' ++ [token])
          (do let _ ← values'.mapM fun value => value.2; pure ())
          (.expected #[.token .parenClose])) := by
  have htok : valuesTokens values ≠ [] := by
    obtain ⟨value, values', rfl⟩ := List.exists_cons_of_ne_nil hne
    obtain ⟨_, token, tokens, hvalue, _⟩ := hvalues value (List.mem_cons_self ..)
    simp [valuesTokens, hvalue]
  refine ⟨fun maximum found => ⟨true, between p maximum found.toArray⟩, fun _ _ _ => rfl,
    fun maximum hlength => ?_, fun maximum found _ hv hlength => ?_,
    fun maximum found _ _ hv hlength htoken =>
      opened_rejects (results_rejects_beyond hv found.toArray (by simpa using hlength) htoken)⟩
  · have := paren_waits (results_waits_end hvalues #[] (maximum := maximum)
      (by simpa using hlength)) htok
    simpa [between, ClosedMaximumParser.new, ParenMaximumParser.new] using this
  · have := opened_finishes (results_finishes hv found.toArray (by simpa using hlength))
    simpa [ParenMaximumParser.new] using this

/--
The list parser with a maximum and its own `(` on its `(`, fewer values than the maximum and then
tokens on which its inner parser wants more, not starting with `)`: it wants more, as a parser
that holds the maximum, the results so far and the inner parser within its value. A maximum set
on it applies to the values after that value; it finishes once the inner parser finishes the
value and as many further values as the maximum leaves and the `)` follow.
-/
theorem parenMaximum_waits_inner {version : Version} {p : P}
    {values : List (List Parser.Internal.Input × PM H R)} (hvalues : ValuesParse version p values)
    {tokens : List Parser.Internal.Input} {α : Type} {program : PM H α} {after : α → P}
    (h : Outcome.Waits version p tokens program after)
    (hfirst : ∃ token tokens', tokens = token :: tokens' ∧ token ≠ .parenClose) :
    ∃ after' : Nat → List R × α → ParenMaximumParser H P,
      (∀ maximum x n, (after' maximum x).setMaxElements n = after' n x) ∧
      (∀ maximum, values.length < maximum →
        Outcome.Waits version (ParenMaximumParser.new (H := H) p maximum)
          (.parenOpen :: (valuesTokens values ++ tokens))
          (do let found ← values.mapM fun value => value.2; let a ← program; pure (found, a))
          (after' maximum)) ∧
      ∀ maximum found a {tokens' : List Parser.Internal.Input} {program' : PM H R}
        {values' : List (List Parser.Internal.Input × PM H R)},
        Outcome.Finishes version (after a) tokens' program' p → tokens' ≠ [] →
        ValuesParse version p values' → found.length + 1 + values'.length ≤ maximum →
        Outcome.Finishes version (after' maximum (found, a))
          (tokens' ++ valuesTokens values' ++ [.parenClose])
          ((fun results => (found ++ results).toArray) <$> (program' >>= fun first =>
            (values'.mapM fun value => value.2) >>= fun others => pure (first :: others)))
          (ParenMaximumParser.new p maximum) := by
  have hne : valuesTokens values ++ tokens ≠ [] := by
    obtain ⟨_, _, rfl, _⟩ := hfirst
    simp
  refine ⟨fun maximum x =>
    ⟨true, { maximum, outside := false, results := x.1.toArray, inner := after x.2 }⟩,
    fun _ _ _ => rfl, fun maximum hlength => ?_,
    fun maximum found a _ _ _ hq hne' hv hlength => ?_⟩
  · have := paren_waits (results_waits_inner hvalues #[] (maximum := maximum)
      (by simpa using hlength) h hfirst) hne
    simpa [between, ClosedMaximumParser.new, ParenMaximumParser.new] using this
  · have := opened_finishes (results_resume_finishes hq hne' hv found.toArray
      (by simpa using hlength))
    simpa [Functor.map_map, ParenMaximumParser.new] using this

end

end BSmtLib.Facts.Proofs.Parser.Category.Maximum
