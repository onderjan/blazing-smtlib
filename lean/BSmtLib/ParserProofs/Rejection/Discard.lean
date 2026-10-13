import BSmtLib.ParserProofs.Rejection.Library
import BSmtLib.ParserProofs.Trace

/-!
# Where the traversal asks for the discarding

After `exit`, the library's parser asks its producer to discard the rest of the input and goes
back to reading commands; it relies on its producer, which hands over nothing after `exit` but the
end of the input. `RejectsFirstUnviable` speaks only of such items: where the traversal has asked
for the discarding before an item, the item is the end of the input. The traversal asks for it
exactly where the items before end with `exit` (`AfterExit`, `discard_afterExit`), so there the
item is no first item that no script continues with, and everywhere else the parser rejects such
an item (`rejects_items`).
-/

namespace BSmtLib.ParserProofs.Rejection

open BSmtLibSpec.Grammar
open BSmtLibSpec.Grammar.Syntax BSmtLibSpec.Grammar.File BSmtLibSpec.Grammar.Properties
open BSmtLibSpec.Parser
open BSmtLibSpec.Parser.Properties
open BSmtLibSpec.Parser.Traversal
open Lang

/-- Commands, each followed by more in a version, and then `exit`, are a script. -/
theorem script_of_chain_exit {version last : BSmtLibSpec.Lexicon.Version} {done : List Tree.Command}
    (h : Chain version done last) : Script version (done ++ [.exit]) := by
  induction h with
  | nil => exact .stop trivial rfl
  | cons hv hm _ ih => exact .command hv hm ih

/-- What a parser receives for commands, each followed by more in a version, and then `exit`:
their items, then the end of the input. -/
theorem received_chain_exit {version last : BSmtLibSpec.Lexicon.Version} {done : List Tree.Command}
    (h : Chain version done last) :
    received (done ++ [.exit]) =
      cmdToks done ++ toks Tree.Command.exit.tokens ++ [.endOfInput] := by
  induction h with
  | nil => rfl
  | cons _ hm _ ih =>
    rw [List.cons_append, received_cons (modeAfter_read hm).1, ih, cmdToks_cons]
    simp [toks]

/-- After the `)` of `exit`, the traversal asks for the discarding. -/
theorem requestsAt_exit {version last : BSmtLibSpec.Lexicon.Version} {done : List Tree.Command}
    (h : Chain version done last) :
    (requestsAt (done ++ [.exit]) ((cmdToks done).length + 2)).2 = true := by
  induction h with
  | nil => rfl
  | @cons version next rest last c hv hm _ ih =>
    have hc := tokens_ne_nil c
    rw [List.cons_append, cmdToks_cons, List.length_append, toks_length]
    have h₁ : ¬ c.tokens.length + (cmdToks rest).length + 2 + 1 < c.tokens.length := by omega
    have h₂ : ¬ c.tokens.length + (cmdToks rest).length + 2 + 1 = c.tokens.length := by omega
    simp only [requestsAt, h₁, h₂, ↓reduceIte,
      show c.tokens.length + (cmdToks rest).length + 2 - c.tokens.length =
        (cmdToks rest).length + 2 by omega]
    exact ih

/-- A discarding asked for after the last processing among events is among them. -/
theorem mem_of_discardOf {events : List Event} (h : discardOf events = true) :
    .producerDiscard ∈ events := by
  unfold discardOf at h
  obtain ⟨e, he, hd⟩ := List.any_eq_true.mp h
  have : e = .producerDiscard := by cases e <;> simp_all
  subst this
  exact (afterLastProcess_suffix events).subset he

/-- Where the items before a position of what a parser takes end with `exit`, the traversal has
asked for the discarding before the item there arrives. -/
theorem discard_afterExit {version : BSmtLibSpec.Lexicon.Version} {commands : List Tree.Command}
    {taken : List Received} {ending : Ending} (htakes : Takes version commands taken ending)
    {count : Nat} (hcount : count < taken.length) (hafter : AfterExit version (taken.take count)) :
    .producerDiscard ∈ eventsBefore count (record version commands) := by
  obtain ⟨done, last, hchain, hagree⟩ := hafter
  obtain ⟨rfl, -⟩ := takes_after_exit htakes hchain hcount hagree
  have hlen := congrArg List.length hagree
  rw [List.length_take, Nat.min_eq_left (Nat.le_of_lt hcount)] at hlen
  simp only [List.length_append, toks_length, exit_tokens_length] at hlen
  have hk : (cmdToks done).length + 2 < (received (done ++ [.exit])).length := by
    rw [received_chain_exit hchain]
    simp [exit_tokens_length]
  have hreq := (requests_record (script_of_chain_exit hchain) _ hk).2
  rw [requestsAt_exit hchain, show (cmdToks done).length + 2 + 1 = count by omega] at hreq
  exact mem_of_discardOf hreq

/-- The library's parser rejects the first item that no script continues with. -/
theorem library_rejects : RejectsFirstUnviable libraryParser := by
  intro version commands taken ending items count rejected htakes hcount hrejected hagree hlexC
    hdiscard hunviable
  refine rejects_items version commands taken ending items count htakes hcount rejected hrejected
    hagree hlexC (fun hafter => hunviable ?_) hunviable
  -- after `exit`, the item is the end of the input, which some script continues with
  have hend := hdiscard (discard_afterExit htakes hcount hafter)
  have hitem := takes_afterExit htakes hcount hafter
  refine ⟨commands, taken, ending, htakes, ?_⟩
  change (items.map libraryParser.stands).take (count + 1) <+: taken
  rw [List.take_add_one, hagree, hend, ← hitem, ← List.take_add_one]
  exact List.take_prefix _ _

end BSmtLib.ParserProofs.Rejection
