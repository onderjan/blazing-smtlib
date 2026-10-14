module

public import BSmtLib.Facts.Proofs.Reader.Outcome
public import BSmtLib.Facts.Proofs.Reader.Valid

@[expose] public section

/-!
# The commands of a reading, split off what a parser takes

What a parser takes for commands (`Takes`) is read in readings: commands that keep the version, up
to a version declaration, after whose `)` the version is switched (`takes_switch`), or up to the
end of the input, where `exit` may come last (`takes_final`). Where a reading ends is told by what
the producer is asked for after each item (`requestsAt`).
-/

namespace BSmtLib.Facts.Proofs.Reader.Split

open BSmtLibSpec BSmtLibSpec.Grammar
open BSmtLibSpec.Parser.Properties (Takes Ending)
open BSmtLibSpec.Parser.Traversal (Received)
open BSmtLib.Facts.Proofs.Parser.Trace (requestsAt)
open BSmtLib.Facts.Proofs.Reader.Outcome BSmtLib.Facts.Proofs.Reader.Requests
open BSmtLib.Facts.Proofs.Reader.Valid

theorem requestsAt_cons_inner {c : Tree.Command} {rest : List Tree.Command} {k : Nat}
    (h : k + 1 < c.tokens.length) : requestsAt (c :: rest) k = (none, false) := by
  simp [requestsAt, h]

theorem requestsAt_cons_last {c : Tree.Command} {rest : List Tree.Command} {k : Nat}
    (h : k + 1 = c.tokens.length) :
    (requestsAt (c :: rest) k).1 = c.declaredVersion := by
  simp [requestsAt, h]

theorem requestsAt_cons_after {c : Tree.Command} {rest : List Tree.Command} {k : Nat}
    (h : c.tokens.length ≤ k) :
    requestsAt (c :: rest) k = requestsAt rest (k - c.tokens.length) := by
  simp [requestsAt, show ¬ k + 1 < c.tokens.length by omega,
    show ¬ k + 1 = c.tokens.length by omega]

/-- A discarding is asked for only after the `)` of `exit`, where no switch is. -/
theorem requestsAt_discard : ∀ (commands : List Tree.Command) (k : Nat),
    (requestsAt commands k).2 = true →
      (requestsAt commands k).1 = none ∧ Tree.Command.exit ∈ commands
  | [], _, h => by simp [requestsAt] at h
  | c :: rest, k, h => by
    by_cases h1 : k + 1 < c.tokens.length
    · rw [requestsAt_cons_inner h1] at h; cases h
    · by_cases h2 : k + 1 = c.tokens.length
      · simp only [requestsAt, h2, Nat.lt_irrefl, ↓reduceIte] at h ⊢
        cases c <;> first | (simp at h; done) | simp [Tree.Command.declaredVersion]
      · rw [requestsAt_cons_after (by omega)] at h ⊢
        obtain ⟨h₁, h₂⟩ := requestsAt_discard rest _ h
        exact ⟨h₁, List.mem_cons_of_mem _ h₂⟩

theorem prefix_append_split {α : Type} {xs ys P : List α} (h : P <+: xs ++ ys)
    (hlen : xs.length ≤ P.length) : P = xs ++ P.drop xs.length ∧ P.drop xs.length <+: ys := by
  have hP : P = (xs ++ ys).take P.length := List.prefix_iff_eq_take.mp h
  rw [List.take_append, List.take_of_length_le hlen] at hP
  obtain ⟨Q, hQ⟩ : ∃ Q, Q = ys.take (P.length - xs.length) := ⟨_, rfl⟩
  rw [← hQ] at hP
  subst hP
  refine ⟨by simp, ?_⟩
  rw [List.drop_left, hQ]
  exact List.take_prefix _ _

/-- The commands of a reading that a version declaration ends: from a version, the items for
commands that keep it, up to and including the declaration's `)`, after which a switch is asked
for and none before. They are split off what a parser takes, which goes on in the declared
version. -/
theorem takes_switch {version : Lexicon.Version} {commands : List Tree.Command}
    {taken : List Received} {ending : Ending} (ht : Takes version commands taken ending) :
    ∀ (P : List Received) (declared : Lexicon.Version), P <+: taken → 0 < P.length →
      P.length < taken.length → (requestsAt commands (P.length - 1)).1 = some declared →
      (∀ k, k + 1 < P.length → (requestsAt commands k).1 = none) →
      ∃ init decl rest, commands = init ++ decl :: rest ∧
        (doneTokens (init ++ [decl])).map .token = P ∧
        (∀ c ∈ init, c.Valid version ∧ c.modeAfter version = some (.read version)) ∧
        decl.Valid version ∧ decl.modeAfter version = some (.read declared) ∧
        Takes declared rest (taken.drop P.length) ending := by
  induction ht with
  | done =>
    intro P declared _ hpos hlt
    simp only [List.length_singleton] at hlt
    omega
  | @command v next rest items ending c hv hm hrest ih =>
    intro P declared hp hpos hlt hreq hnone
    have hm' := Parser.Script.modeAfter_read hm
    by_cases h1 : P.length < c.tokens.length
    · rw [requestsAt_cons_inner (by omega)] at hreq
      cases hreq
    · by_cases h2 : P.length = c.tokens.length
      · rw [requestsAt_cons_last (by omega)] at hreq
        have hnext : next = declared := by rw [hm'.2, hreq]; rfl
        subst hnext
        have hP : P = c.tokens.map .token := by
          have := List.prefix_iff_eq_take.mp hp
          rw [this, h2, List.take_append_of_le_length (by simp), List.take_of_length_le (by simp)]
        refine ⟨[], c, rest, rfl, by simp [doneTokens, hP], by simp, hv, hm, ?_⟩
        rw [h2, List.drop_append_of_le_length (by simp), List.drop_of_length_le (by simp)]
        simpa using hrest
      · have hdecl : c.declaredVersion = none := by
          have := hnone (c.tokens.length - 1) (by have := tokens_length_pos c; omega)
          rwa [requestsAt_cons_last (by have := tokens_length_pos c; omega)] at this
        have hnext : next = v := by rw [hm'.2, hdecl]; rfl
        subst hnext
        obtain ⟨hPsplit, hP'⟩ := prefix_append_split hp (by simp; omega)
        simp only [List.length_map] at hPsplit hP'
        have hlen' : (P.drop c.tokens.length).length = P.length - c.tokens.length := by simp
        obtain ⟨init, decl, rest', hrest', htoks, hinit, hdv, hdm, htk⟩ :=
          ih (P.drop c.tokens.length) declared hP' (by rw [hlen']; omega)
            (by rw [hlen']; simp at hlt; omega)
            (by
              rw [hlen', show P.length - c.tokens.length - 1 = P.length - 1 - c.tokens.length by
                omega, ← requestsAt_cons_after (c := c) (by omega)]
              exact hreq)
            (by
              intro k hk
              rw [hlen'] at hk
              have := hnone (k + c.tokens.length) (by omega)
              rwa [requestsAt_cons_after (by omega), Nat.add_sub_cancel] at this)
        refine ⟨c :: init, decl, rest', by rw [hrest']; rfl, ?_, ?_, hdv, hdm, ?_⟩
        · rw [hPsplit, ← htoks]
          simp [doneTokens]
        · intro c' hc'
          rcases List.mem_cons.mp hc' with rfl | hc'
          · exact ⟨hv, hm⟩
          · exact hinit c' hc'
        · rw [List.drop_append, List.drop_eq_nil_of_le (by simp; omega), List.nil_append]
          rw [hlen'] at htk
          simpa using htk
  | @stop v last hv hm =>
    obtain rfl := Parser.Script.modeAfter_unparsed hm
    intro P declared _ hpos hlt hreq _
    simp only [List.length_append, List.length_map, List.length_singleton] at hlt
    by_cases h1 : P.length < Tree.Command.exit.tokens.length
    · rw [requestsAt_cons_inner (by omega)] at hreq
      cases hreq
    · rw [requestsAt_cons_last (by omega)] at hreq
      simp [Tree.Command.declaredVersion] at hreq
  | @refused v last hv hm =>
    intro P declared _ hpos hlt hreq _
    simp only [List.length_map] at hlt
    rw [requestsAt_cons_inner (by omega)] at hreq
    cases hreq

/-- The commands of the last reading: from a version, the items for commands that keep it,
possibly followed by `exit`, then the end of the input, with no switch asked for. -/
theorem takes_final {version : Lexicon.Version} {commands : List Tree.Command}
    {taken : List Received} {ending : Ending} (ht : Takes version commands taken ending) :
    ending = .finished → ∀ X : List Received, taken = X ++ [.endOfInput] →
      (∀ k < X.length, (requestsAt commands k).1 = none) →
      ∃ cmds, (∀ c ∈ cmds, c.Valid version ∧ c.modeAfter version = some (.read version)) ∧
        ((commands = cmds ∧ (doneTokens cmds).map .token = X) ∨
          (commands = cmds ++ [.exit] ∧ Tree.Command.exit.Valid version ∧
            Tree.Command.exit.modeAfter version = some .unparsed ∧
            (doneTokens (cmds ++ [.exit])).map .token = X)) := by
  induction ht with
  | done =>
    intro _ X hX _
    have : X = [] := by
      cases X with
      | nil => rfl
      | cons x xs => simp at hX
    subst this
    exact ⟨[], by simp, Or.inl ⟨rfl, rfl⟩⟩
  | @command v next rest items ending c hv hm hrest ih =>
    intro hend X hX hnone
    have hm' := Parser.Script.modeAfter_read hm
    have hne : items ≠ [] := by
      rintro rfl
      have := takes_finished_last hrest hend
      simp at this
    -- `X` starts with the command's tokens
    have hlenX : c.tokens.length ≤ X.length := by
      have := congrArg List.length hX
      simp only [List.length_append, List.length_map, List.length_singleton] at this
      have : items.length ≠ 0 := by simpa using hne
      omega
    obtain ⟨hXsplit, -⟩ := prefix_append_split (xs := c.tokens.map .token) (ys := items)
      (P := X) ⟨[.endOfInput], by rw [← hX]⟩ (by simpa using hlenX)
    simp only [List.length_map] at hXsplit
    have hitems : items = X.drop c.tokens.length ++ [.endOfInput] := by
      have := hX
      rw [hXsplit, List.append_assoc] at this
      exact (List.append_cancel_left this)
    have hdecl : c.declaredVersion = none := by
      have := hnone (c.tokens.length - 1) (by have := tokens_length_pos c; omega)
      rwa [requestsAt_cons_last (by have := tokens_length_pos c; omega)] at this
    have hnext : next = v := by rw [hm'.2, hdecl]; rfl
    subst hnext
    obtain ⟨cmds, hvalid, hcases⟩ := ih hend (X.drop c.tokens.length) hitems (by
      intro k hk
      simp only [List.length_drop] at hk
      have := hnone (k + c.tokens.length) (by omega)
      rwa [requestsAt_cons_after (by omega), Nat.add_sub_cancel] at this)
    refine ⟨c :: cmds, ?_, ?_⟩
    · intro c' hc'
      rcases List.mem_cons.mp hc' with rfl | hc'
      · exact ⟨hv, hm⟩
      · exact hvalid c' hc'
    · rcases hcases with ⟨rfl, htoks⟩ | ⟨rfl, hev, hem, htoks⟩
      · refine Or.inl ⟨rfl, ?_⟩
        rw [hXsplit, ← htoks]
        simp [doneTokens]
      · refine Or.inr ⟨rfl, hev, hem, ?_⟩
        rw [hXsplit, ← htoks]
        simp [doneTokens]
  | @stop v last hv hm =>
    obtain rfl := Parser.Script.modeAfter_unparsed hm
    intro _ X hX _
    have hX' : X = Tree.Command.exit.tokens.map .token := by
      have := List.append_cancel_right hX
      exact this.symm
    exact ⟨[], by simp, Or.inr ⟨rfl, hv, hm, by simp [doneTokens, hX']⟩⟩
  | refused => intro hend; cases hend

end BSmtLib.Facts.Proofs.Reader.Split
