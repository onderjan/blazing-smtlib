import BSmtLib.Facts.Proofs.Parser.Rejection.Script

/-!
# The version in force at an item does not depend on the reading

Two readings of the same items as what a parser takes, from the same version, agree on the
version in force at each item they share: the tokens of a command are no proper start of another
command's tokens (the readers of `BSmtLibSpec.Facts.Proofs.Grammar.Read` read a command back from
its tokens, whatever follows them), so the readings split the items into the same commands.
-/

namespace BSmtLib.Facts.Proofs.Parser.Rejection.Unique

open BSmtLibSpec.Grammar
open BSmtLibSpec.Parser.Properties
open BSmtLibSpec.Parser.Traversal
open BSmtLib.Facts.Proofs.Parser.Rejection.Basic.Lang
open BSmtLib.Facts.Proofs.Parser.Rejection.Script BSmtLib.Facts.Proofs.Parser.Rejection.«Sort»
open BSmtLib.Facts.Proofs.Parser.Script

/-- A command's tokens that start another's of the same version are that command's. -/
theorem command_prefix {version : BSmtLibSpec.Lexicon.Version} {c c' : Tree.Command}
    (hc : c.Valid version) (hc' : c'.Valid version) {r : List BSmtLibSpec.Grammar.SyntaxToken}
    (h : c'.tokens = c.tokens ++ r) : c = c' ∧ r = [] := by
  have h₁ := BSmtLibSpec.Facts.Proofs.Grammar.OneToOne.readCommand_tokens version c r
      (n := sizeOf c + sizeOf c' + 1) hc
    (by omega)
  have h₂ := BSmtLibSpec.Facts.Proofs.Grammar.OneToOne.readCommand_tokens version c' []
      (n := sizeOf c + sizeOf c' + 1)
    hc' (by omega)
  rw [List.append_nil, h, h₁] at h₂
  simp only [Option.some.injEq, Prod.mk.injEq] at h₂
  exact h₂

/-- The items of a command that start another's of the same version are that command's. -/
theorem toks_prefix {version : BSmtLibSpec.Lexicon.Version} {c c' : Tree.Command}
    (hc : c.Valid version) (hc' : c'.Valid version) {r : List Received}
    (h : toks c'.tokens = toks c.tokens ++ r) : c = c' ∧ r = [] := by
  obtain ⟨a, b, hab, ha, hb⟩ := List.map_eq_append_iff.mp h
  have : a = c.tokens := (List.map_inj_right (fun _ _ h => by cases h; rfl)).mp ha
  subst this
  obtain ⟨hcc, hb'⟩ := command_prefix hc hc' hab
  subst hb'
  exact ⟨hcc, by simpa using hb.symm⟩

/-- Two lists that agree on their first items agree on fewer of them. -/
theorem take_prefix_of_le {α : Type} {l l' : List α} {j : Nat} (k : Nat) (hk : k ≤ j)
    (h : l.take j = l'.take j) : l.take k = l'.take k := by
  have := congrArg (List.take k) h
  simpa [List.take_take, Nat.min_eq_left hk] using this

/-- Where two commands' items, each followed by more, agree on as many items as the first
command has, the first command's items start the second's. -/
theorem toks_split {c c' : Tree.Command} {items items' : List Received} {j : Nat}
    (hj : (toks c.tokens).length ≤ j) (hle : (toks c.tokens).length ≤ (toks c'.tokens).length)
    (h : (toks c.tokens ++ items).take j = (toks c'.tokens ++ items').take j) :
    toks c'.tokens = toks c.tokens ++ (toks c'.tokens).drop (toks c.tokens).length := by
  have hp := take_prefix_of_le _ hj h
  rw [List.take_left' rfl, List.take_append_of_le_length hle] at hp
  conv => lhs; rw [← List.take_append_drop (toks c.tokens).length (toks c'.tokens)]
  rw [← hp]

/-- Two commands of the same version whose items, each followed by more, agree on as many items
as either has, are the same command. -/
theorem commands_agree {version : BSmtLibSpec.Lexicon.Version} {c c' : Tree.Command}
    (hc : c.Valid version) (hc' : c'.Valid version) {items items' : List Received} {j : Nat}
    (hj : (toks c.tokens).length ≤ j) (hj' : (toks c'.tokens).length ≤ j)
    (h : (toks c.tokens ++ items).take j = (toks c'.tokens ++ items').take j) : c = c' := by
  rcases Nat.le_total (toks c.tokens).length (toks c'.tokens).length with hle | hle
  · exact (toks_prefix hc hc' (toks_split hj hle h)).1
  · exact (toks_prefix hc' hc (toks_split hj' hle h.symm)).1.symm

/-- A command's items, followed by more, do not agree with a longer command's of the same
version on as many items as the first command has. -/
theorem command_not_shorter {version : BSmtLibSpec.Lexicon.Version} {c c' : Tree.Command}
    (hc : c.Valid version) (hc' : c'.Valid version) {items items' : List Received} {j : Nat}
    (hj : (toks c.tokens).length ≤ j) (hj' : j < (toks c'.tokens).length)
    (h : (toks c.tokens ++ items).take j = (toks c'.tokens ++ items').take j) : False := by
  have hsplit := toks_split hj (by omega) h
  obtain ⟨rfl, hr⟩ := toks_prefix hc hc' hsplit
  rw [List.drop_eq_nil_iff] at hr
  omega

theorem tokens_ne_nil (c : Tree.Command) : c.tokens.length ≠ 0 := by
  cases c <;> simp [Tree.Command.tokens, commandTokens, paren]

theorem take_cancel {l a a' : List Received} {j : Nat} (hj : l.length ≤ j)
    (h : (l ++ a).take j = (l ++ a').take j) : a.take (j - l.length) = a'.take (j - l.length) := by
  have e : j = l.length + (j - l.length) := by omega
  rw [e, List.take_length_add_append, List.take_length_add_append] at h
  simpa using h

/-- Two commands of the same version whose items, each followed by more, agree before a position
in both: both go on past it, or they are the same command and end before it. -/
theorem split_agree {version : BSmtLibSpec.Lexicon.Version} {c c' : Tree.Command}
    (hc : c.Valid version) (hc' : c'.Valid version) {items items' : List Received} {j : Nat}
    (h : (toks c.tokens ++ items).take j = (toks c'.tokens ++ items').take j) :
    (j < c.tokens.length ∧ j < c'.tokens.length) ∨ (c = c' ∧ c.tokens.length ≤ j) := by
  have hl : (toks c.tokens).length = c.tokens.length := by simp [toks]
  have hl' : (toks c'.tokens).length = c'.tokens.length := by simp [toks]
  by_cases hlt : j < c.tokens.length <;> by_cases hlt' : j < c'.tokens.length
  · exact Or.inl ⟨hlt, hlt'⟩
  · exact (command_not_shorter hc' hc (by omega) (by omega) h.symm).elim
  · exact (command_not_shorter hc hc' (by omega) (by omega) h).elim
  · exact Or.inr ⟨commands_agree hc hc' (by omega) (by omega) h, by omega⟩

theorem exit_tokens_length : Tree.Command.exit.tokens.length = 3 := rfl

theorem toks_length (tokens : List BSmtLibSpec.Grammar.SyntaxToken) :
    (toks tokens).length = tokens.length :=
  List.length_map ..

/-- Where the items before a position of what a parser takes are those of commands, each followed
by more in a version, and then those of `exit`, the commands are those and `exit`, and the end of
the input is all that follows. -/
theorem takes_after_exit {version : BSmtLibSpec.Lexicon.Version} {cs : List Tree.Command}
    {taken : List Received} {ending : Ending} (h : Takes version cs taken ending) :
    ∀ {done : List Tree.Command} {last : BSmtLibSpec.Lexicon.Version} {j : Nat},
    Chain version done last → j < taken.length →
    taken.take j = cmdToks done ++ toks Tree.Command.exit.tokens →
    cs = done ++ [.exit] ∧
      taken = cmdToks done ++ toks Tree.Command.exit.tokens ++ [.endOfInput] := by
  induction h with
  | done =>
    intro done last j _ hj hagree
    simp only [List.length_cons, List.length_nil] at hj
    obtain rfl : j = 0 := by omega
    have := congrArg List.length hagree
    simp only [List.take_zero, List.length_nil, List.length_append, toks_length,
      exit_tokens_length] at this
    omega
  | @command v next rest items ending c hc hm hrest ih =>
    intro done last j hchain hj hagree
    have hlen := congrArg List.length hagree
    rw [List.length_take, Nat.min_eq_left (Nat.le_of_lt hj)] at hlen
    have hcl := tokens_ne_nil c
    cases hchain with
    | nil =>
      rw [cmdToks_nil, List.nil_append] at hagree
      have h' : (toks c.tokens ++ items).take j = (toks Tree.Command.exit.tokens ++ []).take j := by
        rw [hagree, List.append_nil, List.take_of_length_le (by
          simp only [cmdToks_nil, List.nil_append] at hlen; omega)]
      rcases split_agree hc (c' := .exit) (by trivial) h' with ⟨-, hlt⟩ | ⟨rfl, -⟩
      · simp only [cmdToks_nil, List.nil_append, toks_length, exit_tokens_length] at hlen
        rw [exit_tokens_length] at hlt
        omega
      · exact absurd rfl (modeAfter_read hm).1
    | @cons _ next' done' _ d hd hdm hch =>
      rw [cmdToks_cons, List.append_assoc] at hagree
      have h' : (toks c.tokens ++ items).take j =
          (toks d.tokens ++ (cmdToks done' ++ toks Tree.Command.exit.tokens)).take j := by
        rw [hagree, List.take_of_length_le (by
          simp only [cmdToks_cons, List.length_append, toks_length] at hlen ⊢; omega)]
      rcases split_agree hc hd h' with ⟨-, hlt⟩ | ⟨rfl, hle⟩
      · simp only [cmdToks_cons, List.length_append, toks_length, exit_tokens_length] at hlen
        omega
      · rw [hm] at hdm
        cases hdm
        have hl := toks_length c.tokens
        have hc' := take_cancel (l := toks c.tokens) (by omega) h'
        rw [List.take_of_length_le (l := cmdToks done' ++ toks Tree.Command.exit.tokens) (by
          simp only [cmdToks_cons, List.length_append, toks_length] at hlen
          simp only [List.length_append, toks_length]
          omega)] at hc'
        obtain ⟨h1, h2⟩ := ih hch (by simp only [List.length_append, toks_length] at hj; omega) hc'
        refine ⟨by rw [h1]; rfl, ?_⟩
        rw [h2, cmdToks_cons]
        simp only [List.append_assoc]
  | @stop v c hc hm =>
    intro done last j hchain hj hagree
    obtain rfl := modeAfter_unparsed hm
    have hlen := congrArg List.length hagree
    rw [List.length_take, Nat.min_eq_left (Nat.le_of_lt hj)] at hlen
    cases hchain with
    | nil => exact ⟨rfl, by simp⟩
    | @cons _ next' done' _ d hd hdm hch =>
      rw [cmdToks_cons, List.append_assoc] at hagree
      have h' : (toks Tree.Command.exit.tokens ++ [Received.endOfInput]).take j =
          (toks d.tokens ++ (cmdToks done' ++ toks Tree.Command.exit.tokens)).take j := by
        rw [hagree, List.take_of_length_le (by
          simp only [cmdToks_cons, List.length_append, toks_length] at hlen
          simp only [List.length_append, toks_length]
          omega)]
      rcases split_agree hc hd h' with ⟨hlt, -⟩ | ⟨rfl, -⟩
      · simp only [cmdToks_cons, List.length_append, toks_length, exit_tokens_length] at hlen
        rw [exit_tokens_length] at hlt
        omega
      · exact absurd rfl (modeAfter_read hdm).1
  | @refused v c hc hm =>
    intro done last j hchain hj hagree
    have hlen := congrArg List.length hagree
    rw [List.length_take, Nat.min_eq_left (Nat.le_of_lt hj)] at hlen
    have hexit : c ≠ .exit := by
      rintro rfl
      simp [Tree.Command.modeAfter] at hm
    cases hchain with
    | nil =>
      rw [cmdToks_nil, List.nil_append] at hagree
      have h' : (toks c.tokens ++ []).take j = (toks Tree.Command.exit.tokens ++ []).take j := by
        rw [List.append_nil, hagree, List.append_nil, List.take_of_length_le (by
          simp only [cmdToks_nil, List.nil_append] at hlen; omega)]
      rcases split_agree hc (c' := .exit) (by trivial) h' with ⟨-, hlt⟩ | ⟨rfl, -⟩
      · simp only [cmdToks_nil, List.nil_append, toks_length, exit_tokens_length] at hlen
        rw [exit_tokens_length] at hlt
        omega
      · exact absurd rfl hexit
    | @cons _ next' done' _ d hd hdm hch =>
      rw [cmdToks_cons, List.append_assoc] at hagree
      have h' : (toks c.tokens ++ []).take j =
          (toks d.tokens ++ (cmdToks done' ++ toks Tree.Command.exit.tokens)).take j := by
        rw [List.append_nil, hagree, List.take_of_length_le (by
          simp only [cmdToks_cons, List.length_append, toks_length] at hlen
          simp only [List.length_append, toks_length]
          omega)]
      rcases split_agree hc hd h' with ⟨-, hlt⟩ | ⟨rfl, -⟩
      · simp only [cmdToks_cons, List.length_append, toks_length, exit_tokens_length] at hlen
        omega
      · rw [hm] at hdm
        cases hdm

/-- Where the items before a position of what a parser takes are those of commands, each followed
by more in a version, and then those of `exit`, the item there is the end of the input. -/
theorem takes_afterExit {version : BSmtLibSpec.Lexicon.Version} {cs : List Tree.Command}
    {taken : List Received} {ending : Ending} (h : Takes version cs taken ending) {j : Nat}
    (hj : j < taken.length) (hafter : AfterExit version (taken.take j)) :
    taken[j]? = some .endOfInput := by
  obtain ⟨done, last, hchain, hagree⟩ := hafter
  obtain ⟨-, htaken⟩ := takes_after_exit h hchain hj hagree
  have hlen := congrArg List.length hagree
  rw [List.length_take, Nat.min_eq_left (Nat.le_of_lt hj)] at hlen
  rw [htaken, List.getElem?_append_right (by omega)]
  simp [hlen]

theorem versionAt_head {version : BSmtLibSpec.Lexicon.Version} {c : Tree.Command}
    {rest : List Tree.Command} {j : Nat} (hj : j < c.tokens.length) :
    versionAt version (c :: rest) j = version := by
  simp [versionAt, hj]

/-- Two readings of items as what a parser takes, from the same version, agree on the version
in force at an item of both where they agree on the items before it. -/
theorem versionAt_unique {version : BSmtLibSpec.Lexicon.Version} {cs : List Tree.Command}
    {taken : List Received} {ending : Ending} (h : Takes version cs taken ending) :
    ∀ {cs' : List Tree.Command} {taken' : List Received} {ending' : Ending} {j : Nat},
    Takes version cs' taken' ending' → j < taken.length → j < taken'.length →
    taken.take j = taken'.take j → versionAt version cs j = versionAt version cs' j := by
  induction h with
  | done =>
    intro cs' taken' ending' j h' hj _ _
    simp only [List.length_cons, List.length_nil] at hj
    obtain rfl : j = 0 := by omega
    cases h' with
    | done => rfl
    | @command _ _ _ _ _ c => exact (versionAt_head (Nat.pos_of_ne_zero (tokens_ne_nil c))).symm
    | @stop _ c => exact (versionAt_head (Nat.pos_of_ne_zero (tokens_ne_nil c))).symm
    | @refused _ c => exact (versionAt_head (Nat.pos_of_ne_zero (tokens_ne_nil c))).symm
  | @command v next rest items ending c hc hm _ ih =>
    intro cs' taken' ending' j h' hj hj' hagree
    cases h' with
    | done =>
      simp only [List.length_cons, List.length_nil] at hj'
      obtain rfl : j = 0 := by omega
      exact versionAt_head (Nat.pos_of_ne_zero (tokens_ne_nil c))
    | @command _ next' rest' items' ending'' c' hc' hm' h'' =>
      rcases split_agree hc hc' hagree with ⟨hlt, hlt'⟩ | ⟨rfl, hle⟩
      · rw [versionAt_head hlt, versionAt_head hlt']
      · rw [hm] at hm'
        cases hm'
        have hn : ¬ j < c.tokens.length := by omega
        simp only [versionAt, hn, ↓reduceIte]
        obtain ⟨-, hnext⟩ := modeAfter_read hm
        rw [← hnext]
        have hl : (toks c.tokens).length = c.tokens.length := by simp [toks]
        rw [← hl] at hle ⊢
        exact ih h'' (by simp at hj; omega) (by simp at hj'; omega) (take_cancel hle hagree)
    | @stop _ c' hc' hm' =>
      rcases split_agree hc hc' hagree with ⟨hlt, hlt'⟩ | ⟨rfl, -⟩
      · rw [versionAt_head hlt, versionAt_head hlt']
      · rw [hm] at hm'
        cases hm'
    | @refused _ c' hc' hm' =>
      rcases split_agree hc hc' (items' := []) (by simpa using hagree) with ⟨hlt, hlt'⟩ | ⟨rfl, -⟩
      · rw [versionAt_head hlt, versionAt_head hlt']
      · rw [hm] at hm'
        cases hm'
  | @stop v c hc hm =>
    intro cs' taken' ending' j h' hj hj' hagree
    cases h' with
    | done =>
      simp only [List.length_cons, List.length_nil] at hj'
      obtain rfl : j = 0 := by omega
      exact versionAt_head (Nat.pos_of_ne_zero (tokens_ne_nil c))
    | @command _ next' rest' items' ending'' c' hc' hm' h'' =>
      rcases split_agree hc hc' hagree with ⟨hlt, hlt'⟩ | ⟨rfl, -⟩
      · rw [versionAt_head hlt, versionAt_head hlt']
      · rw [hm] at hm'
        cases hm'
    | @stop _ c' hc' hm' =>
      rcases split_agree hc hc' hagree with ⟨hlt, hlt'⟩ | ⟨rfl, -⟩
      · rw [versionAt_head hlt, versionAt_head hlt']
      · rfl
    | @refused _ c' hc' hm' =>
      rcases split_agree hc hc' (items' := []) (by simpa using hagree) with ⟨hlt, hlt'⟩ | ⟨rfl, -⟩
      · rw [versionAt_head hlt, versionAt_head hlt']
      · rw [hm] at hm'
  | @refused v c hc hm =>
    intro cs' taken' ending' j h' hj hj' hagree
    have hlt : j < c.tokens.length := by simpa using hj
    rw [versionAt_head hlt]
    cases h' with
    | done =>
      simp only [List.length_cons, List.length_nil] at hj'
      obtain rfl : j = 0 := by omega
      rfl
    | @command _ next' rest' items' ending'' c' hc' hm' h'' =>
      rcases split_agree hc hc' (items := []) (by simpa using hagree) with ⟨-, hlt'⟩ | ⟨rfl, -⟩
      · rw [versionAt_head hlt']
      · rw [hm] at hm'
        cases hm'
    | @stop _ c' hc' hm' =>
      rcases split_agree hc hc' (items := []) (by simpa using hagree) with ⟨-, hlt'⟩ | ⟨rfl, -⟩
      · rw [versionAt_head hlt']
      · rw [hm] at hm'
        cases hm'
    | @refused _ c' hc' hm' =>
      have hlt' : j < c'.tokens.length := by simpa using hj'
      rw [versionAt_head hlt']

theorem toks_head (c : Tree.Command) : ∃ inner, toks c.tokens = openItem :: inner := by
  obtain ⟨inner, h⟩ := BSmtLibSpec.Facts.Proofs.Parser.Simulation.command_tokens_open c
  exact ⟨inner.map .token, by simp [toks, h, openItem]⟩

theorem not_prefix_endOfInput (c : Tree.Command) (items : List Received) :
    ¬ toks c.tokens ++ items <+: [Received.endOfInput] := by
  obtain ⟨inner, h⟩ := toks_head c
  rw [h]
  rintro ⟨r, hr⟩
  simp [openItem] at hr

theorem not_endOfInput_prefix (c : Tree.Command) (items : List Received) :
    ¬ [Received.endOfInput] <+: toks c.tokens ++ items := by
  obtain ⟨inner, h⟩ := toks_head c
  rw [h]
  rintro ⟨r, hr⟩
  simp [openItem] at hr

/-- What a parser takes for some commands is no proper start of what it takes for others, read
from the same version. -/
theorem takes_prefix {version : BSmtLibSpec.Lexicon.Version} {cs : List Tree.Command}
    {taken : List Received} {ending : Ending} (h : Takes version cs taken ending) :
    ∀ {cs' : List Tree.Command} {taken' : List Received} {ending' : Ending},
    Takes version cs' taken' ending' → taken' <+: taken → taken' = taken ∧ ending' = ending := by
  induction h with
  | done =>
    intro cs' taken' ending' h' hp
    cases h' with
    | done => exact ⟨rfl, rfl⟩
    | @command _ _ _ items _ c => exact (not_prefix_endOfInput c items hp).elim
    | @stop _ c => exact (not_prefix_endOfInput c _ hp).elim
    | @refused _ c => exact (not_prefix_endOfInput c [] (by simpa using hp)).elim
  | @command v next rest items ending c hc hm _ ih =>
    intro cs' taken' ending' h' hp
    obtain ⟨r, hr⟩ := hp
    have agree : ∀ {c' : Tree.Command} {items' : List Received}, c'.Valid v →
        (toks c'.tokens ++ items') ++ r = toks c.tokens ++ items → c = c' := by
      intro c' items' hc' heq
      refine commands_agree hc hc' (items := items) (items' := items' ++ r)
        (j := (toks c.tokens).length + (toks c'.tokens).length) (by omega) (by omega) ?_
      rw [← heq, List.append_assoc]
    cases h' with
    | done => exact (not_endOfInput_prefix c items ⟨r, hr⟩).elim
    | @command _ next' rest' items' ending'' c' hc' hm' h'' =>
      obtain rfl := agree hc' hr
      rw [hm] at hm'
      cases hm'
      rw [List.append_assoc] at hr
      have hitems := List.append_cancel_left hr
      obtain ⟨rfl, rfl⟩ := ih h'' ⟨r, hitems⟩
      exact ⟨rfl, rfl⟩
    | @stop _ c' hc' hm' =>
      obtain rfl := agree hc' hr
      rw [hm] at hm'
      cases hm'
    | @refused _ c' hc' hm' =>
      obtain rfl := agree (items' := []) hc' (by simpa using hr)
      rw [hm] at hm'
      cases hm'
  | @stop v c hc hm =>
    intro cs' taken' ending' h' hp
    obtain ⟨r, hr⟩ := hp
    have agree : ∀ {c' : Tree.Command} {items' : List Received}, c'.Valid v →
        (toks c'.tokens ++ items') ++ r = toks c.tokens ++ [.endOfInput] → c = c' := by
      intro c' items' hc' heq
      refine commands_agree hc hc' (items := [.endOfInput]) (items' := items' ++ r)
        (j := (toks c.tokens).length + (toks c'.tokens).length) (by omega) (by omega) ?_
      rw [← heq, List.append_assoc]
    cases h' with
    | done => exact (not_endOfInput_prefix c _ ⟨r, hr⟩).elim
    | @command _ next' rest' items' ending'' c' hc' hm' h'' =>
      obtain rfl := agree hc' hr
      rw [hm] at hm'
      cases hm'
    | @stop _ c' hc' hm' =>
      obtain rfl := agree hc' hr
      exact ⟨rfl, rfl⟩
    | @refused _ c' hc' hm' =>
      obtain rfl := agree (items' := []) hc' (by simpa using hr)
      rw [hm] at hm'
      cases hm'
  | @refused v c hc hm =>
    intro cs' taken' ending' h' hp
    obtain ⟨r, hr⟩ := hp
    have agree : ∀ {c' : Tree.Command} {items' : List Received}, c'.Valid v →
        (toks c'.tokens ++ items') ++ r = toks c.tokens ++ [] → c = c' := by
      intro c' items' hc' heq
      refine commands_agree hc hc' (items := []) (items' := items' ++ r)
        (j := (toks c.tokens).length + (toks c'.tokens).length) (by omega) (by omega) ?_
      rw [← heq, List.append_assoc]
    cases h' with
    | done => exact (not_endOfInput_prefix c [] ⟨r, by simpa using hr⟩).elim
    | @command _ next' rest' items' ending'' c' hc' hm' h'' =>
      obtain rfl := agree (items' := items') hc' (by simpa using hr)
      rw [hm] at hm'
      cases hm'
    | @stop _ c' hc' hm' =>
      obtain rfl := agree (items' := [.endOfInput]) hc' (by simpa using hr)
      rw [hm] at hm'
      cases hm'
    | @refused _ c' hc' hm' =>
      obtain rfl := agree (items' := []) hc' (by simpa using hr)
      exact ⟨rfl, rfl⟩

end BSmtLib.Facts.Proofs.Parser.Rejection.Unique
