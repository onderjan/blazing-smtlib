import BSmtLib.ParserProofs.Trace
import BSmtLib.ParserProofs.Rejection.Library
import BSmtLib.SpecChecks.Lemmas
import BSmtLib.EndToEnd.Adapters

/-!
# The library's script parser as a consumer of the lexer spec

`scriptConsumer version` is a consumer as `BSmtLibSpec.Lexer` states consumers (`BSmtLibSpec.Lexer.Consumer`):
what it answers after each token is what the library's script parser does in its recording run
on the tokens taken so far (`Rejection.libraryParser`), each read as the parser's token that
stands for it (`itemOf`); it asks the producer for what that run asks for after the last token's
processing: a switch of the version, discarding. It and `itemOf` are adapters, in
`EndToEnd.Adapters`; this module proves what they do.

Along the tokens of a script, its answers are those the parser properties give: it goes on at
every token but the end of the input, and breaks there; it switches after each version
declaration and discards after `exit` (`answer_takes`, `switchTo_takes`, `discards_takes`).
-/

namespace BSmtLib.EndToEnd

open BSmtLibSpec BSmtLibSpec.Lexicon BSmtLibSpec.Grammar BSmtLibSpec.Parser
open BSmtLibSpec.Parser.Properties
open BSmtLibSpec.Grammar.Syntax BSmtLibSpec.Grammar.File BSmtLibSpec.Grammar.Properties
open BSmtLibSpec.Lexicon.Properties
open BSmtLibSpec.Regex (Chars chars)
open BSmtLibSpec.Lexer (Handed Consumer Answer)
open BSmtLibSpec.Parser.Traversal
open BSmtLib.ParserProofs
open BSmtLib.ParserProofs.Rejection
open BSmtLib.Parser (Input)

/-! ## The parser's token for a handed token -/

theorem received_itemOf_ne (handed : Handed) : Bridge.received (itemOf handed) ≠ none := by
  unfold itemOf
  split <;> (try split) <;> simp [Bridge.received]

/-- The end of the input stands for the end of the input. -/
theorem rcv_itemOf_endOfFile (input : Chars) : rcv (itemOf (BSmtLibSpec.Lexer.endOfFile input)) =
    .endOfInput := rfl

/-- The end of the input located anywhere stands for the end of the input. -/
theorem rcv_itemOf_endOfFileAt (location : BSmtLibSpec.Lexer.Location) :
    rcv (itemOf (BSmtLibSpec.Lexer.endOfFileAt location)) = .endOfInput := rfl

/-- A token of a tokenisation, handed over, stands for what it is in the grammar. -/
theorem rcv_itemOf_handed {version : Lexicon.Version} (input : Chars) {token : Lexicon.Token}
    (hcat : categoryRegex version token.category token.text) :
    rcv (itemOf (token.handed version input)) = .token (SyntaxToken.ofToken version token) := by
  obtain ⟨category, offset, text⟩ := token
  cases category with
  | reserved =>
    have hmem : text ∈ (basicReservedWords version ++ commandNames version).map chars :=
      SpecChecks.Lexicon.litOneOf_iff.mp hcat
    obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hmem
    obtain ⟨r, hr⟩ := Option.isSome_iff_exists.mp (decodeReserved_isSome version s hs)
    have hkind : (Token.reservedKind version ⟨.reserved, offset, chars s⟩).isSome := by
      simp only [Token.reservedKind, ne_eq, not_true_eq_false, ite_false]
      split <;> rfl
    obtain ⟨kind, hk⟩ := Option.isSome_iff_exists.mp hkind
    simp only [itemOf, Token.handed, Category.type, Token.content, hk, hr, rcv, Bridge.received,
      Option.getD_some, decodeReserved_spec hr, SyntaxToken.ofToken]
  | simpleSymbol =>
    have hkind : Token.reservedKind version ⟨.simpleSymbol, offset, text⟩ = none := by
      simp [Token.reservedKind]
    simp only [itemOf, Token.handed, Category.type, Token.content, hkind, rcv, Bridge.received,
      Option.getD_some, SyntaxToken.ofToken]
    show Received.token (.symbol ⟨Bridge.chars (bytesOf text), false⟩) = _
    rw [chars_bytesOf]
  | quotedSymbol =>
    simp only [itemOf, Token.handed, Category.type, rcv, Bridge.received, Option.getD_some,
      SyntaxToken.ofToken]
    show Received.token (.symbol ⟨Bridge.chars (bytesOf _), true⟩) = _
    rw [chars_bytesOf]
  | numeral =>
    simp only [itemOf, Token.handed, Category.type, rcv, Bridge.received, Option.getD_some,
      SyntaxToken.ofToken, Token.content]
    show Received.token (.numeral (Bridge.chars (bytesOf text))) = _
    rw [chars_bytesOf]
  | decimal =>
    simp only [itemOf, Token.handed, Category.type, rcv, Bridge.received, Option.getD_some,
      SyntaxToken.ofToken, Token.content]
    show Received.token (.decimal (Bridge.chars (bytesOf text))) = _
    rw [chars_bytesOf]
  | hexadecimal =>
    simp only [itemOf, Token.handed, Category.type, rcv, Bridge.received, Option.getD_some,
      SyntaxToken.ofToken]
    show Received.token (.hexadecimal (Bridge.chars (bytesOf _))) = _
    rw [chars_bytesOf]
  | binary =>
    simp only [itemOf, Token.handed, Category.type, rcv, Bridge.received, Option.getD_some,
      SyntaxToken.ofToken]
    show Received.token (.binary (Bridge.chars (bytesOf _))) = _
    rw [chars_bytesOf]
  | string =>
    simp only [itemOf, Token.handed, Category.type, rcv, Bridge.received, Option.getD_some,
      SyntaxToken.ofToken]
    show Received.token (.string (Bridge.chars (bytesOf _))) = _
    rw [chars_bytesOf]
  | keyword =>
    simp only [itemOf, Token.handed, Category.type, rcv, Bridge.received, Option.getD_some,
      SyntaxToken.ofToken]
    show Received.token (.keyword (Bridge.chars (bytesOf _))) = _
    rw [chars_bytesOf]
  | parenOpen => rfl
  | parenClose => rfl

/-! ## The consumer -/

theorem scriptConsumer_concrete (version : Lexicon.Version) :
    (scriptConsumer version).concrete = false := rfl

/-- For a consumer that does not take whitespace and comments, the entries ready from an offset
are the tokens of the input from there, read on its own. -/
theorem readyFrom_false (feed : Lexicon.Version → List Regex.Chars → Bool → BSmtLibSpec.Lexer.Fed)
    (version : Lexicon.Version) (input : Regex.Chars) (ended : Bool) (offset : Nat) :
    BSmtLibSpec.Lexer.readyFrom feed false version input ended offset =
      BSmtLibSpec.Lexer.segment feed version input ended offset := by
  simp [BSmtLibSpec.Lexer.readyFrom, BSmtLibSpec.Lexer.withLayout]

theorem scriptConsumer_breaksAtEnd (version : Lexicon.Version) :
    (scriptConsumer version).BreaksAtEnd := by
  intro taken token htype
  simp only [scriptConsumer, List.getLast?_append, List.getLast?_singleton, Option.some_or,
    Option.map_some, htype, decide_true]
  generalize (libraryParser.parse version ((taken ++ [token]).map libItem)).2 = ending
  cases ending <;> simp [answerOf]

/-! ## Along what a parser takes -/

/-- In what a parser takes, the end of the input can only be the last item. -/
theorem takes_endOfInput_last {version : Lexicon.Version} {commands : List Tree.Command}
    {taken : List Received} {ending : Ending} (h : Takes version commands taken ending) :
    ∀ i, i + 1 < taken.length → taken[i]? ≠ some .endOfInput := by
  induction h with
  | done => intro i hi; simp at hi
  | @command v next rest items ending first hv hm _ ih =>
    intro i hi
    by_cases hlt : i < first.tokens.length
    · rw [List.getElem?_append_left (by simpa using hlt)]
      simp [List.getElem?_map, List.getElem?_eq_getElem hlt]
    · rw [List.getElem?_append_right (by simp; omega)]
      simp only [List.length_append, List.length_map] at hi
      simp only [List.length_map]
      exact ih _ (by omega)
  | @stop v last hv hm =>
    intro i hi
    simp only [List.length_append, List.length_map, List.length_singleton] at hi
    rw [List.getElem?_append_left (by simp; omega)]
    simp [List.getElem?_map, List.getElem?_eq_getElem (show i < last.tokens.length by omega)]
  | @refused v last hv hm =>
    intro i hi
    simp [List.getElem?_map]

theorem stands_libItem (handed : List Handed) :
    (handed.map libItem).map libraryParser.stands = handed.map (rcv ∘ itemOf) := by
  simp [libraryParser, libItem, Function.comp_def]

/-- The recording run of the library's parser on tokens that stand for a start of what a parser
takes for commands: the traversal's events before the next item, and waiting, or at the end, ending
as what it takes does. -/
theorem parse_takes {version : Lexicon.Version} {commands : List Tree.Command}
    {taken : List Received} {ending : Ending} (htakes : Takes version commands taken ending)
    {handed : List Handed} (hst : handed.map (rcv ∘ itemOf) = taken.take handed.length)
    (hlen : handed.length ≤ taken.length) :
    libraryParser.parse version (handed.map libItem) =
      (eventsBefore handed.length (record version commands),
        if handed.length < taken.length then .waiting else ending) := by
  have hof := takes_ofVersion htakes
  obtain ⟨rest, hrest⟩ := items_for (taken.drop handed.length) fun i r hr => by
    rw [List.getElem?_drop] at hr
    exact inputOf_isSome (hof _ r hr)
  have hall : (handed.map libItem ++ rest : List LibItem).map (rcv ∘ Subtype.val) = taken := by
    rw [List.map_append, hrest]
    have h1 : (handed.map libItem).map (rcv ∘ Subtype.val) = handed.map (rcv ∘ itemOf) := by
      simp [libItem, Function.comp_def]
    rw [h1, hst, List.take_append_drop]
  have := library_follows version commands taken ending (handed.map libItem ++ rest) htakes hall
    handed.length hlen
  have heq : (handed.map libItem ++ rest : List LibItem).take handed.length =
      handed.map libItem := by
    rw [List.take_append_of_le_length (by simp), List.take_of_length_le (by simp)]
  erw [heq] at this
  exact this

theorem getLast_type_ne_endOfFile {version : Lexicon.Version} {commands : List Tree.Command}
    {taken : List Received} {ending : Ending} (htakes : Takes version commands taken ending)
    {handed : List Handed} (hst : handed.map (rcv ∘ itemOf) = taken.take handed.length)
    (hlt : handed.length < taken.length) :
    handed.getLast?.map (·.type) ≠ some .endOfFile := by
  intro h
  obtain ⟨last, hlast, htype⟩ := Option.map_eq_some_iff.mp h
  have hpos : 0 < handed.length := by
    cases handed with
    | nil => simp at hlast
    | cons _ _ => simp
  have hget : handed[handed.length - 1]? = some last := by
    rw [List.getLast?_eq_getElem?] at hlast
    exact hlast
  have := congrArg (·[handed.length - 1]?) hst
  simp only [List.getElem?_map, hget, Option.map_some, List.getElem?_take,
    show handed.length - 1 < handed.length by omega, ite_true, Function.comp_apply] at this
  have hitem : rcv (itemOf last) = .endOfInput := by
    simp [itemOf, htype, rcv, Bridge.received]
  rw [hitem] at this
  exact takes_endOfInput_last htakes (handed.length - 1) (by omega) this.symm

/-- The consumer's answer on tokens that stand for a start of what a parser takes: it goes on
before the end, and at the end answers as what it takes ends. -/
theorem answer_takes {version : Lexicon.Version} {commands : List Tree.Command}
    {taken : List Received} {ending : Ending} (htakes : Takes version commands taken ending)
    {handed : List Handed} (hst : handed.map (rcv ∘ itemOf) = taken.take handed.length)
    (hlen : handed.length ≤ taken.length) :
    (scriptConsumer version).answer handed =
      if handed.length < taken.length then .continue
      else answerOf (handed.getLast?.map (·.type) = some .endOfFile) ending := by
  simp only [scriptConsumer, parse_takes htakes hst hlen]
  split
  · rename_i hlt
    simp [answerOf, getLast_type_ne_endOfFile htakes hst hlt]
  · rfl

/-- The consumer's requests on tokens that stand for a start of what a parser receives for a
script: those of `requestsAt` at the last token. -/
theorem requests_takes {version : Lexicon.Version} {commands : List Tree.Command}
    (hscript : Script version commands) {handed : List Handed}
    (hst : handed.map (rcv ∘ itemOf) = (received commands).take handed.length)
    (hpos : 0 < handed.length) (hlen : handed.length ≤ (received commands).length) :
    (scriptConsumer version).switchTo handed = (requestsAt commands (handed.length - 1)).1 ∧
      (scriptConsumer version).discards handed = (requestsAt commands (handed.length - 1)).2 := by
  simp only [scriptConsumer, parse_takes (takes_of_script hscript) hst hlen]
  have := requests_record hscript (handed.length - 1) (by omega)
  rw [show handed.length - 1 + 1 = handed.length by omega] at this
  exact this

end BSmtLib.EndToEnd
