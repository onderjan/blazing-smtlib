module

public import BSmtLibSpec.Facts.Proofs.Reader.Lexing
public import BSmtLibSpec.Facts.Proofs.Reader.Words
public import BSmtLibSpec.Facts.Proofs.Reader.Requests

@[expose] public section

/-!
# A parser as a lexer's consumer

What a parser that follows the traversal answers as a lexer's consumer, on tokens that stand for
the start of what a parser takes for commands (`parse_of_takes`): its run is the traversal's,
cut before the next item, so it continues, breaks at the end of the input, and asks for the
switch and the discarding that the traversal asks for after the `)` of a command
(`answer_of_takes`, `switchTo_of_takes`, `discards_of_takes`).

A parser is told only what a token stands for. To apply what is known of a parser on a whole
script, the tokens handed over so far are completed by tokens that stand for the rest of the
script (`handedFor`); each item a parser takes is one that a lexer can hand over in 2.7, by
`takes_reserved`.

Not trusted: everything here is proved.
-/

namespace BSmtLibSpec.Facts.Proofs.Reader.Consumer

open BSmtLibSpec.Lexicon BSmtLibSpec.Lexer BSmtLibSpec.Grammar
open BSmtLibSpec.Regex (Chars)
open BSmtLibSpec.Parser BSmtLibSpec.Reader
open BSmtLibSpec.Parser.Properties
open BSmtLibSpec.Facts.Proofs.Reader.Requests BSmtLibSpec.Facts.Proofs.Reader.Words

/-- The location at the start of an input. -/
def origin : Location := ⟨0, 0, 0⟩

/-- A token handed over with the type, the reserved kind and the content, at the origin. -/
def handedAt (type : TokenType) (reserved : Option ReservedKind) (content : Chars) : Handed :=
  { type, start := origin, «end» := origin, reserved, content }

/-- A token that stands for the syntax token. -/
def handedOfToken : SyntaxToken → Handed
  | .parenOpen => handedAt .parenOpen none []
  | .parenClose => handedAt .parenClose none []
  | .numeral digits => handedAt .numeral none digits
  | .decimal text => handedAt .decimal none text
  | .hexadecimal digits => handedAt .hexadecimal none digits
  | .binary digits => handedAt .binary none digits
  | .string content => handedAt .string none content
  | .symbol ⟨name, false⟩ => handedAt .unquotedSymbol none name
  | .symbol ⟨name, true⟩ => handedAt .quotedSymbol none name
  | .keyword name => handedAt .keyword none name
  | .reserved word => handedAt .unquotedSymbol (some .general) word

/-- A token that stands for the item. -/
def handedFor : Traversal.Received → Handed
  | .token token => handedOfToken token
  | .endOfInput => endOfFileAt origin

theorem received_handedFor (item : Traversal.Received) :
    (handedFor item).received = some item := by
  rcases item with token | _
  · rcases token with _ | _ | _ | _ | _ | _ | _ | ⟨name, quoted⟩ | _ | _
    all_goals try rfl
    cases quoted <;> rfl
  · rfl

/-- The hypothesis of `LexesThenParses` on the items a parser takes for the tokens. -/
def StandsFor (parser : RecordingParser) (item : Handed → parser.Item) : Prop :=
  ∀ handed received version, handed.received = some received →
    received.OfVersion version → parser.stands (item handed) = received

/-- What the tokens stand for, for the parser. -/
abbrev stood (parser : RecordingParser) (item : Handed → parser.Item) (taken : List Handed) :
    List Traversal.Received :=
  taken.map fun handed => parser.stands (item handed)

variable {parser : RecordingParser} {item : Handed → parser.Item}

theorem stood_append (taken more : List Handed) :
    stood parser item (taken ++ more) = stood parser item taken ++ stood parser item more := by
  simp [stood]

/-- Every item that a parser takes is one that a lexer hands over in 2.7. -/
theorem ofVersion_of_takes {version : Version} {commands : List Tree.Command}
    {taken : List Traversal.Received} {ending : Ending} (h : Takes version commands taken ending)
    {received : Traversal.Received} (hr : received ∈ taken) : received.OfVersion .v2_7 := by
  rcases received with token | _
  · cases token with
    | reserved word => exact takes_reserved h hr
    | _ => trivial
  · trivial

/-- On tokens that stand for the start of what a parser takes for commands, a parser that
follows the traversal has made the traversal's events before the next item. -/
theorem parse_of_takes (hF : FollowsTheTraversal parser) (hI : StandsFor parser item)
    {version : Version} {commands : List Tree.Command} {all : List Traversal.Received}
    {ending : Ending} (ht : Takes version commands all ending) {taken : List Handed}
    (hs : stood parser item taken = all.take taken.length) (hl : taken.length ≤ all.length) :
    parser.parse version (taken.map item) =
      (eventsBefore taken.length (record version commands),
        if taken.length < all.length then .waiting else ending) := by
  let items := taken.map item ++ (all.drop taken.length).map fun r => item (handedFor r)
  have hmap : items.map parser.stands = all := by
    simp only [items, List.map_append, List.map_map]
    have hd : List.map (parser.stands ∘ fun r => item (handedFor r)) (all.drop taken.length) =
        all.drop taken.length := by
      conv => rhs; rw [← List.map_id (all.drop taken.length)]
      refine List.map_congr_left fun r hr => ?_
      exact hI _ r .v2_7 (received_handedFor r)
        (ofVersion_of_takes ht (List.mem_of_mem_drop hr))
    rw [hd]
    have : List.map (parser.stands ∘ item) taken = all.take taken.length := hs
    rw [this, List.take_append_drop]
  have := hF version commands all ending items ht hmap taken.length hl
  have htake : items.take taken.length = taken.map item := by
    simp [items]
  rwa [htake] at this

/-- The consumer's answer, given the run of the parser. -/
theorem answer_eq (version : Version) (taken : List Handed) :
    (Reader.consumer parser item version).answer taken =
      match (parser.parse version (taken.map item)).2 with
      | .finished => .break ()
      | .waiting =>
        if taken.getLast?.map (·.type) = some .endOfFile then .fail () else .continue
      | .rejected | .failed _ => .fail () := rfl

/-- A parser as a lexer's consumer breaks at the end of the input at the latest. -/
theorem consumer_breaksAtEnd (version : Version) :
    (Reader.consumer parser item version).BreaksAtEnd := by
  intro taken token htype
  rw [answer_eq]
  split <;> simp [htype]

variable (hF : FollowsTheTraversal parser) (hI : StandsFor parser item)
include hF hI

/-- On tokens that stand for a strict start of what a parser takes, the last of which is not
the end of the file, the parser continues. -/
theorem answer_of_takes {version : Version} {commands : List Tree.Command}
    {all : List Traversal.Received} {ending : Ending} (ht : Takes version commands all ending)
    {taken : List Handed} (hs : stood parser item taken = all.take taken.length)
    (hl : taken.length < all.length)
    (hend : taken.getLast?.map (·.type) ≠ some .endOfFile) :
    (Reader.consumer parser item version).answer taken = .continue := by
  rw [answer_eq, parse_of_takes hF hI ht hs (Nat.le_of_lt hl)]
  simp [hl, hend]

/-- On tokens that stand for all that a parser takes for a script, the parser breaks. -/
theorem answer_of_script {version : Version} {commands : List Tree.Command}
    {all : List Traversal.Received} (ht : Takes version commands all .finished)
    {taken : List Handed} (hs : stood parser item taken = all) :
    (Reader.consumer parser item version).answer taken = .break () := by
  have hl : taken.length = all.length := by rw [← hs]; simp
  rw [answer_eq, parse_of_takes hF hI ht (by rw [hs, hl, List.take_length]) (by omega)]
  simp [hl]

/-- On tokens that stand for a start of what a parser takes, the parser switches as the
traversal does. -/
theorem switchTo_of_takes {version : Version} {commands : List Tree.Command}
    {all : List Traversal.Received} {ending : Ending} (ht : Takes version commands all ending)
    {taken : List Handed} (hs : stood parser item taken = all.take taken.length)
    (h₁ : 1 ≤ taken.length) (hl : taken.length ≤ all.length) :
    (Reader.consumer parser item version).switchTo taken =
    (requestsAt commands taken.length).1 := by
  show (requestsAfterLast (parser.parse version (taken.map item)).1).1 = _
  rw [parse_of_takes hF hI ht hs hl, requestsAfterLast_record ht h₁]

/-- On tokens that stand for a start of what a parser takes, the parser has the rest discarded
as the traversal does. -/
theorem discards_of_takes {version : Version} {commands : List Tree.Command}
    {all : List Traversal.Received} {ending : Ending} (ht : Takes version commands all ending)
    {taken : List Handed} (hs : stood parser item taken = all.take taken.length)
    (h₁ : 1 ≤ taken.length) (hl : taken.length ≤ all.length) :
    (Reader.consumer parser item version).discards taken =
    (requestsAt commands taken.length).2 := by
  show (requestsAfterLast (parser.parse version (taken.map item)).1).2 = _
  rw [parse_of_takes hF hI ht hs hl, requestsAfterLast_record ht h₁]

end BSmtLibSpec.Facts.Proofs.Reader.Consumer
