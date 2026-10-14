module

public import BSmtLibSpec.Facts.Proofs.Grammar.OneToOne
public import BSmtLibSpec.Facts.Lexicon.Examples
public import BSmtLibSpec.Parser

@[expose] public section

/-!
# The standard's examples of syntax

Examples the standard gives with its syntactic rules, checked against the grammar: the trees
they are, in which versions, and how a file is read; and the calls the traversal makes for a few
scripts, pinned by their recordings. Not trusted: these are proofs.
-/

namespace BSmtLibSpec.Facts.Grammar.Examples

open BSmtLibSpec.Lexicon BSmtLibSpec.Grammar
open BSmtLibSpec.Parser.Properties
open BSmtLibSpec.Grammar.Syntax
open BSmtLibSpec.Regex (chars)
open BSmtLibSpec.Facts.Proofs.Lexicon.Lemmas
open BSmtLibSpec.Facts.Proofs.Grammar.OneToOne

/-- The symbol `s`, written simple. -/
abbrev simple (s : String) : Tree.Symbol := ⟨chars s, false⟩

/-- The syntax token of the symbol `s`, written simple. -/
abbrev sym (s : String) : SyntaxToken := .symbol (simple s)

/-- The numeral `s`. -/
abbrev num (s : String) : SyntaxToken := .numeral (chars s)

/-- The identifier `s`, not indexed. -/
abbrev ident (s : String) : Tree.Identifier := ⟨simple s, []⟩

/-- The sort `s`, not applied. -/
abbrev sortOf (s : String) : Tree.«Sort» := .mk (ident s) []

/-- The term that is the identifier `s`. -/
abbrev var (s : String) : Tree.Term := .identifier (.plain (ident s))

/-- The numeral constant `s`. -/
abbrev numeral (s : String) : Tree.Term := .constant (.numeral (chars s))

/-- Two sorts with the same tokens are the same sort. -/
theorem sort_eq_of_tokens {s t : Tree.«Sort»} (h : s.tokens = t.tokens) : s = t := by
  have h₁ := readSort_tokens s [] (n := sizeOf s + sizeOf t + 1) (by omega)
  have h₂ := readSort_tokens t [] (n := sizeOf s + sizeOf t + 1) (by omega)
  rw [h, h₂] at h₁
  exact (Prod.mk.inj (Option.some.inj h₁)).1.symm

/-! ## Identifiers and sorts -/

/-- `(_ BitVec 3)` is a sort of 2.0. -/
example : (Tree.«Sort».mk ⟨Facts.Grammar.Examples.simple
    "BitVec", [.numeral (chars "3")]⟩ []).tokens =
      paren [word "_", Facts.Grammar.Examples.sym "BitVec", Facts.Grammar.Examples.num "3"] ∧
    (Tree.«Sort».mk ⟨Facts.Grammar.Examples.simple "BitVec", [.numeral (chars "3")]⟩ []).Valid
    .v2_0 := by
  refine ⟨rfl, ?_⟩
  simp [Tree.«Sort».Valid, Tree.«Sort».ValidAll, Tree.Identifier.Valid, Tree.Index.Valid]

/-- `(List (Array Int Real))` is a sort of 2.0. -/
example : (Tree.«Sort».mk (Facts.Grammar.Examples.ident "List") [.mk
    (Facts.Grammar.Examples.ident "Array") [Facts.Grammar.Examples.sortOf "Int",
    Facts.Grammar.Examples.sortOf "Real"]]).tokens =
    paren [Facts.Grammar.Examples.sym "List", .parenOpen, Facts.Grammar.Examples.sym "Array",
        Facts.Grammar.Examples.sym "Int", Facts.Grammar.Examples.sym "Real", .parenClose] := rfl

/-- `(_ move up)`, with a symbol as its index, is a sort from 2.5 on. -/
example : (Tree.«Sort».mk ⟨Facts.Grammar.Examples.simple
    "move", [.symbol (Facts.Grammar.Examples.simple "up")]⟩ []).Valid .v2_5 := by
  simp [Tree.«Sort».Valid, Tree.«Sort».ValidAll, Tree.Identifier.Valid, Tree.Index.Valid,
    versionAtLeast, Version.upTo]

/-- `(_ move up)` is no sort of 2.0, where indices are numerals: the only tree written so is
not one of 2.0. -/
example : ¬ ∃ s : Tree.«Sort», s.Valid .v2_0 ∧
    s.tokens = paren [word "_", Facts.Grammar.Examples.sym "move", Facts.Grammar.Examples.sym "up"]
        := by
  rintro ⟨s, hv, hs⟩
  have := Facts.Grammar.Examples.sort_eq_of_tokens
      (t := .mk ⟨Facts.Grammar.Examples.simple "move", [.symbol
          (Facts.Grammar.Examples.simple "up")]⟩ []) hs
  subst this
  simp [Tree.«Sort».Valid, Tree.Identifier.Valid, Tree.Index.Valid, versionAtLeast,
    Version.upTo] at hv

/-- `(Array Int Real)` is a sort of every version. -/
example : IsSort .v2_0 (paren [sym "Array", sym "Int", sym "Real"])
    (.mk (ident "Array") [sortOf "Int", sortOf "Real"]) := by
  refine ⟨?_, rfl⟩
  simp [Tree.Sort.Valid, Tree.Sort.ValidAll, Tree.Identifier.Valid]

/-! ## S-expressions and attributes -/

/-- `(a (b 1))` is an s-expression of every version. -/
example : IsSExpr .v2_0 (paren [sym "a", .parenOpen, sym "b", num "1", .parenClose])
    (.list [.symbol (simple "a"), .list [.symbol (simple "b"), .constant (.numeral (chars "1"))]])
    := by
  refine ⟨?_, rfl⟩
  simp [Tree.SExpr.Valid, Tree.SExpr.ValidAll]

/-- `(assert)`, with a reserved word, is an s-expression from 2.6 on, and none of 2.5. -/
example : IsSExpr .v2_6 (paren [word "assert"]) (.list [.reserved (chars "assert")]) ∧
    ¬ IsSExpr .v2_5 (paren [word "assert"]) (.list [.reserved (chars "assert")]) := by
  refine ⟨⟨?_, rfl⟩, fun h => ?_⟩
  · simp [Tree.SExpr.Valid, Tree.SExpr.ValidAll, versionAtLeast, Version.upTo, commandNames,
      addedCommandNames, chars]
  · simp [IsSExpr, Tree.SExpr.Valid, Tree.SExpr.ValidAll, versionAtLeast, Version.upTo] at h

/-- `:named a` is an attribute of every version. -/
example : IsAttribute .v2_0 [.keyword (chars "named"), sym "a"]
    ⟨chars "named", some (.symbol (simple "a"))⟩ := by
  refine ⟨?_, rfl⟩
  simp [Tree.Attribute.Valid, Tree.AttributeValue.Valid]

/-! ## Terms -/

/-- `(f x 1)` is a term of every version. -/
example : IsTerm .v2_0 (paren [Facts.Grammar.Examples.sym "f", Facts.Grammar.Examples.sym "x",
    Facts.Grammar.Examples.num "1"])
    (.application (.plain (Facts.Grammar.Examples.ident "f")) [Facts.Grammar.Examples.var "x",
    Facts.Grammar.Examples.numeral "1"]) := by
  refine ⟨?_, rfl⟩
  simp [Tree.Term.Valid, Tree.Term.ValidAll, Tree.QualIdentifier.Valid, Tree.Identifier.Valid]

/-! ## Commands -/

/-- `(declare-fun f (Int) Int)` is a command of 2.0. -/
example : IsCommand .v2_0
    (commandTokens "declare-fun" [Facts.Grammar.Examples.sym "f", .parenOpen,
    Facts.Grammar.Examples.sym "Int", .parenClose, Facts.Grammar.Examples.sym "Int"])
    (.declareFun (Facts.Grammar.Examples.simple "f") [Facts.Grammar.Examples.sortOf "Int"]
    (Facts.Grammar.Examples.sortOf "Int")) := by
  refine ⟨?_, rfl⟩
  simp [Tree.Command.Valid, Tree.«Sort».Valid, Tree.«Sort».ValidAll, Tree.Identifier.Valid]

/-- The list datatype of the standard:
`(declare-datatypes ((List 1)) ((par (T) ((nil) (cons (head T) (tail (List T)))))))`, a command
from 2.6 on. -/
example : IsCommand .v2_6
    (commandTokens "declare-datatypes"
      (paren (paren [Facts.Grammar.Examples.sym "List", Facts.Grammar.Examples.num "1"]) ++
        paren (paren (word "par" :: paren [Facts.Grammar.Examples.sym "T"] ++
          paren (paren [Facts.Grammar.Examples.sym "nil"] ++
            paren (Facts.Grammar.Examples.sym "cons" ::
                paren [Facts.Grammar.Examples.sym "head", Facts.Grammar.Examples.sym "T"] ++
              paren [Facts.Grammar.Examples.sym "tail", .parenOpen, Facts.Grammar.Examples.sym
                  "List", Facts.Grammar.Examples.sym "T", .parenClose]))))))
    (.declareDatatypes [⟨Facts.Grammar.Examples.simple "List", chars "1"⟩]
      [⟨[Facts.Grammar.Examples.simple "T"], [⟨Facts.Grammar.Examples.simple "nil", []⟩,
        ⟨Facts.Grammar.Examples.simple "cons",
          [⟨Facts.Grammar.Examples.simple "head", Facts.Grammar.Examples.sortOf "T"⟩,
              ⟨Facts.Grammar.Examples.simple "tail", .mk
                  (Facts.Grammar.Examples.ident "List") [Facts.Grammar.Examples.sortOf "T"]⟩]⟩]⟩])
                      := by
  refine ⟨?_, rfl⟩
  simp [Tree.Command.Valid, Tree.DatatypeDec.Valid, Tree.ConstructorDec.Valid,
    Tree.SelectorDec.Valid, Tree.«Sort».Valid, Tree.«Sort».ValidAll, Tree.Identifier.Valid,
    versionAtLeast, Version.upTo]

/-- `(check-sat-assuming (p (not q)))` has terms in 2.7 and propositional literals in 2.6: one
sequence of tokens, two trees, each of one version. -/
example :
    IsCommand .v2_7 (commandTokens "check-sat-assuming" (paren [Facts.Grammar.Examples.sym "p",
        .parenOpen, Facts.Grammar.Examples.sym "not", Facts.Grammar.Examples.sym "q", .parenClose]))
      (.checkSatAssuming [Facts.Grammar.Examples.var "p", .application
          (.plain (Facts.Grammar.Examples.ident "not")) [Facts.Grammar.Examples.var "q"]]) ∧
    IsCommand .v2_6 (commandTokens "check-sat-assuming" (paren [Facts.Grammar.Examples.sym "p",
        .parenOpen, Facts.Grammar.Examples.sym "not", Facts.Grammar.Examples.sym "q", .parenClose]))
      (.checkSatAssumingLiterals
        [.positive (Facts.Grammar.Examples.simple "p"), .negative
            (Facts.Grammar.Examples.simple "not") (Facts.Grammar.Examples.simple "q")]) := by
  refine ⟨⟨?_, rfl⟩, ⟨?_, rfl⟩⟩
  · simp [Tree.Command.Valid, Tree.Term.Valid, Tree.Term.ValidAll, Tree.QualIdentifier.Valid,
      Tree.Identifier.Valid, versionAtLeast, Version.upTo]
  · simp [Tree.Command.Valid, Tree.PropLiteral.Valid, versionAtLeast, Version.upTo]

/-! ## Version declarations -/

/-- `(set-info :smt-lib-version 2.6)` is a command of 2.7 too, read in 2.7; after it, the rest
of the file is read in 2.6. -/
example :
    IsCommand .v2_7 (commandTokens "set-info" [.keyword (chars "smt-lib-version"),
      .decimal (chars "2.6")])
      (.setInfo ⟨chars "smt-lib-version", some (.constant (.decimal (chars "2.6")))⟩) ∧
    Tree.Command.modeAfter .v2_7
      (.setInfo ⟨chars "smt-lib-version", some (.constant (.decimal (chars "2.6")))⟩) =
        some (.read .v2_6) := by
  refine ⟨⟨by simp [Tree.Command.Valid, Tree.Attribute.Valid, Tree.AttributeValue.Valid], rfl⟩,
    ?_⟩
  rfl

/-- A declaration of a version that is not supported cannot stand in a file. -/
example : Tree.Command.modeAfter .v2_7
    (.setInfo ⟨chars "smt-lib-version", some (.constant (.decimal (chars "3.0")))⟩) = none := by
  rfl

/-- `exit` stops the reading. -/
example : Tree.Command.modeAfter .v2_7 .exit = some .unparsed := rfl

/-! ## Reading a file -/

/-- `(exit)` followed by what is not even lexable is a file of one command: what follows `exit`
is not read. -/
example : File .v2_7 (chars "(exit)" ++ chars " \"") [.exit] := by
  refine File.From.stop (tokens := [⟨.parenOpen, 0, chars "("⟩, ⟨.reserved, 1, chars "exit"⟩,
    ⟨.parenClose, 5, chars ")"⟩]) ⟨?_, ⟨.parenClose, 5, chars ")"⟩, rfl, rfl⟩ ⟨trivial, rfl⟩ rfl
  apply Tokenization.From.token (category := .parenOpen) (w := []) (s := chars "(")
    (rest := chars "exit)") whitespace_nil rfl (Or.inl rfl)
  apply Tokenization.From.token (category := .reserved) (w := []) (s := chars "exit")
    (rest := chars ")") whitespace_nil (litOneOf_iff.mpr (by decide))
    (delimited_by (Or.inr (oneOf_one.mpr (by decide))))
  apply Tokenization.From.token (category := .parenClose) (w := []) (s := chars ")") (rest := [])
    whitespace_nil rfl (Or.inr (Or.inl rfl))
  exact Tokenization.From.done ⟨[], [], rfl, whitespace_nil, Or.inl rfl⟩

/-! ## The calls the traversal makes

The calls of the recording of a script (`BSmtLibSpec.Parser.Properties.record`), each handled value
the number of calls before it, the handler's switch to the starting version counted.
-/

instance (n : Nat) : OfNat Recorded.sort n := inferInstanceAs (OfNat Nat n)
instance (n : Nat) : OfNat Recorded.sExpr n := inferInstanceAs (OfNat Nat n)
instance (n : Nat) : OfNat Recorded.«attribute» n := inferInstanceAs (OfNat Nat n)
instance (n : Nat) : OfNat Recorded.term n := inferInstanceAs (OfNat Nat n)
instance (n : Nat) : OfNat Recorded.scope n := inferInstanceAs (OfNat Nat n)

/-- An empty script: the handler's switch to the starting version, then the end of the input. -/
example : record .v2_7 [] = [.handlerSwitch .v2_7, .arrive .endOfInput, .process .endOfInput] :=
  rfl

/-- A version declaration: the `set-info` is handled as any other; the producer's switch, which
is not a call, then the handler's switch follow it. -/
example : (record .v2_7
      [.setInfo ⟨chars "smt-lib-version", some (.constant (.decimal (chars "2.6")))⟩,
      .checkSat]).filter Event.isCall =
    [.handlerSwitch .v2_7,
      .call .attribute (.handleAttribute (chars "smt-lib-version")
        (some (.constant (.decimal (chars "2.6"))))),
      .call .nothing (.commandSetInfo 1),
      .handlerSwitch .v2_6,
      .call .nothing .commandCheckSat] := rfl

/-- `(exit)`: after its `)` and the handler's call for it, the producer discards the rest of the
input; the end of the input arrives after that, and nothing else. -/
example : (record .v2_7 [.exit, .checkSat]).drop 7 =
    [.call .nothing .commandExit, .producerDiscard, .arrive .endOfInput,
      .process .endOfInput] := rfl

/-- `(assert (let ((x 1)) x))`: the bound term, the start of the scope with the bindings, the
body, the end of the scope. -/
example : (record .v2_7 [.assert (.«let» [(Facts.Grammar.Examples.simple "x",
    Facts.Grammar.Examples.numeral "1")] (Facts.Grammar.Examples.var "x"))]).filter
      Event.isCall =
    [.handlerSwitch .v2_7,
      .call .term (.handleTerm (.constant (.numeral (chars "1")))),
      .call .scope (.startLet [(Facts.Grammar.Examples.simple "x", 1)]),
      .call .term (.handleTerm (.identifier (Facts.Grammar.Examples.ident "x") none)),
      .call .term (.endLet 2 3),
      .call .nothing (.commandAssert 4)] := rfl

/-- `(assert (match l ((nil 0) ((cons h t) h))))`: the scrutinee and its early check, each case
in its scope, its end with the scrutinee again, then the end of the match. -/
example : (record .v2_7 [.assert (.«match» (Facts.Grammar.Examples.var "l")
      [(.single (.symbol (Facts.Grammar.Examples.simple "nil")), Facts.Grammar.Examples.numeral
          "0"),
        (.constructor (Facts.Grammar.Examples.simple "cons") [.symbol
            (Facts.Grammar.Examples.simple "h"), .symbol
                (Facts.Grammar.Examples.simple "t")], Facts.Grammar.Examples.var "h")])]
      ).filter Event.isCall =
    [.handlerSwitch .v2_7,
      .call .term (.handleTerm (.identifier (Facts.Grammar.Examples.ident "l") none)),
      .call .nothing (.startMatch 1),
      .call .scope (.startMatchCase 1 (.single (.symbol (Facts.Grammar.Examples.simple "nil")))),
      .call .term (.handleTerm (.constant (.numeral (chars "0")))),
      .call .term (.endMatchCase 3 1 4),
      .call .scope (.startMatchCase 1
        (.constructor (Facts.Grammar.Examples.simple "cons") [.symbol
            (Facts.Grammar.Examples.simple "h"), .symbol (Facts.Grammar.Examples.simple "t")])),
      .call .term (.handleTerm (.identifier (Facts.Grammar.Examples.ident "h") none)),
      .call .term (.endMatchCase 6 1 7),
      .call .term (.endMatch 1 [(.single (.symbol (Facts.Grammar.Examples.simple "nil")), 5),
        (.constructor (Facts.Grammar.Examples.simple "cons") [.symbol
            (Facts.Grammar.Examples.simple "h"), .symbol (Facts.Grammar.Examples.simple "t")], 8)]),
      .call .nothing (.commandAssert 9)] := rfl

/-- `(assert (! p :a :b 1))`: the attribute `:a`, which has no value, is handled only after
`:b`, the token that shows it has none; `:b` with its value right after the value. -/
example : (record .v2_7 [.assert (.annotated (Facts.Grammar.Examples.var "p")
      [⟨chars "a", none⟩, ⟨chars "b", some (.constant (.numeral (chars "1")))⟩])]).filter
        Event.isCall =
    [.handlerSwitch .v2_7,
      .call .term (.handleTerm (.identifier (Facts.Grammar.Examples.ident "p") none)),
      .call .attribute (.handleAttribute (chars "a") none),
      .call .attribute (.handleAttribute (chars "b") (some (.constant (.numeral (chars "1"))))),
      .call .term (.annotateTerm 1 [2, 3]),
      .call .nothing (.commandAssert 4)] := rfl

/-- The same script: before `:b` arrives, the item at position 6, `:a` is not handled yet;
before the item after it arrives, it is. -/
example :
    (eventsBefore 6 (record .v2_7 [.assert (.annotated (Facts.Grammar.Examples.var "p")
      [⟨chars "a", none⟩, ⟨chars "b", some (.constant (.numeral (chars "1")))⟩])])).filter
        Event.isCall =
      [.handlerSwitch .v2_7, .call .term (.handleTerm
          (.identifier (Facts.Grammar.Examples.ident "p") none))] ∧
    (eventsBefore 7 (record .v2_7 [.assert (.annotated (Facts.Grammar.Examples.var "p")
      [⟨chars "a", none⟩, ⟨chars "b", some (.constant (.numeral (chars "1")))⟩])])).filter
        Event.isCall =
      [.handlerSwitch .v2_7, .call .term (.handleTerm
          (.identifier (Facts.Grammar.Examples.ident "p") none)),
        .call .attribute (.handleAttribute (chars "a") none)] := ⟨rfl, rfl⟩

/-- `(define-funs-rec ((f () Int) (g () Int)) (1 2))`: the signatures, then each body between its
start, with its signature, and its end. -/
example : (record .v2_7
      [.defineFunsRec [⟨Facts.Grammar.Examples.simple "f", [], Facts.Grammar.Examples.sortOf
          "Int"⟩, ⟨Facts.Grammar.Examples.simple "g", [], Facts.Grammar.Examples.sortOf "Int"⟩]
      [Facts.Grammar.Examples.numeral "1", Facts.Grammar.Examples.numeral "2"]]).filter
          Event.isCall =
    [.handlerSwitch .v2_7,
      .call .sort (.handleSort (Facts.Grammar.Examples.ident "Int") []),
      .call .sort (.handleSort (Facts.Grammar.Examples.ident "Int") []),
      .call .nothing (.startDefineFunsRec [⟨Facts.Grammar.Examples.simple "f", [], 1⟩,
          ⟨Facts.Grammar.Examples.simple "g", [], 2⟩]),
      .call .nothing (.startRecursiveBody ⟨Facts.Grammar.Examples.simple "f", [], 1⟩),
      .call .term (.handleTerm (.constant (.numeral (chars "1")))),
      .call .nothing (.endRecursiveBody 5),
      .call .nothing (.startRecursiveBody ⟨Facts.Grammar.Examples.simple "g", [], 2⟩),
      .call .term (.handleTerm (.constant (.numeral (chars "2")))),
      .call .nothing (.endRecursiveBody 8),
      .call .nothing .endDefineFunsRec] := rfl

/-- The same script: the start of the second body comes when its first token, `2`, the item at
position 18, arrives: not before that arrival, and before its processing. -/
example :
    (eventsBefore 18 (record .v2_7
      [.defineFunsRec [⟨Facts.Grammar.Examples.simple "f", [], Facts.Grammar.Examples.sortOf
          "Int"⟩, ⟨Facts.Grammar.Examples.simple "g", [], Facts.Grammar.Examples.sortOf "Int"⟩]
      [Facts.Grammar.Examples.numeral "1", Facts.Grammar.Examples.numeral "2"]])).filter
          Event.isCall =
      [.handlerSwitch .v2_7,
        .call .sort (.handleSort (Facts.Grammar.Examples.ident "Int") []),
        .call .sort (.handleSort (Facts.Grammar.Examples.ident "Int") []),
        .call .nothing (.startDefineFunsRec [⟨Facts.Grammar.Examples.simple "f", [], 1⟩,
            ⟨Facts.Grammar.Examples.simple "g", [], 2⟩]),
        .call .nothing (.startRecursiveBody ⟨Facts.Grammar.Examples.simple "f", [], 1⟩),
        .call .term (.handleTerm (.constant (.numeral (chars "1")))),
        .call .nothing (.endRecursiveBody 5)] ∧
    (eventsBeforeProcessing 18 (record .v2_7
      [.defineFunsRec [⟨Facts.Grammar.Examples.simple "f", [], Facts.Grammar.Examples.sortOf
          "Int"⟩, ⟨Facts.Grammar.Examples.simple "g", [], Facts.Grammar.Examples.sortOf "Int"⟩]
      [Facts.Grammar.Examples.numeral "1", Facts.Grammar.Examples.numeral "2"]])).filter
          Event.isCall =
      [.handlerSwitch .v2_7,
        .call .sort (.handleSort (Facts.Grammar.Examples.ident "Int") []),
        .call .sort (.handleSort (Facts.Grammar.Examples.ident "Int") []),
        .call .nothing (.startDefineFunsRec [⟨Facts.Grammar.Examples.simple "f", [], 1⟩,
            ⟨Facts.Grammar.Examples.simple "g", [], 2⟩]),
        .call .nothing (.startRecursiveBody ⟨Facts.Grammar.Examples.simple "f", [], 1⟩),
        .call .term (.handleTerm (.constant (.numeral (chars "1")))),
        .call .nothing (.endRecursiveBody 5),
        .call .nothing (.startRecursiveBody ⟨Facts.Grammar.Examples.simple "g", [], 2⟩)] :=
            ⟨rfl, rfl⟩

/-- The list datatype of the standard: the sorts declared, then the datatype with its parameter,
the sorts of its selectors, its end, and the end of the declarations. -/
example : (record .v2_7 [.declareDatatypes [⟨Facts.Grammar.Examples.simple "List", chars "1"⟩]
      [⟨[Facts.Grammar.Examples.simple "T"], [⟨Facts.Grammar.Examples.simple "nil", []⟩,
        ⟨Facts.Grammar.Examples.simple "cons",
          [⟨Facts.Grammar.Examples.simple "head", Facts.Grammar.Examples.sortOf "T"⟩,
              ⟨Facts.Grammar.Examples.simple "tail", .mk
                  (Facts.Grammar.Examples.ident "List") [Facts.Grammar.Examples.sortOf "T"]⟩]⟩]⟩]]
      ).filter Event.isCall =
    [.handlerSwitch .v2_7,
      .call .nothing (.startDeclareDatatypes [(Facts.Grammar.Examples.simple "List", chars "1")]),
      .call .nothing (.startDatatypeDeclaration [Facts.Grammar.Examples.simple "T"]),
      .call .sort (.handleSort (Facts.Grammar.Examples.ident "T") []),
      .call .sort (.handleSort (Facts.Grammar.Examples.ident "T") []),
      .call .sort (.handleSort (Facts.Grammar.Examples.ident "List") [4]),
      .call .nothing (.endDatatypeDeclaration [⟨Facts.Grammar.Examples.simple "nil", []⟩,
        ⟨Facts.Grammar.Examples.simple "cons", [(Facts.Grammar.Examples.simple "head", 3),
            (Facts.Grammar.Examples.simple "tail", 5)]⟩]),
      .call .nothing .endDeclareDatatypes] := rfl

end BSmtLibSpec.Facts.Grammar.Examples
