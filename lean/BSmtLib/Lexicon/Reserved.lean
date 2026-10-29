module

public import BSmtLib.Version
import all Init.Data.Array.Basic
import all Init.Data.String.Defs
import all Std.Data.ByteSlice

public section

/- LEAN: in Rust, `lexicon` declares `reserved` as a submodule and re-exports its types. Here the
root module `BSmtLib` imports this module, as it does the other modules of the lexicon, and
`BSmtLib.Token` imports it, as `Token` names `Reserved`. -/

namespace BSmtLib.Lexicon.Reserved

/-- General reserved word, e.g. `_`, `as` or `let`. -/
inductive GeneralReserved where
  /-- Reserved word `BINARY`. -/
  | binary
  /-- Reserved word `DECIMAL`. -/
  | decimal
  /-- Reserved word `HEXADECIMAL`. -/
  | hexadecimal
  /-- Reserved word `NUMERAL`. -/
  | numeral
  /-- Reserved word `STRING`. -/
  | string
  /-- Reserved word `_`. -/
  | underscore
  /-- Reserved word `!`. -/
  | exclamationMark
  /-- Reserved word `as`. -/
  | as
  /-- Reserved word `lambda`. -/
  | lambda
  /-- Reserved word `let`. -/
  | «let»
  /-- Reserved word `exists`. -/
  | «exists»
  /-- Reserved word `forall`. -/
  | «forall»
  /-- Reserved word `match`. -/
  | «match»
  /-- Reserved word `par`. -/
  | par
  deriving BEq, Hashable, Repr, Inhabited

/-- Reserved word that names a standard command, e.g. `assert` or `check-sat`. -/
inductive CommandNameReserved where
  /-- Reserved word `assert`. -/
  | assert
  /-- Reserved word `check-sat`. -/
  | checkSat
  /-- Reserved word `check-sat-assuming`. -/
  | checkSatAssuming
  /-- Reserved word `declare-const`. -/
  | declareConst
  /-- Reserved word `declare-datatype`. -/
  | declareDatatype
  /-- Reserved word `declare-datatypes`. -/
  | declareDatatypes
  /-- Reserved word `declare-fun`. -/
  | declareFun
  /-- Reserved word `declare-sort`. -/
  | declareSort
  /-- Reserved word `declare-sort-parameter`. -/
  | declareSortParameter
  /-- Reserved word `define-const`. -/
  | defineConst
  /-- Reserved word `define-fun`. -/
  | defineFun
  /-- Reserved word `define-fun-rec`. -/
  | defineFunRec
  /-- Reserved word `define-funs-rec`. -/
  | defineFunsRec
  /-- Reserved word `define-sort`. -/
  | defineSort
  /-- Reserved word `echo`. -/
  | echo
  /-- Reserved word `exit`. -/
  | exit
  /-- Reserved word `get-assertions`. -/
  | getAssertions
  /-- Reserved word `get-assignment`. -/
  | getAssignment
  /-- Reserved word `get-info`. -/
  | getInfo
  /-- Reserved word `get-model`. -/
  | getModel
  /-- Reserved word `get-option`. -/
  | getOption
  /-- Reserved word `get-proof`. -/
  | getProof
  /-- Reserved word `get-unsat-assumptions`. -/
  | getUnsatAssumptions
  /-- Reserved word `get-unsat-core`. -/
  | getUnsatCore
  /-- Reserved word `get-value`. -/
  | getValue
  /-- Reserved word `pop`. -/
  | pop
  /-- Reserved word `push`. -/
  | push
  /-- Reserved word `reset`. -/
  | reset
  /-- Reserved word `reset-assertions`. -/
  | resetAssertions
  /-- Reserved word `set-info`. -/
  | setInfo
  /-- Reserved word `set-logic`. -/
  | setLogic
  /-- Reserved word `set-option`. -/
  | setOption
  deriving BEq, Hashable, Repr, Inhabited

/-- Reserved word (general or a command name), e.g. `let` or `check-sat`. -/
inductive _root_.BSmtLib.Lexicon.Reserved where
  /-- General reserved word, e.g. `_`, `as` or `let`. -/
  | general (reserved : Reserved.GeneralReserved)
  /-- Reserved word that names a standard command, e.g. `assert` or `check-sat`. -/
  | commandName (reserved : Reserved.CommandNameReserved)
  deriving BEq, Hashable, Repr, Inhabited

namespace GeneralReserved

/-- Returns the spelling of the reserved word. -/
def asStr : GeneralReserved → String
  | .binary => "BINARY"
  | .decimal => "DECIMAL"
  | .hexadecimal => "HEXADECIMAL"
  | .numeral => "NUMERAL"
  | .string => "STRING"
  | .underscore => "_"
  | .exclamationMark => "!"
  | .as => "as"
  | .lambda => "lambda"
  | .let => "let"
  | .exists => "exists"
  | .forall => "forall"
  | .match => "match"
  | .par => "par"

/- LEAN: Rust builds the enums, `as_str` and the word table with one `macro_rules!`. Lean
macros could do that too, but would be harder to read than the enums written out; the
word table is built from these lists of all variants instead. -/
/-- Every general reserved word. -/
def all : Array GeneralReserved :=
  #[.binary, .decimal, .hexadecimal, .numeral, .string, .underscore, .exclamationMark, .as,
    .lambda, .let, .exists, .forall, .match, .par]

end GeneralReserved

namespace CommandNameReserved

/-- Returns the spelling of the reserved word. -/
def asStr : CommandNameReserved → String
  | .assert => "assert"
  | .checkSat => "check-sat"
  | .checkSatAssuming => "check-sat-assuming"
  | .declareConst => "declare-const"
  | .declareDatatype => "declare-datatype"
  | .declareDatatypes => "declare-datatypes"
  | .declareFun => "declare-fun"
  | .declareSort => "declare-sort"
  | .declareSortParameter => "declare-sort-parameter"
  | .defineConst => "define-const"
  | .defineFun => "define-fun"
  | .defineFunRec => "define-fun-rec"
  | .defineFunsRec => "define-funs-rec"
  | .defineSort => "define-sort"
  | .echo => "echo"
  | .exit => "exit"
  | .getAssertions => "get-assertions"
  | .getAssignment => "get-assignment"
  | .getInfo => "get-info"
  | .getModel => "get-model"
  | .getOption => "get-option"
  | .getProof => "get-proof"
  | .getUnsatAssumptions => "get-unsat-assumptions"
  | .getUnsatCore => "get-unsat-core"
  | .getValue => "get-value"
  | .pop => "pop"
  | .push => "push"
  | .reset => "reset"
  | .resetAssertions => "reset-assertions"
  | .setInfo => "set-info"
  | .setLogic => "set-logic"
  | .setOption => "set-option"

/- LEAN: as `GeneralReserved.all`, not in Rust, whose macro builds the word table. -/
/-- Every command-name reserved word. -/
def all : Array CommandNameReserved :=
  #[.assert, .checkSat, .checkSatAssuming, .declareConst, .declareDatatype, .declareDatatypes,
    .declareFun, .declareSort, .declareSortParameter, .defineConst, .defineFun, .defineFunRec,
    .defineFunsRec, .defineSort, .echo, .exit, .getAssertions, .getAssignment, .getInfo,
    .getModel, .getOption, .getProof, .getUnsatAssumptions, .getUnsatCore, .getValue, .pop,
    .push, .reset, .resetAssertions, .setInfo, .setLogic, .setOption]

end CommandNameReserved

/-- Returns the spelling of the reserved word. -/
def asStr : Reserved → String
  | .general word => word.asStr
  | .commandName word => word.asStr

/-- The version that made the word reserved. -/
private def since : Reserved → Version
  -- SMT-LIB 2.7: lambda terms, sort parameters, constant definitions
  | .general .lambda
  | .commandName .declareSortParameter
  | .commandName .defineConst => .v2_7
  -- SMT-LIB 2.6: datatypes and matching on them
  | .general .match
  | .commandName .declareDatatype
  | .commandName .declareDatatypes => .v2_6
  -- SMT-LIB 2.5: the remaining special-constant categories and added commands
  | .general .binary
  | .general .hexadecimal
  | .commandName .checkSatAssuming
  | .commandName .declareConst
  | .commandName .defineFunRec
  | .commandName .defineFunsRec
  | .commandName .echo
  | .commandName .getModel
  | .commandName .getUnsatAssumptions
  | .commandName .reset
  | .commandName .resetAssertions => .v2_5
  -- everything else is reserved since SMT-LIB 2.0
  | _ => .v2_0

/-- Returns `true` if the word is reserved in the given version. -/
@[inline]
def isInVersion (self : Reserved) (version : Version) : Bool :=
  version ≥ self.since

/-- Every reserved word with its classification. -/
private def reservedWords : Array (ByteArray × Reserved) :=
  GeneralReserved.all.map (fun word => (word.asStr.toUTF8, Reserved.general word))
    ++ CommandNameReserved.all.map (fun word => (word.asStr.toUTF8, Reserved.commandName word))

/- LEAN: public, in `Internal`, as the type of `Internal.reservedSlot` names it. Its value is
exposed for the fused reader (`Parser.Internal.Fused.Reserved`), which hashes into the table
with the number itself. -/
/-- Number of slots of the reserved-word table. -/
@[expose] def Internal.reservedSlots : Nat := 128

/-!
The reserved-word table and its hash. They are public, in `Internal`, only so that the proofs
of the lexers can read them; they are not a part of the library's interface.
-/

/-- Every reserved word has a byte. -/
private theorem reservedWords_nonempty :
    ∀ entry ∈ reservedWords, 0 < entry.1.toByteSlice.size := by
  decide +kernel

namespace Internal

/--
Returns the slot in the reserved-word table corresponding to the non-empty symbol.

A perfect hash of the reserved words over their length and their first, last, and
middle byte: no two reserved words share a slot, which a check after
`reservedTable` ensures when the module is built.
-/
@[inline]
def reservedSlot (symbol : ByteSlice) (nonempty : 0 < symbol.size) : Fin reservedSlots :=
  let len := symbol.size
  let first := symbol[0].toNat
  let last := symbol[len - 1].toNat
  let mid := symbol[len / 2]'(Nat.div_lt_self nonempty (by decide)) |>.toNat
  ⟨(first + last * 4 + len * 34 + mid * 54) % reservedSlots, Nat.mod_lt _ (by decide)⟩

/- LEAN: Rust computes the table in a `static` at compile time. A Lean definition without
arguments is computed once, when the module is loaded. The table is built as a vector of its
fixed size, so that every write is within it; each word comes with the proof that it has a byte,
which its slot needs. -/
/--
The reserved words by slot, each with the version that made it reserved.

The empty word is used as a sentinel value for empty slots.
-/
def reservedTable : Array (ByteArray × Reserved × Version) :=
  let empty : Vector (ByteArray × Reserved × Version) reservedSlots :=
    Vector.replicate reservedSlots (ByteArray.empty, Reserved.general .underscore, Version.v2_5)
  let table := reservedWords.attach.foldl (init := empty) fun table ⟨(word, reserved), member⟩ =>
    table.set (reservedSlot word.toByteSlice (reservedWords_nonempty _ member)).val
      (word, reserved, reserved.since) (Fin.isLt _)
  table.toArray

/-- The table has a slot for every hash. -/
theorem size_reservedTable : reservedTable.size = reservedSlots := by
  simp [reservedTable]

end Internal

/- LEAN: the Rust `assert!` in a `const` context that the hash is perfect, every word in a slot
of its own, is a `#guard` in `BSmtLib.Facts.Asserts`, checked when the facts are built. A word
that shared a slot would have been overwritten in the table by a later one. -/

/-- Returns the reserved word that the symbol spells in the version, if any. -/
@[inline]
def fromBytes? (symbol : ByteSlice) (version : Version) : Option Reserved :=
  -- make sure that the symbol is not an empty word, which is a sentinel
  if h : symbol.size = 0 then
    none
  else
    -- the slot holds a reserved word or a sentinel
    let slot := Internal.reservedSlot symbol (Nat.pos_of_ne_zero h)
    let (word, reserved, since) :=
      Internal.reservedTable[slot.val]'(by rw [Internal.size_reservedTable]; exact slot.isLt)
    -- if the symbol is equal to the reserved word and the version has it, return it
    if word.toByteSlice == symbol && version ≥ since then some reserved else none

/-- Returns `true` if the reserved word is the name of a standard command. -/
@[inline]
def isCommandName : Reserved → Bool
  | .commandName _ => true
  | .general _ => false

namespace GeneralReserved

/-- Returns the word of this group that the symbol spells in the version, if any. -/
@[inline]
def fromBytes? (symbol : ByteSlice) (version : Version) : Option GeneralReserved :=
  match Reserved.fromBytes? symbol version with
  | some (.general reserved) => some reserved
  | _ => none

end GeneralReserved

namespace CommandNameReserved

/-- Returns the word of this group that the symbol spells in the version, if any. -/
@[inline]
def fromBytes? (symbol : ByteSlice) (version : Version) : Option CommandNameReserved :=
  match Reserved.fromBytes? symbol version with
  | some (.commandName reserved) => some reserved
  | _ => none

end CommandNameReserved

end BSmtLib.Lexicon.Reserved
