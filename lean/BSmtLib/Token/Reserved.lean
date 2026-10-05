import BSmtLib.Bytes
import BSmtLib.Token

/- LEAN: in Rust, `token` declares `reserved` as a submodule and re-exports its types, while
`reserved` uses `Version` from `token`. Lean modules cannot import each other, so this
module imports `BSmtLib.Token` and declares its types in the same namespace; the root
module `BSmtLib` imports both. -/

namespace BSmtLib

/-- General reserved words of the SMT-LIB2 grammar. -/
inductive GeneralReserved where
  | binary
  | decimal
  | hexadecimal
  | numeral
  | string
  | underscore
  | exclamationMark
  | as
  | lambda
  | «let»
  | «exists»
  | «forall»
  | «match»
  | par
  deriving BEq, Repr, Inhabited

/--
Reserved words naming standard SMT-LIB2 commands.

Standard SMT-LIB2 commands are reserved words.
-/
inductive CommandNameReserved where
  | assert
  | checkSat
  | checkSatAssuming
  | declareConst
  | declareDatatype
  | declareDatatypes
  | declareFun
  | declareSort
  | declareSortParameter
  | defineConst
  | defineFun
  | defineFunRec
  | defineFunsRec
  | defineSort
  | echo
  | exit
  | getAssertions
  | getAssignment
  | getInfo
  | getModel
  | getOption
  | getProof
  | getUnsatAssumptions
  | getUnsatCore
  | getValue
  | pop
  | push
  | reset
  | resetAssertions
  | setInfo
  | setLogic
  | setOption
  deriving BEq, Repr, Inhabited

/-- Reserved words in SMT-LIB2, including standard command names. -/
inductive Reserved where
  | general (reserved : GeneralReserved)
  | commandName (reserved : CommandNameReserved)
  deriving BEq, Repr, Inhabited

namespace GeneralReserved

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

/-- Every command-name reserved word. -/
def all : Array CommandNameReserved :=
  #[.assert, .checkSat, .checkSatAssuming, .declareConst, .declareDatatype, .declareDatatypes,
    .declareFun, .declareSort, .declareSortParameter, .defineConst, .defineFun, .defineFunRec,
    .defineFunsRec, .defineSort, .echo, .exit, .getAssertions, .getAssignment, .getInfo,
    .getModel, .getOption, .getProof, .getUnsatAssumptions, .getUnsatCore, .getValue, .pop,
    .push, .reset, .resetAssertions, .setInfo, .setLogic, .setOption]

end CommandNameReserved

namespace Reserved

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

/-- Whether the word is reserved in the version. -/
@[inline]
def isInVersion (self : Reserved) (version : Version) : Bool :=
  version ≥ self.since

/-- Every reserved word with its classification. -/
private def reservedWords : Array (ByteArray × Reserved) :=
  GeneralReserved.all.map (fun word => (word.asStr.toUTF8, Reserved.general word))
    ++ CommandNameReserved.all.map (fun word => (word.asStr.toUTF8, Reserved.commandName word))

/-- Number of slots of the reserved-word table. -/
private def reservedSlots : Nat := 128

/-!
The reserved-word table and its hash. They are public, in `Internal`, only so that the proofs
of the lexers can read them; they are not a part of the library's interface.
-/

namespace Internal

/--
Returns the slot in the reserved-word table corresponding to the non-empty symbol.

A perfect hash of the reserved words over their length and their first, last, and
middle byte: no two reserved words share a slot, which a check after
`reservedTable` ensures when the module is built.
-/
@[inline]
def reservedSlot (symbol : ByteSlice) : Nat :=
  let len := symbol.size
  let first := (symbol.get! 0).toNat
  let last := (symbol.get! (len - 1)).toNat
  let mid := (symbol.get! (len / 2)).toNat
  (first + last * 4 + len * 34 + mid * 54) % reservedSlots

/--
The reserved words by slot, each with the version that made it reserved.

The empty word is used as a sentinel value for empty slots.
-/
/- LEAN: Rust computes the table in a `static` at compile time. A Lean definition without
arguments is computed once, when the module is loaded. `Id.run do` runs imperative-looking
code (`let mut`, `for`) that has no side effects. -/
def reservedTable : Array (ByteArray × Reserved × Version) := Id.run do
  let mut table := Array.replicate reservedSlots (ByteArray.empty, Reserved.general .underscore, Version.v2_5)
  for (word, reserved) in reservedWords do
    table := table.set! (reservedSlot word.toByteSlice) (word, reserved, reserved.since)
  table

end Internal

open Internal

/- LEAN: `#guard` evaluates the condition when the module is built and fails the build if
it is false; it stands in for the Rust `assert!` in a `const` context. A word that shared
a slot would have been overwritten in the table by a later one. -/
-- the reserved-word hash must be perfect: every word lands in a slot of its own
#guard reservedWords.all fun (word, _) =>
  (reservedTable[reservedSlot word.toByteSlice]!).1 == word

/-- The reserved word that the symbol spells in the version, if any. -/
@[inline]
def fromBytes? (symbol : ByteSlice) (version : Version) : Option Reserved :=
  -- make sure that the symbol is not an empty word, which is a sentinel
  if symbol.size == 0 then
    none
  else
    -- the slot holds a reserved word or a sentinel
    let (word, reserved, since) := reservedTable[reservedSlot symbol]!
    -- if the symbol is equal to the reserved word and the version has it, return it
    if word.toByteSlice == symbol && version ≥ since then some reserved else none

/-- The reserved word that the symbol spells in the version, if any. -/
@[inline]
def fromSymbol? (symbol : Bytes) (version : Version) : Option Reserved :=
  fromBytes? symbol.asSlice version

/-- Whether the reserved word is the name of a standard command. -/
@[inline]
def isCommandName : Reserved → Bool
  | .commandName _ => true
  | .general _ => false

end Reserved

namespace GeneralReserved

/-- The word of this group that the symbol spells in the version, if any. -/
@[inline]
def fromBytes? (symbol : ByteSlice) (version : Version) : Option GeneralReserved :=
  match Reserved.fromBytes? symbol version with
  | some (.general reserved) => some reserved
  | _ => none

end GeneralReserved

namespace CommandNameReserved

/-- The word of this group that the symbol spells in the version, if any. -/
@[inline]
def fromBytes? (symbol : ByteSlice) (version : Version) : Option CommandNameReserved :=
  match Reserved.fromBytes? symbol version with
  | some (.commandName reserved) => some reserved
  | _ => none

end CommandNameReserved

end BSmtLib
