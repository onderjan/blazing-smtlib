module

public meta import Lean
public meta import BSmtLib.Facts.Naming
public meta import BSmtLib.Facts.RustItems
public meta import BSmtLib.Facts.RustOnly

@[expose] public meta section

/-!
# The Rust counterparts of the public names, checked

Every public name of the library has a counterpart among the public items of the Rust crate
(`BSmtLib.Facts.RustItems`), or its declaration gives a reason why it has none, in a comment
that begins with `LEAN:`.

A name is public unless it is private, below a namespace `Internal`, or one of the names that
Lean derives (`BSmtLib.Facts.Naming.subject`). Theorems and instances need neither: Rust has no
theorems, and an instance is the counterpart of a trait implementation, which has no name. The
library is the modules below `BSmtLib` outside `BSmtLib.Facts`.

The Lean name of a Rust item follows from its path: the modules become the namespaces, each
written in upper camel case (`parser::category::term` is `BSmtLib.Parser.Category.Term`); a type
loses the prefix `Smt`, so that a view takes the plain name and an owned type keeps its suffix `Buf`
(`lexicon::value::SmtSymbol` is `BSmtLib.Lexicon.Value.Symbol`, `lexicon::value::SmtSymbolBuf`
is `BSmtLib.Lexicon.Value.SymbolBuf`); a type named like its module is the module's own name
(`lexer::SmtLexer` is `BSmtLib.Lexer`); a function or method is written in lower camel case, with
`?` for a result that may be absent (`from_decimal` may be `fromDecimal?`, as `peek` may be
`peek?`, and a suffix `_opt` becomes the `?`), and with the Lean names of the Rust types it names
(`to_u32` is `toUInt32`, `into_vec` is `intoByteArray`).

A `LEAN:` comment counts for a declaration when it is in the declaration's header (between its
documentation comment and its name), or is the block comment right above the paragraph (the lines
without a blank one between them) that the header begins in; a declaration that a macro makes
has the macro's use as its header.

`#counterparts` lists the public names that have a reason and no counterpart, and fails with an
error for each public name that has neither.

It checks the other direction too. Every public item of the Rust crate has a public Lean
counterpart, but a method of a trait implementation, which the trait's implementation stands
for: a method `x_mut` may be the function `modifyX`, which returns the value with its part
changed, and a method `into_x` the reader `x`, as Lean values are not moved out of. Every trait
implementation of a public type has an instance of the trait's class for the type's counterpart,
if the trait has a class (`stdClasses` for the traits of the standard library). The counterpart of
a structure with private fields has private constructors only. An item that fails one of these
checks has an entry with a reason in `BSmtLib.Facts.RustOnly.reasons`; `#counterparts` lists the
entries, and fails with an error for each item that fails a check without one, and for each entry
that no item needs.

This module is a tool of the facts, not a part of any of them, and not trusted.
-/

namespace BSmtLib.Facts.Counterparts

open Lean Elab Command BSmtLib.Facts.Naming

/-- The words of a Rust identifier in snake case. -/
def words (s : String) : List String :=
  (s.splitOn "_").filter (· != "")

/-- The first character in upper case. -/
def capitalize (s : String) : String :=
  match s.toList with
  | c :: cs => String.ofList (c.toUpper :: cs)
  | [] => s

/-- A Rust module name in upper camel case: `qualified_ident` is `QualifiedIdent`. -/
def pascal (s : String) : String :=
  String.join ((words s).map capitalize)

/-- A Rust function name in lower camel case: `lex_slice` is `lexSlice`. -/
def camel (s : String) : String :=
  match words s with
  | w :: ws => w ++ String.join (ws.map capitalize)
  | [] => s

/-- Whether a Rust identifier is a constant's: upper case and underscores only. -/
def isConstant (s : String) : Bool :=
  s.any Char.isUpper && s.all fun c => c.isUpper || c.isDigit || c == '_'

/-- Whether a Rust identifier names a type or a trait: it begins in upper case and is not a
constant's. -/
def isTypeName (s : String) : Bool :=
  (s.front.isUpper) && !isConstant s

/-- The Lean names of a function or method `s`. -/
def memberNames (s : String) : List String :=
  if isConstant s then [s]
  -- an associated type keeps its name
  else if isTypeName s then [s]
  else
    -- the words of the Rust types: a vector of bytes is a `ByteArray`, an unsigned integer
    -- type is Lean's of its width
    let ws := (words s).flatMap fun w => match w with
      | "vec" => ["byte", "array"]
      | "u32" => ["u", "int32"]
      | "u64" => ["u", "int64"]
      | "u128" => ["u", "int128"]
      | "usize" => ["u", "size"]
      | w => [w]
    if ws.getLast? == some "opt" then [camel ("_".intercalate ws.dropLast) ++ "?"]
    else
      let c := camel ("_".intercalate ws)
      -- a method that lends a part mutably returns the value with the part changed by a
      -- function, and one that moves a part out is the part's reader
      let changed := if ws.getLast? == some "mut" then [camel ("_".intercalate ("modify" ::
        ws.dropLast))] else []
      let moved := if ws.head? == some "into" && ws.length > 1 then [camel ("_".intercalate
        ws.tail)] else []
      [c, c ++ "?"] ++ changed ++ moved

/-- The Lean name of the Rust type `s`: the type without the prefix `Smt`. -/
def typeName (s : String) : String :=
  if s.startsWith "Smt" then (s.drop 3).toString else s

/-- The Lean names of the Rust item at `path`. -/
def leanNames (path : String) : List Name := Id.run do
  let parts := path.splitOn "::"
  let modules := parts.takeWhile (!isTypeName ·)
  let rest := parts.drop modules.length
  -- a module-level function or constant: the last of the lower-case parts
  let (modules, rest) :=
    if rest.isEmpty && !modules.isEmpty then (modules.dropLast, [modules.getLast!])
    else (modules, rest)
  let moduleName := modules.foldl (fun n m => n.str (pascal m)) `BSmtLib
  match rest with
  | [member] =>
    if isTypeName member then [typeAt moduleName (typeName member)]
    else (memberNames member).map moduleName.str
  | [type, member] =>
    let t := typeAt moduleName (typeName type)
    (memberNames member).map t.str
  | _ => []
where
  /-- The type `t` in the namespace of its module, at the module's own name if it is named like
  the module. -/
  typeAt (moduleName : Name) (t : String) : Name :=
    if moduleName.getString! == t then moduleName else moduleName.str t

/-- The Lean names of all the Rust crate's public items. -/
def counterparts : NameSet := Id.run do
  let mut out : NameSet := {}
  for path in RustItems.items do
    for n in leanNames path do
      out := out.insert n
  return out

/-- Whether the library declares `name` in `module` as a name the rule applies to. -/
def checkedName (env : Environment) (module name : Name) (info : ConstantInfo) (theorem? : Bool) :
    Bool :=
  (`BSmtLib).isPrefixOf module && !(`BSmtLib.Facts).isPrefixOf module &&
    subject env name info && isPublic name && !theorem? && !Meta.isInstanceCore env name

/-- The lines of the block comment that ends on line `last` (0-based) of `lines`, if one does. -/
def commentAbove (lines : Array String) (last : Nat) : List String := Id.run do
  let some line := lines[last]? | return []
  unless line.trimAscii.toString.endsWith "-/" do return []
  let mut i := last
  let mut block : List String := []
  repeat
    let l := lines[i]!
    block := l :: block
    if (l.trimAscii.toString.startsWith "/-") || i == 0 then break
    i := i - 1
  return block

/-- The first line (0-based) of the paragraph of `lines` that line `i` is in: the lines without a
blank one between them, up to the end of a block comment above. -/
def paragraphStart (lines : Array String) (i : Nat) : Nat := Id.run do
  let mut j := i
  while j > 0 do
    let above := lines[j - 1]!.trimAscii.toString
    if above.isEmpty || above.endsWith "-/" then break
    j := j - 1
  return j

/-- Whether the declaration at `ranges`, in the file with the lines `lines`, has a `LEAN:`
reason. -/
def hasReason (lines : Array String) (ranges : DeclarationRanges) : Bool :=
  let start := ranges.range.pos.line - 1
  let stop := ranges.selectionRange.pos.line - 1
  let header := (List.range (stop + 1 - start)).filterMap fun i => lines[start + i]?
  let first := paragraphStart lines start
  let above := if first == 0 then [] else commentAbove lines (first - 1)
  (header ++ above).any fun l => (l.splitOn "/- LEAN:").length > 1

/-- The classes that stand for the traits of the standard library: `Debug` is `Repr`,
`PartialEq` is `BEq`, `Hash` is `Hashable`, `Default` is `Inhabited`, `Ord` is `Ord`, `Index` is
`GetElem` and `Display` is `ToString`. The other traits of the standard library have no
counterpart: `Clone` and `Copy` (Lean values are copied freely), `Eq`, `StructuralPartialEq` and
`PartialOrd` (with `BEq` and `Ord`), `IndexMut`, `Borrow` and `From` (a conversion is a named
function, checked as the item it is), `Error` (the cause of an error is one of its fields), and
the iterator traits (a container is iterated through its array). -/
def stdClasses : List (String × Name) :=
  [("core::fmt::Debug", `Repr), ("core::cmp::PartialEq", `BEq), ("core::hash::Hash", `Hashable),
    ("core::default::Default", `Inhabited), ("core::cmp::Ord", `Ord),
    ("core::ops::index::Index", `GetElem), ("core::fmt::Display", `ToString)]

/-- The Lean classes that stand for the trait at `trait`, given the Rust items `all`: the class
of a trait of the crate, the class of `stdClasses` for one of the standard library; none if the
trait has no counterpart. -/
def classNames (all : Std.HashSet String) (trait : String) : List Name :=
  if all.contains trait then leanNames trait
  else ((stdClasses.lookup trait).map ([·])).getD []

/-- The conclusion of a type: what is left of it after its binders. -/
def conclusion : Expr → Expr
  | .forallE _ _ body _ => conclusion body
  | e => e

/-- The pairs of a class and a constant that an argument of the class mentions, of every
instance in `env`: `(Repr, BSmtLib.Span.Location)` for `instance : Repr Location`. -/
def instancePairs (env : Environment) : Std.HashSet (Name × Name) := Id.run do
  let mut out : Std.HashSet (Name × Name) := {}
  for (name, _) in (Meta.instanceExtension.getState env).instanceNames.toList do
    let some info := env.find? name | continue
    let c := conclusion info.type
    let .const cls _ := c.getAppFn | continue
    for arg in c.getAppArgs do
      for n in arg.getUsedConstants do
        out := out.insert (cls, n)
  return out

/-- The keys of the reasons why a Rust item has no Lean counterpart (`RustOnly.reasons`): an
item is named by its path, a trait implementation by `impl <trait> for <type>`, the private
fields of a structure by `fields of <type>`. -/
def implKey (type trait : String) : String := s!"impl {trait} for {type}"

@[inherit_doc implKey]
def fieldsKey (type : String) : String := s!"fields of {type}"

/--
`#counterparts` checks that every public name of the library has a Rust counterpart or a
`LEAN:` reason: it lists how many have a counterpart, and the names that have a reason instead;
and fails with an error for each name that has neither.

It also checks the other direction: that every public item of the Rust crate but a method of a
trait implementation has a Lean counterpart; that every trait implementation of a public type
whose trait has a counterpart class has an instance of the class for the type's counterpart;
and that the counterpart of every structure with private fields has private constructors only.
What fails one of these checks needs an entry in `RustOnly.reasons`; the command lists the
entries, and fails with an error for each item that fails a check without an entry, and for each
entry that is not needed.
-/
syntax (name := counterpartsCmd) "#counterparts" : command

@[command_elab counterpartsCmd]
def elabCounterparts : CommandElab := fun _ => do
  -- the library as a whole, with the kinds and positions of its declarations, which a module
  -- importing it does not see
  let full ← importModules #[{ module := `BSmtLib }] {}
  let env ← getEnv
  -- the package's directory, from this file's path below it
  let file ← IO.FS.realPath (← getFileName)
  let some dir := (List.range 3).foldlM (fun (p : System.FilePath) _ => p.parent) file |
    throwError "#counterparts: no package directory above {file}"
  let known := counterparts
  let mut files : Std.HashMap Name (Array String) := {}
  let mut matched := 0
  let mut reasoned : Array Name := #[]
  let mut neither : Array (Name × Name) := #[]
  for (name, info) in env.constants.map₁.toList do
    let some idx := env.getModuleIdxFor? name | continue
    let module := env.header.moduleNames[idx.toNat]!
    let theorem? := match full.find? name with
      | some (.thmInfo _) => true
      | _ => false
    unless checkedName env module name info theorem? do continue
    if known.contains name then
      matched := matched + 1
      continue
    let lines ← match files[module]? with
      | some lines => pure lines
      | none => do
        let path := module.components.foldl (fun p c => p / c.toString) dir
        let lines := (← IO.FS.readFile (path.addExtension "lean")).splitOn "\n" |>.toArray
        files := files.insert module lines
        pure lines
    match ← withEnv full (findDeclarationRanges? name) with
    | some ranges =>
      if hasReason lines ranges then reasoned := reasoned.push name
      else neither := neither.push (module, name)
    | none => neither := neither.push (module, name)
  let lines := #[s!"{matched} public names with a Rust counterpart; " ++
      s!"{reasoned.size} with a `LEAN:` reason instead:"] ++
    (sortNames reasoned).map (s!"  {·}")
  logInfo (String.intercalate "\n" lines.toList)
  for (module, name) in neither.qsort (fun a b => a.2.toString < b.2.toString) do
    logError m!"{name}, declared in {module}, has no Rust counterpart and no `LEAN:` reason"
  -- the other direction: from the Rust items to the Lean names
  let all : Std.HashSet String := RustItems.items.foldl (·.insert ·) {}
  let implOnly : Std.HashSet String := RustItems.implMembers.foldl (·.insert ·) {}
  let present (n : Name) : Bool := isPublic n && (env.find? n).isSome
  let mut failing : Array (String × String) := #[]
  let mut items := 0
  for path in RustItems.items do
    if implOnly.contains path then continue
    items := items + 1
    unless (leanNames path).any present do
      failing := failing.push (path, "has no Lean counterpart")
  let pairs := instancePairs env
  let mut impls := 0
  for (type, trait) in RustItems.impls do
    let classes := classNames all trait
    if classes.isEmpty then continue
    impls := impls + 1
    let types := leanNames type
    unless classes.any (fun c => types.any fun t => pairs.contains (c, t)) do
      failing := failing.push (implKey type trait,
        s!"has no instance of {classes} for {types}")
  for type in RustItems.privateFields do
    for n in leanNames type do
      let some (.inductInfo info) := env.find? n | continue
      unless info.ctors.all isPrivateName do
        failing := failing.push (fieldsKey type,
          s!"are private, and {n} has a public constructor")
  let reasons := RustOnly.reasons
  let keys : Std.HashSet String := reasons.foldl (·.insert ·.1) {}
  let failed : Std.HashSet String := failing.foldl (·.insert ·.1) {}
  logInfo (String.intercalate "\n" (s!"{items} Rust items, {impls} trait implementations with \
      a counterpart class and {RustItems.privateFields.size} structures with private fields; \
      {reasons.size} without a counterpart, with a reason:" ::
    ((reasons.toList.map (·.1)).mergeSort (· ≤ ·)).map (s!"  {·}")))
  -- one error for each kind, listing the items, as there can be many
  let unexplained := failing.filter (!keys.contains ·.1)
  unless unexplained.isEmpty do
    logError (String.intercalate "\n" ("Rust items that fail a check, with no reason in \
        `RustOnly.reasons`:" :: unexplained.toList.map fun (key, message) =>
      s!"  {key} {message}"))
  let unneeded := reasons.filter (!failed.contains ·.1)
  unless unneeded.isEmpty do
    logError (String.intercalate "\n" ("Reasons in `RustOnly.reasons` that no item needs:" ::
      unneeded.toList.map (s!"  {·.1}")))

end BSmtLib.Facts.Counterparts
