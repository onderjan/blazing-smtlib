module

public meta import Lean
public meta import BSmtLib.Facts.Naming
public meta import BSmtLib.Facts.RustItems

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
loses the prefix `Smt`, an owned type also its suffix `Buf`, and a view whose owned type exists
gets the suffix `View` (`plain::SmtSymbolBuf` is `BSmtLib.Plain.Symbol`, `plain::SmtSymbol` is
`BSmtLib.Plain.SymbolView`); a type named like its module is the module's own name
(`lexer::SmtLexer` is `BSmtLib.Lexer`); a function or method is written in lower camel case, with
`?` for a result that may be absent (`from_decimal_opt` is `fromDecimal?`, and `peek` may also be
`peek?`).

A `LEAN:` comment counts for a declaration when it is in the declaration's header (between its
documentation comment and its name), or is the block comment right above the paragraph (the lines
without a blank one between them) that the header begins in; a declaration that a macro makes
has the macro's use as its header.

`#counterparts` lists the public names that have a reason and no counterpart, and fails with an
error for each public name that has neither.

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
  else
    -- the words of the Rust types: an owned buffer is the Lean type without `Buf`, and a
    -- vector of bytes is a `ByteArray`
    let ws := (words s).flatMap fun w => if w == "vec" then ["byte", "array"] else [w]
    let ws := if ws.getLast? == some "buf" then ws.dropLast else ws
    if ws.getLast? == some "opt" then [camel ("_".intercalate ws.dropLast) ++ "?"]
    else let c := camel ("_".intercalate ws); [c, c ++ "?"]

/-- The Lean name of the Rust type `s` of the module `module`, given the Rust items `all`. -/
def typeName (all : Std.HashSet String) (module : String) (s : String) : String :=
  let stripped := if s.startsWith "Smt" then (s.drop 3).toString else s
  if stripped.endsWith "Buf" then (stripped.dropEnd 3).toString
  else if s.startsWith "Smt" && all.contains s!"{module}::{s}Buf" then stripped ++ "View"
  else stripped

/-- The Lean names of the Rust item at `path`, given the Rust items `all`. -/
def leanNames (all : Std.HashSet String) (path : String) : List Name := Id.run do
  let parts := path.splitOn "::"
  let modules := parts.takeWhile (!isTypeName ·)
  let rest := parts.drop modules.length
  -- a module-level function or constant: the last of the lower-case parts
  let (modules, rest) :=
    if rest.isEmpty && !modules.isEmpty then (modules.dropLast, [modules.getLast!])
    else (modules, rest)
  let moduleName := modules.foldl (fun n m => n.str (pascal m)) `BSmtLib
  let rustModule := "::".intercalate modules
  match rest with
  | [member] =>
    if isTypeName member then [typeAt moduleName (typeName all rustModule member)]
    else (memberNames member).map moduleName.str
  | [type, member] =>
    let t := typeAt moduleName (typeName all rustModule type)
    (memberNames member).map t.str
  | _ => []
where
  /-- The type `t` in the namespace of its module, at the module's own name if it is named like
  the module. -/
  typeAt (moduleName : Name) (t : String) : Name :=
    if moduleName.getString! == t then moduleName else moduleName.str t

/-- The Lean names of all the Rust crate's public items. -/
def counterparts : NameSet := Id.run do
  let all : Std.HashSet String := RustItems.items.foldl (·.insert ·) {}
  let mut out : NameSet := {}
  for path in RustItems.items do
    for n in leanNames all path do
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

/--
`#counterparts` checks that every public name of the library has a Rust counterpart or a
`LEAN:` reason: it lists how many have a counterpart, and the names that have a reason instead;
and fails with an error for each name that has neither.
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

end BSmtLib.Facts.Counterparts
