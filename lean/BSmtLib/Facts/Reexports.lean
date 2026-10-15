module

public meta import BSmtLib.Facts.Naming

@[expose] public meta section

/-!
# The re-exports, generated and checked

The counterparts of the Rust crate's `pub use` lines are `export` lines in the generated module
`BSmtLib.Reexports`: for an item `X` that `pub use` gives the name `N.x`, `export` gives `X` the
second name `N.x`, and each public member `X.y` of it the second name `N.x.y`, so that the second
name reaches all that the first one does. A member is public unless it is private, a detail Lean
derives for internal use, below a namespace `Internal` within the item, or one of the names
Lean derives from a declaration (`BSmtLib.Facts.Naming.derived`); only members declared in the
library count, not those that the facts add.

`uses` lists the `pub use` lines and their items; `render` makes the module from them and the
library. The executable `reexports` (`WriteReexports.lean`) writes the module, and
`#reexports` fails when the module differs from what `render` makes now, or when a second name
does not resolve.

This module is a tool of the facts, not a part of any of them, and not trusted.
-/

namespace BSmtLib.Facts.Reexports

open Lean Elab Command BSmtLib.Facts.Naming

/-- A `pub use` line of the Rust crate and the items it re-exports. -/
structure Use where
  /-- The Rust line and where it is, with a note, for the comment. -/
  rust : String
  /-- The namespace in which the items get their second names. -/
  target : Name
  /-- The items, named one by one, each with what the line names it by. -/
  items : List (String × Name) := []
  /-- The Rust path of the modules, for a `pub use` of `*`. -/
  path : String := ""
  /-- The modules all of whose public types are re-exported, for a `pub use` of `*`. -/
  modules : List Name := []
  /-- The types of those modules that are not re-exported. -/
  excluded : List Name := []

/-- The `pub use` lines of the Rust crate, in the order of `lib.rs` and then of the public
modules. -/
def uses : List Use := [
  { rust := "`pub use crate::bytes::*` in `lib.rs`", target := `BSmtLib,
    path := "crate::bytes", modules := [`BSmtLib.Bytes] },
  { rust := "`pub use crate::multiple::*` in `lib.rs`, which has no counterpart",
    target := `BSmtLib },
  { rust := "`pub use crate::nodes::*` in `lib.rs`; the parser's `Nodes.Symbol` would take the \
      name of `Plain.Symbol`", target := `BSmtLib,
    path := "crate::nodes", modules := [`BSmtLib.Nodes], excluded := [`BSmtLib.Nodes.Symbol] },
  { rust := "`pub use crate::plain::*` in `lib.rs`", target := `BSmtLib,
    path := "crate::plain", modules := [`BSmtLib.Plain] },
  { rust := "`pub use crate::span::*` in `lib.rs`", target := `BSmtLib,
    path := "crate::span", modules := [`BSmtLib.Span] },
  { rust := "`pub use crate::traits::*` in `lib.rs`", target := `BSmtLib,
    path := "crate::traits", modules := [`BSmtLib.Traits] },
  { rust := "`pub use reserved::{SmtCommandNameReserved, SmtGeneralReserved, SmtReserved}` in \
      `token.rs`; `Reserved` is itself `BSmtLib.Token.Reserved`", target := `BSmtLib.Token,
    items := [("reserved::SmtCommandNameReserved", `BSmtLib.Token.Reserved.CommandNameReserved),
      ("reserved::SmtGeneralReserved", `BSmtLib.Token.Reserved.GeneralReserved)] },
  { rust := "`pub use error::{SmtLexError, SmtLexErrorCause, SmtLexicalErrorKind}` in `lexer.rs`",
    target := `BSmtLib.Lexer,
    items := [("error::SmtLexError", `BSmtLib.Lexer.Error.LexError),
      ("error::SmtLexErrorCause", `BSmtLib.Lexer.Error.LexErrorCause),
      ("error::SmtLexicalErrorKind", `BSmtLib.Lexer.Error.LexicalErrorKind)] },
  { rust := "`pub use recovery::{SmtFailFast, SmtLexRecovery, SmtRecovering}` in `lexer.rs`",
    target := `BSmtLib.Lexer,
    items := [("recovery::SmtFailFast", `BSmtLib.Lexer.Recovery.FailFast),
      ("recovery::SmtLexRecovery", `BSmtLib.Lexer.Recovery.LexRecovery),
      ("recovery::SmtRecovering", `BSmtLib.Lexer.Recovery.Recovering)] },
  { rust := "`pub use {…}` in `parser/category.rs`, for the parsers that have a counterpart",
    target := `BSmtLib.Parser.Category,
    items := [("s_expr::SmtSExprParser", `BSmtLib.Parser.Category.SExpr.SExprParser),
      ("sort::SmtSortParser", `BSmtLib.Parser.Category.Sort.SortParser),
      ("term::SmtTermParser", `BSmtLib.Parser.Category.Term.TermParser)] },
  { rust := "`pub use adapter::*` in `parser.rs`", target := `BSmtLib.Parser,
    items := [("adapter::*", `BSmtLib.Parser.Adapter.ParseAdapter)] },
  { rust := "`pub use category::*` in `parser.rs`, for the items that have a counterpart",
    target := `BSmtLib.Parser,
    items := [("category::*", `BSmtLib.Parser.Category.SExpr.SExprParser),
      ("category::*", `BSmtLib.Parser.Category.Sort.SortParser),
      ("category::*", `BSmtLib.Parser.Category.Term.TermParser)] },
  { rust := "`pub use command::*` in `parser.rs`, for the items that have a counterpart",
    target := `BSmtLib.Parser,
    items := [("command::*", `BSmtLib.Parser.Command.CommandParser),
      ("command::*", `BSmtLib.Parser.Command.CommandOutcome)] },
  { rust := "`pub use script::*` in `parser.rs`", target := `BSmtLib.Parser,
    items := [("script::*", `BSmtLib.Parser.Script.ScriptParser)] },
  { rust := "`pub use state::*` in `parser.rs`; `ParseState` is itself `BSmtLib.Parser.ParseState`",
    target := `BSmtLib.Parser }]

/-- The modules the generated module imports: those the library's root imports but for it. -/
def sources : List Name :=
  [`BSmtLib.ControlFlow, `BSmtLib.Bytes, `BSmtLib.Plain, `BSmtLib.Span, `BSmtLib.Nodes,
    `BSmtLib.Traits, `BSmtLib.Token, `BSmtLib.Token.Reserved, `BSmtLib.Token.SyntaxToken,
    `BSmtLib.Token.Lookahead, `BSmtLib.Token.Produce, `BSmtLib.Token.ConsumeFrom,
    `BSmtLib.Lexer.CharClass,
    `BSmtLib.Lexer.Error, `BSmtLib.Lexer.Helpers, `BSmtLib.Lexer.Recovery, `BSmtLib.Lexer,
    `BSmtLib.Parser, `BSmtLib.Parser.Category, `BSmtLib.Parser.Command, `BSmtLib.Parser.Script,
    `BSmtLib.Parser.Adapter, `BSmtLib.Parser.Internal.Fused, `BSmtLib.Reader]

/-- The generated module. -/
def generated : Name := `BSmtLib.Reexports

/-- Its path, relative to the package's directory. -/
-- a literal, not computed: the executable `reexports` runs this module's code but does not run
-- its initializer, which a module imported with `meta` alone has only at compile time, so a
-- constant here that is computed when the module is initialized is never set in the executable
def path : System.FilePath := "BSmtLib/Reexports.lean"

/-- The command that writes it, run in the package's directory. -/
def command : String := "lake exe reexports"

/-- The module that declares `name` in `env`. -/
def moduleOf (env : Environment) (name : Name) : Option Name :=
  (env.getModuleIdxFor? name).map fun idx => env.header.moduleNames[idx.toNat]!

/-- Whether `module` is a module of the library, other than its root and the generated module. -/
def library (module : Name) : Bool :=
  (`BSmtLib).isPrefixOf module && !(`BSmtLib.Facts).isPrefixOf module &&
    module != `BSmtLib && module != generated

/-- The items of a `pub use`, each with what the line names it by: those named, or the public
types right below its modules. -/
def itemsOf (env : Environment) (use : Use) : Array (String × Name) := Id.run do
  let mut found := #[]
  for (name, info) in env.constants.map₁.toList do
    if use.modules.contains name.getPrefix && isType info && isPublic name &&
        !use.excluded.contains name && subject env name info then
      found := found.push name
  return use.items.toArray ++ (sortNames found).map (s!"{use.path}::*", ·)

/-- The public members of `item`, declared in the library. -/
def membersOf (env : Environment) (item : Name) : Array Name := Id.run do
  let mut members := #[]
  for (name, _) in env.constants.map₁.toList do
    if item.isPrefixOf name && name != item && !isPrivateName name &&
        !name.isInternalDetail && !derived name &&
        !((name.replacePrefix item .anonymous).components.contains `Internal) &&
        ((moduleOf env name).any library) then
      members := members.push name
  return sortNames members
/-- The words that the syntax declared in Lean's prelude makes tokens, beyond those of its
built-in syntax; a name of the library that is one of them breaks the generated module, which
then fails to build until the word is added here. -/
def declaredTokens : List String := ["exists"]

/-- A component of a name as `export` takes it: in `«»` if it is a token, a word of Lean's
built-in syntax such as `forall` (`tokens`) or of `declaredTokens`, or is no plain
identifier. -/
def component (tokens : Parser.TokenTable) (s : String) : String :=
  let plain := (s.front.isAlpha || s.front == '_') &&
    s.all fun c => c.isAlphanum || c == '_' || c == '\'' || c == '!' || c == '?'
  if !plain || (tokens.find? s).isSome || declaredTokens.contains s then "«" ++ s ++ "»" else s

/-- A name as `export` takes it. -/
def nameText (tokens : Parser.TokenTable) (name : Name) : String :=
  ".".intercalate (name.components.map fun c => component tokens c.toString)

/-- `export ns (ids…)`, broken into lines of at most 100 characters. -/
def exportLines (tokens : Parser.TokenTable) (ns : Name) (ids : Array String) :
    Array String := Id.run do
  let mut lines := #[]
  let mut line := s!"export {nameText tokens ns} ("
  let mut first := true
  for id in ids do
    let sep := if first then "" else " "
    if (line ++ sep ++ id ++ ")").length > 100 && !first then
      lines := lines.push line
      line := "  " ++ id
    else
      line := line ++ sep ++ id
    first := false
  return lines.push (line ++ ")")

/-- The lines of the generated module for one item: its second name, then those of its members,
grouped by the namespace they are declared in. -/
def itemLines (tokens : Parser.TokenTable) (env : Environment) (target item : Name) :
    Array String := Id.run do
  let some last := item.components.getLast? | return #[]
  let alias := target ++ last
  let text := nameText tokens
  let mut lines := #[s!"namespace {text target}", ""] ++
    exportLines tokens item.getPrefix #[component tokens last.toString] ++
    #["", s!"end {text target}"]
  let members := membersOf env item
  let parents := sortNames (members.map (·.getPrefix)).toList.eraseDups.toArray
  for parent in parents do
    let ids := (members.filter (·.getPrefix == parent)).filterMap fun m =>
      m.components.getLast?.map (component tokens ·.toString)
    let ns := alias ++ parent.replacePrefix item .anonymous
    lines := lines ++ #["", s!"namespace {text ns}", ""] ++ exportLines tokens parent ids ++
      #["", s!"end {text ns}"]
  return lines
/-- `text` as a comment `/-! … -/`, broken into lines of at most 100 characters. -/
def commentLines (text : String) : Array String := Id.run do
  let mut lines := #[]
  let mut line := "/-!"
  for word in (text ++ " -/").splitOn " " do
    if (line ++ " " ++ word).length > 100 then
      lines := lines.push line
      line := word
    else
      line := line ++ " " ++ word
  return lines.push line

/-- The generated module, from `uses` and the library in `env`; `tokens` are those of Lean's
built-in syntax. -/
def render (tokens : Parser.TokenTable) (env : Environment) : String := Id.run do
  let mut lines := #["module", ""] ++ sources.toArray.map (s!"public import {·}") ++ #["",
    "public section",
    "",
    "/-!",
    "# The re-exports",
    "",
    "The counterparts of the Rust crate's `pub use` lines: each item gets a second name, and so",
    "does each public member of it. Generated by `BSmtLib.Facts.Reexports.render`; do not edit.",
    s!"Regenerate it with `{command}` in `lean/`. The naming check (`BSmtLib.Facts.Names`)",
    "fails when it is stale.",
    "-/"]
  for use in uses do
    lines := lines ++ #[""] ++ commentLines use.rust
    for (rust, item) in itemsOf env use do
      lines := lines ++ #["", s!"-- `{item}`, by `pub use {rust}`"] ++
        itemLines tokens env use.target item
  return "\n".intercalate lines.toList ++ "\n"

/-- The number of second names `export` gives for `uses` in `env`. -/
def count (env : Environment) : Nat × Nat :=
  uses.foldl (init := (0, 0)) fun (items, members) use =>
    let found := itemsOf env use
    let more := found.foldl (fun n (_, item) => n + (membersOf env item).size) 0
    (items + found.size, members + more)

/--
`#reexports` checks the generated module `BSmtLib.Reexports`: it fails if the file differs from
what `render` makes now, naming the command that writes it, and for each item or member whose
second name does not resolve to it; and lists how many items and members it re-exports.
-/
syntax (name := reexportsCmd) "#reexports" : command

@[command_elab reexportsCmd]
def elabReexports : CommandElab := fun _ => do
  let env ← getEnv
  -- the package's directory, from this file's path below it
  let file ← IO.FS.realPath (← getFileName)
  let some dir := (List.range 3).foldlM (fun (p : System.FilePath) _ => p.parent) file |
    throwError "#reexports: no package directory above {file}"
  -- the modules the generated module is made from, as `reexports` imports them
  let sourceEnv ← importModules (sources.toArray.map ({ module := · })) {}
  let expected := render (← Parser.builtinTokenTable.get) sourceEnv
  let actual ← (IO.FS.readFile (dir / path) : IO String)
  unless actual == expected do
    logError m!"{path} is stale: regenerate it with `{command}` in the package's directory"
  let resolvesTo (alias name : Name) : Bool := (getAliases env alias false).contains name
  for use in uses do
    for (_, item) in itemsOf env use do
      let some last := item.components.getLast? | continue
      let alias := use.target ++ last
      unless resolvesTo alias item do
        logError m!"{item} has no second name {alias}"
      for member in membersOf env item do
        let memberAlias := alias ++ member.replacePrefix item .anonymous
        unless resolvesTo memberAlias member do
          logError m!"the member {member} of {item} has no second name {memberAlias}"
  let (items, members) := count env
  logInfo m!"{items} items re-exported, with {members} members"

end BSmtLib.Facts.Reexports
