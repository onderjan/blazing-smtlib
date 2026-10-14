module

public meta import Lean

@[expose] public meta section

/-!
# The naming rule, checked

The declarations of the library, of the specification and of their facts are named after the
modules that declare them, so that a name says which file to open:

- a declaration is named under its module's path, and where several module paths prefix a name,
  the longest is its module; a declaration named exactly like its module complies;
- a module may add to the namespace of a type that a sibling module (one in the same directory)
  declares, when the addition is about the type and is used by dot notation;
- names that Lean derives (automatic instance names, matchers, equation lemmas, auxiliary
  definitions, syntax kinds) and private declarations are exempt.

`#naming` checks the rule on every module below `BSmtLib` and `BSmtLibSpec` in the environment.
It lists the additions to a sibling's type, which the rule allows but whose use by dot notation
it does not check, and fails with an error for every other declaration outside its module's path
that is not among the exceptions it is given.

`#resolves` shows what names resolve to; `BSmtLib.Facts.Reexports` checks the re-exports.

This module is a tool of the facts, not a part of any of them, and not trusted: it only checks
and lists, and `#guard_msgs` around it pins the lists.
-/

namespace BSmtLib.Facts.Naming

open Lean Elab Command

/-- The modules that the rule is checked on. -/
def checked (module : Name) : Bool :=
  (`BSmtLib).isPrefixOf module || (`BSmtLibSpec).isPrefixOf module

/-- The suffixes of the names that Lean derives from a declaration. -/
def derivedSuffixes : List String :=
  ["brecOn", "below", "binductionOn", "casesOn", "recOn", "rec", "noConfusion",
    "noConfusionType", "ctorIdx", "toCtorIdx", "ofNat", "injEq", "inj", "sizeOf_spec",
    "eq_def", "induct", "mutual_induct", "fun_cases", "induct_unfolding", "ext_iff", "ctorElim",
    "ctorElimType", "elim", "eq_unfold", "fun_cases_unfolding", "partial_correctness",
    "fixpoint_induct", "match", "proof", "eq", "eq_iff", "splitter", "congr_simp"]

/-- Whether the component `s` is the derived suffix `p`, possibly numbered (`eq_1`). -/
def numbered (s p : String) : Bool :=
  s == p || (s.startsWith (p ++ "_") &&
    ((s.toList.drop (p.length + 1)).all fun ch => ch.isDigit || ch == '_'))

/-- Whether a proper prefix of `name` is an instance: then `name` is one of its parts. -/
partial def belowInstance (env : Environment) : Name → Bool
  | .anonymous => false
  | p@(.str q _) => Meta.isInstanceCore env p || belowInstance env q
  | p@(.num q _) => Meta.isInstanceCore env p || belowInstance env q

/-- Whether the constant is a syntax kind or a parser, which a `syntax` command derives. -/
def isSyntaxKind (info : ConstantInfo) : Bool :=
  match info.type.getAppFn.constName? with
  | some n => n == ``Lean.ParserDescr || n == ``Lean.TrailingParserDescr ||
      n == ``Lean.Parser.Parser || n == ``Lean.Parser.TrailingParser
  | none => false

/-- Whether `name` is a declaration that the rule applies to: one of its own, not derived by
Lean, not private, and not an automatic instance name. -/
def subject (env : Environment) (name : Name) (info : ConstantInfo) : Bool :=
  !name.hasMacroScopes && !isPrivateName name && !isAuxRecursor env name &&
    !isNoConfusion env name && !(env.isProjectionFn name) && !(Meta.isMatcherCore env name) &&
    !(info matches .ctorInfo _ | .recInfo _) && !isSyntaxKind info &&
    !(name.components.any fun c =>
      let s := c.toString
      s.startsWith "_" || derivedSuffixes.any (numbered s ·)) &&
    !(belowInstance env name.getPrefix) &&
    !(Meta.isInstanceCore env name && (name.components.getLast?.any fun c =>
      c.toString.startsWith "inst"))

/-- The longest module path among `modules` that prefixes `name`, the name itself included. -/
partial def longestModule (modules : NameSet) : Name → Option Name
  | .anonymous => none
  | n => if modules.contains n then some n else longestModule modules n.getPrefix

/-- Whether the constant is a type, or a function that returns one: what dot notation reaches. -/
def isType (info : ConstantInfo) : Bool :=
  match info with
  | .inductInfo _ => true
  | .defnInfo d => (d.type.getForallBodyMaxDepth 1000).isSort
  | .axiomInfo d => (d.type.getForallBodyMaxDepth 1000).isSort
  | _ => false

/-- How a declaration stands to the rule. -/
inductive Standing where
  | complies
  /-- An addition to the namespace of a type that the sibling module declares. -/
  | sibling (typeModule : Name)
  | outside (module : Name)

/-- How the declaration `name` of the module `module` stands to the rule. -/
def standing (env : Environment) (modules : NameSet) (module name : Name) : Standing :=
  match longestModule modules name with
  | some m =>
    if m == module then .complies
    else
      let parent := name.getPrefix
      let typeModule := (env.getModuleIdxFor? parent).map fun i => env.header.moduleNames[i.toNat]!
      match env.find? parent, typeModule with
      | some info, some tm =>
        if isType info && tm == m && tm.getPrefix == module.getPrefix then .sibling tm
        else .outside m
      | _, _ => .outside m
  | none => .outside .anonymous

/-- Names sorted by how they print. -/
def sortNames (names : Array Name) : Array Name :=
  names.qsort fun a b => a.toString < b.toString

/--
`#naming except N₁ N₂ …` checks the naming rule on the modules below `BSmtLib` and
`BSmtLibSpec`: it lists the declarations that add to the namespace of a sibling module's type,
grouped by module, and the exceptions `N₁ N₂ …` with the modules they are declared in; and fails
with an error for each other declaration outside its module's path, and for each exception that
does not lie outside it.
-/
syntax (name := namingCmd) "#naming" (" except" (ppSpace ident)+)? : command

@[command_elab namingCmd]
def elabNaming : CommandElab := fun stx => do
  let exceptions : Array Name :=
    if stx[1].isNone then #[] else stx[1][1].getArgs.map (·.getId)
  let env ← getEnv
  let moduleNames := env.header.moduleNames.filter checked
  let modules : NameSet := moduleNames.foldl (·.insert ·) {}
  let mut count := 0
  let mut siblings : Array (Name × Name) := #[]
  let mut excepted : Array (Name × Name) := #[]
  let mut outside : Array (Name × Name × Name) := #[]
  for (name, info) in env.constants.map₁.toList do
    let some idx := env.getModuleIdxFor? name | continue
    let module := env.header.moduleNames[idx.toNat]!
    unless checked module do continue
    unless subject env name info do continue
    count := count + 1
    match standing env modules module name with
    | .complies => pure ()
    | .sibling _ => siblings := siblings.push (module, name)
    | .outside m =>
      if exceptions.contains name then excepted := excepted.push (module, name)
      else outside := outside.push (module, name, m)
  let mut lines : Array String :=
    #[s!"{count} declarations in {moduleNames.size} modules; " ++
      s!"{siblings.size} add to a sibling's type:"]
  for module in sortNames (siblings.map (·.1)).toList.eraseDups.toArray do
    lines := lines.push s!"{module}:"
    for name in sortNames ((siblings.filter (·.1 == module)).map (·.2)) do
      lines := lines.push s!"  {name}"
  lines := lines.push s!"{excepted.size} exceptions:"
  for (module, name) in excepted.qsort (fun a b => a.2.toString < b.2.toString) do
    lines := lines.push s!"  {name} in {module}"
  logInfo (String.intercalate "\n" lines.toList)
  for (module, name, m) in outside.qsort (fun a b => a.2.1.toString < b.2.1.toString) do
    logError m!"{name}, declared in {module}, lies outside its module's path: its longest module \
      path is {m}"
  for name in exceptions do
    unless excepted.any (·.2 == name) do
      logError m!"the exception {name} is not a declaration outside its module's path"

/-- Whether the declaration is public: not private, and below no namespace `Internal`. -/
def isPublic (name : Name) : Bool :=
  !isPrivateName name && !name.isInternalDetail && !name.components.contains `Internal

/-- Whether a component of `name` is a suffix that Lean derives. -/
def derived (name : Name) : Bool :=
  name.components.any fun c => derivedSuffixes.any (numbered c.toString ·)

/--
`#resolves N₁ N₂ …` shows, for each name, the declaration it resolves to at the root of a file
that imports the library and opens nothing, or that it resolves to none.
-/
syntax (name := resolvesCmd) "#resolves" (ppSpace ident)+ : command

@[command_elab resolvesCmd]
def elabResolves : CommandElab := fun stx => do
  let env ← getEnv
  let names := stx[1].getArgs.map (·.getId)
  let lines := names.map fun name =>
    match ResolveName.resolveGlobalName env {} .anonymous [] name with
    | [(target, [])] => s!"{name} ↦ {target}"
    | [] => s!"{name} ↦ none"
    | many => s!"{name} ↦ {many.map (·.1)}"
  logInfo (String.intercalate "\n" lines.toList)

end BSmtLib.Facts.Naming
