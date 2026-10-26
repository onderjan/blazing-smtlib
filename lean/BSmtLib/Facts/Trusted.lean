module

public meta import Lean

@[expose] public meta section

/-!
# The trusted adapters of the root theorems

A root theorem of a proof library is stated with the specification formalism (`BSmtLibSpec`), the
library, Lean, and definitions of the proof libraries that put the library into the formalism's
shapes: the adapters. A theorem stated with a wrong adapter is a theorem about the wrong thing, so
the adapters are trusted together with the formalism and the statements.

`#adapters` computes that set from the environment. It starts from the constants in the
statements of the theorems declared in the current module, and follows:

- the types and the bodies of the definitions it reaches;
- the constructors of the inductive types and structures;
- the types of everything.

It stops at the constants of the formalism, of the library, of the lexers of the chain and of
Lean. Every other constant it reaches is an adapter. A theorem reached in a body is a proof and is
not followed: only what a statement means is trusted. A module sees an imported
definition whose body its module does not expose without the body, and does not see a private
declaration of another module at all; the walk cannot follow such a constant, so it fails on it
instead of passing over it.

The lexers of the chain (`BSmtLib.Lexer.Internal.VNaive`, `WRustPort` and `X1BatchInCore`) are
what the root theorems of `BSmtLib.Facts.Lexer` are about, as the library is what the others are
about: a theorem says that its subject meets the formalism, so its subject need not be
trusted.

`#trusts` is the same walk for theorems stated with the library's public API rather than the
formalism (`BSmtLib.Facts`, `BSmtLib.Facts.PublicApi`). For each theorem, it lists:

- the small definitions its statement reaches;
- every constant of the formalism, of the library's internals, of the lexers of the chain or
  of another module that the statement names.

So a statement that rests on more than its small definitions and the public API shows so in the
pinned list.

This module is a tool of the proof libraries, not a part of any of them, and not trusted: it only
lists, and `#guard_msgs` around it pins the list.
-/

namespace BSmtLib.Facts.Trusted

open Lean Elab Command

/-- What a module is, for the trust of the root theorems. -/
inductive Side where
  /-- Lean's standard library. -/
  | lean
  /-- The trusted formalism: `BSmtLibSpec` and the modules below it, but for
  `BSmtLibSpec.Facts`. -/
  | spec
  /-- The library: `BSmtLib` and the modules below it that are none of the others. -/
  | library
  /-- The lexers of the chain from the formalism to the library's lexer:
  `BSmtLib.Lexer.Internal.VNaive`, `WRustPort` and `X1BatchInCore`, and the modules below them. -/
  | chain
  /-- Everything else: the facts about the library and about the formalism, this tool. -/
  | other
  deriving BEq

/-- The lexers of the chain, below `BSmtLib.Lexer.Internal`. -/
def chainLexers : List Name :=
  [`VNaive, `WRustPort, `X1BatchInCore]

/-- The side of the module named `module`. -/
def sideOf (module : Name) : Side :=
  match module.components with
  | `BSmtLibSpec :: `Facts :: _ => .other
  | `BSmtLibSpec :: _ => .spec
  | `BSmtLib :: `Facts :: _ => .other
  | `BSmtLib :: `Lexer :: `Internal :: lexer :: _ =>
    if chainLexers.contains lexer then .chain else .library
  | `BSmtLib :: _ => .library
  | root :: _ => if [`Init, `Std, `Lean].contains root then .lean else .other
  | [] => .other

/-- The module that declares `name`; the current module for a constant declared in it. -/
def moduleOf (env : Environment) (name : Name) : Name :=
  match env.getModuleIdxFor? name with
  | some idx => env.header.moduleNames[idx.toNat]!
  | none => env.mainModule

/-- The constants that the meaning of a constant rests on: those in its type and, for a
definition, in its body; for an inductive type its constructors, for a constructor or a recursor
its type. Theorems are left out. -/
def dependencies (env : Environment) (info : ConstantInfo) : Array Name :=
  let fromType := info.type.getUsedConstants
  let fromRest := match info with
    | .defnInfo d => d.value.getUsedConstants
    | .opaqueInfo d => d.value.getUsedConstants
    | .inductInfo d => d.ctors.toArray
    | .ctorInfo d => #[d.induct]
    | .recInfo d => d.all.toArray
    | _ => #[]
  (fromType ++ fromRest).filter fun name =>
    match env.find? name with
    | some (.thmInfo _) => false
    | _ => true

/-- An adapter, with the module that declares it and the constant it was first reached from. -/
structure Adapter where
  /-- The adapter. -/
  name : Name
  /-- The module that declares it. -/
  module : Name
  /-- The constant it was first reached from: a theorem, by its statement, or another adapter. -/
  reachedFrom : Name

/-- A constant that the walk reaches but cannot read: one that the environment does not hold,
such as a private declaration of another module, or one whose body it does not hold, such as a
definition that its module does not expose, which an importing module sees as an axiom. -/
structure Unseen where
  /-- The constant. -/
  name : Name
  /-- The module that declares it, the current module if the environment does not hold it. -/
  module : Name
  /-- The constant it was first reached from. -/
  reachedFrom : Name

/-- The adapters reached from the constants `roots`, each paired with the constant it is in, and
the constants reached that are neither of the formalism, the library, the chain nor Lean
and whose meaning the walk cannot read. -/
def adaptersFrom (env : Environment) (roots : Array (Name × Name)) :
    MetaM (Array Adapter × Array Unseen) := do
  let mut seen : NameSet := {}
  let mut todo := roots
  let mut found : Array Adapter := #[]
  let mut unseen : Array Unseen := #[]
  while 0 < todo.size do
    let (name, parent) := todo.back!
    todo := todo.pop
    if seen.contains name then continue
    seen := seen.insert name
    let module := moduleOf env name
    if sideOf module != .other then continue
    let some info := env.find? name
      | unseen := unseen.push { name, module, reachedFrom := parent }; continue
    if info matches .thmInfo _ then continue
    -- an auxiliary proof is seen as an axiom: a proof, which is not followed
    if info matches .axiomInfo _ then
      if ← Meta.isProp info.type then continue
      unseen := unseen.push { name, module, reachedFrom := parent }; continue
    found := found.push { name, module, reachedFrom := parent }
    todo := todo ++ (dependencies env info).map (·, name)
  return (found, unseen)

/-- The theorems declared in the current module, internal ones left out. -/
def localTheorems (env : Environment) : Array Name :=
  env.constants.map₂.foldl (init := #[]) fun acc name info =>
    if info matches .thmInfo _ && !name.isInternalDetail then acc.push name else acc

/-- Whether `name` is a declaration of its own in the source, not one that Lean derives from
another: a constructor, a field, a recursor, a matcher, an auxiliary definition. -/
def declared (env : Environment) (name : Name) : Bool :=
  !name.isInternalDetail && !isAuxRecursor env name && !isNoConfusion env name &&
    !(env.isProjectionFn name) && !(Meta.isMatcherCore env name) &&
    !(name matches .str _ "ctorIdx") &&
    !((env.find? name).any fun info => info matches .ctorInfo _ | .recInfo _)

/-- Names sorted by how they print. -/
def sortNames (names : Array Name) : Array Name :=
  names.qsort fun a b => a.toString < b.toString

/--
`#adapters within M₁ M₂ …` lists the adapters of the theorems declared in the current module,
the declarations of their own (`declared`), grouped by the module that declares them; and fails
with an error for each adapter, of its own or derived, declared in a module that is none of
`M₁ M₂ …` and below none of them, and for each constant it reaches outside the formalism,
the library, the chain and Lean that it cannot read: one the environment does not hold or holds
without its body.
-/
syntax (name := adaptersCmd) "#adapters" " within" (ppSpace ident)+ : command

@[command_elab adaptersCmd]
def elabAdapters : CommandElab := fun stx => do
  let allowed := stx[2].getArgs.map (·.getId)
  let env ← getEnv
  let theorems := localTheorems env
  let roots := theorems.foldl (init := #[]) fun acc thm =>
    match env.find? thm with
    | some info => acc ++ info.type.getUsedConstants.map (·, thm)
    | none => acc
  let (found, unseen) ← liftTermElabM (adaptersFrom env roots)
  let shown := found.filter fun adapter => declared env adapter.name
  let modules := sortNames (shown.map (·.module)).toList.eraseDups.toArray
  let mut lines : Array String :=
    #[s!"{theorems.size} theorems, stated with {shown.size} adapters:"]
  for module in modules do
    lines := lines.push s!"{module}:"
    for name in sortNames ((shown.filter (·.module == module)).map (·.name)) do
      lines := lines.push s!"  {name}"
  logInfo (String.intercalate "\n" lines.toList)
  for adapter in found do
    unless allowed.any (·.isPrefixOf adapter.module) do
      logError m!"the adapter {adapter.name}, reached from {adapter.reachedFrom}, is declared in \
        {adapter.module}, outside the modules of adapters {allowed.toList}"
  for constant in unseen do
    logError m!"the constant {constant.name}, reached from {constant.reachedFrom} and declared in \
      {constant.module}, cannot be read here: its module keeps it private or does not expose \
      its body, so the adapters it rests on cannot be listed"

/-! ## What a statement rests on beside the public API -/

/-- Whether a name of the library is one of its internals. -/
def internal (name : Name) : Bool :=
  name.components.contains `Internal || isPrivateName name

/-- What a theorem's statement rests on, by where it is declared. -/
structure Reached where
  /-- The small definitions: the adapters of the modules given to `#trusts`. -/
  small : Array Name := #[]
  /-- The constants of the formalism. -/
  spec : Array Name := #[]
  /-- The library's internals. -/
  internals : Array Name := #[]
  /-- The constants of the lexers of the chain. -/
  chain : Array Name := #[]
  /-- The constants of other modules. -/
  other : Array Name := #[]
  /-- The constants it reaches but cannot read, as `adaptersFrom` reports them. -/
  unseen : Array Unseen := #[]

/-- What the constants `roots` rest on, the small definitions being those declared in the
modules `small` and below them; a small definition or another constant outside the formalism,
the library, the chain and Lean that it cannot read is reported in `unseen`. -/
def reach (env : Environment) (small : Array Name) (thm : Name) (roots : Array Name) :
    MetaM Reached := do
  let mut seen : NameSet := {}
  let mut todo := roots.map (·, thm)
  let mut found : Reached := {}
  while 0 < todo.size do
    let (name, parent) := todo.back!
    todo := todo.pop
    if seen.contains name then continue
    seen := seen.insert name
    let module := moduleOf env name
    let some info := env.find? name
      | if sideOf module == .other then
          found := { found with
            unseen := found.unseen.push { name, module, reachedFrom := parent } }
        continue
    if info matches .thmInfo _ then continue
    match sideOf module with
    | .lean => pure ()
    | .spec =>
      if declared env name then found := { found with spec := found.spec.push name }
    | .library =>
      if internal name then found := { found with internals := found.internals.push name }
    | .chain =>
      if declared env name then found := { found with chain := found.chain.push name }
    | .other =>
      if small.any (·.isPrefixOf module) then
        -- an auxiliary proof is seen as an axiom: a proof, which is not followed
        if info matches .axiomInfo _ then
          unless ← Meta.isProp info.type do
            found := { found with
              unseen := found.unseen.push { name, module, reachedFrom := parent } }
          continue
        if declared env name then found := { found with small := found.small.push name }
        todo := todo ++ (dependencies env info).map (·, name)
      else if declared env name then found := { found with other := found.other.push name }
  return found

/-- The line of a list of names, `none` if there are none; each name without the longest of the
prefixes `strip` that it has. -/
def line (label : String) (strip : Array Name) (names : Array Name) : Option String :=
  if names.isEmpty then none
  else
    let shown := (sortNames names).toList.map fun name =>
      let prefix_ := strip.foldl (init := Name.anonymous) fun best p =>
        if p.isPrefixOf name && best.getNumParts < p.getNumParts then p else best
      (name.replacePrefix prefix_ .anonymous).toString
    -- the lines wrapped at 100 columns
    let (lines, last) := shown.foldl (init := (#[], s!"  {label}:")) fun (lines, current) name =>
      if current.length + name.length + 2 ≤ 100 then
        (lines, if current.endsWith ":" then current ++ " " ++ name else current ++ ", " ++ name)
      else (lines.push (current ++ ","), "    " ++ name)
    some ("\n".intercalate (lines.push last).toList)

/--
`#trusts within M₁ M₂ …` lists, for each theorem declared in the current module, in the order of
their names, what its statement rests on beside Lean and the library's public API: the small
definitions it reaches, those declared in the modules `M₁ M₂ …` and below them, shown without
their module's path, whose types and bodies it follows as `#adapters` follows adapters; and the
constants of the formalism, of the library's internals (a name with a component `Internal`,
or a private name), of the lexers of the chain and of other modules that its statement or a
small definition names; and fails with an error for each small definition whose body it cannot
read and for each constant outside the formalism, the library, the chain and Lean that the
environment does not hold.
-/
syntax (name := trustsCmd) "#trusts" " within" (ppSpace ident)+ : command

@[command_elab trustsCmd]
def elabTrusts : CommandElab := fun stx => do
  let small := stx[2].getArgs.map (·.getId)
  let env ← getEnv
  let theorems := sortNames (localTheorems env)
  let mut lines : Array String := #[]
  for thm in theorems do
    let some info := env.find? thm | continue
    let reached ← liftTermElabM (reach env small thm info.type.getUsedConstants)
    for constant in reached.unseen do
      logError m!"the constant {constant.name}, reached from {constant.reachedFrom} and declared \
        in {constant.module}, cannot be read here: its module keeps it private or does not \
        expose its body, so what {thm} rests on cannot be listed"
    lines := lines.push s!"{thm}:"
    let parts := [line "small" small reached.small, line "spec" #[] reached.spec,
      line "internal" #[] reached.internals, line "chain" #[] reached.chain,
      line "other" #[] reached.other]
    let parts := parts.filterMap id
    if parts.isEmpty then lines := lines.push "  public API only"
    lines := lines ++ parts.toArray
  logInfo (String.intercalate "\n" lines.toList)

end BSmtLib.Facts.Trusted
