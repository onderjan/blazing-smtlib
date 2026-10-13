import Lean

/-!
# The trusted adapters of the root theorems

A root theorem of a proof library is stated with the specification (`BSmtLibSpec`), the library,
Lean, and definitions of the proof libraries that put the library into the specification's
shapes: the adapters. A theorem stated with a wrong adapter is a theorem about the wrong thing,
so the adapters are trusted together with the specification and the statements.

`#adapters` computes that set from the environment. Starting from the constants in the statements
of the theorems declared in the current module, it follows the types and the bodies of the
definitions it reaches, the constructors of the inductive types and structures, and the types of
everything, and stops at the constants of the specification, of the library, of the lexers of the
chain and of Lean. Every other constant it reaches is an adapter. A theorem reached in a body is a
proof and is not followed: only what a statement means is trusted.

The lexers of the chain (`BSmtLib.Proofs.Lexer`) are what the root theorems of `BSmtLib.Proofs`
are about, as the library is what the others are about: a theorem says that its subject meets the
specification, so its subject need not be trusted.

This module is a tool of the proof libraries, not a part of any of them, and not trusted: it only
lists, and `#guard_msgs` around it pins the list.
-/

namespace BSmtLib.Trusted

open Lean Elab Command

/-- What a module is, for the trust of the root theorems. -/
inductive Side where
  /-- Lean's standard library. -/
  | lean
  /-- The trusted specification: `BSmtLibSpec` and the modules below it. -/
  | spec
  /-- The library: `BSmtLib` and the modules below it that are none of the others. -/
  | library
  /-- The lexers of the chain from the specification to the library's lexer:
  `BSmtLib.Proofs.Lexer` and the modules below it. -/
  | chain
  /-- Everything else: the proof libraries, the checks of the specification, this tool. -/
  | other
  deriving BEq

/-- The modules right below `BSmtLib` that are not the library. -/
def notLibrary : List Name :=
  [`SpecChecks, `Proofs, `ParserProofs, `EndToEnd, `Trusted]

/-- The side of the module named `module`. -/
def sideOf (module : Name) : Side :=
  match module.components with
  | `BSmtLibSpec :: _ => .spec
  | [`BSmtLib] => .library
  | `BSmtLib :: `Proofs :: `Lexer :: _ => .chain
  | `BSmtLib :: part :: _ =>
    if notLibrary.contains part then .other
    else .library
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

/-- The adapters reached from the constants `roots`, each paired with the constant it is in. -/
def adaptersFrom (env : Environment) (roots : Array (Name × Name)) : Array Adapter := Id.run do
  let mut seen : NameSet := {}
  let mut todo := roots
  let mut found : Array Adapter := #[]
  while 0 < todo.size do
    let (name, parent) := todo.back!
    todo := todo.pop
    if seen.contains name then continue
    seen := seen.insert name
    let module := moduleOf env name
    if sideOf module != .other then continue
    let some info := env.find? name | continue
    if info matches .thmInfo _ then continue
    found := found.push { name, module, reachedFrom := parent }
    todo := todo ++ (dependencies env info).map (·, name)
  return found

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
`M₁ M₂ …` and below none of them.
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
  let found := adaptersFrom env roots
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

end BSmtLib.Trusted
