module

import Lean

/-!
# The declaration audit

The part of `lake exe audit` that reads the built tree, and all that `lake exe audit --fast`
runs. Run in the package's directory after `lake build`, it loads every module of the library,
of the specification and of their facts with all its private declarations and its compiled
code, and requires four things:

- **Axioms.** Every declaration depends on no axioms but `propext`, `Classical.choice` and
  `Quot.sound`. The declarations in `sorryAllowed` may depend on `sorryAx` beside them.
- **Constructs.** No declaration is an axiom (`native_decide` declares one of its own),
  `unsafe`, `@[implemented_by]` or `@[extern]`, and none uses `Lean.ofReduceBool`,
  `Lean.ofReduceNat` or `Lean.trustCompiler`, by which a proof trusts the compiler. The
  definitions marked `partial` are those in `partialAllowed`.
- **The kernel on.** `set_option debug.skipKernelTC` leaves no trace in the environment, so the
  audit reads the sources and the lakefile's settings and rejects every line whose code (its
  comment left out) names `skipKernelTC`.
- **Panics.** The compiled code of the library (the modules below `BSmtLib` but those below
  `BSmtLib.Facts`, the lexers of the chain too), outside its meta code, reaches no panic: its call
  graph, followed through the standard library, reaches neither `panicCore` nor a primitive whose
  name carries `!` (`Array.get!Internal`, `ByteArray.get!`, …), which panic in their C
  implementation. The declarations in `panicAllowed` may.

The three allow-lists only shrink: an entry that is no longer needed is an error, so it is
removed when its declaration is fixed, and an entry is added only by an edit that review sees.

The `#guard_msgs in #print axioms` after each theorem in the facts stay the record of each
theorem's axioms; this audit covers every declaration, private and auxiliary ones too.

It prints what it found and every violation, and exits with 1 if there was one.
-/

open Lean

namespace Audit.Declarations

/-- The source directories whose modules are audited: the library, the specification and their
facts. -/
def sourceRoots : List String := ["BSmtLib", "BSmtLibSpec"]

/-- The axioms that every declaration may depend on. -/
def allowedAxioms : List Name := [``propext, ``Classical.choice, ``Quot.sound]

/-- The declarations that may depend on `sorryAx`: the theorems of `BSmtLib.Facts.PublicApi`
whose proofs are still to come. Shrink-only. -/
def sorryAllowed : List Name := []

/-- The definitions that may be `partial`: the loops of the reader and the lexer over a whole
input from a buffered reader, and two functions of the naming check. Shrink-only. -/
def partialAllowed : List Name := [
  `BSmtLib.Reader.readFrom,
  `BSmtLib.Lexer.lexFrom,
  `BSmtLib.Facts.Naming.belowInstance,
  `BSmtLib.Facts.Naming.longestModule]

/-- The declarations of the library whose compiled code may reach a panic. Shrink-only: none
is left. -/
def panicAllowed : List Name := []

/-- The axioms through which a proof trusts the compiler, as `native_decide` does. -/
def compilerAxioms : List Name := [``Lean.ofReduceBool, ``Lean.ofReduceNat, ``Lean.trustCompiler]

/-- The module of a source file, from its path relative to the package's directory. -/
def moduleOfPath (path : System.FilePath) : Name :=
  let parts := (path.withExtension "").components
  parts.foldl (fun name part => .str name part) .anonymous

/-- The `.lean` files below `dir`, sorted. -/
partial def leanFiles (dir : System.FilePath) : IO (Array System.FilePath) := do
  let mut found := #[]
  for entry in ← dir.readDir do
    if ← entry.path.isDir then found := found ++ (← leanFiles entry.path)
    else if entry.path.extension == some "lean" then found := found.push entry.path
  return found.qsort (·.toString < ·.toString)

/-- Whether the module is one of the audited ones. -/
def audited (module : Name) : Bool :=
  sourceRoots.any fun root => (Name.mkSimple root).isPrefixOf module

/-- Whether the module is the library's: below `BSmtLib` but not below `BSmtLib.Facts`. -/
def library (module : Name) : Bool :=
  (`BSmtLib).isPrefixOf module && !(`BSmtLib.Facts).isPrefixOf module

/-- The suffixes of the names that the compiler and the elaborator derive from a declaration. -/
def derivedSuffixes : List String :=
  ["_boxed", "_closed_", "_lam_", "_elam_", "_redArg", "_unsafe_rec", "_proof_", "_cstage",
    "_rarg", "_lambda_", "_unary", "_binary", "_mutual", "spec_", "proof_", "match_", "eq_"]

/-- Whether the name component is one that the compiler or the elaborator derives. -/
def derivedComponent (c : Name) : Bool :=
  match c with
  | .str _ s => derivedSuffixes.any fun p => s.startsWith p
  | _ => false

/-- The declaration that a derived or compiled name belongs to: a specialisation
`f._at_.g.spec_n` belongs to `g`; trailing derived components (`_proof_1`, `_closed_2`, `_lam_0`,
`_boxed`, `_redArg`, `_unsafe_rec`, `match_1`, …) are dropped. -/
def declOf (name : Name) : Name :=
  let comps := name.componentsRev
  -- the components after the last `_at_`, if any
  let comps := match comps.findIdx? (· == `_at_) with
    | some i => comps.take i
    | none => comps
  let comps := comps.dropWhile derivedComponent
  comps.foldr (fun c acc => acc ++ c) .anonymous

/-- The declaration that a derived or compiled name belongs to, as `declOf` finds it, a private
one by its user name. -/
def ownerOf (name : Name) : Name :=
  let decl := declOf name
  (privateToUserName? decl).getD decl

/-- A violation, with the module it was found in. -/
structure Violation where
  module : Name
  message : String

/-- The module that declares `name`, anonymous if none. -/
def moduleOf (env : Environment) (name : Name) : Name :=
  match env.getModuleIdxFor? name with
  | some idx => env.header.moduleNames[idx.toNat]?.getD .anonymous
  | none => .anonymous

/-- Names sorted by how they print. -/
def sortNames (names : Array Name) : Array Name :=
  names.qsort fun a b => a.toString < b.toString

/-! ## Axioms -/

/-- The axioms that the constants seen so far depend on. A constant is entered as depending on
none before its dependencies are walked, so that a cycle (an inductive type and its
constructors) ends; an axiom within such a cycle is still found from the cycle's other
members, as `Lean.collectAxioms` finds it. -/
abbrev AxiomsM := ReaderT Environment (StateM (Std.HashMap Name (Array Name)))

/-- The axioms that the constant `name` depends on, as `Lean.collectAxioms` collects them: by its
type, its value, and an inductive type's constructors. -/
partial def axiomsOf (name : Name) : AxiomsM (Array Name) := do
  if let some known := (← get).get? name then return known
  modify (·.insert name #[])
  let env ← read
  let fromExprs (es : List Expr) : AxiomsM (Array Name) := do
    let mut found := #[]
    for e in es do
      for c in e.getUsedConstants do
        for ax in ← axiomsOf c do
          unless found.contains ax do found := found.push ax
    return found
  let found ← match env.find? name with
    | some (.axiomInfo v) => do
      let found ← fromExprs [v.type]
      pure (if found.contains name then found else found.push name)
    | some (.defnInfo v) => fromExprs [v.type, v.value]
    | some (.thmInfo v) => fromExprs [v.type, v.value]
    | some (.opaqueInfo v) => fromExprs [v.type, v.value]
    | some (.ctorInfo v) => fromExprs [v.type]
    | some (.recInfo v) => fromExprs [v.type]
    | some (.inductInfo v) => fromExprs (v.type :: v.ctors.map mkConst)
    | _ => pure #[]
  modify (·.insert name found)
  return found

/-- Audits the axioms of every declaration; returns the number of declarations, the
violations, and the entries of `sorryAllowed` that were needed. -/
def auditAxioms (env : Environment) (names : Array Name) :
    IO (Nat × Array Violation × Array Name) := do
  let mut byOwner : Std.HashMap Name (Name × Array Name) := {}
  let mut cache : Std.HashMap Name (Array Name) := {}
  for name in names do
    let (axioms, cache') := (axiomsOf name).run env |>.run cache
    cache := cache'
    let extra := axioms.filter (!allowedAxioms.contains ·)
    if extra.isEmpty then continue
    let owner := ownerOf name
    let (_, known) := byOwner.getD owner (moduleOf env name, #[])
    byOwner := byOwner.insert owner
      (moduleOf env name, known ++ extra.filter (!known.contains ·))
  let mut violations := #[]
  let mut used := #[]
  for owner in sortNames (byOwner.toArray.map (·.1)) do
    let (module, extra) := byOwner.getD owner (.anonymous, #[])
    if sorryAllowed.contains owner && extra.all (· == ``sorryAx) then
      used := used.push owner
    else
      violations := violations.push { module, message :=
        s!"{owner} depends on the axioms {(sortNames extra).toList}" }
  for entry in sorryAllowed do
    unless used.contains entry do
      violations := violations.push { module := .anonymous, message :=
        s!"sorryAllowed lists {entry}, which does not depend on sorryAx (any more): remove it" }
  return (names.size, violations, used)

/-! ## Constructs -/

/-- Audits the constructs of every declaration; returns the violations and the
`partial` definitions found. -/
def auditConstructs (env : Environment) (names : Array Name) :
    IO (Array Violation × Array Name) := do
  let mut violations := #[]
  let mut partials := #[]
  for name in names do
    let some info := env.find? name | continue
    let module := moduleOf env name
    let flag (what : String) : Array Violation → Array Violation :=
      (·.push { module, message := s!"{name} {what}" })
    if info matches .axiomInfo _ then violations := flag "is an axiom" violations
    if info.isUnsafe then violations := flag "is unsafe" violations
    if let some target := Compiler.getImplementedBy? env name then
      violations := flag s!"is implemented by {target}" violations
    if isExtern env name then violations := flag "is @[extern]" violations
    let used := info.type.getUsedConstants ++ (info.value?.map (·.getUsedConstants)).getD #[]
    for ax in compilerAxioms do
      if used.contains ax then
        violations := flag s!"uses {ax}, by which a proof trusts the compiler (native_decide)"
          violations
    -- a `partial` definition is an opaque constant, compiled from its `_unsafe_rec`
    if info matches .opaqueInfo _ && env.contains (name ++ `_unsafe_rec) then
      let owner := ownerOf name
      unless partials.contains owner do partials := partials.push owner
  for owner in partials do
    unless partialAllowed.contains owner do
      violations := violations.push { module := moduleOf env owner, message :=
        s!"{owner} is partial and not in partialAllowed" }
  for entry in partialAllowed do
    unless partials.contains entry do
      violations := violations.push { module := .anonymous, message :=
        s!"partialAllowed lists {entry}, which is not a partial definition (any more): remove it" }
  return (violations, sortNames partials)

/-! ## Panics -/

/-- The functions that a compiled body calls. -/
partial def calls : IR.FnBody → Array Name → Array Name
  | .vdecl _ _ v b, acc =>
    let acc := match v with
      | .fap f _ | .pap f _ => acc.push f
      | _ => acc
    calls b acc
  | .jdecl _ _ v b, acc => calls b (calls v acc)
  | .case _ _ _ alts, acc => alts.foldl (fun acc alt => calls alt.body acc) acc
  | e, acc => if e.isTerminal then acc else calls e.body acc

/-- The functions that the compiled declaration `name` calls, none for a primitive. -/
def callees (env : Environment) (name : Name) : Array Name :=
  match IR.findEnvDecl env name with
  | some (.fdecl _ _ _ body _) => (calls body #[]).toList.eraseDups.toArray
  | _ => #[]

/-- Whether calling `name` panics outright: `panicCore`, to which every panic comes, or a
primitive without a compiled body whose name carries `!`, such as `Array.get!Internal`. -/
def panics (env : Environment) (name : Name) : Bool :=
  name == ``panicCore ||
    (name.toString.contains '!' && !(IR.findEnvDecl env name matches some (.fdecl ..)))

/-- A site of the library that reaches a panic: the declaration, and a path of calls from one of
its compiled functions to the panic. -/
structure PanicSite where
  owner : Name
  module : Name
  path : Array Name

/-- The library's compiled functions outside meta code, the declarations they belong to, and the
sites among them that reach a panic. -/
def auditPanics (env : Environment) : IO (Nat × Array PanicSite) := do
  -- the library's compiled functions, and the functions they call, with a call that reaches each
  let mut roots : Array Name := #[]
  for h : idx in [0:env.header.moduleNames.size] do
    let module := env.header.moduleNames[idx]
    unless library module do continue
    for decl in IR.declMapExt.getModuleIREntries env idx ++
        IR.declMapExt.getModuleEntries env idx (level := .private) do
      unless isMarkedMeta env (declOf decl.name) || isMarkedMeta env decl.name do
        roots := roots.push decl.name
  roots := roots.toList.eraseDups.toArray
  let mut parent : Std.HashMap Name Name := {}
  let mut todo := roots.map (·, Name.anonymous)
  let mut reached : Array Name := #[]
  while h : 0 < todo.size do
    let (name, from_) := todo.back
    todo := todo.pop
    if parent.contains name then continue
    parent := parent.insert name from_
    reached := reached.push name
    unless panics env name do
      todo := todo ++ (callees env name).map (·, name)
  -- the functions that reach a panic, by the calls backwards
  let mut callers : Std.HashMap Name (Array Name) := {}
  for name in reached do
    unless panics env name do
      for callee in callees env name do
        callers := callers.insert callee ((callers.getD callee #[]).push name)
  let mut toPanic : Std.HashMap Name Name := {}
  let mut work : Array Name := #[]
  for name in reached do
    if panics env name then toPanic := toPanic.insert name name; work := work.push name
  while h : 0 < work.size do
    let name := work.back
    work := work.pop
    for caller in callers.getD name #[] do
      unless toPanic.contains caller do
        toPanic := toPanic.insert caller name
        work := work.push caller
  -- the library's functions that reach a panic, by declaration
  let mut sites : Array PanicSite := #[]
  let mut seenOwners : NameSet := {}
  for name in sortNames roots do
    unless toPanic.contains name do continue
    let owner := ownerOf name
    if seenOwners.contains owner then continue
    seenOwners := seenOwners.insert owner
    let mut path := #[name]
    let mut current := name
    for _ in [0:64] do
      match toPanic.get? current with
      | some next => if next == current then break else path := path.push next; current := next
      | none => break
    sites := sites.push { owner, module := moduleOf env name, path }
  return (roots.size, sites)

/-! ## The kernel turned off -/

/-- The lines of the file at `path` whose code, the part before the comment marker `comment`,
names `skipKernelTC`, which `set_option debug.skipKernelTC` uses to let declarations in without
the kernel's check. -/
def skipKernelTC (path : System.FilePath) (comment : String) : IO (Array String) := do
  let lines := (← IO.FS.readFile path).splitOn "\n"
  let mut found := #[]
  for line in lines, number in List.range lines.length do
    if ((line.splitOn comment).headD "").contains "skipKernelTC" then
      found := found.push s!"{path}:{number + 1}: sets debug.skipKernelTC, which lets \
        declarations in without the kernel's check"
  return found

/-! ## The run -/

/-- Runs the declaration audit; the exit code is 1 if there was a violation. -/
public def run : IO UInt32 := do
  initSearchPath (← findSysroot)
  let mut modules : Array Name := #[]
  let mut skips : Array Violation := #[]
  for root in sourceRoots do
    for file in ← leanFiles root do
      modules := modules.push (moduleOfPath file)
      let module := moduleOfPath file
      skips := skips ++ (← skipKernelTC file "--").map ({ module, message := · })
  let lakefile ← skipKernelTC "lakefile.toml" "#"
  skips := skips ++ lakefile.map ({ module := .anonymous, message := · })
  for module in modules do
    if (← findOLean module |>.toBaseIO) matches .error _ then
      IO.eprintln s!"no .olean for {module}: build the package first (lake build)"
      return 1
  let env ← importModules (modules.map ({ module := · })) {} (level := .private)
  let names := env.constants.map₁.toList.filterMap fun (name, _) =>
    if audited (moduleOf env name) then some name else none
  let names := sortNames names.toArray
  let mut violations : Array Violation := skips
  IO.println s!"{modules.size} modules, {names.size} declarations"
  let start ← IO.monoMsNow
  let (count, axiomViolations, sorried) ← auditAxioms env names
  violations := violations ++ axiomViolations
  IO.println s!"axioms: {count} declarations; {sorried.size} allowed to use sorryAx \
    ({(← IO.monoMsNow) - start} ms)"
  let start ← IO.monoMsNow
  let (constructViolations, partials) ← auditConstructs env names
  violations := violations ++ constructViolations
  IO.println s!"constructs: partial definitions {partials.toList} ({(← IO.monoMsNow) - start} ms)"
  let start ← IO.monoMsNow
  let (functions, sites) ← auditPanics env
  IO.println s!"panics: {functions} compiled functions of the library, {sites.size} reach a panic \
    ({(← IO.monoMsNow) - start} ms)"
  for site in sites do
    IO.println s!"  {site.module}: {site.owner} via {site.path.toList}"
    unless panicAllowed.contains site.owner do
      violations := violations.push { module := site.module, message :=
        s!"{site.owner} reaches a panic: {" → ".intercalate (site.path.toList.map toString)}" }
  for entry in panicAllowed do
    unless sites.any (·.owner == entry) do
      violations := violations.push { module := .anonymous, message :=
        s!"panicAllowed lists {entry}, which reaches no panic (any more): remove it" }
  for violation in violations do
    IO.eprintln s!"error: {if violation.module.isAnonymous then "" else s!"{violation.module}: "}\
      {violation.message}"
  if violations.isEmpty then
    IO.println "audit passed"
    return 0
  else
    IO.eprintln s!"audit failed: {violations.size} violations"
    return 1

end Audit.Declarations
