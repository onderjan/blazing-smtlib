module

public meta import Lean

@[expose] public meta section

/-!
# The public items of the Rust crate, extracted

The Rust crate's public interface is read from the JSON documentation that `rustdoc` writes
(`cargo +nightly rustdoc --lib -- -Z unstable-options --output-format json
--document-hidden-items` in `rust/`). Public are the items reachable from the crate root: the
public items of the public modules, the items that a `pub use` re-exports (a glob re-exports the
public items of its module), the public methods of the inherent implementations of the public
types, the methods of their trait implementations, and the methods of the public traits. Each is
named by the path of its definition without the crate, `lexer::SmtLexer::lex_slice` for the
method `lex_slice` of `SmtLexer`, defined in `lexer.rs`. Items hidden from the documentation
count: they are public.

Besides the items, the documentation gives three lists: the items that are only methods of trait
implementations (`lexer::SmtLexer::fmt`, of `impl Debug for SmtLexer`), which the trait's
implementation stands for; the trait implementations of the public types, each as the type's
path and the trait's path, with the crate's name for a trait of another crate
(`reader::SmtReadError` and `core::fmt::Debug`); and the public structures with private fields
(`span::SmtLocation`), which the documentation leaves out.

`extract` makes the lists from the documentation; `render` makes the generated module
`BSmtLib.Facts.RustItems` from them, which the executable `rust-items`
(`Tools/WriteRustItems.lean`, outside the audited modules, as two executables' roots in one
environment would both declare `main`) writes.

This module is a tool of the facts, not a part of any of them, and not trusted.
-/

namespace BSmtLib.Facts.RustApi

open Lean

/-- The definition path of the item `id`, without the crate, if the documentation has one. -/
def pathOf (paths : Json) (id : Nat) : Option String := do
  let entry ← (paths.getObjVal? (toString id)).toOption
  let crate ← (entry.getObjValAs? Nat "crate_id").toOption
  guard (crate == 0)
  let parts ← (entry.getObjValAs? (Array String) "path").toOption
  return "::".intercalate (parts.toList.drop 1)

/-- The path of the trait `id` of a trait implementation: without the crate for one of this
crate, with it for one of another crate. -/
def traitPathOf (paths : Json) (id : Nat) : Option String := do
  let entry ← (paths.getObjVal? (toString id)).toOption
  let crate ← (entry.getObjValAs? Nat "crate_id").toOption
  let parts ← (entry.getObjValAs? (Array String) "path").toOption
  let parts := if crate == 0 then parts.toList.drop 1 else parts.toList
  return "::".intercalate parts

/-- The kind of an item: the one key of its `inner` object. -/
def innerKind (item : Json) : Option (String × Json) := do
  let inner ← (item.getObjVal? "inner").toOption
  match inner with
  | .obj kvs => kvs.toArray.toList.head?.map fun ⟨k, v⟩ => (k, v)
  | _ => none

/-- The public items of the crate, as `extract` finds them. -/
structure Items where
  /-- The paths of the public items. -/
  items : Array String
  /-- The paths among `items` that only methods of trait implementations have. -/
  implMembers : Array String
  /-- The trait implementations of the public types: the type's path and the trait's. -/
  impls : Array (String × String)
  /-- The paths of the public structures with private fields. -/
  privateFields : Array String

/-- The state of the walk: the items visited and the names found. -/
structure Walk where
  visited : Std.HashSet Nat := {}
  names : Array String := #[]
  /-- The paths of the members of trait implementations. -/
  implMembers : Array String := #[]
  /-- The paths of the members of everything else. -/
  ownMembers : Array String := #[]
  impls : Array (String × String) := #[]
  privateFields : Array String := #[]

/-- The trait of an implementation `impl`, if it is a trait implementation that the walk
records: one that the compiler did not make and that is not a blanket implementation; with its
members, all of them for a trait implementation, the public ones for an inherent one. -/
def implMembers (index paths : Json) (impl : Json) : Option (Option String × Array String) :=
  Id.run do
  let some (kind, body) := innerKind impl | return none
  unless kind == "impl" do return none
  if (body.getObjValAs? Bool "is_synthetic").toOption == some true then return none
  if (body.getObjVal? "blanket_impl").toOption.any (· != .null) then return none
  let trait? := match (body.getObjVal? "trait").toOption with
    | some .null | none => none
    | some trait => some ((trait.getObjValAs? Nat "id").toOption.bind (traitPathOf paths)
        |>.getD "")
  let items := (body.getObjValAs? (Array Nat) "items").toOption.getD #[]
  let mut out := #[]
  for id in items do
    let some item := (index.getObjVal? (toString id)).toOption | continue
    let some name := (item.getObjValAs? String "name").toOption | continue
    let visibility := (item.getObjValAs? String "visibility").toOption.getD ""
    if trait?.isSome || visibility == "public" then out := out.push name
  return some (trait?, out)

/-- Whether the structure `body` has private fields, which the documentation leaves out. -/
def hasPrivateFields (body : Json) : Bool :=
  match (body.getObjVal? "kind").toOption with
  | some kind =>
    (kind.getObjVal? "plain" >>= (·.getObjValAs? Bool "has_stripped_fields")).toOption ==
        some true ||
      ((kind.getObjValAs? (Array Json) "tuple").toOption.getD #[]).any (· == .null)
  | none => false

/-- Visits the item `id`: records it and what it makes reachable, to the depth `fuel`. -/
def visit (index paths : Json) : (fuel : Nat) → (id : Nat) → Walk → Walk
  | 0, _, walk => walk
  | fuel + 1, id, walk => Id.run do
    if walk.visited.contains id then return walk
    let mut walk := { walk with visited := walk.visited.insert id }
    let some item := (index.getObjVal? (toString id)).toOption | return walk
    let some (kind, body) := innerKind item | return walk
    match kind with
    | "module" =>
      for child in (body.getObjValAs? (Array Nat) "items").toOption.getD #[] do
        let some c := (index.getObjVal? (toString child)).toOption | continue
        if (c.getObjValAs? String "visibility").toOption == some "public" then
          walk := visit index paths fuel child walk
      return walk
    | "use" =>
      match (body.getObjValAs? Nat "id").toOption with
      | some target => return visit index paths fuel target walk
      | none => return walk
    | _ =>
      let some path := pathOf paths id | return walk
      walk := { walk with names := walk.names.push path }
      if kind == "struct" && hasPrivateFields body then
        walk := { walk with privateFields := walk.privateFields.push path }
      let impls := (body.getObjValAs? (Array Nat) "impls").toOption.getD #[]
      for implId in impls do
        let some impl := (index.getObjVal? (toString implId)).toOption | continue
        let some (trait?, members) := implMembers index paths impl | continue
        if let some trait := trait? then
          walk := { walk with impls := walk.impls.push (path, trait) }
        for member in members do
          let p := s!"{path}::{member}"
          walk := { walk with names := walk.names.push p }
          if trait?.isSome then walk := { walk with implMembers := walk.implMembers.push p }
          else walk := { walk with ownMembers := walk.ownMembers.push p }
      if kind == "trait" then
        for member in (body.getObjValAs? (Array Nat) "items").toOption.getD #[] do
          let some m := (index.getObjVal? (toString member)).toOption | continue
          let some name := (m.getObjValAs? String "name").toOption | continue
          let p := s!"{path}::{name}"
          walk := { walk with names := walk.names.push p, ownMembers := walk.ownMembers.push p }
      return walk

/-- The strings sorted, without repetitions. -/
def sortedSet (names : Array String) : Array String :=
  (names.filter (· != "")).toList.eraseDups.toArray.qsort (· < ·)

/-- The public items of the crate whose documentation is `doc`, sorted. -/
def extract (doc : Json) : Except String Items := do
  let index ← doc.getObjVal? "index"
  let paths ← doc.getObjVal? "paths"
  let root ← doc.getObjValAs? Nat "root"
  -- every visit but a repeated one records an item, so the depth is at most their number
  let fuel := match index with | .obj kvs => kvs.size + 1 | _ => 1
  let walk := visit index paths fuel root {}
  let own : Std.HashSet String := (walk.names.filter (!walk.implMembers.contains ·) ++
    walk.ownMembers).foldl (·.insert ·) {}
  let implOnly := walk.implMembers.filter (!own.contains ·)
  let impls := (walk.impls.filter (·.2 != "")).toList.eraseDups.toArray.qsort
    fun a b => a.1 < b.1 || (a.1 == b.1 && a.2 < b.2)
  return Items.mk (sortedSet walk.names) (sortedSet implOnly) impls
    (sortedSet walk.privateFields)

/-- The lines of the definition `name` of an array of strings, documented by `doc`. -/
def renderArray (doc name type : String) (entries : Array String) : List String :=
  [s!"/-- {doc} -/", s!"def {name} : Array {type} := #["] ++
    if entries.isEmpty then ["]"] else
      entries.toList.mapIdx fun i n => s!"  {n}" ++ (if i + 1 == entries.size then "]" else ",")

/-- The generated module that lists `items`. -/
def render (items : Items) : String :=
  let header := ["module", "",
    "@[expose] public section", "",
    "/-!", "# The public items of the Rust crate",
    "",
    "Generated by `BSmtLib.Facts.RustApi.render` from the crate's JSON documentation; do not",
    "edit. Regenerate it with `lake exe rust-items <json>` in `lean/`, the JSON written by",
    "`cargo +nightly rustdoc --lib -- -Z unstable-options --output-format json",
    "--document-hidden-items` in `rust/`.",
    "-/", "",
    "namespace BSmtLib.Facts.RustItems", ""]
  let quote (s : String) := s!"\"{s}\""
  let body :=
    renderArray "The public items of the Rust crate, by the paths of their definitions." "items"
        "String" (items.items.map quote) ++ [""] ++
      renderArray "The items that only methods of trait implementations have." "implMembers"
        "String" (items.implMembers.map quote) ++ [""] ++
      renderArray "The trait implementations of the public types: the type and the trait."
        "impls" "(String × String)" (items.impls.map fun (t, tr) => s!"({quote t}, {quote tr})")
        ++ [""] ++
      renderArray "The public structures with private fields." "privateFields" "String"
        (items.privateFields.map quote)
  "\n".intercalate (header ++ body ++ ["", "end BSmtLib.Facts.RustItems"]) ++ "\n"

end BSmtLib.Facts.RustApi
