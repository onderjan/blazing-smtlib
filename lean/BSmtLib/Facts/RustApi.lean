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

`extract` makes the list from the documentation; `render` makes the generated module
`BSmtLib.Facts.RustItems` from it, which the executable `rust-items`
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

/-- The kind of an item: the one key of its `inner` object. -/
def innerKind (item : Json) : Option (String × Json) := do
  let inner ← (item.getObjVal? "inner").toOption
  match inner with
  | .obj kvs => kvs.toArray.toList.head?.map fun ⟨k, v⟩ => (k, v)
  | _ => none

/-- The state of the walk: the items visited and the names found. -/
structure Walk where
  visited : Std.HashSet Nat := {}
  names : Array String := #[]

/-- The members of an implementation `impl`: all its items for a trait implementation, its
public ones for an inherent one; none for an implementation that the compiler made. -/
def implMembers (index : Json) (impl : Json) : Array String := Id.run do
  let some (kind, body) := innerKind impl | return #[]
  unless kind == "impl" do return #[]
  if (body.getObjValAs? Bool "is_synthetic").toOption == some true then return #[]
  if (body.getObjVal? "blanket_impl").toOption.any (· != .null) then return #[]
  let isTrait := (body.getObjVal? "trait").toOption.any (· != .null)
  let items := (body.getObjValAs? (Array Nat) "items").toOption.getD #[]
  let mut out := #[]
  for id in items do
    let some item := (index.getObjVal? (toString id)).toOption | continue
    let some name := (item.getObjValAs? String "name").toOption | continue
    let visibility := (item.getObjValAs? String "visibility").toOption.getD ""
    if isTrait || visibility == "public" then out := out.push name
  return out

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
      let impls := (body.getObjValAs? (Array Nat) "impls").toOption.getD #[]
      for implId in impls do
        let some impl := (index.getObjVal? (toString implId)).toOption | continue
        for member in implMembers index impl do
          walk := { walk with names := walk.names.push s!"{path}::{member}" }
      if kind == "trait" then
        for member in (body.getObjValAs? (Array Nat) "items").toOption.getD #[] do
          let some m := (index.getObjVal? (toString member)).toOption | continue
          let some name := (m.getObjValAs? String "name").toOption | continue
          walk := { walk with names := walk.names.push s!"{path}::{name}" }
      return walk

/-- The public items of the crate whose documentation is `doc`, sorted. -/
def extract (doc : Json) : Except String (Array String) := do
  let index ← doc.getObjVal? "index"
  let paths ← doc.getObjVal? "paths"
  let root ← doc.getObjValAs? Nat "root"
  -- every visit but a repeated one records an item, so the depth is at most their number
  let fuel := match index with | .obj kvs => kvs.size + 1 | _ => 1
  let walk := visit index paths fuel root {}
  let names := walk.names.filter (· != "")
  return (names.toList.eraseDups.toArray).qsort (· < ·)

/-- The generated module that lists `names`. -/
def render (names : Array String) : String :=
  let header := #["module", "",
    "@[expose] public section", "",
    "/-!", "# The public items of the Rust crate",
    "",
    "Generated by `BSmtLib.Facts.RustApi.render` from the crate's JSON documentation; do not",
    "edit. Regenerate it with `lake exe rust-items <json>` in `lean/`, the JSON written by",
    "`cargo +nightly rustdoc --lib -- -Z unstable-options --output-format json",
    "--document-hidden-items` in `rust/`.",
    "-/", "",
    "namespace BSmtLib.Facts.RustItems", "",
    "/-- The public items of the Rust crate, by the paths of their definitions. -/",
    "def items : Array String := #["]
  let body := names.toList.mapIdx fun i n =>
    s!"  \"{n}\"" ++ (if i + 1 == names.size then "]" else ",")
  "\n".intercalate (header.toList ++ body ++ ["", "end BSmtLib.Facts.RustItems"]) ++ "\n"

end BSmtLib.Facts.RustApi
