module

public meta import BSmtLib.Facts.RustApi
-- Lean for the run too: a module imported with `meta` alone is not initialized when the
-- executable runs
import Lean

/-!
# Writing the public items of the Rust crate

The executable `rust-items`: `lake exe rust-items <json>`, run in the package's directory, writes
the generated module `BSmtLib.Facts.RustItems` (`BSmtLib/Facts/RustItems.lean`) from the
crate's JSON documentation `<json>`, by `BSmtLib.Facts.RustApi.extract`.
-/

open Lean BSmtLib.Facts.RustApi

/-- Writes the generated module from the documentation named by the one argument. -/
public meta def main (args : List String) : IO UInt32 := do
  let [json] := args | IO.eprintln "usage: rust-items <rustdoc json>"; return 2
  let doc ← IO.ofExcept (Json.parse (← IO.FS.readFile json))
  let items ← IO.ofExcept (extract doc)
  -- a literal: a computed constant of a module imported with `meta` alone is not initialized
  IO.FS.writeFile "BSmtLib/Facts/RustItems.lean" (render items)
  IO.println s!"wrote BSmtLib/Facts/RustItems.lean, {items.items.size} items, \
    {items.impls.size} trait implementations, {items.privateFields.size} structures with private \
    fields"
  return 0
