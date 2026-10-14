module

public import BSmtLib.Nodes

public section

/-!
# Definitions

The definitions whose body is a term, by the call that ends them.
-/

namespace BSmtLib.Parser.Command.Definition

open BSmtLib.Nodes

/-- The definitions whose body is a term, by the call that ends them: `define-const` with its
name and its handled sort. -/
inductive DefinitionEnd (HandledSort : Type) where
  | defineConst (symbol : Symbol) (sort : HandledSort)
  | defineFun
  | defineFunRec

end BSmtLib.Parser.Command.Definition
