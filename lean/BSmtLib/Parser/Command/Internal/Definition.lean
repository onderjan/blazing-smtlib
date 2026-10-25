module

public import BSmtLib.Grammar.Nodes

public section

/-!
# Definitions

The definitions whose body is a term, by the call that ends them.
-/

namespace BSmtLib.Parser.Command.Internal.Definition

open BSmtLib.Lexicon.Value (Symbol)
open BSmtLib.Grammar.Nodes

/-- The definitions whose body is a term, by the call that ends them: `define-const` with its
name and its handled sort. -/
inductive DefinitionEnd (HandledSort : Type) where
  | defineConst (symbol : Symbol) (sort : HandledSort)
  | defineFun
  | defineFunRec

end BSmtLib.Parser.Command.Internal.Definition
