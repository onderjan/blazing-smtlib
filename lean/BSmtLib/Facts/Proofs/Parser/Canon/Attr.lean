module

public import Lean.Meta.Tactic.Simp.RegisterCommand
public meta import Lean.Meta.Tactic.Simp.Attr

public section

/-!
# The simp set of canonicalisation

`canon_simps` holds the lemmas that push `Canon.canon` through constructors and projections and
take it out of what depends on contents only.
-/

register_simp_attr canon_simps
