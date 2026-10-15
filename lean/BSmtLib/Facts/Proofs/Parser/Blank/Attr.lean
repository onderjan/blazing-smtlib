module

public import Lean.Meta.Tactic.Simp.RegisterCommand
public meta import Lean.Meta.Tactic.Simp.Attr

public section

/-!
# The simp set of blanking

`blank_simps` holds the lemmas that push `Basic.Blanks.blank` through constructors, containers
and projections.
-/

register_simp_attr blank_simps
