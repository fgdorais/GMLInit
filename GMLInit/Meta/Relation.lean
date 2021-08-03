import GMLInit.Logic.Relation

syntax "reflexivity" ("using" term:max)? : tactic
macro_rules
| `(tactic|reflexivity) => `(tactic|apply Relation.Reflexive.rfl)
| `(tactic|reflexivity using $r:term) => `(tactic|apply Relation.Reflexive.rfl (r:=$r))

syntax "irreflexivity" ("using" term:max)? : tactic
macro_rules
| `(tactic|irreflexivity) => `(tactic|apply Relation.Irreflexive.irrfl)
| `(tactic|irreflexivity using $r:term) => `(tactic|apply Relation.Irreflexive.irrfl (r:=$r))

syntax "symmetry" ("using" term:max ("," term:max)?)? : tactic 
macro_rules
| `(tactic|symmetry) => `(tactic|first|apply Relation.HSymmetric.symm _)
| `(tactic|symmetry using $r) => `(tactic|apply Relation.Symmetric.symm (r:=$r) _)
| `(tactic|symmetry using $r, $s) => `(tactic|apply Relation.HSymmetric.symm (r:=$r) (s:=$s) _)

syntax "antisymmetry" "using" term:max ("," term:max)? : tactic
macro_rules
| `(tactic|antisymmetry using $r) => `(tactic|apply Relation.Antisymmetric.antisymm (r:=$r))
| `(tactic|antisymmetry using $r, $s) => `(tactic|apply Relation.HAntisymmetric.antisymm (r:=$r) (s:=$s))

syntax "transitivity" term:max ("using" term:max ("," term:max)?)? : tactic
macro_rules
| `(tactic|transitivity $y) => `(tactic|apply Relation.HTransitive.trans (y:=$y))
| `(tactic|transitivity $y using $r) => `(tactic|apply Relation.Transitive.trans (r:=$r) (y:=$y))
| `(tactic|transitivity $y using $r, $s) => `(tactic|apply Relation.HTransitive.trans (r:=$r) (s:=$s) (y:=$y))
