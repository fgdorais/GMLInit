import GMLInit.Logic.ListConnectives

syntax "constr_all" : tactic
macro_rules
| `(tactic| constr_all) => `(tactic| first | apply All.cons; rotate_left; constr_all | exact All.nil)
