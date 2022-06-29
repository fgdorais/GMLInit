import GMLInit.Logic.Stable
import GMLInit.Meta.Basic

namespace Meta

syntax "by_contradiction" withPosition(colGe ("|" "assuming" (ident <|> "_") "=>" tacticSeq)) : tactic
macro_rules
| `(tactic|by_contradiction | assuming $h => $rest) =>
  `(tactic|apply Stable.by_contradiction _; intro $h:ident; ($rest))

syntax "by_contrapositive" ("with" term)? : tactic
macro_rules
| `(tactic|by_contrapositive) =>
  `(tactic|exact Stable.by_contrapositive _)
| `(tactic|by_contrapositive with $t) =>
  `(tactic|apply Stable.by_contrapositive _ $t)

syntax "by_no_counterexample" term:51 " = " ident withPosition(colGe ("|" "assuming" (ident <|> "_") "=>" tacticSeq)) : tactic
macro_rules
| `(tactic|by_no_counterexample $t:term = $x:ident | assuming $h => $rest) =>
  `(tactic|apply Stable.by_no_counterexample _ $t; intro ⟨$x,$h⟩; ($rest))

end Meta
