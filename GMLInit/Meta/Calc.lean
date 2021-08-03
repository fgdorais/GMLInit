import GMLInit.Logic.Relation

namespace Meta

syntax calcStep := colGe term ":=" term

syntax "calc" withPosition(calcStep+) : term
macro_rules
| `(calc $p:term := $h:term) => `(($h : $p))
| `(calc $p:term := $h:term $rest:calcStep*) => `(Relation.HTransitive.trans ($h : $p) (calc $rest:calcStep*))

syntax "calc" withPosition(calcStep+) : tactic
macro_rules
| `(tactic|calc $rest:calcStep*) => `(tactic|exact calc $rest*)

end Meta
