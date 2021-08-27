import GMLInit.Logic.Relation

namespace Meta

syntax "calc" withPosition(calcStep+) : tactic
macro_rules
| `(tactic|calc $rest:calcStep*) => `(tactic|exact calc $rest*)

end Meta
