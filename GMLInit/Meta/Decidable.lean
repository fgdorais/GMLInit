import GMLInit.Logic.Decidable
import GMLInit.Meta.Basic

namespace Meta

syntax (name := truth_table) "truth_table" (colGt term),+ : tactic
macro_rules
| `(tactic| truth_table $p:term) => `(tactic| induction ($p:term : Prop) using Decidable.casesTFOn <;> skip)
| `(tactic| truth_table $p:term,$ps:term,*) => `(tactic| induction ($p:term : Prop) using Decidable.casesTFOn <;> truth_table $ps,*)

-- From Mario Carneiro <https://leanprover.zulipchat.com/#narrow/stream/270676-lean4/topic/Improving.20this.20syntax/near/276313034>
macro "by_cases" ps:term,* "with" alts:Lean.Parser.Tactic.matchAlts : tactic =>
  `(tactic| match $[inferInstanceAs (Decidable $ps)],* with $alts:matchAlts)

end Meta
