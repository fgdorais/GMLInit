import GMLInit.Logic.Decidable
import GMLInit.Meta.Basic

namespace Meta

syntax "truth_table" term:max* : tactic
macro_rules
| `(tactic|truth_table) => `(tactic|simp)
| `(tactic|truth_table $p:term $ps:term*) =>
  `(tactic|induction ($p : Prop) using Decidable.casesTFOn <;> truth_table $ps*)

-- From Mario Carneiro <https://leanprover.zulipchat.com/#narrow/stream/270676-lean4/topic/Improving.20this.20syntax/near/276313034>
macro "by_cases" ps:term,* "with" alts:Lean.Parser.Tactic.matchAlts : tactic =>
  `(tactic| match $[inferInstanceAs (Decidable $ps)],* with $alts:matchAlts)

end Meta
