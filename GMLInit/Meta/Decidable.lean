import GMLInit.Logic.Decidable
import GMLInit.Meta.Basic

namespace Meta

syntax (name := truth_table) "truth_table " (colGt term),+ : tactic
macro_rules
| `(tactic| truth_table $p:term) => `(tactic| induction ($p:term : Prop) using Decidable.casesTFOn <;> skip)
| `(tactic| truth_table $p:term,$ps:term,*) => `(tactic| induction ($p:term : Prop) using Decidable.casesTFOn <;> truth_table $ps,*)

-- Adapted from Mario Carneiro <https://leanprover.zulipchat.com/#narrow/stream/270676-lean4/topic/Improving.20this.20syntax/near/276313034>
syntax (name := by_cases) "by_cases " term,* ("using " ident)? "with " Lean.Parser.Tactic.matchAlts : tactic

set_option hygiene false in macro_rules
| `(tactic| by_cases $ps,* with $alts) =>
  `(tactic| match $[inferInstanceAs (Decidable ($ps : Prop))],* with $alts:matchAlts)
| `(tactic| by_cases $ps:term,* using Decidable with $alts) =>
  `(tactic| match $[inferInstanceAs (Decidable ($ps : Prop))],* with $alts:matchAlts)
| `(tactic| by_cases $ps:term,* using Complemented with $alts) =>
  `(tactic| match $[inferInstanceAs (Complemented ($ps : Prop))],* with $alts:matchAlts)
| `(tactic| by_cases $ps:term,* using WeaklyDecidable with $alts) =>
  `(tactic| match $[inferInstanceAs (WeaklyDecidable ($ps : Prop))],* with $alts:matchAlts)
| `(tactic| by_cases $ps:term,* using WeaklyComplemented with $alts) =>
  `(tactic| match $[inferInstanceAs (WeaklyComplemented ($ps : Prop))],* with $alts:matchAlts)

end Meta
