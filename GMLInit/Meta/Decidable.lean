import GMLInit.Class.DecLift
import GMLInit.Meta.Basic

namespace Meta
open Lean.Parser.Tactic (location)

syntax (name := truth_table) "truth_table " (colGt term),+ : tactic
macro_rules
| `(tactic| truth_table $p:term) => `(tactic| induction ($p:term : Prop) using Decidable.casesTFOn <;> skip)
| `(tactic| truth_table $p:term,$ps:term,*) => `(tactic| induction ($p:term : Prop) using Decidable.casesTFOn <;> truth_table $ps,*)

syntax "dec_lift_hyp" ident* : tactic
macro_rules
| `(tactic| dec_lift_hyp $h:ident $hs:ident*) =>
  `(tactic| have htmp := iff_of_dec_lift_eq_dec_lift $h; try clear $h; have $h := htmp; clear htmp; dec_lift_hyp $hs:ident*)
| `(tactic| dec_lift_hyp) => `(tactic| skip)

syntax (name := dec_lift) "dec_lift" (location)? : tactic
macro_rules
| `(tactic| dec_lift at $ids:ident* ⊢) =>
  `(tactic| dec_lift at $ids:ident*; dec_lift)
| `(tactic| dec_lift at $ids:ident*) =>
  `(tactic| dec_lift_hyp $ids:ident*; simp only [DecLift.toProp, iff_true, true_iff, iff_false, false_iff] at $ids:ident*)
| `(tactic| dec_lift) => `(tactic| apply dec_lift_eq_dec_lift_of_iff; simp only [DecLift.toProp, iff_true, true_iff, iff_false, false_iff])

end Meta
