import GMLInit.Logic.Decidable
import GMLInit.Meta.Basic

namespace Meta

syntax "truth_table" term:max* : tactic
macro_rules
| `(tactic|truth_table) => `(tactic|simp)
| `(tactic|truth_table $p:term $ps:term*) =>
  `(tactic|induction ($p : Prop) using Decidable.casesTFOn <;> truth_table $ps*)

syntax by_cases_true := "|" &"isTrue" (ident <|> "_") "=>" (hole <|> syntheticHole <|> tacticSeq)
syntax by_cases_false := "|" &"isFalse" (ident <|> "_") "=>" (hole <|> syntheticHole <|> tacticSeq)
syntax "by_cases" term "with" withPosition((colGe by_cases_true) (colGe by_cases_false)) : tactic
macro_rules
| `(tactic|by_cases $p with | isTrue $ht => $tt | isFalse $hf => $tf) =>
  `(tactic|match inferInstanceAs (Decidable $p) with | Decidable.isTrue $ht => $tt | Decidable.isFalse $hf => $tf)

end Meta
