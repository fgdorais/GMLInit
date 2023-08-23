import GMLInit.Logic.Basic

syntax (name:=congrs) "congrs" (term:max <|> hole <|> syntheticHole)+ : term
syntax (name:=congrArgs) "congrArgs" (term:max <|> hole <|> syntheticHole)+ : term
macro_rules
| `(congrs $t:term) => `($t)
| `(congrs $t:term $h:term $hs*) => `(congrs (congr $t $h) $hs*)
| `(congrArgs $t:term $hs*) => `(congrs (Eq.refl $t) $hs*)
