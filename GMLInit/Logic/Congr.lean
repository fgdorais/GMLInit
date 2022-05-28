import GMLInit.Logic.Basic

syntax (name:=congrs) "congrs" (term:max <|> hole <|> syntheticHole)+ : term
syntax (name:=congrArgs) "congrArgs" (term:max <|> hole <|> syntheticHole)+ : term
macro_rules
| `(congrs $t) => `($t)
| `(congrs $t $h $hs*) => `(congrs (congr $t $h) $hs*)
| `(congrArgs $t $hs*) => `(congrs (Eq.refl $t) $hs*)
