import GMLInit.Prelude
import Lean

/-- simp attribute for `elim_casts` tactic -/
register_simp_attr elim_casts

/-- simp attribute for `clean` tactic -/
register_simp_attr clean

-- could be a useful addition to Init/Prelude.lean
partial def Lean.Syntax.filter (stx : Syntax) (p : Syntax → Bool) : Array Syntax :=
  match stx with
  | stx@(Syntax.node _ _ args) =>
    let as := args.concatMap (λ stx => filter stx p)
    if p stx then as.push stx else as
  | stx => if p stx then #[stx] else #[]

-- could be a useful addition to Lean/Elab/Tactic/Location.lean
def Lean.Elab.Tactic.joinLocation : Location → Location → Location
| .wildcard, _ => .wildcard
| _, .wildcard => .wildcard
| .targets hs₁ g₁, .targets hs₂ g₂ => .targets (hs₁ ++ hs₂) (g₁ || g₂)

