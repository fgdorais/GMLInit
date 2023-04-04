import GMLInit.Data.Equiv.Basic

namespace Prod

def idLeftEquiv.{u} (β) : Equiv (PUnit.{u+1} × β) β where
  fwd := Prod.snd
  rev := (PUnit.unit, .)
  fwd_eq_iff_rev_eq := by intro | (PUnit.unit, b), b' => constr <;> intro | rfl => rfl

def idRightEquiv.{u} (α) : Equiv (α × PUnit.{u+1}) α where
  fwd := Prod.fst
  rev := (., PUnit.unit)
  fwd_eq_iff_rev_eq := by intro | (a, PUnit.unit), a' => constr <;> intro | rfl => rfl

def commEquiv (α β) : Equiv (α × β) (β × α) where
  fwd := swap
  rev := swap
  fwd_eq_iff_rev_eq := by intro | (a, b), (b', a') => constr <;> intro | rfl => rfl

def assocEquiv (α β γ) : Equiv ((α × β) × γ) (α × (β × γ)) where
  fwd | ((a, b), c) => (a, (b, c))
  rev | (a, (b, c)) => ((a, b), c)
  fwd_eq_iff_rev_eq := by intro | ((a, b), c), (a', (b', c')) => constr <;> intro | rfl => rfl

protected def equiv {α₁ α₂ β₁ β₂} (e : Equiv α₁ α₂) (f : Equiv β₁ β₂) : Equiv (α₁ × β₁) (α₂ × β₂) where
  fwd | (x₁, y₁) => (e.fwd x₁, f.fwd y₁)
  rev | (x₂, y₂) => (e.rev x₂, f.rev y₂)
  fwd_eq_iff_rev_eq := by intro
    | (x₁, y₁), (x₂,y₂) =>
      constr
      · intro | rfl => exact Prod.eq (e.rev_fwd x₁) (f.rev_fwd y₁)
      · intro | rfl => exact Prod.eq (e.fwd_rev x₂) (f.fwd_rev y₂)

end Prod
