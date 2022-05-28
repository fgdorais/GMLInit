import GMLInit.Data.Basic
import GMLInit.Data.Equiv
import GMLInit.Meta.Basic

namespace Prod

protected def eq {α β} : {p q : α × β} → (fst : p.fst = q.fst) → (snd : p.snd = q.snd) → p = q
| (_,_), (_,_), rfl, rfl => rfl

protected def eta {α β} : (p : α × β) → p = (p.fst, p.snd)
| (_,_) => rfl

def swap {α β} : α × β → β × α
| (a, b) => (b, a)

def idLeftEquiv (β) : Equiv (PUnit × β) β where
  fwd := snd
  rev := ((),.)
  spec := by intro | ((), b), b' => constr <;> intro | rfl => rfl

def idRightEquiv (α) : Equiv (α × PUnit) α where
  fwd := fst
  rev := (.,())
  spec := by intro | (a,()), a' => constr <;> intro | rfl => rfl

def commEquiv (α β) : Equiv (α × β) (β × α) where
  fwd := swap
  rev := swap
  spec := by intro | (a, b), (b', a') => constr <;> intro | rfl => rfl

def assocEquiv (α β γ) : Equiv ((α × β) × γ) (α × (β × γ)) where
  fwd | ((a, b), c) => (a, (b, c))
  rev | (a, (b, c)) => ((a, b), c)
  spec := by intro | ((a, b), c), (a', (b', c')) => constr <;> intro | rfl => rfl

protected def equiv {α₁ α₂ β₁ β₂} (e : Equiv α₁ α₂) (f : Equiv β₁ β₂) : Equiv (α₁ × β₁) (α₂ × β₂) where
  fwd | (x₁, y₁) => (e.fwd x₁, f.fwd y₁)
  rev | (x₂, y₂) => (e.rev x₂, f.rev y₂)
  spec := by intro
    | (x₁, y₁), (x₂,y₂) =>
      constr
      · intro | rfl => exact Prod.eq (e.rev_fwd x₁) (f.rev_fwd y₁)
      · intro | rfl => exact Prod.eq (e.fwd_rev x₂) (f.fwd_rev y₂)

end Prod
