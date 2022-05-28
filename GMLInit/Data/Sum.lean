import GMLInit.Data.Basic
import GMLInit.Data.Equiv
import GMLInit.Meta.Basic

namespace Sum

def swap {α β} : Sum α β → Sum β α
| inl a => inr a
| inr b => inl b

def idLeftEquiv (β) : Equiv (Sum Empty β) β where
  fwd | inr b => b
  rev := inr
  spec := by intro | inr b, b' => constr <;> intro | rfl => rfl

def idRightEquiv (α) : Equiv (Sum α Empty) α where
  fwd | inl a => a
  rev := inl
  spec := by intro | inl a, a' => constr <;> intro | rfl => rfl

def commEquiv (α β) : Equiv (Sum α β) (Sum β α) where
  fwd := swap
  rev := swap
  spec := by intro
    | inl _, inl _ => constr <;> (intro h; cases h)
    | inl a, inr a' => constr <;> intro | rfl => rfl
    | inr b, inl b' => constr <;> intro | rfl => rfl
    | inr _, inr _ => constr <;> (intro h; cases h)

def assocEquiv (α β γ) : Equiv (Sum (Sum α β) γ) (Sum α (Sum β γ)) where
  fwd
  | inl (inl a) => inl a
  | inl (inr b) => inr (inl b)
  | inr c => inr (inr c)
  rev
  | inl a => inl (inl a)
  | inr (inl b) => inl (inr b)
  | inr (inr c) => inr c
  spec := by intro
    | inl (inl a), inl a' => constr <;> intro | rfl => rfl
    | inl (inl a), inr (inl b') => constr <;> (intro h; cases h)
    | inl (inl a), inr (inr c') => constr <;> (intro h; cases h)
    | inl (inr b), inl a' => constr <;> (intro h; cases h)
    | inl (inr b), inr (inl b') => constr <;> intro | rfl => rfl
    | inl (inr b), inr (inr c') => constr <;> (intro h; cases h)
    | inr c, inl a' => constr <;> (intro h; cases h)
    | inr c, inr (inl b') => constr <;> (intro h; cases h)
    | inr c, inr (inr c') => constr <;> intro | rfl => rfl

protected def equiv {α₁ α₂ β₁ β₂} (e : Equiv α₁ α₂) (f : Equiv β₁ β₂) : Equiv (Sum α₁ β₁) (Sum α₂ β₂) where
  fwd
  | Sum.inl a₁ => Sum.inl (e.fwd a₁)
  | Sum.inr b₁ => Sum.inr (f.fwd b₁)
  rev
  | Sum.inl a₂ => Sum.inl (e.rev a₂)
  | Sum.inr b₂ => Sum.inr (f.rev b₂)
  spec := by intro
    | Sum.inl a₁, Sum.inl a₂ =>
      constr
      · intro | rfl => clean; rw [e.rev_fwd]
      · intro | rfl => clean; rw [e.fwd_rev]
    | Sum.inl a₁, Sum.inr b₂ => constr <;> (intro; contradiction)
    | Sum.inr b₁, Sum.inl a₂ => constr <;> (intro; contradiction)
    | Sum.inr b₁, Sum.inr b₂ =>
      constr
      · intro | rfl => clean; rw [f.rev_fwd]
      · intro | rfl => clean; rw [f.fwd_rev]

end Sum
