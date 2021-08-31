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
  spec | inr b, b' => ⟨λ h => congrArg inr h.symm, λ h => inr.inj h.symm⟩

def idRightEquiv (α) : Equiv (Sum α Empty) α where
  fwd | inl a => a
  rev := inl
  spec | inl a, a' => ⟨λ h => congrArg inl h.symm, λ h => inl.inj h.symm⟩

def commEquiv (α β) : Equiv (Sum α β) (Sum β α) where
  fwd := swap
  rev := swap
  spec
  | inl _, inl _ => by constr <;> (intro; contradiction)
  | inl a, inr a' => by constr <;> (intro h; injection h with h; rw [h]; rfl)
  | inr b, inl b' => by constr <;> (intro h; injection h with h; rw [h]; rfl)
  | inr _, inr _ => by constr <;> (intro; contradiction)

def assocEquiv (α β γ) : Equiv (Sum (Sum α β) γ) (Sum α (Sum β γ)) where
  fwd
  | inl (inl a) => inl a
  | inl (inr b) => inr (inl b)
  | inr c => inr (inr c)
  rev
  | inl a => inl (inl a)
  | inr (inl b) => inl (inr b)
  | inr (inr c) => inr c
  spec
  | inl (inl a), inl a' => by
    constr
    · intro h
      injection h with h
      rw [h]
    · intro h
      injection h with h
      injection h with h
      rw [h]
  | inl (inl a), inr (inl b') => by
    constr
    · intro
      contradiction
    · intro h
      injection h with h
      contradiction
  | inl (inl a), inr (inr c') => by
    constr
    · intro
      contradiction
    · intro
      contradiction
  | inl (inr b), inl a' => by
    constr
    · intro h
      contradiction
    · intro h
      injection h with h
      contradiction
  | inl (inr b), inr (inl b') => by
    constr
    · intro h
      injection h with h
      injection h with h
      rw [h]
    · intro h
      injection h with h
      injection h with h
      rw [h]
  | inl (inr b), inr (inr c') => by
    constr
    · intro h
      injection h with h
      contradiction
    · intro
      contradiction
  | inr c, inl a' => by
    constr
    · intro
      contradiction
    · intro
      contradiction
  | inr c, inr (inl b') => by
    constr
    · intro h
      injection h with h
      contradiction
    · intro
      contradiction
  | inr c, inr (inr c') => by
    constr
    · intro h
      injection h with h
      injection h with h
      rw [h]
    · intro h
      injection h with h
      rw [h]

protected def equiv {α₁ α₂ β₁ β₂} (e : Equiv α₁ α₂) (f : Equiv β₁ β₂) : Equiv (Sum α₁ β₁) (Sum α₂ β₂) where
  fwd
  | Sum.inl a₁ => Sum.inl (e.fwd a₁)
  | Sum.inr b₁ => Sum.inr (f.fwd b₁)
  rev
  | Sum.inl a₂ => Sum.inl (e.rev a₂)
  | Sum.inr b₂ => Sum.inr (f.rev b₂)
  spec
  | Sum.inl a₁, Sum.inl a₂ => by
    constr
    · intro h
      injection h
      apply congrArg Sum.inl
      rw [←e.spec]
      assumption
    · intro h
      injection h
      apply congrArg Sum.inl
      rw [e.spec]
      assumption
  | Sum.inl a₁, Sum.inr b₂ => by constr <;> (intro; contradiction)
  | Sum.inr b₁, Sum.inl a₂ => by constr <;> (intro; contradiction)
  | Sum.inr b₁, Sum.inr b₂ => by
    constr
    · intro h
      injection h
      apply congrArg Sum.inr
      rw [←f.spec]
      assumption
    · intro h
      injection h
      apply congrArg Sum.inr
      rw [f.spec]
      assumption

end Sum
