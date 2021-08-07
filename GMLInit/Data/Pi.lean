import GMLInit.Data.Basic
import GMLInit.Data.Equiv
import GMLInit.Logic.Eq
import GMLInit.Meta.Basic

namespace Function

def equiv {α₁ α₂ β₁ β₂} (e : Equiv α₁ α₂) (f : Equiv β₁ β₂) : Equiv (α₁ → β₁) (α₂ → β₂) where
  fwd h₁ := f.fwd ∘ h₁ ∘ e.rev
  rev h₂ := f.rev ∘ h₂ ∘ e.fwd
  spec h₁ h₂ := by
    split
    · intro H
      rw [←H]
      funext x₁
      unfold Function.comp
      rw [e.rev_fwd, f.rev_fwd]
    · intro H
      rw [←H]
      funext x₂
      unfold Function.comp
      rw [e.fwd_rev, f.fwd_rev]

end Function

namespace Pi

def equivFst {α₁ α₂} (β : α₁ → Sort _) (e : Equiv α₁ α₂) : Equiv ((x₁ : α₁) → β x₁) ((x₂ : α₂) → β (e.rev x₂)) where
  fwd f₁ x₂ := f₁ (e.rev x₂)
  rev f₂ x₁ := e.rev_fwd x₁ ▸ f₂ (e.fwd x₁)
  spec f₁ f₂ := by
    split
    · intro h
      cases h
      funext x₁
      apply dcast_eq_of_heq_of_eq
      clean
      rw [e.rev_fwd x₁]
      reflexivity using (.≅.)
    · intro h
      cases h
      funext x₂
      apply dcast_eq_of_heq_of_eq
      rw [e.fwd_rev x₂]
      reflexivity using (.≅.)

def equivSnd {α} {β₁ : α → Sort _} {β₂ : α → Sort _} (e : (x : α) → Equiv (β₁ x) (β₂ x)) : Equiv ((x : α) → β₁ x) ((x : α) → β₂ x) where
  fwd f₁ x := (e x).fwd (f₁ x)
  rev f₂ x := (e x).rev (f₂ x)
  spec f₁ f₂ := by
    split
    · intro h
      cases h
      funext x
      clean
      rw [(e x).rev_fwd]
    · intro h
      cases h
      funext x
      clean
      rw [(e x).fwd_rev]

protected def equiv {α₁ α₂} {β₁ : α₁ → Sort _} {β₂ : α₂ → Sort _} (e : Equiv α₁ α₂) (f : (x₁ : α₁) → Equiv (β₁ x₁) (β₂ (e.fwd x₁))) : Equiv ((x₁ : α₁) → β₁ x₁) ((x₂ : α₂) → β₂ x₂) :=
  Equiv.comp h3 (Equiv.comp h2 h1) where
  h1 := equivFst β₁ e
  h2 := equivSnd (λ x₂ => f (e.rev x₂))
  h3 := {
    rev := λ m x => (e.fwd_rev x).symm ▸ m x
    fwd := λ n x => (e.fwd_rev x) ▸ n x
    spec := λ m n => by
      split
      · intro h
        rw [←h]
        funext x
        simp only [dcast_trans]
        rw [dcast_refl]
      · intro h
        rw [←h]
        funext x
        simp only [dcast_trans]
        rw [dcast_refl]
  }

end Pi