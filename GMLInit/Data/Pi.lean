import GMLInit.Data.Basic
import GMLInit.Data.Equiv
import GMLInit.Meta.Basic

namespace Function

def equiv {α₁ α₂ β₁ β₂} (e : Equiv α₁ α₂) (f : Equiv β₁ β₂) : Equiv (α₁ → β₁) (α₂ → β₂) where
  fwd h₁ := f.fwd ∘ h₁ ∘ e.rev
  rev h₂ := f.rev ∘ h₂ ∘ e.fwd
  spec := by
    intros
    constr
    · intro
      | rfl =>
        funext x₁
        unfold Function.comp
        rw [e.rev_fwd, f.rev_fwd]
    · intro
      | rfl =>
        funext x₂
        unfold Function.comp
        rw [e.fwd_rev, f.fwd_rev]

end Function

namespace Pi

def equivFst {α₁ α₂} (β : α₁ → Sort _) (e : Equiv α₁ α₂) : Equiv ((x₁ : α₁) → β x₁) ((x₂ : α₂) → β (e.rev x₂)) where
  fwd f₁ x₂ := f₁ (e.rev x₂)
  rev f₂ x₁ := e.rev_fwd x₁ ▸ f₂ (e.fwd x₁)
  spec := by
    intro f x
    constr
    · intro
      | rfl =>
        funext x₁
        apply eq_of_heq
        clean
        rw [e.rev_fwd x₁]
        reflexivity using (.≅.)
    · intro
      | rfl =>
        funext x₂
        apply eq_of_heq
        clean
        rw [e.fwd_rev x₂]
        reflexivity using (.≅.)

def equivSnd {α} {β₁ : α → Sort _} {β₂ : α → Sort _} (e : (x : α) → Equiv (β₁ x) (β₂ x)) : Equiv ((x : α) → β₁ x) ((x : α) → β₂ x) where
  fwd f₁ x := (e x).fwd (f₁ x)
  rev f₂ x := (e x).rev (f₂ x)
  spec := by
    intros
    constr
    · intro | rfl => funext x; exact (e x).rev_fwd ..
    · intro | rfl => funext x; exact (e x).fwd_rev ..

protected def equiv {α₁ α₂} {β₁ : α₁ → Sort _} {β₂ : α₂ → Sort _} (e : Equiv α₁ α₂) (f : (x₁ : α₁) → Equiv (β₁ x₁) (β₂ (e.fwd x₁))) : Equiv ((x₁ : α₁) → β₁ x₁) ((x₂ : α₂) → β₂ x₂) :=
  Equiv.comp h3 (Equiv.comp h2 h1) where
  h1 := equivFst β₁ e
  h2 := equivSnd (λ x₂ => f (e.rev x₂))
  h3 := {
    rev := λ m x => (e.fwd_rev x).symm ▸ m x
    fwd := λ n x => (e.fwd_rev x) ▸ n x
    spec := by
      intros
      constr <;> (intro | rfl => funext x; rw [eqNdrec_symm])
  }

end Pi
