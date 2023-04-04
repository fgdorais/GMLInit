import GMLInit.Data.Equiv.Basic

namespace Sigma

def equivFst {α₁ α₂ : Type _} {β : α₁ → Type _} (e : Equiv α₁ α₂) : Equiv ((x₁ : α₁) × β x₁) ((x₂ : α₂) × β (e.rev x₂)) where
  fwd | ⟨x₁, y₁⟩ => ⟨e.fwd x₁, (e.rev_fwd x₁).symm ▸ y₁⟩
  rev | ⟨x₂, y₂⟩ => ⟨e.rev x₂, y₂⟩
  fwd_eq_iff_rev_eq := by intro
    | ⟨x₁, y₁⟩, ⟨x₂, y₂⟩ =>
      constr
      · intro
        | rfl =>
          apply Sigma.eq
          · exact e.rev_fwd ..
          · elim_casts
            reflexivity
      · intro
        | rfl =>
          apply Sigma.eq
          · exact e.fwd_rev ..
          · elim_casts
            reflexivity

def equivSnd {α : Type _} {β₁ : α → Type _} {β₂ : α → Type _} (e : (x : α) → Equiv (β₁ x) (β₂ x)) : Equiv ((x : α) × β₁ x) ((x : α) × β₂ x) where
  fwd | ⟨x, y₁⟩ => ⟨x, (e x).fwd y₁⟩
  rev | ⟨x, y₂⟩ => ⟨x, (e x).rev y₂⟩
  fwd_eq_iff_rev_eq := by intro
    | ⟨x₁, y₁⟩, ⟨x₂, y₂⟩ =>
      constr
      · intro
        | rfl =>
          apply Sigma.eq
          · reflexivity
          · apply heq_of_eq
            exact (e x₁).rev_fwd ..
      · intro
        | rfl =>
          apply Sigma.eq
          · reflexivity
          · apply heq_of_eq
            exact (e x₂).fwd_rev ..

protected def equiv {α₁ α₂ : Type _} {β₁ : α₁ → Type _} {β₂ : α₂ → Type _} (e : Equiv α₁ α₂) (f : (x : α₁) → Equiv (β₁ x) (β₂ (e.fwd x))) : Equiv ((x : α₁) × β₁ x) ((x : α₂) × β₂ x) :=
  Equiv.comp h3 (Equiv.comp h2 h1)
where
  h1 := equivFst e
  h2 := equivSnd fun x₂ => f (e.rev x₂)
  h3 := {
    fwd := fun ⟨x₁, y₁⟩ => ⟨x₁, (e.fwd_rev x₁).symm ▸ y₁⟩
    rev := fun ⟨x₂, y₂⟩ => ⟨x₂, (e.fwd_rev x₂).symm ▸ y₂⟩
    fwd_eq_iff_rev_eq := by intro
      | ⟨x₁, y₁⟩, ⟨x₂, y₂⟩ =>
        constr
        · intro
          | rfl =>
            apply Sigma.eq
            · reflexivity
            · elim_casts
              reflexivity
        · intro
          | rfl =>
            apply Sigma.eq
            · reflexivity
            · elim_casts
              reflexivity
  }

protected def equivProd (α β) : Equiv (α × β) (Sigma fun _ : α => β) where
  fwd | (x,y) => ⟨x,y⟩
  rev | ⟨x,y⟩ => (x,y)
  fwd_eq_iff_rev_eq := by intro | (x₁,y₁), ⟨x₂,y₂⟩ => constr <;> intro | rfl => rfl

end Sigma
