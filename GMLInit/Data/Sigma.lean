import GMLInit.Data.Basic
import GMLInit.Data.Equiv
import GMLInit.Meta.Basic

namespace Sigma

protected theorem eq {α} {β : α → Sort _} : {x₁ x₂ : Sigma β} → x₁.fst = x₂.fst → x₁.snd ≅ x₂.snd → x₁ = x₂
| ⟨_, _⟩, ⟨_, _⟩, rfl, .rfl => rfl

protected theorem eta {α} {β : α → Sort _} (p : Sigma β) : p = ⟨p.fst, p.snd⟩ := Sigma.eq rfl .rfl

variable {α₁} {β₁ : α₁ → Sort _} {α₂} {β₂ : α₂ → Sort _}

def equivFst {α₁ α₂} (β : α₁ → Sort _) (e : Equiv α₁ α₂) : Equiv ((x₁ : α₁) × β x₁) ((x₂ : α₂) × β (e.rev x₂)) where
  fwd | ⟨x₁, y₁⟩ => ⟨e.fwd x₁, (e.rev_fwd x₁).symm ▸ y₁⟩
  rev | ⟨x₂, y₂⟩ => ⟨e.rev x₂, y₂⟩
  spec := by intro
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

def equivSnd {α} {β₁ : α → Sort _} {β₂ : α → Sort _} (e : (x : α) → Equiv (β₁ x) (β₂ x)) : Equiv ((x : α) × β₁ x) ((x : α) × β₂ x) where
  fwd | ⟨x, y₁⟩ => ⟨x, (e x).fwd y₁⟩
  rev | ⟨x, y₂⟩ => ⟨x, (e x).rev y₂⟩
  spec := by intro
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

protected def equiv (e : Equiv α₁ α₂) (f : (x : α₁) → Equiv (β₁ x) (β₂ (e.fwd x))) : Equiv ((x : α₁) × β₁ x) ((x : α₂) × β₂ x) :=
  Equiv.comp h3 (Equiv.comp h2 h1)
where
  h1 := equivFst β₁ e
  h2 := equivSnd fun x₂ => f (e.rev x₂)
  h3 := {
    fwd := fun ⟨x₁, y₁⟩ => ⟨x₁, (e.fwd_rev x₁).symm ▸ y₁⟩
    rev := fun ⟨x₂, y₂⟩ => ⟨x₂, (e.fwd_rev x₂).symm ▸ y₂⟩
    spec := by intro
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

protected def equivProd (α β) : Equiv (α × β) (Sigma (fun _ : α => β)) where
  fwd | (x,y) => ⟨x,y⟩
  rev | ⟨x,y⟩ => (x,y)
  spec := by intro | (x₁,y₁), ⟨x₂,y₂⟩ => constr <;> intro | rfl => rfl

end Sigma
