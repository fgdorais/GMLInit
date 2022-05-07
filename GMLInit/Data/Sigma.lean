import GMLInit.Data.Basic
import GMLInit.Data.Equiv
import GMLInit.Meta.Basic

namespace Sigma

protected lemma eq {α} {β : α → Sort _} {x₁ x₂ : α} {y₁ : β x₁} {y₂ : β x₂} :
  (fst : x₁ = x₂) → (snd : y₁ ≅ y₂) → Sigma.mk x₁ y₁ = Sigma.mk x₂ y₂ := by
  intro h1 h2
  cases h1
  cases h2
  reflexivity

protected lemma eta {α} {β : α → Sort _} (p : Sigma β) : p = ⟨p.fst, p.snd⟩ := by
  cases p
  apply Sigma.eq
  · reflexivity
  · reflexivity using (.≅.)

variable {α₁} {β₁ : α₁ → Sort _} {α₂} {β₂ : α₂ → Sort _}

def equivFst {α₁ α₂} (β : α₁ → Sort _) (e : Equiv α₁ α₂) : Equiv ((x₁ : α₁) × β x₁) ((x₂ : α₂) × β (e.rev x₂)) where
  fwd | ⟨x₁, y₁⟩ => ⟨e.fwd x₁, (e.rev_fwd x₁).symm ▸ y₁⟩
  rev | ⟨x₂, y₂⟩ => ⟨e.rev x₂, y₂⟩
  spec := by intro
    | ⟨x₁, y₁⟩, ⟨x₂, y₂⟩ =>
      constr
      · intro h
        cases h
        apply Sigma.eq
        · exact e.rev_fwd x₁
        · elim_casts
          reflexivity using (.≅.)
      · intro h
        cases h
        apply Sigma.eq
        · exact e.fwd_rev x₂
        · elim_casts
          reflexivity using (.≅.)

def equivSnd {α} {β₁ : α → Sort _} {β₂ : α → Sort _} (e : (x : α) → Equiv (β₁ x) (β₂ x)) : Equiv ((x : α) × β₁ x) ((x : α) × β₂ x) where
  fwd | ⟨x, y₁⟩ => ⟨x, (e x).fwd y₁⟩
  rev | ⟨x, y₂⟩ => ⟨x, (e x).rev y₂⟩
  spec := by intro
    | ⟨x₁, y₁⟩, ⟨x₂, y₂⟩ =>
      constr
      · intro h
        cases h
        apply Sigma.eq
        · reflexivity
        · rw [(e x₁).rev_fwd]
          reflexivity using (.≅.)
      · intro h
        cases h
        apply Sigma.eq
        · reflexivity
        · rw [(e x₁).fwd_rev]
          reflexivity using (.≅.)

protected def equiv (e : Equiv α₁ α₂) (f : (x : α₁) → Equiv (β₁ x) (β₂ (e.fwd x))) : Equiv ((x : α₁) × β₁ x) ((x : α₂) × β₂ x) :=
  Equiv.comp h3 (Equiv.comp h2 h1) where
  h1 := equivFst β₁ e
  h2 := equivSnd (λ x₂ => f (e.rev x₂))
  h3 := {
    fwd := λ ⟨x₁, y₁⟩ => ⟨x₁, (e.fwd_rev x₁).symm ▸ y₁⟩
    rev := λ ⟨x₂, y₂⟩ => ⟨x₂, (e.fwd_rev x₂).symm ▸ y₂⟩
    spec := by intro
      | ⟨x₁, y₁⟩, ⟨x₂, y₂⟩ =>
        constr
        · intro h
          cases h
          apply Sigma.eq
          · reflexivity
          · elim_casts
            reflexivity using (.≅.)
        · intro h
          cases h
          apply Sigma.eq
          · reflexivity
          · elim_casts
            reflexivity using (.≅.)
  }

protected def equivProd (α β): Equiv (α × β) (Sigma (λ _ : α => β)) where
  fwd | (x,y) => ⟨x,y⟩
  rev | ⟨x,y⟩ => (x,y)
  spec := by intro
    | (x₁,y₁), ⟨x₂,y₂⟩ =>
      constr
      · intro h
        cases h
        rfl
      · intro h
        cases h
        rfl

end Sigma
