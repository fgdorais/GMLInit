import GMLInit.Data.Set.Basic
import GMLInit.Logic.Relation

namespace Set
open Set.Notation
variable {s t u : Set α}

def Subset (s t : Set α) : Prop := ∀ x, x ∈ s → x ∈ t

theorem subset_refl (s : Set α) : s ⊆ s := by
  intro x hs
  exact hs
instance (α) : Relation.Reflexive (α:=Set α) (.⊆.) := ⟨subset_refl⟩

theorem subset_trans : s ⊆ t → t ⊆ u → s ⊆ u := by
  intro hst htu x hs
  apply htu
  apply hst
  exact hs
instance (α) : Relation.Transitive (α:=Set α) (.⊆.) := ⟨subset_trans⟩

theorem subset_antisymm : s ⊆ t → t ⊆ s → s = t := by
  intro hst hts
  apply Set.ext
  intro x
  constr
  · exact hst x
  · exact hts x
instance (α) : Relation.Antisymmetric (α:=Set α) (.⊆.) := ⟨subset_antisymm⟩

theorem empty_subset (s : Set α) : Set.empty ⊆ s := by
  intro x h
  contradiction

theorem eq_empty_of_subset_empty : s ⊆ Set.empty → s = Set.empty := by
  intro hs
  antisymmetry using (.⊆.)
  · exact hs
  · exact empty_subset s

theorem subset_univ (s : Set α) : s ⊆ Set.univ := by
  intro _ _
  trivial

theorem eq_univ_of_univ_subset : Set.univ ⊆ s → s = Set.univ := by
  intro hs
  antisymmetry using (.⊆.)
  · exact subset_univ s
  · exact hs

theorem pure_subset_of_mem {x : α} : x ∈ s → pure x ⊆ s := by
  intro | hs, _, rfl => exact hs

theorem subset_union_left (s t : Set α) : s ⊆ s ∪ t := by
  intro x hs
  left
  exact hs

theorem subset_union_right (s t : Set α) : t ⊆ s ∪ t := by
  intro x ht
  right
  exact ht

theorem union_subset_of_subset_of_subset : s ⊆ u → t ⊆ u → s ∪ t ⊆ u := by
  intro hsu htu x
  intro
  | Or.inl hxs =>
    exact hsu x hxs
  | Or.inr hxt =>
    exact htu x hxt

theorem union_subset_union_left : s ⊆ t → (∀ u, u ∪ s ⊆ u ∪ t) := by
  intro hst u x
  intro
  | Or.inl hu =>
    left
    exact hu
  | Or.inr hs =>
    right
    exact hst x hs

theorem union_subset_union_right : s ⊆ t → (∀ u, s ∪ u ⊆ t ∪ u) := by
  intro hst u x
  intro
  | Or.inl hs =>
    left
    exact hst x hs
  | Or.inr hu =>
    right
    exact hu

theorem union_subset_union {s₁ s₂ t₁ t₂ : Set α} : s₁ ⊆ s₂ → t₁ ⊆ t₂ → s₁ ∪ t₁ ⊆ s₂ ∪ t₂ := by
  intro hs ht x
  intro
  | Or.inl hs₁ =>
    left
    exact hs x hs₁
  | Or.inr ht₁ =>
    right
    exact ht x ht₁

theorem inter_subset_left (s t : Set α) : s ∩ t ⊆ s := by
  intro x ⟨hs,_⟩
  exact hs

theorem inter_subset_right (s t : Set α) : s ∩ t ⊆ t := by
  intro x ⟨_,ht⟩
  exact ht

theorem subset_inter_of_subset_of_subset : u ⊆ s → u ⊆ t → u ⊆ s ∩ t := by
  intro hus hut x hxu
  constr
  · exact hus x hxu
  · exact hut x hxu

theorem inter_subset_inter_left : s ⊆ t → (∀ u, u ∩ s ⊆ u ∩ t) := by
  intro hst u x ⟨hu, hs⟩
  constr
  · exact hu
  · exact hst x hs

theorem inter_subset_inter_right : s ⊆ t → (∀ u, s ∩ u ⊆ t ∩ u) := by
  intro hst u x ⟨hs, hu⟩
  constr
  · exact hst x hs
  · exact hu

theorem inter_subset_inter {s₁ s₂ t₁ t₂ : Set α} : s₁ ⊆ s₂ → t₁ ⊆ t₂ → s₁ ∩ t₁ ⊆ s₂ ∩ t₂ := by
  intro hs ht x ⟨hs₁,ht₁⟩
  constr
  · exact hs x hs₁
  · exact ht x ht₁

theorem map_subset_map (f : α → β) : s ⊆ t → f <$> s ⊆ f <$> t := by
  intro hst y ⟨x,hx,h⟩
  cases h
  exists x
  constr
  · exact hst x hx
  · rfl

theorem bind_subset_bind (f : α → Set β) : s ⊆ t → s >>= f ⊆ t >>= f := by
  intro hst y ⟨x,hx,h⟩
  exists x
  constr
  · exact hst x hx
  · exact h

theorem val_subset_bind (f : α → Set β) {x : α} : x ∈ s → f x ⊆ s >>= f := by
  intro hxs y hfxy
  exists x

theorem bind_subset_of_val_subset {t : Set β} {f : α → Set β} : (∀ x, x ∈ s → f x ⊆ t) → s >>= f ⊆ t := by
  intro h y ⟨x, hxs, hfxy⟩
  exact h x hxs y hfxy

end Set
