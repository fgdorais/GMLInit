import GMLInit.Data.Set.Basic

namespace Set
open Set.Notation

protected abbrev insert (s : Set α) (a : α) := Set.pure a ∪ s

protected abbrev insertIf (s : Set α) (a : α) (p : Prop) := Set.pureIf a p ∪ s

theorem mem_insert_iff_eq_or_mem (a : α) (s : Set α) : x ∈ s.insert a ↔ x = a ∨ x ∈ s := Iff.rfl

theorem mem_insertIf_iff_eq_and_cond_or_mem (a : α) (s : Set α) : x ∈ s.insertIf a p ↔ (x = a ∧ p) ∨ x ∈ s := Iff.rfl

theorem mem_insert_self (a : α) (s : Set α) : a ∈ s.insert a := Or.inl rfl

theorem mem_insertIf_self_of_cond (a : α) (s : Set α) {p : Prop} (h : p) : a ∈ s.insertIf a p := Or.inl ⟨rfl, h⟩

theorem mem_insert_of_mem (a : α) (s : Set α) : x ∈ s → x ∈ s.insert a := Or.inr

theorem mem_insertIf_of_mem (a : α) (s : Set α) {p : Prop} : x ∈ s → x ∈ s.insertIf a p := Or.inr

theorem insertIf_true_eq_insert (a : α) (s : Set α) : s.insertIf a True = s.insert a := by
  apply Set.ext
  intro x
  constr
  · intro
    | Or.inl ⟨_,_⟩ => left; assumption
    | Or.inr _ => right; assumption
  · intro
    | Or.inl _ => left; constr; assumption; trivial
    | Or.inr _ => right; assumption

theorem insert_idem (a : α) (s : Set α) : (s.insert a).insert a = s.insert a :=
  calc
  _ = (Set.pure a ∪ Set.pure a) ∪ s := by rw [union_assoc]
  _ = Set.pure a ∪ s := by rw [union_idem]

theorem insertIf_idem (a : α) (s : Set α) : (s.insertIf a p).insertIf a p = s.insertIf a p:= 
  calc
  _ = (Set.pureIf a p ∪ Set.pureIf a p) ∪ s := by rw [union_assoc]
  _ = Set.pureIf a p ∪ s := by rw [union_idem]

theorem insert_comm (a₁ a₂ : α) (s : Set α) : (s.insert a₁).insert a₂ = (s.insert a₂).insert a₁ :=
  calc
  _ = (Set.pure a₂ ∪ Set.pure a₁) ∪ s := by rw [union_assoc]
  _ = (Set.pure a₁ ∪ Set.pure a₂) ∪ s := by rw [union_comm (Set.pure a₁) (Set.pure a₂)]
  _ = Set.pure a₁ ∪ (Set.pure a₂ ∪ s) := by rw [union_assoc]

theorem insertIf_comm (a₁ a₂ : α) (s : Set α) : (s.insertIf a₁ p₁).insertIf a₂ p₂ = (s.insertIf a₂ p₂).insertIf a₁ p₁ :=
  calc
  _ = (Set.pureIf a₂ p₂ ∪ Set.pureIf a₁ p₁) ∪ s := by rw [union_assoc]
  _ = (Set.pureIf a₁ p₁ ∪ Set.pureIf a₂ p₂) ∪ s := by rw [union_comm (Set.pureIf a₁ p₁) (Set.pureIf a₂ p₂)]
  _ = Set.pureIf a₁ p₁ ∪ (Set.pureIf a₂ p₂ ∪ s) := by rw [union_assoc]

theorem insert_union_left (a : α) (s t : Set α) : s.insert a ∪ t = (s ∪ t).insert a :=
  calc
  _ = Set.pure a ∪ (s ∪ t) := by rw [union_assoc]

theorem insert_union_right (a : α) (s t : Set α) : s ∪ t.insert a = (s ∪ t).insert a :=
  calc
  _ = (s ∪ Set.pure a) ∪ t := by rw [union_assoc]
  _ = (Set.pure a ∪ s) ∪ t := by rw [union_comm (Set.pure a) s]
  _ = Set.pure a ∪ (s ∪ t) := by rw [union_assoc]

theorem insertIf_union_left (a : α) (s t : Set α) : s.insertIf a p ∪ t = (s ∪ t).insertIf a p :=
  calc
  _ = Set.pureIf a p ∪ (s ∪ t) := by rw [union_assoc]

theorem insertIf_union_right (a : α) (s t : Set α) : s ∪ t.insertIf a p = (s ∪ t).insertIf a p := 
  calc
  _ = (s ∪ Set.pureIf a p) ∪ t := by rw [union_assoc]
  _ = (Set.pureIf a p ∪ s) ∪ t := by rw [union_comm (Set.pureIf a p) s]
  _ = Set.pureIf a p ∪ (s ∪ t) := by rw [union_assoc]

theorem insert_inter_left (a : α) (s t : Set α) : s.insert a ∩ t = (s ∩ t).insertIf a (a ∈ t) := 
  calc
  _ = (Set.pure a ∩ t) ∪ (s ∩ t) := by rw [inter_distrib_right]
  _ = Set.pureIf a (a ∈ t) ∪ (s ∩ t) := by rw [pure_inter]

theorem insert_inter_right (a : α) (s t : Set α) : s ∩ t.insert a = (s ∩ t).insertIf a (a ∈ s) := 
  calc
  _ = (s ∩ Set.pure a) ∪ (s ∩ t) := by rw [inter_distrib_left]
  _ = Set.pureIf a (a ∈ s) ∪ (s ∩ t) := by rw [inter_pure]

theorem insertIf_inter_left (a : α) (p : Prop) (s t : Set α) : s.insertIf a p ∩ t = (s ∩ t).insertIf a (p ∧ a ∈ t) := 
  calc
  _ = (Set.pureIf a p ∩ t) ∪ (s ∩ t) := by rw [inter_distrib_right]
  _ = Set.pureIf a (p ∧ a ∈ t) ∪ (s ∩ t) := by rw [pureIf_inter]

theorem insertIf_inter_right (a : α) (p : Prop) (s t : Set α) : s ∩ t.insertIf a p = (s ∩ t).insertIf a (p ∧ a ∈ s) := 
  calc
  _ = (s ∩ Set.pureIf a p) ∪ (s ∩ t) := by rw [inter_distrib_left]
  _ = Set.pureIf a (p ∧ a ∈ s) ∪ (s ∩ t) := by rw [inter_pureIf]

theorem insert_map (f : α → β) (a : α) (s : Set α) : (s.insert a).map f = (s.map f).insert (f a) := 
  calc
  _ = (Set.pure a).map f ∪ s.map f := by rw [union_map]
  _ = Set.pure (f a) ∪ s.map f := by rw [Set.map_pure]

theorem insertIf_map (f : α → β) (a : α) (p : Prop) (s : Set α) : (s.insertIf a p).map f = (s.map f).insertIf (f a) p :=
  calc
  _ = (Set.pureIf a p).map f ∪ s.map f := by rw [union_map]
  _ = Set.pureIf (f a) p ∪ s.map f := by rw [Set.map_pureIf]

theorem insert_bind (f : α → Set β) (a : α) (s : Set α) : (s.insert a).bind f = f a ∪ s.bind f := 
  calc
  _ = (Set.pure a).bind f ∪ s.bind f := by rw [union_bind]
  _ = f a ∪ s.bind f := by rw [Set.pure_bind]

theorem insertIf_bind (f : α → Set β) (a : α) (p : Prop) (s : Set α) : (s.insertIf a p).bind f = (f a ∩ Set.const p) ∪ s.bind f := 
  calc
  _ = (Set.pureIf a p).bind f ∪ s.bind f := by rw [union_bind]
  _ = (f a ∩ Set.const p) ∪ s.bind f := by rw [Set.pureIf_bind]

theorem insert_join (s : Set (Set α)) (t : Set α) : (s.insert t).join = t ∪ s.join := insert_bind id t s

theorem insertIf_join (s : Set (Set α)) (t : Set α) (p : Prop) : (s.insertIf t p).join = (t ∩ Set.const p) ∪ s.join := insertIf_bind id t p s

theorem insert_seq (f : Set (α → β)) (a : α) (s : Set α) : Set.seq f (s.insert a) = f.map (λ f => f a) ∪ Set.seq f s := by
  unfold Set.seq
  apply Set.ext
  intro y
  constr
  · intro ⟨f,hf,h⟩
    clean at h
    rw [insert_map] at h
    match h with
    | Or.inl h => cases h; left; exists f
    | Or.inr ⟨x,hxs,h⟩ => cases h; right; exists f; constr; assumption; exists x
  · intro
    | Or.inl ⟨f,hf,h⟩ => cases h; exists f; constr; assumption; exists a; constr; left; rfl; rfl
    | Or.inr ⟨f,hf,x,hx,h⟩ => cases h; exists f; constr; assumption; exists x; constr; right; assumption; rfl

theorem insertIf_seq (f : Set (α → β)) (a : α) (p : Prop) (s : Set α) : Set.seq f (s.insertIf a p) = (f.map (λ f => f a) ∩ Set.const p) ∪ Set.seq f s := by
  unfold Set.seq
  apply Set.ext
  intro y
  constr
  · intro ⟨f,hf,h⟩
    clean at h
    rw [insertIf_map] at h
    match h with
    | Or.inl ⟨h, hp⟩ =>
      left
      constr
      · exists f
        constr
        · exact hf
        · exact h.symm
      · exact hp
    | Or.inr ⟨x,hxs,h⟩ =>
      right
      exists f
      constr
      · exact hf
      · exists x
  · intro
    | Or.inl ⟨⟨f,hf,h⟩,hp⟩ =>
      exists f
      constr
      · exact hf
      · exists a
        constr
        · left
          constr
          · rfl
          · exact hp
        · exact h
    | Or.inr ⟨f,hf,x,hx,h⟩ =>
      exists f
      constr
      · exact hf
      · exists x
        constr
        · right
          exact hx
        · exact h

end Set
