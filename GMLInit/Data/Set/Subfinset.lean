import GMLInit.Data.Set.Basic
import GMLInit.Data.Set.Insert

set_option checkBinderAnnotations false in
class inductive Set.IsSubfinite : Set α → Prop
| protected empty : IsSubfinite Set.empty
| protected insertIf (s : Set α) [inst : IsSubfinite s] (a : α) (p : Prop := True) : IsSubfinite (s.insertIf a p)
attribute [instance] Set.IsSubfinite.empty Set.IsSubfinite.insertIf

namespace Set.IsSubfinite
open Set Set.Notation

protected instance pure (x : α) : IsSubfinite (Set.pure x) := by
  have : Set.pure x = Set.empty.insertIf x True := by
    apply Set.ext
    intro x
    constr
    · intro h
      cases h
      left
      constr
      · rfl
      · trivial
    · intro
      | Or.inl ⟨h,_⟩ => cases h; rfl
      | Or.inr h => contradiction
  rw [this]
  infer_instance

protected instance union (s t : Set α) [hs : IsSubfinite s] [ht : IsSubfinite t] : IsSubfinite (Set.union s t) := by
  induction hs with
  | empty =>
    rw [empty_union]
    exact ht
  | insertIf s a p H =>
    rw [insertIf_union_left]
    exact IsSubfinite.insertIf (inst:=H) (p := p) ..

protected instance inter_left (s t : Set α) [hs : IsSubfinite s] : IsSubfinite (Set.inter s t) := by
  induction hs with
  | empty =>
    rw [empty_inter]
    exact IsSubfinite.empty
  | insertIf s a p H =>
    rw [insertIf_inter_left]
    exact IsSubfinite.insertIf (inst:=H) (p := p ∧ a ∈ t) ..

protected instance inter_right (s t : Set α) [ht : IsSubfinite t] : IsSubfinite (Set.inter s t) := by
  induction ht with
  | empty =>
    rw [inter_empty]
    exact IsSubfinite.empty
  | insertIf t a p H =>
    rw [insertIf_inter_right]
    exact IsSubfinite.insertIf (inst:=H) (p := p ∧ a ∈ s) ..

protected instance map (f : α → β) (s : Set α) [hs : IsSubfinite s] : IsSubfinite (s.map f) := by
  induction hs with
  | empty =>
    rw [empty_map]
    exact IsSubfinite.empty
  | insertIf s a p H =>
    rw [insertIf_map]
    exact IsSubfinite.insertIf (inst:=H) (p := p) ..

protected instance bind (f : α → Set β) [hf : (x : α) → IsSubfinite (f x)] (s : Set α) [hs : IsSubfinite s] : IsSubfinite (s.bind f) := by
  induction hs with
  | empty =>
    rw [empty_bind]
    exact IsSubfinite.empty
  | insertIf s a p H =>
    rw [insertIf_bind]
    exact IsSubfinite.union (ht:=H) ..

protected instance seq (f : Set (α → β)) [hf : IsSubfinite f] (s : Set α) [hs : IsSubfinite s] : IsSubfinite (Set.seq f s) := by
  induction hs with
  | empty =>
    rw [empty_seq]
    exact IsSubfinite.empty
  | insertIf s a p H =>
    rw [insertIf_seq]
    exact IsSubfinite.union (ht:=H) ..

protected instance seqLeft (s : Set α) [hs : IsSubfinite s] (t : Set β) [ht : IsSubfinite t] : IsSubfinite (Set.seqLeft s t) := by
  clean unfold Set.seqLeft
  infer_instance

protected instance seqRight (s : Set α) [hs : IsSubfinite s] (t : Set β) [ht : IsSubfinite t] : IsSubfinite (Set.seqRight s t) := by
  clean unfold Set.seqRight
  infer_instance

end Set.IsSubfinite

structure Subfinset (α) extends Set α where
  isSubfinite : toSet.IsSubfinite
attribute [instance] Subfinset.isSubfinite

instance (α) : CoeSort (Subfinset α) (Set α) := ⟨Subfinset.toSet⟩

protected theorem Subfinset.eq {α} : {s t : Subfinset α} → s.toSet = t.toSet → s = t
| ⟨_,_⟩, ⟨_,_⟩, rfl => rfl

protected theorem Subfinset.ext {α} {s t : Subfinset α} : (∀ x, s.Mem x ↔ t.Mem x) → s = t :=
  λ h => Subfinset.eq (Set.ext h)

instance : Monad Subfinset where
  pure a := ⟨pure a, Set.IsSubfinite.pure a⟩
  map f s := ⟨f <$> s.toSet, Set.IsSubfinite.map f s.toSet⟩
  bind s f := ⟨s.toSet >>= λ x => (f x).toSet, Set.IsSubfinite.bind (λ x => (f x).toSet) s.toSet⟩
  seq f s := ⟨f.toSet <*> (s ()).toSet, Set.IsSubfinite.seq f.toSet (s ()).toSet⟩
  seqLeft s t := ⟨s.toSet <* (t ()).toSet, Set.IsSubfinite.seqLeft s.toSet (t ()).toSet⟩
  seqRight s t := ⟨s.toSet *> (t ()).toSet, Set.IsSubfinite.seqRight s.toSet (t ()).toSet⟩

instance : LawfulMonad Subfinset where
  id_map := by
    intro _ ⟨_,_⟩
    apply Subfinset.eq
    simp only [Functor.map, Set.id_map]
  comp_map := by
    intro _ _ _ f g ⟨_,_⟩
    apply Subfinset.eq
    simp only [Functor.map, Set.comp_map]
  map_const := by intros; rfl
  map_pure f a := by
    apply Subfinset.eq
    simp only [Functor.map, Pure.pure, Set.map_pure]
  pure_bind := by
    intros
    apply Subfinset.eq
    simp only [Bind.bind, Pure.pure, Set.pure_bind]
  bind_assoc := by
    intros
    apply Subfinset.eq
    simp only [Bind.bind, Set.bind_assoc]
  bind_pure_comp := by
    intros
    apply Subfinset.eq
    simp only [Bind.bind, Pure.pure, Functor.map, Set.bind_pure_comp]
  bind_map := by
    intros
    apply Subfinset.eq
    simp only [Bind.bind, Functor.map, Seq.seq, Set.bind_map]
  pure_seq f s := by
    intros
    apply Subfinset.eq
    simp only [Seq.seq, Pure.pure, Functor.map, Set.pure_seq]
  seq_assoc := by
    intros
    apply Subfinset.eq
    simp only [Seq.seq, Functor.map, Set.seq_assoc]
  seqLeft_eq _ _ := rfl
  seqRight_eq _ _ := rfl
