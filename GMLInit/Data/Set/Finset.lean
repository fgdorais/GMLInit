import GMLInit.Data.Set.Basic
import GMLInit.Data.Set.Insert

set_option checkBinderAnnotations false in
class inductive Set.IsFinite : Set α → Prop
| protected empty : IsFinite Set.empty
| protected insert (s : Set α) [inst : IsFinite s] (a : α) : IsFinite (s.insert a)
attribute [instance] Set.IsFinite.empty Set.IsFinite.insert

namespace Set.IsFinite
open Set Set.Notation

protected instance pure (a : α) : IsFinite (Set.pure a) := by
  rw [←union_empty (Set.pure a)]
  infer_instance

protected instance union (s t : Set α) [hs : IsFinite s] [ht : IsFinite t] : IsFinite (s ∪ t) := by
  induction hs with
  | empty =>
    rw [empty_union]
    exact ht
  | insert s a H =>
    rw [insert_union_left]
    exact IsFinite.insert (inst:=H) (s ∪ t) a

protected instance map (f : α → β) (s : Set α) [hs : IsFinite s] : IsFinite (s.map f) := by
  induction hs with
  | empty =>
    rw [empty_map]
    exact IsFinite.empty
  | insert s a H =>
    rw [insert_map]
    exact IsFinite.insert (inst:=H) (s.map f) (f a)

protected instance bind (f : α → Set β) [hf : (x : α) → IsFinite (f x)] (s : Set α) [hs : IsFinite s] : IsFinite (s.bind f) := by
  induction hs with
  | empty =>
    rw [empty_bind]
    exact IsFinite.empty
  | insert s a H =>
    rw [insert_bind]
    exact IsFinite.union (ht:=H) (f a) (s.bind f)

protected instance seq (f : Set (α → β)) [hf : IsFinite f] (s : Set α) [hs : IsFinite s] : IsFinite (Set.seq f s) := by
  induction hs with
  | empty =>
    rw [empty_seq]
    exact IsFinite.empty
  | insert s a H =>
    rw [insert_seq]
    exact IsFinite.union (ht:=H) (f.map λ f => f a) (Set.seq f s)

protected instance seqLeft (s : Set α) [hs : IsFinite s] (t : Set β) [ht : IsFinite t] : IsFinite (Set.seqLeft s t) := by
  unfold Set.seqLeft
  infer_instance

protected instance seqRight (s : Set α) [hs : IsFinite s] (t : Set β) [ht : IsFinite t] : IsFinite (Set.seqRight s t) := by
  unfold Set.seqRight
  infer_instance

end Set.IsFinite

structure Finset (α) extends Set α where
  isFinite : toSet.IsFinite
attribute [instance] Finset.isFinite

instance (α) : CoeSort (Finset α) (Set α) := ⟨Finset.toSet⟩

protected theorem Finset.eq {α} : {s t : Finset α} → s.toSet = t.toSet → s = t
| ⟨_,_⟩, ⟨_,_⟩, rfl => rfl

protected theorem Finset.ext {α} {s t : Finset α} : (∀ x, s.Mem x ↔ t.Mem x) → s = t :=
  λ h => Finset.eq (Set.ext h)

instance : Monad Finset where
  pure a := ⟨pure a, Set.IsFinite.pure a⟩
  map f s := ⟨f <$> s.toSet, Set.IsFinite.map f s.toSet⟩
  bind s f := ⟨s.toSet >>= λ x => (f x).toSet, Set.IsFinite.bind (λ x => (f x).toSet) s.toSet⟩
  seq f s := ⟨f.toSet <*> (s ()).toSet, Set.IsFinite.seq f.toSet (s ()).toSet⟩
  seqLeft s t := ⟨s.toSet <* (t ()).toSet, Set.IsFinite.seqLeft s.toSet (t ()).toSet⟩
  seqRight s t := ⟨s.toSet *> (t ()).toSet, Set.IsFinite.seqRight s.toSet (t ()).toSet⟩

instance : LawfulMonad Finset where
  id_map := by
    intro _ ⟨_,_⟩
    apply Finset.eq
    unfold Functor.map
    rw [Set.id_map]
  comp_map := by
    intro _ _ _ f g ⟨_,_⟩
    apply Finset.eq
    unfold Functor.map
    rw [Set.comp_map]
  map_const := by intros; rfl
  map_pure f a := by
    apply Finset.eq
    unfold Functor.map Pure.pure
    rw [Set.map_pure]
  pure_bind := by
    intros
    apply Finset.eq
    unfold Bind.bind Pure.pure
    rw [Set.pure_bind]
  bind_assoc := by
    intros
    apply Finset.eq
    unfold Bind.bind
    rw [Set.bind_assoc]
  bind_pure_comp := by
    intros
    apply Finset.eq
    unfold Bind.bind Pure.pure Functor.map
    rw [Set.bind_pure_comp]
  bind_map := by
    intros
    apply Finset.eq
    unfold Bind.bind Functor.map Seq.seq
    rw [Set.bind_map]
  pure_seq f s := by
    intros
    apply Finset.eq
    unfold Seq.seq Pure.pure Functor.map
    rw [Set.pure_seq]
  seq_assoc := by
    intros
    apply Finset.eq
    unfold Seq.seq Functor.map
    rw [Set.seq_assoc]
  seqLeft_eq _ _ := rfl
  seqRight_eq _ _ := rfl
