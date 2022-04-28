import GMLInit.Data.Basic
import GMLInit.Meta.Basic
import GMLInit.Meta.Relation

structure Set.{u} (α : Sort u) where
  protected Mem : α → Prop

namespace Set
variable {α β γ}

namespace Notation
set_option hygiene false
scoped notation x:50 " ∈ " s:51 => Set.Mem s x
scoped infix:50 " ⊆ " => Set.Subset
scoped infixr:55 " ∪ " => Set.union
scoped infixr:60 " ∩ " => Set.inter
end Notation
open Notation

protected def eq : {s t : Set α} → s.Mem = t.Mem → s = t
| ⟨_⟩, ⟨_⟩, rfl => rfl

protected def ext {s t : Set α} : (∀ x, s.Mem x ↔ t.Mem x) → s = t :=
  λ h => Set.eq (funext λ x => propext (h x))

protected def const (p : Prop) : Set α where
  Mem _ := p

protected def empty : Set α :=
  Set.const False

protected def univ : Set α :=
  Set.const True

protected def pure (a : α) : Set α where
  Mem x := x = a

protected def pureIf (a : α) (p : Prop) : Set α where
  Mem x := x = a ∧ p

protected def complement (s : Set α) : Set α where
  Mem x := ¬ x ∈ s

protected def union (s t : Set α) : Set α where
  Mem x := x ∈ s ∨ x ∈ t

protected def inter (s t : Set α) : Set α where
  Mem x := x ∈ s ∧ x ∈ t

protected def inv (f : α → β) (s : Set β) : Set α where
  Mem x := f x ∈ s

protected def map (f : α → β) (s : Set α) : Set β where
  Mem y := ∃ x, x ∈ s ∧ f x = y

protected def bind (s : Set α) (f : α → Set β) : Set β where
  Mem y := ∃ x, x ∈ s ∧ y ∈ f x

protected def join (s : Set (Set α)) : Set α :=
  s.bind id

protected def seq (f : Set (α → β)) (s : Set α) : Set β :=
  f.bind s.map

protected def seqLeft (s : Set α) (t : Set β) : Set α := Set.seq (s.map λ x _ => x) t

protected def seqRight (s : Set α) (t : Set β) : Set β := Set.seq (s.map λ _ y => y) t

protected theorem id_map (s : Set α) : s.map id = s := by
  apply Set.ext
  intro x
  constr
  · intro ⟨_, hx, rfl⟩
    exact hx
  · intro hx
    refine ⟨x, hx, rfl⟩

protected theorem comp_map (f : α → β) (g : β → γ) (s : Set α) : s.map (g ∘ f) = (s.map f).map g := by
  apply Set.ext
  intro z
  constr
  · intro ⟨x, hx, hxz⟩
    refine ⟨f x, ⟨x, hx, rfl⟩, hxz⟩
  · intro ⟨y, ⟨x, hx, hxy⟩, hyz⟩
    refine ⟨x, hx, ?_⟩
    rw [←hyz, ←hxy, Function.comp_apply]

protected theorem map_pure (f : α → β) (a : α) : (Set.pure a).map f = Set.pure (f a) := by
  apply Set.ext
  intro y
  constr
  · intro ⟨_, rfl, h⟩
    rw [←h]
    rfl
  · intro (h : y = f a)
    refine ⟨a, rfl, h.symm⟩

protected theorem map_pureIf (f : α → β) (a : α) (p : Prop) : (Set.pureIf a p).map f = Set.pureIf (f a) p := by
  apply Set.ext
  intro y
  constr
  · intro ⟨_, ⟨rfl, hp⟩, h⟩
    refine ⟨h.symm, hp⟩
  · intro ⟨h, hp⟩
    refine ⟨a, ⟨rfl, hp⟩, h.symm⟩

protected theorem pure_bind (a : α) (f : α → Set β) : (Set.pure a).bind f = f a := by
  apply Set.ext
  intro y
  constr
  · intro ⟨_, rfl, h⟩
    exact h
  · intro h
    refine ⟨a, rfl, h⟩

protected theorem pureIf_bind (a : α) (p : Prop) (f : α → Set β) : (Set.pureIf a p).bind f = f a ∩ Set.const p := by
  apply Set.ext
  intro y
  constr
  · intro ⟨_, ⟨rfl, hp⟩, h⟩
    refine ⟨h, hp⟩
  · intro ⟨h, hp⟩
    refine ⟨a, ⟨rfl, hp⟩, h⟩

protected theorem bind_assoc (s : Set α) (f : α → Set β) (g : β → Set γ) : (s.bind f).bind g = s.bind λ x => (f x).bind g := by
  apply Set.ext
  intro z
  constr
  · intro ⟨y, ⟨x, hx, hy⟩, hz⟩
    refine ⟨x, hx, ⟨y, hy, hz⟩⟩
  · intro ⟨x, hx, ⟨y, hy, hz⟩⟩
    refine ⟨y, ⟨x, hx, hy⟩, hz⟩

protected theorem bind_comm (f : α → β → Set γ) (s : Set α) (t : Set β) : (s.bind λ x => t.bind (f x .)) = t.bind λ y => s.bind (f . y) := by
  apply Set.ext
  intro z
  constr
  · intro ⟨x, hx, ⟨y, hy, hz⟩⟩
    refine ⟨y, hy, ⟨x, hx, hz⟩⟩
  · intro ⟨y, hy, ⟨x, hx, hz⟩⟩
    refine ⟨x, hx, ⟨y, hy, hz⟩⟩

protected theorem bind_pure_comp (f : α → β) (s : Set α) : s.bind (λ x => Set.pure (f x)) = s.map f := by
  apply Set.ext
  intro y
  constr
  · intro ⟨x, hx, (h : y = f x)⟩
    refine ⟨x, hx, h.symm⟩
  · intro ⟨x, hx, h⟩
    refine ⟨x, hx, h.symm⟩

protected theorem bind_id (s : Set (Set α)) : s.bind id = s.join := rfl

protected theorem bind_map (f : Set (α → β)) (s : Set α) : f.bind s.map = Set.seq f s := rfl

protected theorem pure_seq (f : α → β) (s : Set α) : Set.seq (Set.pure f) s = s.map f := by
  apply Set.ext
  intro y
  constr
  · intro ⟨_, rfl, h⟩
    exact h
  · intro ⟨x, hx, h⟩
    refine ⟨f, rfl, ⟨x, hx, h⟩⟩

protected theorem seq_assoc (s : Set α) (f : Set (α → β)) (g : Set (β → γ)) : g.seq (f.seq s) = ((g.map (.∘.)).seq f).seq s := by
  apply Set.ext
  intro z
  constr
  · intro ⟨g',hg',⟨y,⟨f',hf',⟨x,hx,hy⟩⟩,hz⟩⟩
    cases hz
    exists (g' ∘ f')
    constr
    · exists (g' ∘ .)
      constr
      · exists g'
      · exists f'
    · exists x
      constr
      · exact hx
      · cases hy
        rfl
  · intro ⟨gof,⟨go,⟨g',hg',hgo⟩,⟨f',hf',hgof'⟩⟩,⟨x,hx,hz⟩⟩
    cases hgof'
    cases hgo
    cases hz
    exists g'
    constr
    · exact hg'
    · exists f' x
      constr
      · exists f'
        constr
        · exact hf'
        · exists x
      · rfl

instance : Monad Set where
  bind := Set.bind
  pure := Set.pure
  map := Set.map
  seq f s := Set.seq f (s ())
  seqLeft s t := Set.seqLeft s (t ())
  seqRight s t := Set.seqRight s (t ())

instance : LawfulMonad Set where
  id_map := Set.id_map
  comp_map := Set.comp_map
  map_const := rfl
  map_pure := Set.map_pure
  pure_bind := Set.pure_bind
  bind_assoc := Set.bind_assoc
  bind_pure_comp := Set.bind_pure_comp
  bind_map := Set.bind_map
  pure_seq := Set.pure_seq
  seq_assoc := Set.seq_assoc
  seqLeft_eq _ _ := rfl
  seqRight_eq _ _ := rfl

theorem union_empty (s : Set α) : s ∪ Set.empty = s := by
  apply Set.ext
  intro x
  constr
  · intro
    | Or.inl _ => assumption
    | Or.inr _ => contradiction
  · intro h
    left
    exact h

theorem empty_union (s : Set α) : Set.empty ∪ s = s := by
  apply Set.ext
  intro x
  constr
  · intro
    | Or.inl _ => contradiction
    | Or.inr _ => assumption
  · intro h
    right
    exact h

theorem inter_empty (s : Set α) : s ∩ Set.empty = Set.empty := by
  apply Set.ext
  intro x
  constr
  · intro ⟨_, _⟩
    assumption
  · intro _
    contradiction

theorem empty_inter (s : Set α) : Set.empty ∩ s = Set.empty := by
  apply Set.ext
  intro x
  constr
  · intro ⟨_, _⟩
    assumption
  · intro _
    contradiction

theorem empty_map (f : α → β) : Set.empty.map f = Set.empty := by
  apply Set.ext
  intro x
  constr
  · intro ⟨_,_,_⟩
    contradiction
  · intro _
    contradiction

theorem empty_bind (f : α → Set β) : Set.empty.bind f = Set.empty := by
  apply Set.ext
  intro x
  constr
  · intro ⟨_,_,_⟩
    contradiction
  · intro _
    contradiction

theorem empty_seq (f : Set (α → β)) : Set.seq f Set.empty = Set.empty := by
  apply Set.ext
  intro x
  constr
  · intro ⟨_, _, (hx : x ∈ Set.empty.map _)⟩
    rw [empty_map] at hx
    contradiction
  · intro _
    contradiction

theorem pure_inter (a : α) (s : Set α) : Set.pure a ∩ s = Set.pureIf a (a ∈ s) := by
  apply Set.ext
  intro x
  constr
  · intro ⟨rfl, hs⟩
    refine ⟨rfl, hs⟩
  · intro ⟨rfl, hs⟩
    refine ⟨rfl, hs⟩

theorem inter_pure (a : α) (s : Set α) : s ∩ Set.pure a = Set.pureIf a (a ∈ s) := by
  apply Set.ext
  intro x
  constr
  · intro ⟨hs, rfl⟩
    refine ⟨rfl, hs⟩
  · intro ⟨rfl, hs⟩
    refine ⟨hs, rfl⟩

theorem pureIf_inter (a : α) (p : Prop) (s : Set α) : Set.pureIf a p ∩ s = Set.pureIf a (p ∧ a ∈ s) := by
  apply Set.ext
  intro x
  constr
  · intro ⟨⟨rfl, hp⟩, hs⟩
    refine ⟨rfl, ⟨hp, hs⟩⟩
  · intro ⟨rfl, ⟨hp, hs⟩⟩
    refine ⟨⟨rfl, hp⟩, hs⟩

theorem inter_pureIf (a : α) (p : Prop) (s : Set α) : s ∩ Set.pureIf a p = Set.pureIf a (p ∧ a ∈ s) := by
  apply Set.ext
  intro x
  constr
  · intro ⟨hs, rfl, hp⟩
    refine ⟨rfl, hp, hs⟩
  · intro ⟨rfl, hp, hs⟩
    refine ⟨hs, rfl, hp⟩

theorem union_idem (s : Set α) : s ∪ s = s := by
  apply Set.ext
  intro x
  constr
  · open Or in intro
    | inl hs => exact hs
    | inr hs => exact hs
  · intro hs
    left
    exact hs

theorem union_comm (s t : Set α) : s ∪ t = t ∪ s := by
  apply Set.ext
  intro x
  constr
  · open Or in intro
    | inl hs => right; exact hs
    | inr ht => left; exact ht
  · open Or in intro
    | inl ht => right; exact ht
    | inr hs => left; exact hs

theorem union_assoc (s t u : Set α) : (s ∪ t) ∪ u = s ∪ (t ∪ u) := by
  apply Set.ext
  intro x
  constr
  · open Or in intro
    | inl (inl hs) => exact inl hs
    | inl (inr ht) => exact inr (inl ht)
    | inr hu => exact inr (inr hu)
  · open Or in intro
    | inl hs => left; left; exact hs
    | inr (inl ht) => left; right; exact ht
    | inr (inr hu) => right; exact hu

theorem union_map (f : α → β) (s t : Set α) : (s ∪ t).map f = s.map f ∪ t.map f := by
  apply Set.ext
  intro y
  constr
  · open Or in intro
    | ⟨x, inl hs, h⟩ => left; refine ⟨x, hs, h⟩
    | ⟨x, inr ht, h⟩ => right; refine ⟨x, ht, h⟩
  · open Or in intro
    | inl ⟨x, hs, h⟩ => refine ⟨x, inl hs, h⟩
    | inr ⟨x, ht, h⟩ => refine ⟨x, inr ht, h⟩

theorem union_bind (f : α → Set β) (s t : Set α) : (s ∪ t).bind f = s.bind f ∪ t.bind f := by
  apply Set.ext
  intro y
  constr
  · open Or in intro
    | ⟨x, inl hs, h⟩ => left; refine ⟨x, hs, h⟩
    | ⟨x, inr ht, h⟩ => right; refine ⟨x, ht, h⟩
  · open Or in intro
    | inl ⟨x, hs, h⟩ => refine ⟨x, inl hs, h⟩
    | inr ⟨x, ht, h⟩ => refine ⟨x, inr ht, h⟩

theorem inter_idem (s : Set α) : s ∩ s = s := by
  apply Set.ext
  intro x
  constr
  · intro ⟨hs, _⟩
    exact hs
  · intro hs
    exact ⟨hs, hs⟩

theorem inter_comm (s t : Set α) : s ∩ t = t ∩ s := by
  apply Set.ext
  intro x
  constr
  · intro ⟨hs, ht⟩
    exact ⟨ht, hs⟩
  · intro ⟨ht, hs⟩
    exact ⟨hs, ht⟩

theorem inter_assoc (s t u : Set α) : (s ∩ t) ∩ u = s ∩ (t ∩ u) := by
  apply Set.ext
  intro x
  constr
  · intro ⟨⟨hs, ht⟩, hu⟩
    exact ⟨hs, ⟨ht, hu⟩⟩
  · intro ⟨hs, ⟨ht, hu⟩⟩
    exact ⟨⟨hs, ht⟩, hu⟩

theorem union_distrib_left (s t u : Set α) : s ∪ (t ∩ u) = (s ∪ t) ∩ (s ∪ u) := by
  apply Set.ext
  intro x
  constr
  · open Or in intro
    | inl hs => constr; left; exact hs; left; exact hs
    | inr ⟨ht,hu⟩ => constr; right; exact ht; right; exact hu
  · open Or in intro
    | ⟨inl hs, _⟩ => left; exact hs
    | ⟨_, inl hs⟩ => left; exact hs
    | ⟨inr ht, inr hu⟩ => right; constr; exact ht; exact hu

theorem union_distrib_right (s t u : Set α) : (s ∩ t) ∪ u  = (s ∪ u) ∩ (t ∪ u) := by
  apply Set.ext
  intro x
  constr
  · open Or in intro
    | inl ⟨hs,ht⟩ => constr; left; exact hs; left; exact ht
    | inr hu => constr; right; exact hu; right; exact hu
  · open Or in intro
    | ⟨inr hu, _⟩ => right; exact hu
    | ⟨_, inr hu⟩ => right; exact hu
    | ⟨inl hs, inl ht⟩ => left; constr; exact hs; exact ht

theorem inter_distrib_left (s t u : Set α) : s ∩ (t ∪ u) = (s ∩ t) ∪ (s ∩ u) := by
  apply Set.ext
  intro x
  constr
  · open Or in intro
    | ⟨hs, inl ht⟩ => left; constr; exact hs; exact ht
    | ⟨hs, inr hu⟩ => right; constr; exact hs; exact hu
  · open Or in intro
    | inl ⟨hs, ht⟩ => constr; exact hs; left; exact ht
    | inr ⟨hs, hu⟩ => constr; exact hs; right; exact hu

theorem inter_distrib_right (s t u : Set α) : (s ∪ t) ∩ u = (s ∩ u) ∪ (t ∩ u) := by
  apply Set.ext
  intro x
  constr
  · open Or in intro
    | ⟨inl hs, hu⟩ => left; constr; exact hs; exact hu
    | ⟨inr ht, hu⟩ => right; constr; exact ht; exact hu
  · open Or in intro
    | inl ⟨hs, hu⟩ => constr; left; exact hs; exact hu
    | inr ⟨ht, hu⟩ => constr; right; exact ht; exact hu

end Set
