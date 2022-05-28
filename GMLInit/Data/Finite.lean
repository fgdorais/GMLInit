import GMLInit.Data.Basic
import GMLInit.Data.Fin
import GMLInit.Data.Index
import GMLInit.Data.List
import GMLInit.Data.Option
import GMLInit.Data.Prod
import GMLInit.Data.Pi
import GMLInit.Data.Sigma
import GMLInit.Data.Sum
import GMLInit.Data.Subtype

protected theorem Quotient.liftBeta {s : Setoid α} (f : α → β) (h : ∀ x₁ x₂, x₁ ≈ x₂ → f x₁ = f x₂) (x : α) : Quotient.lift f h (Quotient.mk s x) = f x := rfl

class Finite.{u} (α : Type u) : Type u where
  list : List α
  find : α → Index list
  spec (a : α) (i : Index list) : find a = i ↔ i.val = a

namespace Finite

abbrev enum (α) [self : Finite α] := self.list

protected abbrev Index (α) [Finite α] := Index (enum α)

protected theorem val_find {α} [Finite α] (a : α) : (find a).val = a := by rw [←Finite.spec]

protected theorem find_val {α} [Finite α] (i : Index (enum α)) : find i.val = i := by rw [Finite.spec]

protected def equivIndex (α) [Finite α] : Equiv α (Finite.Index α) where
  fwd a := find a
  rev i := i.val
  spec := by intros; apply Finite.spec

section
variable (α : Type _) (β : Type _) (γ : α → Type _) [Finite α] [Finite β] [(x : α) → Finite (γ x)]

instance : DecidableEq α
| x, y =>
  if h: Finite.find x = Finite.find y
  then Decidable.isTrue $ by rw [Finite.spec] at h; rw [←h, ←Finite.spec]
  else Decidable.isFalse $ by intro | rfl => contradiction

protected def ofEquiv (α' : Type _) (e : Equiv α α') : Finite α' where
  list := (enum α).map e.fwd
  find x := (find (e.rev x)).map e.fwd
  spec x i := by
    constr
    · intro h
      rw [←h, Index.val_map, Finite.val_find, e.fwd_rev]
    · intro h
      clean at h
      rw [←Index.map_unmap e.fwd i, Index.val_map, Equiv.spec] at h
      let h := (Finite.spec _ _).mpr h.symm
      simp only [h, Index.map_unmap]

instance : Finite Empty where
  list := []
  find x := nomatch x
  spec x i := nomatch x

instance : Finite Unit where
  list := [()]
  find x := Index.head
  spec | (), Index.head => by simp

instance : Finite Bool where
  list := [false, true]
  find
  | false => Index.head
  | true => Index.tail Index.head
  spec
  | true, Index.head => by simp
  | true, Index.tail Index.head => by simp
  | false, Index.head => by simp
  | false, Index.tail Index.head => by simp

instance {α} (xs : List α) : Finite (Index xs) where
  list := xs.indexIota
  find := Index.iota
  spec i j := by
    constr
    · intro | rfl => exact Index.val_iota ..
    · intro | rfl => exact Index.iota_val ..

instance (n : Nat) : Finite (Fin n) where
  list := Fin.iota n
  find := Fin.iotaFind
  spec i j := by
    constr
    · intro h
      rw [←h, Fin.val_iotaFind]
    · intro h
      rw [←h, Fin.iotaFind_val]

instance : Finite (Option α) :=
  Finite.ofEquiv (Index (List.option (enum α))) (Option α) (Equiv.comp e₁ e₂).inv
where
  e₁ := Index.optionEquiv (enum α)
  e₂ := Option.equiv (Finite.equivIndex α)

instance : Finite (Sum α β) :=
  Finite.ofEquiv (Index (List.sum (enum α) (enum β))) (Sum α β) (Equiv.comp e₁ e₂).inv
where
  e₁ := Index.sumEquiv (enum α) (enum β)
  e₂ := Sum.equiv (Finite.equivIndex α) (Finite.equivIndex β)

instance : Finite ((x : α) × γ x) :=
  Finite.ofEquiv (Index (List.sigma (enum α) (λ i => enum (γ i.val)))) ((x : α) × γ x) (Equiv.comp e₁ e₂).inv
where
  e₁ := Index.sigmaEquiv (enum α) (λ i => enum (γ i.val))
  e₂ := (Sigma.equiv (Finite.equivIndex α).inv (λ i => (Finite.equivIndex (γ i.val)).inv)).inv

instance : Finite (α × β) := Finite.ofEquiv (Sigma (λ _ : α => β)) (α × β) (Sigma.equivProd α β).inv

instance : Finite (α → β) :=
  Finite.ofEquiv (Index (List.arr (enum α) (enum β))) (α → β) (Equiv.comp e₁ e₂).inv
where
  e₁ := Index.arrEquiv (enum α) (enum β)
  e₂ := Function.equiv (Finite.equivIndex α) (Finite.equivIndex β)

instance (p : α → Prop) [DecidablePred p] : Finite { x // p x } :=
  Finite.ofEquiv (Index ((enum α).sublist p)) {x // p x} (Equiv.comp e₁ e₂).inv
where
  e₁ := Index.sublistEquiv p (enum α)
  e₂ := Subtype.equiv (Finite.equivIndex α) (λ x => by unfold Finite.equivIndex; rw [Finite.val_find]; reflexivity)

instance (s : Setoid α) [DecidableRel s.r] : Finite (Quotient s) where
  list := ((enum α).dedup s).map (Quotient.mk s)
  find := Quotient.lift (λ x => ((find x).dedup s).map (Quotient.mk s)) $ by
    intro x y (h : s.r x y)
    have : (find x).dedup s = (find y).dedup s := by
      apply Index.dedup_eq_dedup_of_rel
      rw [Finite.val_find x, Finite.val_find y]
      exact h
    simp only [this]
  spec x i := by
    induction x using Quotient.ind with
    | _ x =>
      rw [Quotient.liftBeta]
      constr
      · intro
        | rfl =>
          rw [Index.val_map]
          apply Quotient.sound
          transitivity (find x).val using s.r, (.=.)
          · symmetry
            exact Index.val_dedup ..
          · exact Finite.val_find ..
      · intro h
        rw [Index.val_unmap (Quotient.mk s)] at h
        rw [Index.map_eq_iff_eq_unmap]
        apply Index.dedup_eq_of_rel
        apply Quotient.exact
        rw [Finite.val_find, ←h]

end

variable {α} [Finite α]

protected def any (p : α → Bool) : Bool := List.any (enum α) p

protected def all (p : α → Bool) : Bool := List.all (enum α) p

theorem forall_iff_all (p : α → Bool) : (∀ x, p x) ↔ Finite.all p := by
  unfold Finite.all
  rw [List.all_eq_true]
  constr
  · intro h
    apply All.introIdx
    intro i
    rw [←Index.map_unmap _ i, Index.val_map]
    apply h
  · intro h x
    rw [←Finite.val_find x, ←Index.val_map (λ x => p x = true)]
    apply All.projIdx h

theorem exists_iff_any (p : α → Bool) : (∃ x, p x) ↔ Finite.any p := by
  unfold Finite.any
  rw [List.any_eq_true]
  constr
  · intro
    | ⟨x,hx⟩ =>
      rw [←Finite.val_find x, ←Index.val_map (λ x => p x = true)] at hx
      apply Any.introIdx
      exact hx
  · intro h
    match Any.elimIdx h with
    | ⟨i,hi⟩ =>
      rw [←Index.map_unmap _ i, Index.val_map] at hi
      apply Exists.intro
      exact hi

instance (p : α → Prop) [DecidablePred p] : Decidable (∀ x, p x) :=
  match h : Finite.all (λ x => decide (p x)) with
  | true => Decidable.isTrue $ by
    rw [←forall_iff_all] at h
    intro x
    apply of_decide_eq_true
    exact h x
  | false => Decidable.isFalse $ by
    rw [←Bool.not_eq_true] at h
    revert h
    apply mt
    intro h
    rw [←forall_iff_all]
    intro x
    apply decide_eq_true
    exact h x

instance (p : α → Prop) [DecidablePred p] : Decidable (∃ x, p x) :=
  match h : Finite.any (λ x => decide (p x)) with
  | true => Decidable.isTrue $ by
    rw [←exists_iff_any] at h
    match h with
    | ⟨x, hx⟩ =>
      exists x
      apply of_decide_eq_true
      exact hx
  | false => Decidable.isFalse $ by
    rw [←Bool.not_eq_true] at h
    revert h
    apply mt
    intro h
    rw [←exists_iff_any]
    match h with
    | ⟨x,hx⟩ =>
      exists x
      apply decide_eq_true
      exact hx

end Finite
