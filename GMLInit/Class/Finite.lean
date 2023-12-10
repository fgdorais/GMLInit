import GMLInit.Class.DecLift
import GMLInit.Data.Array
import GMLInit.Data.Fin

instance {α} (β : α → Type _) [DecidableEq α] [(x : α) → DecidableEq (β x)] : DecidableEq ((x : α) × β x)
| a₁, a₂ =>
  match a₁, a₂, inferInstanceAs (Decidable (a₁.fst = a₂.fst)) with
  | ⟨_,y₁⟩, ⟨_,y₂⟩, isTrue rfl =>
    if h : y₁ = y₂ then
      isTrue <| Sigma.eq rfl (heq_of_eq h)
    else
      isFalse fun | rfl => h rfl
  | ⟨_,_⟩, ⟨_,_⟩, isFalse hne => isFalse fun | rfl => hne rfl

class Finite (α : Type _) extends Array α where
  find : α → Fin toArray.size
  find_eq_iff_get_eq (x : α) (i : Fin toArray.size) : find x = i ↔ toArray.get i = x
  decEq : DecidableEq α := by infer_instance

attribute [instance] Finite.decEq

namespace Finite
variable (α) [inst : Finite α]

protected abbrev size := inst.toArray.size

protected abbrev get := inst.toArray.get

theorem get_find (x : α) : Finite.get α (Finite.find x) = x := by
  rw [←find_eq_iff_get_eq]

theorem find_get (i : Fin (Finite.size α)) : Finite.find (Finite.get α i) = i := by
  rw [find_eq_iff_get_eq]

protected def toEquiv : Equiv α (Fin (Finite.size α)) where
  fwd := Finite.find
  rev := Finite.get α
  fwd_eq_iff_rev_eq {x i} := Finite.find_eq_iff_get_eq x i

protected def ofEquiv {α n} [DecidableEq α] (e : Equiv α (Fin n)) : Finite α where
  toArray := Array.ofFn e.rev
  find x := (Array.size_ofFn e.rev).symm ▸ e.fwd x
  find_eq_iff_get_eq x i := by
    constructor
    · intro h
      rw [Array.get_ofFn]
      rw [←e.fwd_eq_iff_rev_eq]
      rw [←h]
      elim_casts
    · intro h
      rw [Array.get_ofFn] at h
      rw [←e.fwd_eq_iff_rev_eq] at h
      clean
      rw [h]
      elim_casts

protected abbrev all {α} [Finite α] (p : α → Bool) : Bool :=
  Fin.all fun i => p (Finite.get α i)

theorem forall_eq_true_of_all_eq_true {α} [Finite α] {p : α → Bool} : Finite.all p = true → ∀ x, p x = true := by
  intro h x
  have hall := Fin.forall_eq_true_of_all_eq_true h
  rw [←hall (Finite.find x)]
  rw [Finite.get_find]

theorem exists_eq_false_of_all_eq_false {α} [Finite α] {p : α → Bool} : Finite.all p = false → ∃ x, p x = false := by
  intro h
  match Fin.exists_eq_false_of_all_eq_false h with
  | ⟨i, h⟩ => exists (Finite.get α i)

instance (p : α → Prop) [DecidablePred p] : Decidable (∀ x, p x) :=
  match hall : Finite.all fun x => decide (p x) with
  | false => isFalse $ by
    intro h
    match exists_eq_false_of_all_eq_false hall with
    | ⟨x, hx⟩ => absurd h x; exact of_decide_eq_false hx
  | true => isTrue $ by
    intro x
    apply of_decide_eq_true
    exact forall_eq_true_of_all_eq_true hall ..

theorem decide_forall (p : α → Prop) [DecidablePred p] : decide (∀ x, p x) = Finite.all fun x => decide (p x) := by
  match h : Finite.all fun x => decide (p x) with
  | false =>
    apply decide_eq_false
    match exists_eq_false_of_all_eq_false h with
    | ⟨x, hx⟩ =>
      intro h
      rw [decide_eq_true (h x)] at hx
      contradiction
  | true =>
    apply decide_eq_true
    intro x
    apply of_decide_eq_true
    apply forall_eq_true_of_all_eq_true h

instance {α} (p : α → Bool) [Finite α] [(x : α) → DecLift (p x)] : DecLift (Finite.all p) where
  toProp := ∀ x, DecLift.toProp (p x)
  instDecidable := inferInstance
  decide_eq := by rw [decide_forall]; congr; funext x; rw [DecLift.decide_eq]

protected abbrev any {α} [Finite α] (p : α → Bool) : Bool :=
  Fin.any fun i => p (Finite.get α i)

theorem exists_eq_true_of_any_eq_true {α} [Finite α] {p : α → Bool} : Finite.any p = true → ∃ x, p x = true := by
  intro h
  match Fin.exists_eq_true_of_any_eq_true h with
  | ⟨i, h⟩ => exists (Finite.get α i)

theorem forall_eq_false_of_any_eq_false {α} [Finite α] {p : α → Bool} : Finite.any p = false → ∀ x, p x = false := by
  intro h x
  have hany := Fin.forall_eq_false_of_any_eq_false h
  rw [←hany (Finite.find x)]
  rw [Finite.get_find]

instance (p : α → Prop) [DecidablePred p] : Decidable (∃ x, p x) :=
  match hany : Finite.any fun x => decide (p x) with
  | true => isTrue $ by
    match exists_eq_true_of_any_eq_true hany with
    | ⟨x, hx⟩ => exists x; exact of_decide_eq_true hx
  | false => isFalse $ by
    intro ⟨x, hx⟩
    absurd hx
    apply of_decide_eq_false
    exact forall_eq_false_of_any_eq_false hany ..

theorem decide_exists (p : α → Prop) [DecidablePred p] : decide (∃ x, p x) = Finite.any fun x => decide (p x) := by
  match h : Finite.any fun x => decide (p x) with
  | true =>
    apply decide_eq_true
    match exists_eq_true_of_any_eq_true h with
    | ⟨x, hx⟩ =>
      exists x
      exact of_decide_eq_true hx
  | false =>
    apply decide_eq_false
    intro ⟨x, hx⟩
    absurd forall_eq_false_of_any_eq_false h x
    rw [decide_eq_true hx]
    trivial

instance {α} (p : α → Bool) [Finite α] [(x : α) → DecLift (p x)] : DecLift (Finite.any p) where
  toProp := ∃ x, DecLift.toProp (p x)
  instDecidable := inferInstance
  decide_eq := by rw [decide_exists]; congr; funext x; rw [DecLift.decide_eq]

instance : Finite Empty := Finite.ofEquiv Fin.equivEmpty.inv

instance : Finite Unit := Finite.ofEquiv Fin.equivUnit.inv

instance : Finite Bool := Finite.ofEquiv Fin.equivBool.inv

instance : Finite Ordering := Finite.ofEquiv Fin.equivOrdering.inv

instance (n) : Finite (Fin n) := Finite.ofEquiv Equiv.id

instance (α) [Finite α] : Finite (Option α) :=
  let e₁ := Fin.equivOption (Finite.size α)
  let e₂ := Option.equiv (Finite.toEquiv α)
  Finite.ofEquiv <| Equiv.comp e₁.inv e₂

instance (α β) [DecidableEq β] [Finite α] [Finite β] : Finite (α ⊕ β) :=
  let e₁ := Fin.equivSum (Finite.size α) (Finite.size β)
  let e₂ := Sum.equiv (Finite.toEquiv α) (Finite.toEquiv β)
  Finite.ofEquiv <| Equiv.comp e₁.inv e₂

instance (α β) [DecidableEq β] [Finite α] [Finite β] : Finite (α × β) :=
  let e₁ := Fin.equivProd (Finite.size α) (Finite.size β)
  let e₂ := Prod.equiv (Finite.toEquiv α) (Finite.toEquiv β)
  Finite.ofEquiv <| Equiv.comp e₁.inv e₂

instance {α : Type _} (β : α → Type _) [Finite α] [(x : α) → Finite (β x)] : Finite ((x : α) × (β x)) :=
  let e₁ := Fin.equivSigma (fun i => Finite.size (β ((Finite.toEquiv α).rev i)))
  let e₂ := Sigma.equiv (Finite.toEquiv α).inv (fun i => (Finite.toEquiv (β ((Finite.toEquiv α).inv.fwd i))).inv)
  Finite.ofEquiv <| Equiv.comp e₁.inv e₂.inv

instance (α β) [Finite α] [DecidableEq β] : DecidableEq (α → β)
| f₁, f₂ =>
  if h : ∀ x, f₁ x = f₂ x then
    isTrue <| funext h
  else
    isFalse fun | rfl => h fun _ => rfl

instance (α β) [DecidableEq β] [Finite α] [Finite β] : Finite (α → β) :=
  let e₁ := Fin.equivFun (Finite.size β) (Finite.size α)
  let e₂ := Fun.equivND (Finite.toEquiv α) (Finite.toEquiv β)
  Finite.ofEquiv <| Equiv.comp e₁.inv e₂

instance {α} (β : α → Type _) [Finite α] [(x : α) → DecidableEq (β x)] : DecidableEq ((x : α) → β x)
| f₁, f₂ =>
  if h : ∀ x, f₁ x = f₂ x then
    isTrue <| funext h
  else
    isFalse fun | rfl => h fun _ => rfl

instance {α : Type _} (β : α → Type _) [Finite α] [(x : α) → Finite (β x)] : Finite ((x : α) → β x) :=
  let e₁ := Fin.equivPi (fun i => Finite.size (β ((Finite.toEquiv α).rev i)))
  let e₂ := Fun.equiv (Finite.toEquiv α).inv (fun i => (Finite.toEquiv (β ((Finite.toEquiv α).inv.fwd i))).inv)
  Finite.ofEquiv <| Equiv.comp e₁.inv e₂.inv

instance (p : α → Prop) [DecidablePred p] [Finite α] : Finite (Subtype p) :=
  let e₁ := Fin.equivSubtype fun i => p ((Finite.toEquiv α).rev i)
  let e₂ := Subtype.equiv (Finite.toEquiv α) (by intro; simp [Equiv.rev_fwd])
  Finite.ofEquiv <| Equiv.comp e₁.inv e₂

instance (s : Setoid α) [DecidableRel s.r] [Finite α] : Finite (Quotient s) :=
  let s' : Setoid (Fin (Finite.size α)) := {
    r := fun i j => (Finite.toEquiv α).rev i ≈ (Finite.toEquiv α).rev j
    iseqv := Equivalence.mk (fun _ => s.refl _) s.symm s.trans
  }
  let e₁ := Fin.equivQuotient s'
  let e₂ := Quotient.equiv (s₁:=s) (s₂:=s') (Finite.toEquiv α) $ by
    intro x y
    constructor
    · intro h
      show (Finite.toEquiv α).rev ((Finite.toEquiv α).fwd x) ≈ (Finite.toEquiv α).rev ((Finite.toEquiv α).fwd y)
      rw [Equiv.rev_fwd, Equiv.rev_fwd]
      exact h
    · intro h
      have h : (Finite.toEquiv α).rev ((Finite.toEquiv α).fwd x) ≈ (Finite.toEquiv α).rev ((Finite.toEquiv α).fwd y) := h
      rw [Equiv.rev_fwd, Equiv.rev_fwd] at h
      exact h
  Finite.ofEquiv <| Equiv.comp e₁.inv e₂

end Finite

