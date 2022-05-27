import GMLInit.Data.Basic
import GMLInit.Data.Bool
import GMLInit.Data.Equiv
import GMLInit.Logic.ListConnectives
import GMLInit.Meta.Basic

namespace List

instance {α} : (xs : List α) → Decidable (xs = [])
| [] => isTrue rfl
| _::_ => isFalse List.noConfusion

instance {α} : (xs : List α) → Decidable ([] = xs)
| [] => isTrue rfl
| _::_ => isFalse List.noConfusion

protected def extAux {α} : (as₁ as₂ : List α) → List Prop
| [], [] => []
| [], a₂::as₂ => [False]
| a₁::as₁, [] => [False]
| a₁::as₁, a₂::as₂ => (a₁ = a₂) :: List.extAux as₁ as₂

protected theorem ext {α} : (as₁ as₂ : List α) → All (List.extAux as₁ as₂) → as₁ = as₂
| [], [], _ => rfl
| [], a₂::as₂, All.cons h _ => False.elim h
| a₁::as₁, [], All.cons h _ => False.elim h
| a₁::as₁, a₂::as₂, All.cons h hs => h ▸ List.ext as₁ as₂ hs ▸ rfl

protected theorem extIff {α} (as₁ as₂ : List α) : All (List.extAux as₁ as₂) ↔ as₁ = as₂ := by
  constr
  exact List.ext as₁ as₂
  intro h
  cases h
  induction as₁ with
  | nil => exact All.nil
  | cons _ _ H => exact All.cons rfl H

protected theorem extEq {α} (as₁ as₂ : List α) : All (List.extAux as₁ as₂) = (as₁ = as₂) :=
  propext (List.extIff as₁ as₂)

@[simp] lemma nil_map {α β} (f : α → β) : [].map f = [] := rfl

@[simp] lemma cons_map {α β} (f : α → β) (a : α) (as : List α) : (a :: as).map f = f a :: as.map f := rfl

@[simp] lemma pure_map {α β} (f : α → β) (a : α) : [a].map f = [f a] := rfl

@[simp] lemma append_map {α β} (f : α → β) (as bs : List α) : (as ++ bs).map f = as.map f ++ bs.map f := by
  induction as generalizing bs with
  | nil => rfl
  | cons a as H => rw [cons_append, cons_map, cons_map, cons_append, H]

@[simp] lemma id_map {α} (as : List α) : as.map id = as := by
  induction as with
  | nil => rfl
  | cons a as H => unfold map; rw [H]; rfl

lemma comp_map {α β γ} (f : α → β) (g : β → γ) (as : List α) : as.map (g ∘ f) = (as.map f).map g := by
  induction as with
  | nil => rfl
  | cons a as H => unfold map; rw [H, Function.comp_apply]

@[simp] lemma nil_bind {α β} (f : α → List β) : [].bind f = [] := rfl

@[simp] lemma cons_bind {α β} (f : α → List β) (a : α) (as : List α) : (a :: as).bind f = f a ++ as.bind f := rfl

@[simp] lemma pure_bind {α β} (f : α → List β) (a : α) : [a].bind f = f a := by rw [cons_bind, nil_bind, append_nil]

@[simp] lemma append_bind {α β} (f : α → List β) (as bs : List α) : (as ++ bs).bind f = as.bind f ++ bs.bind f := by
  induction as generalizing bs with
  | nil => rfl
  | cons a as H => rw [cons_append, cons_bind, cons_bind, append_assoc, H]

lemma bind_assoc {α β γ} (f : α → List β) (g : β → List γ) (as : List α) : (as.bind f).bind g = as.bind (λ a => (f a).bind g) := by
  induction as with
  | nil => rfl
  | cons a as H => rw [cons_bind, cons_bind, append_bind, H]

def equiv {α β} (e : Equiv α β) : Equiv (List α) (List β) where
  fwd := List.map e.fwd
  rev := List.map e.rev
  spec := by
    intros
    constr
    · intro h; rw [←h, ←comp_map, e.comp_rev_fwd, id_map]
    · intro h; rw [←h, ←comp_map, e.comp_fwd_rev, id_map]

@[simp] lemma all_nil {α} (p : α → Bool) : [].all p = true := rfl

@[simp] lemma all_cons {α} (p : α → Bool) (x : α) (xs : List α) : (x :: xs).all p = (p x && xs.all p) := rfl

lemma all_eq_true {α} (p : α → Bool) (xs : List α) : xs.all p = true ↔ All (xs.map λ x => p x = true) := by
  induction xs generalizing p with
  | nil => rw [all_nil, nil_map]; simp
  | cons x xs H => rw [all_cons, cons_map, All.cons_eq, ←H, Bool.and_eq_true_iff]; simp

lemma all_eq_false {α} (p : α → Bool) (xs : List α) : xs.all p = false ↔ Any (xs.map λ x => p x = false) := by
  induction xs generalizing p with
  | nil => rw [all_nil, nil_map]; simp
  | cons x xs H => rw [all_cons, cons_map, Any.cons_eq, ←H, Bool.and_eq_false_iff]; simp

@[simp] lemma any_nil {α} (p : α → Bool) : [].any p = false := rfl

@[simp] lemma any_cons {α} (p : α → Bool) (x : α) (xs : List α) : (x :: xs).any p = (p x || xs.any p) := rfl

lemma any_eq_true {α} (p : α → Bool) (xs : List α) : xs.any p = true ↔ Any (xs.map λ x => p x = true) := by
  induction xs generalizing p with
  | nil => rw [any_nil, nil_map, Any.nil_eq]; simp
  | cons x xs H => rw [any_cons, cons_map, Any.cons_eq, ←H, Bool.or_eq_true_iff]; simp

lemma any_eq_false {α} (p : α → Bool) (xs : List α) : xs.any p = false ↔ All (xs.map λ x => p x = false) := by
  induction xs generalizing p with
  | nil => rw [any_nil, nil_map, All.nil_eq]; simp
  | cons x xs H => rw [any_cons, cons_map, All.cons_eq, ←H, Bool.or_eq_false_iff]; simp

end List
