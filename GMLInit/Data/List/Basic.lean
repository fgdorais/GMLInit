import GMLInit.Data.Basic
import GMLInit.Data.Bool
import GMLInit.Data.Nat
import GMLInit.Logic.ListConnectives
import GMLInit.Meta.Basic

namespace List

instance {α} : (xs : List α) → Decidable (xs = [])
| [] => isTrue rfl
| _::_ => isFalse List.noConfusion

instance {α} : (xs : List α) → Decidable ([] = xs)
| [] => isTrue rfl
| _::_ => isFalse List.noConfusion

protected def ext'Aux {α} : (as₁ as₂ : List α) → List Prop
| [], [] => []
| [], _::_ => [False]
| _::_, [] => [False]
| a₁::as₁, a₂::as₂ => (a₁ = a₂) :: List.ext'Aux as₁ as₂

protected theorem ext' {α} : (as₁ as₂ : List α) → All (List.ext'Aux as₁ as₂) → as₁ = as₂
| [], [], _ => rfl
| [], _::_, All.cons h _ => False.elim h
| _::_₁, [], All.cons h _ => False.elim h
| _::as₁, _::as₂, All.cons h hs => h ▸ List.ext' as₁ as₂ hs ▸ rfl

protected theorem ext'Iff {α} (as₁ as₂ : List α) : All (List.ext'Aux as₁ as₂) ↔ as₁ = as₂ := by
  constr
  exact List.ext' as₁ as₂
  intro h
  cases h
  induction as₁ with
  | nil => exact All.nil
  | cons _ _ H => exact All.cons rfl H

protected theorem ext'Eq {α} (as₁ as₂ : List α) : All (List.ext'Aux as₁ as₂) = (as₁ = as₂) :=
  propext (List.ext'Iff as₁ as₂)

instance (x : α) (xs : List α) : Nat.IsPos (List.length (x :: xs)) := ⟨Nat.zero_lt_succ _⟩

lemma map_pure {α β} (f : α → β) (a : α) : [a].map f = [f a] := rfl

lemma map_comp {α β γ} (f : α → β) (g : β → γ) (as : List α) : as.map (g ∘ f) = (as.map f).map g := by
  symmetry
  exact map_map ..

@[simp] lemma pure_bind {α β} (f : α → List β) (a : α) : [a].bind f = f a := by rw [cons_bind, nil_bind, append_nil]

lemma bind_assoc {α β γ} (f : α → List β) (g : β → List γ) (as : List α) : (as.bind f).bind g = as.bind (λ a => (f a).bind g) := by
  induction as with
  | nil => rfl
  | cons a as H => rw [cons_bind, cons_bind, append_bind, H]

lemma all_eq_true_iff_all_true {α} (p : α → Bool) (xs : List α) : xs.all p = true ↔ All (xs.map λ x => p x = true) := by
  induction xs generalizing p with
  | nil => rw [all_nil, map_nil]; simp
  | cons x xs H => rw [all_cons, map_cons, All.cons_eq, ←H, Bool.and_eq_true_iff]

lemma all_eq_false_iff_any_false {α} (p : α → Bool) (xs : List α) : xs.all p = false ↔ Any (xs.map λ x => p x = false) := by
  induction xs generalizing p with
  | nil => rw [all_nil, map_nil]; simp
  | cons x xs H => rw [all_cons, map_cons, Any.cons_eq, ←H, Bool.and_eq_false_iff]

lemma any_eq_true_iff_any_true {α} (p : α → Bool) (xs : List α) : xs.any p = true ↔ Any (xs.map λ x => p x = true) := by
  induction xs generalizing p with
  | nil => rw [any_nil, map_nil, Any.nil_eq]; simp
  | cons x xs H => rw [any_cons, map_cons, Any.cons_eq, ←H, Bool.or_eq_true_iff]

lemma any_eq_false_iff_all_false {α} (p : α → Bool) (xs : List α) : xs.any p = false ↔ All (xs.map λ x => p x = false) := by
  induction xs generalizing p with
  | nil => rw [any_nil, map_nil, All.nil_eq]; simp
  | cons x xs H => rw [any_cons, map_cons, All.cons_eq, ←H, Bool.or_eq_false_iff]

theorem replicate_zero {α} (a : α) : replicate 0 a = [] := rfl

theorem replicate_add {α} (a : α) : (m n : Nat) → replicate n a ++ replicate m a = replicate (m + n) a
| _, 0 => rfl
| _, _+1 => congrArg (a :: .) (replicate_add ..)

end List
