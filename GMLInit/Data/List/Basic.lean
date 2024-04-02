import GMLInit.Data.Basic
import GMLInit.Data.Bool
import GMLInit.Data.Fin.Basic
import GMLInit.Data.Nat
import GMLInit.Meta.Basic

namespace List
open Logic

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
  constructor
  exact List.ext' as₁ as₂
  intro h
  cases h
  induction as₁ with
  | nil => exact All.nil
  | cons _ _ H => exact All.cons rfl H

protected theorem ext'Eq {α} (as₁ as₂ : List α) : All (List.ext'Aux as₁ as₂) = (as₁ = as₂) :=
  propext (List.ext'Iff as₁ as₂)

instance (x : α) (xs : List α) : Nat.IsPos (List.length (x :: xs)) := ⟨Nat.zero_lt_succ _⟩

lemma all_eq_true_iff_all_true {α} (p : α → Bool) (xs : List α) : xs.all p = true ↔ All (xs.map λ x => p x = true) := by
  induction xs generalizing p with
  | nil => rw [map_nil, all_nil_eq]; simp
  | cons x xs H => rw [all_cons, map_cons, all_cons_eq, ←H, Bool.and_eq_true_iff]

lemma all_eq_false_iff_any_false {α} (p : α → Bool) (xs : List α) : xs.all p = false ↔ Any (xs.map λ x => p x = false) := by
  induction xs generalizing p with
  | nil => rw [map_nil, any_nil_eq]; simp
  | cons x xs H => rw [all_cons, map_cons, any_cons_eq, ←H, Bool.and_eq_false_iff]

lemma any_eq_true_iff_any_true {α} (p : α → Bool) (xs : List α) : xs.any p = true ↔ Any (xs.map λ x => p x = true) := by
  induction xs generalizing p with
  | nil => rw [any_nil, map_nil, any_nil_eq]; simp
  | cons x xs H => rw [any_cons, map_cons, any_cons_eq, ←H, Bool.or_eq_true_iff]

lemma any_eq_false_iff_all_false {α} (p : α → Bool) (xs : List α) : xs.any p = false ↔ All (xs.map λ x => p x = false) := by
  induction xs generalizing p with
  | nil => rw [any_nil, map_nil, all_nil_eq]; simp
  | cons x xs H => rw [any_cons, map_cons, all_cons_eq, ←H, Bool.or_eq_false_iff]

/- take -/

@[deprecated take_cons_succ]
theorem take_cons {α} (a : α) (as : List α) (n : Nat) : take (n+1) (a :: as) = a :: take n as := rfl

@[deprecated take_length]
theorem take_all {α} (as : List α) : take as.length as = as := by
  induction as with
  | nil => rfl
  | cons a as ih =>
    rw [length_cons]
    rw [take_cons_succ]
    rw [ih]

/- drop -/

@[deprecated drop_succ_cons]
theorem drop_cons {α} (a : α) (as : List α) (n : Nat) : drop (n+1) (a :: as) = drop n as := rfl

@[deprecated drop_length]
theorem drop_all {α} (as : List α) : as.drop as.length = [] := by
  induction as with
  | nil =>
    rw [drop_nil]
  | cons a as ih =>
    rw [length_cons]
    rw [drop_succ_cons]
    rw [ih]

@[deprecated drop_eq_get_cons]
theorem drop_get {α} (as : List α) (n : Nat) (hn : n < as.length) : drop n as = as[n] :: drop (n+1) as := by
  induction as generalizing n with
  | nil => absurd hn; exact Nat.not_lt_zero n
  | cons a as ih =>
    match n with
    | 0 =>
      rw [drop_succ_cons]
      rw [drop]
      rw [getElem_eq_get]
      rw [get]
      rw [drop]
    | n+1 =>
      rw [drop_succ_cons]
      rw [drop_succ_cons]
      rw [getElem_eq_get]
      rw [get_cons_succ]
      rw [←getElem_eq_get]
      exact ih ..
