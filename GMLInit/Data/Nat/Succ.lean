import GMLInit.Meta.Stable
import GMLInit.Data.Nat.Basic
import GMLInit.Data.Nat.IsPos
import GMLInit.Data.Nat.Order

namespace Nat

attribute [local eliminator] Nat.recDiagAux

protected theorem pred_zero' : 0 - 1 = 0 := rfl

protected theorem pred_succ' (x : Nat) : (x + 1) - 1 = x := rfl

protected theorem succ_pred' (x : Nat) (h : x > 0 := by nat_is_pos) : (x - 1) + 1 = x := by
  cases x with
  | zero => contradiction
  | succ x => rw [Nat.pred_succ']

protected theorem zero_lt_succ' (x : Nat) : 0 < x + 1 := Nat.zero_lt_succ x

protected theorem not_succ_le_zero' (x : Nat) : ¬ x + 1 ≤ 0 := Nat.not_succ_le_zero x

protected theorem lt_succ_self' (x : Nat) : x < x + 1 := Nat.lt_succ_self x

protected theorem not_succ_le_self' (x : Nat) : ¬ x + 1 ≤ x := Nat.not_succ_le_self x

protected theorem succ_le_succ' {x y : Nat} : x ≤ y → x + 1 ≤ y + 1 := Nat.succ_le_succ

protected theorem le_of_succ_le_succ' {x y : Nat} : x + 1 ≤ y + 1 → x ≤ y := Nat.le_of_succ_le_succ

protected theorem succ_lt_succ' {x y : Nat} : x < y → x + 1 < y + 1 := Nat.succ_lt_succ

protected theorem lt_of_succ_lt_succ' {x y : Nat} : x + 1 < y + 1 → x < y := Nat.lt_of_succ_lt_succ

protected theorem succ_le_of_lt' {x y : Nat} : x + 1 ≤ y → x < y := Nat.succ_le_of_lt

protected theorem lt_of_succ_le' {x y : Nat} : x + 1 ≤ y → x < y := Nat.lt_of_succ_le

protected theorem lt_succ_of_le' {x y : Nat} : x ≤ y → x < y + 1 := Nat.lt_succ_of_le

protected theorem le_of_lt_succ' {x y : Nat} : x < y + 1 → x ≤ y := Nat.le_of_lt_succ

protected theorem succ_le_iff_lt (x y : Nat) : x + 1 ≤ y ↔ x < y :=
  ⟨Nat.lt_of_succ_le, Nat.succ_le_of_lt⟩

protected theorem lt_succ_iff_le (x y : Nat) : x < y + 1 ↔ x ≤ y :=
  ⟨Nat.le_of_lt_succ, Nat.lt_succ_of_le⟩

protected theorem succ_le_succ_iff_le (x y : Nat) : x + 1 ≤ y + 1 ↔ x ≤ y :=
  ⟨Nat.le_of_succ_le_succ, Nat.succ_le_succ⟩

protected theorem succ_lt_succ_iff_lt (x y : Nat) : x + 1 < y + 1 ↔ x < y :=
  ⟨Nat.lt_of_succ_lt_succ, Nat.succ_lt_succ⟩

theorem pred_le_iff_le_succ' (x y : Nat) : x - 1 ≤ y ↔ x ≤ y + 1 := Nat.pred_le_iff_le_succ ..

protected theorem succ_lt_iff_lt_pred (x y : Nat) : x + 1 < y ↔ x < y - 1 := by
  rw [←Nat.not_le, ←Nat.not_le]
  apply Iff.mt
  exact Nat.pred_le_iff_le_succ' y x

protected theorem succ_le_or_eq_zero_iff_le_pred (x y : Nat) : x + 1 ≤ y ∨ x = 0 ↔ x ≤ y - 1 := by
  cases x, y with
  | zero_left x => simp
  | zero_right y => simp
  | succ_succ x y =>
    constr
    · intro
      | Or.inl h => exact Nat.le_of_succ_le_succ h
      | Or.inr h => absurd h; apply Nat.succ_ne_zero
    · intro h
      left
      exact Nat.succ_le_succ h

protected theorem pred_lt_or_eq_zero_iff_lt_succ (x y : Nat) : x - 1 < y ∨ x = 0 ↔ x < y + 1 := by
  cases x, y with
  | zero_left x => simp [Nat.zero_lt_succ]
  | zero_right y =>
    constructor
    · simp [Nat.not_lt_zero]; intro h; rw [h]; exact Nat.zero_lt_one
    · simp [Nat.not_lt_zero]; intro h; exact Nat.eq_zero_of_le_zero (Nat.le_of_succ_le_succ h)
  | succ_succ x y =>
    constr
    · intro
      | Or.inl h => exact Nat.succ_lt_succ h
      | Or.inr h => absurd h; apply Nat.succ_ne_zero
    · intro h
      left
      exact Nat.lt_of_succ_lt_succ h

end Nat
