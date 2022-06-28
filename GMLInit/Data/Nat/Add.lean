import GMLInit.Data.Nat.Basic
import GMLInit.Data.Nat.IsPos
import GMLInit.Data.Nat.Order
import GMLInit.Data.Nat.Succ

namespace Nat

-- assert theorem add_zero (x : Nat) : x + 0 = x

-- assert theorem zero_add (x : Nat) : 0 + x = x

protected theorem add_succ' (x y : Nat) : x + (y + 1) = (x + y) + 1 := Nat.add_succ x y

protected theorem succ_add' (x y : Nat) : (x + 1) + y = (x + y) + 1 := Nat.succ_add x y

protected theorem one_add (x : Nat) : 1 + x = x + 1 := by
  rw [Nat.succ_add, Nat.zero_add]

-- assert theorem add_comm (x y : Nat) : x + y = y + x := core

-- assert theorem add_assoc (x y z : Nat) : (x + y) + z = x + (y + z)

-- assert theorem add_left_comm (x y z : Nat) : x + (y + z) = y + (x + z) := rfl

-- assert theorem add_right_comm (x y z : Nat) : (x + y) + z = (x + z) + y := rfl

protected theorem add_cross_comm (x₁ x₂ y₁ y₂ : Nat) : (x₁ + x₂) + (y₁ + y₂) = (x₁ + y₁) + (x₂ + y₂) := calc
  _ = x₁ + (x₂ + (y₁ + y₂)) := by rw [Nat.add_assoc]
  _ = x₁ + (y₁ + (x₂ + y₂)) := by rw [Nat.add_left_comm x₂ y₁ y₂]
  _ = (x₁ + y₁) + (x₂ + y₂) := by rw [Nat.add_assoc]

protected theorem add_left_cancel' (x : Nat) {y z : Nat} : x + y = x + z → y = z := Nat.add_left_cancel

protected theorem add_right_cancel' (x : Nat) {y z : Nat} : y + x = z + x → y = z := Nat.add_right_cancel

-- assert theorem le_add_left (x y : Nat) : x ≤ y + x

-- assert theorem le_add_right (x y : Nat) : x ≤ x + y

protected theorem lt_add_left (x y : Nat) (h : y > 0 := by nat_is_pos) : x < y + x := calc
  _ = 0 + x := by rw [Nat.zero_add]
  _ < y + x := by apply Nat.add_lt_add_right h

protected theorem lt_add_right (x y : Nat) (h : y > 0 := by nat_is_pos) : x < x + y := calc
  _ = x + 0 := by rw [Nat.add_zero]
  _ < x + y := by apply Nat.add_lt_add_left h

theorem pos_add_left (x y : Nat) (h : x > 0 := by nat_is_pos) : x + y > 0 := calc
  0 ≤ y := by apply Nat.zero_le
  _ < x + y := by apply Nat.lt_add_left _ _

theorem pos_add_right (x y : Nat) (h : y > 0 := by nat_is_pos) : x + y > 0 := calc
  0 ≤ x := by apply Nat.zero_le
  _ < x + y := by apply Nat.lt_add_right _ _

protected theorem eq_zero_of_add_eq_zero_right : {x y : Nat} → x + y = 0 → y = 0
| _, 0, _ => rfl
| _, _+1, h => Nat.noConfusion h

protected theorem eq_zero_of_add_eq_zero_left {x y : Nat} : x + y = 0 → x = 0 := by
  intro h
  rw [Nat.add_comm] at h
  exact Nat.eq_zero_of_add_eq_zero_right h

-- assert theorem add_le_add {x₁ x₂ y₁ y₂ : Nat} : x₁ ≤ x₂ → y₁ ≤ y₂ → x₁ + y₁ ≤ x₂ + y₂

-- assert theorem add_le_add_left {x y : Nat} (h : x ≤ y) (z : Nat) : z + x ≤ z + y

-- assert theorem add_le_add_right {x y : Nat} (h : x ≤ y) (z : Nat) : x + z ≤ y + z

-- assert theorem add_lt_add {x₁ x₂ y₁ y₂ : Nat} : x₁ < x₂ → y₁ < y₂ → x₁ + y₁ < x₂ + y₂

-- assert theorem add_lt_add_left {x y : Nat} (h : x ≤ y) (z : Nat) : z + x ≤ z + y

-- assert theorem add_lt_add_right {x y : Nat} (h : x ≤ y) (z : Nat) : x + z ≤ y + z

protected theorem add_lt_add_of_le_of_lt {x₁ x₂ y₁ y₂ : Nat} : x₁ ≤ x₂ → y₁ < y₂ → x₁ + y₁ < x₂ + y₂ := by
  intro h₁ h₂
  transitivity (x₁ + y₂) using LT.lt, LE.le
  · apply Nat.add_lt_add_left h₂
  · apply Nat.add_le_add_right h₁

protected theorem add_lt_add_of_lt_of_le {x₁ x₂ y₁ y₂ : Nat} : x₁ < x₂ → y₁ ≤ y₂ → x₁ + y₁ < x₂ + y₂ := by
  intro h₁ h₂
  transitivity (x₁ + y₂) using LE.le, LT.lt
  · apply Nat.add_le_add_left h₂
  · apply Nat.add_lt_add_right h₁

protected theorem le_of_add_le_add_left' (x : Nat) {y z : Nat} : x + y ≤ x + z → y ≤ z := Nat.le_of_add_le_add_left

protected theorem le_iff_add_le_add_left (x y z : Nat) : x ≤ y ↔ z + x ≤ z + y :=
  ⟨λ h => Nat.add_le_add_left h z, Nat.le_of_add_le_add_left⟩

protected theorem le_of_add_le_add_right' (x : Nat) {y z : Nat} : y + x ≤ z + x → y ≤ z := Nat.le_of_add_le_add_right

protected theorem le_iff_add_le_add_right (x y z : Nat) : x ≤ y ↔ x + z ≤ y + z :=
  ⟨λ h => Nat.add_le_add_right h z, Nat.le_of_add_le_add_right⟩

protected theorem lt_of_add_lt_add_left {x y z : Nat} : x + y < x + z → y < z := by
  induction x with
  | zero =>
    rw [Nat.zero_add, Nat.zero_add]
    exact id
  | succ x H =>
    rw [Nat.succ_add, Nat.succ_add]
    intro h
    apply H
    exact Nat.lt_of_succ_lt_succ h

protected theorem lt_of_add_lt_add_left' (x : Nat) {y z : Nat} : x + y < x + z → y < z := Nat.lt_of_add_lt_add_left

protected theorem lt_iff_add_lt_add_left (x y z : Nat) : x < y ↔ z + x < z + y :=
  ⟨λ h => Nat.add_lt_add_left h z, Nat.lt_of_add_lt_add_left⟩

protected theorem lt_of_add_lt_add_right {x y z : Nat} : y + x < z + x → y < z := by
  induction x with
  | zero =>
    exact id
  | succ x H =>
    intro h
    apply H
    apply Nat.le_of_succ_le_succ h

protected theorem lt_of_add_lt_add_right' (x : Nat) {y z : Nat} : y + x < z + x → y < z := Nat.lt_of_add_lt_add_right

protected theorem lt_iff_add_lt_add_right (x y z : Nat) : x < y ↔ x + z < y + z :=
  ⟨λ h => Nat.add_lt_add_right h z, Nat.lt_of_add_lt_add_right⟩

end Nat
