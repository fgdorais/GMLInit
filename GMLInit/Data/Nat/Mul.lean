import GMLInit.Data.Nat.Basic
import GMLInit.Data.Nat.Add

namespace Nat

protected theorem mul_succ' (x y : Nat) : x * (y + 1) = x * y + x := Nat.mul_succ ..

protected theorem succ_mul' (x y : Nat) : (x + 1) * y = x * y + y := Nat.succ_mul ..

protected theorem mul_pred (x y : Nat) : x * (y - 1) = x * y - x := by
  rw [Nat.mul_sub_left_distrib, Nat.mul_one]

protected theorem pred_mul (x y : Nat) : (x - 1) * y = x * y - y := by
  rw [Nat.mul_sub_right_distrib, Nat.one_mul]

@[deprecated Nat.mul_mul_mul_comm]
protected theorem mul_cross_comm (x₁ x₂ y₁ y₂ : Nat) : (x₁ * x₂) * (y₁ * y₂) = (x₁ * y₁) * (x₂ * y₂) := Nat.mul_mul_mul_comm ..

@[deprecated Nat.mul_sub_left_distrib]
protected theorem mul_sub (x y z : Nat) : x * (y - z) = x * y - x * z := Nat.mul_sub_left_distrib ..

@[deprecated Nat.mul_sub_right_distrib]
protected theorem sub_mul (x y z : Nat) : (x - y) * z = x * z - y * z := Nat.mul_sub_right_distrib ..

protected theorem lt_mul_of_gt_one_of_pos_left {x y : Nat} (h : x > 0 := by nat_is_pos) : y > 1 → x < y * x := by
  intro hy
  cases y with
  | zero => contradiction
  | succ y =>
    rw [Nat.succ_mul]
    apply Nat.lt_add_of_pos_left
    apply Nat.mul_pos
    · exact Nat.lt_of_succ_lt_succ hy
    · exact h

protected theorem lt_mul_of_gt_one_right {x y : Nat} (h : x > 0 := by nat_is_pos) : y > 1 → x < x * y := by
  intro hy
  cases y with
  | zero => contradiction
  | succ y =>
    rw [Nat.mul_succ]
    apply Nat.lt_add_of_pos_left
    apply Nat.mul_pos
    · exact h
    · exact Nat.lt_of_succ_lt_succ hy
