import GMLInit.Data.Nat.Basic
import GMLInit.Data.Nat.IsPos
import GMLInit.Data.Nat.Order
import GMLInit.Data.Nat.Succ
import GMLInit.Data.Nat.Add
import GMLInit.Data.Nat.Sub

namespace Nat

-- assert theorem mul_zero (x : Nat) : x * 0 = 0

-- assert theorem zero_mul (x : Nat) : 0 * x = 0

-- assert theorem mul_one (x : Nat) : x * 1 = x

-- assert theorem one_mul (x : Nat) : 1 * x = x

-- assert theorem mul_two (x : Nat) : x * 2 = x + x

-- assert theorem two_mul (x : Nat) : 2 * x = x + x

protected theorem mul_succ' (x y : Nat) : x * (y + 1) = x * y + x := Nat.mul_succ ..

protected theorem succ_mul' (x y : Nat) : (x + 1) * y = x * y + y := Nat.succ_mul ..

protected theorem mul_pred (x y : Nat) : x * (y - 1) = x * y - x := by
  rw [Nat.mul_sub_left_distrib, Nat.mul_one]

protected theorem pred_mul (x y : Nat) : (x - 1) * y = x * y - y := by
  rw [Nat.mul_sub_right_distrib, Nat.one_mul]

-- assert theorem mul_comm (x y : Nat) : x * y = y * x

-- assert theorem mul_assoc (x y z : Nat) : (x * y) * z = x * (y * z)

-- assert theorem mul_left_comm (x y z : Nat) : x * (y * z) = y * (x * z)

-- assert theorem mul_right_comm (x y z : Nat) : (x * y) * z = (x * z) * y

@[deprecated Nat.mul_mul_mul_comm]
protected theorem mul_cross_comm (x₁ x₂ y₁ y₂ : Nat) : (x₁ * x₂) * (y₁ * y₂) = (x₁ * y₁) * (x₂ * y₂) := Nat.mul_mul_mul_comm ..

-- assert theorem mul_add (x y z : Nat) : x * (y + z) = x * y + x * z

-- assert theorem add_mul (x y z : Nat) : (x + y) * z = x * z + y * z

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

-- assert theorem mul_le_mul {x₁ x₂ y₁ y₂ : Nat} : x₁ ≤ x₂ → y₁ ≤ y₂ → x₁ * y₁ ≤ x₂ * y₂

-- assert theorem mul_le_mul_left {x y : Nat} (z : Nat) : x ≤ y → z * x ≤ z * y

-- assert theorem mul_le_mul_right {x y : Nat} (z : Nat) : x ≤ y → x * z ≤ y * z

-- assert theorem mul_lt_mul_of_pos_left {x y z : Nat} : x < y → z > 0 → z * x < z * y

-- assert theorem mul_lt_mul_of_pos_right {x y z : Nat} : x < y → z > 0 → x * z < y * z

@[deprecated Nat.mul_lt_mul_of_pos_left]
protected theorem mul_lt_mul_left {x y z : Nat} : x < y → (h : z > 0 := by nat_is_pos) → z * x < z * y := Nat.mul_lt_mul_of_pos_left

@[deprecated Nat.mul_lt_mul_of_pos_right]
protected theorem mul_lt_mul_right {x y z : Nat} : x < y → (h : z > 0 := by nat_is_pos) → x * z < y * z := Nat.mul_lt_mul_of_pos_right

-- assert theorem mul_lt_mul_of_lt_of_lt {x₁ x₂ y₁ y₂ : Nat} : x₁ < x₂ → y₁ < y₂ → x₁ * y₁ < x₂ * y₂

-- protected theorem mul_lt_mul_of_le_of_lt' {x₁ x₂ y₁ y₂ : Nat} : x₁ ≤ x₂ → y₁ < y₂ → (h : x₂ > 0 := by nat_is_pos) → x₁ * y₁ < x₂ * y₂ := Nat.mul_lt_mul_of_le_of_lt

-- protected theorem mul_lt_mul_of_lt_of_le' {x₁ x₂ y₁ y₂ : Nat} : x₁ < x₂ → y₁ ≤ y₂ → (h : y₂ > 0 := by nat_is_pos) → x₁ * y₁ < x₂ * y₂ := Nat.mul_lt_mul_of_lt_of_le

protected theorem le_of_mul_le_mul_of_pos_left {x y z : Nat} : x > 0 → x * y ≤ x * z → y ≤ z := by
  intro hx hxyz
  by_cases y > z with
  | isTrue h =>
    absurd hxyz
    apply Nat.not_le_of_gt
    exact Nat.mul_lt_mul_of_pos_left h hx
  | isFalse h =>
    exact Nat.le_of_not_gt h

protected theorem le_of_mul_le_mul_of_pos_right {x y z : Nat} : x > 0 → y * x ≤ z * x → y ≤ z := by
  intro hx hxyz
  by_cases y > z with
  | isTrue h =>
    absurd hxyz
    apply Nat.not_le_of_gt
    exact Nat.mul_lt_mul_of_pos_right h hx
  | isFalse h =>
    exact Nat.le_of_not_gt h

-- protected theorem le_of_mul_le_mul_left' (x : Nat) {y z : Nat} : (h : x > 0 := by nat_is_pos) → x * y ≤ x * z → y ≤ z := Nat.le_of_mul_le_mul_of_pos_left

-- protected theorem le_of_mul_le_mul_right' (x : Nat) {y z : Nat} : (h : x > 0 := by nat_is_pos) → y * x ≤ z * x → y ≤ z := Nat.le_of_mul_le_mul_of_pos_right

protected theorem lt_of_mul_lt_mul_left (x : Nat) {y z : Nat} : x * y < x * z → y < z := by
  intro h
  by_cases y ≥ z with
  | isTrue ht =>
    absurd h
    apply Nat.not_lt_of_ge
    apply Nat.mul_le_mul_left
    exact ht
  | isFalse h =>
    apply Nat.lt_of_not_ge
    exact h

protected theorem lt_of_mul_lt_mul_right (x : Nat) {y z : Nat} : y * x < z * x → y < z := by
  intro h
  by_cases y ≥ z with
  | isTrue ht =>
    absurd h
    apply Nat.not_lt_of_ge
    apply Nat.mul_le_mul_right
    exact ht
  | isFalse h =>
    apply Nat.lt_of_not_ge
    exact h

end Nat
