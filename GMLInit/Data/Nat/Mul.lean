import GMLInit.Data.Nat.Basic
import GMLInit.Data.Nat.IsPos
import GMLInit.Data.Nat.Order
import GMLInit.Data.Nat.Succ
import GMLInit.Data.Nat.Add
import GMLInit.Data.Nat.Sub

namespace Nat

attribute [local eliminator] Nat.recDiagAux

-- assert theorem mul_zero (x : Nat) : x * 0 = 0

-- assert theorem zero_mul (x : Nat) : 0 * x = 0

-- assert theorem mul_one (x : Nat) : x * 1 = x

-- assert theorem one_mul (x : Nat) : 1 * x = x

protected theorem mul_two (x : Nat) : x * 2 = x + x := by
  rw [Nat.mul_succ, Nat.mul_one]

protected theorem two_mul (x : Nat) : 2 * x = x + x := by
  rw [Nat.succ_mul, Nat.one_mul]

protected theorem mul_succ' (x y : Nat) : x * (y + 1) = x * y + x := Nat.mul_succ x y

protected theorem succ_mul' (x y : Nat) : (x + 1) * y = x * y + y := Nat.succ_mul x y

protected theorem mul_pred (x y : Nat) : x * (y - 1) = x * y - x := by
  cases y with
  | zero => rw [Nat.pred_zero', Nat.mul_zero, Nat.zero_sub]
  | succ y => rw [Nat.pred_succ', Nat.mul_succ, Nat.add_sub_cancel_right]

protected theorem pred_mul (x y : Nat) : (x - 1) * y = x * y - y := by
  cases x with
  | zero => rw [Nat.pred_zero', Nat.zero_mul, Nat.zero_sub]
  | succ x => rw [Nat.pred_succ', Nat.succ_mul, Nat.add_sub_cancel_right]

-- assert theorem mul_comm (x y : Nat) : x * y = y * x

-- assert theorem mul_assoc (x y z : Nat) : (x * y) * z = x * (y * z)

-- assert theorem mul_left_comm (x y z : Nat) : x * (y * z) = y * (x * z)

protected theorem mul_right_comm (x y z : Nat) : (x * y) * z = (x * z) * y := 
  calc
  _ = x * (y * z) := by rw [Nat.mul_assoc]
  _ = x * (z * y) := by rw [Nat.mul_comm y z]
  _ = (x * z) * y := by rw [Nat.mul_assoc]

protected theorem mul_cross_comm (x₁ x₂ y₁ y₂ : Nat) : (x₁ * x₂) * (y₁ * y₂) = (x₁ * y₁) * (x₂ * y₂) := 
  calc
  _ = x₁ * (x₂ * (y₁ * y₂)) := by rw [Nat.mul_assoc]
  _ = x₁ * (y₁ * (x₂ * y₂)) := by rw [Nat.mul_left_comm x₂ y₁ y₂]
  _ = (x₁ * y₁) * (x₂ * y₂) := by rw [Nat.mul_assoc]

-- assert theorem mul_add (x y z : Nat) : x * (y + z) = x * y + x * z

-- assert theorem add_mul (x y z : Nat) : (x + y) * z = x * z + y * z

protected theorem mul_sub (x y z : Nat) : x * (y - z) = x * y - x * z := by
  induction y, z with
  | left y => rw [Nat.sub_zero, Nat.mul_zero, Nat.sub_zero]
  | right z => rw [Nat.zero_sub, Nat.mul_zero, Nat.zero_sub]
  | diag y z H =>
    calc
    _ = x * (y - z) := by rw [Nat.succ_sub_succ]
    _ = x * y - x * z := by rw [H]
    _ = (x * y + x) - (x * z + x) := by rw [Nat.add_sub_add]
    _ = x * (y + 1) - x * (z + 1) := by rw [Nat.mul_succ, Nat.mul_succ]

protected theorem sub_mul (x y z : Nat) : (x - y) * z = x * z - y * z := by
  induction x, y with
  | left x => rw [Nat.sub_zero, Nat.zero_mul, Nat.sub_zero]
  | right y => rw [Nat.zero_sub, Nat.zero_mul, Nat.zero_sub]
  | diag x y H => 
    calc
    _ = (x - y) * z := by rw [Nat.succ_sub_succ]
    _ = x * z - y * z := by rw [H]
    _ = (x * z + z) - (y * z + z) := by rw [Nat.add_sub_add]
    _ = (x + 1) * z - (y + 1) * z := by rw [Nat.succ_mul, Nat.succ_mul]

protected theorem le_mul_of_pos_left (x : Nat) {y : Nat} : y > 0 → x ≤ y * x := by
  cases y with
  | zero => intro; contradiction
  | succ y => intro; rw [Nat.succ_mul]; apply Nat.le_add_left

protected theorem le_mul_of_pos_right (x : Nat) {y : Nat} : y > 0 → x ≤ x * y := by
  cases y with
  | zero => intro; contradiction
  | succ y => intro; rw [Nat.mul_succ]; apply Nat.le_add_left

protected theorem lt_mul_of_gt_one_of_pos_left {x y : Nat} (h : x > 0 := by nat_is_pos) : y > 1 → x < y * x := by
  intro hy
  cases y with
  | zero => contradiction
  | succ y =>
    rw [Nat.succ_mul]
    apply Nat.lt_add_left
    apply Nat.mul_pos
    · exact Nat.lt_of_succ_lt_succ hy
    · exact h

protected theorem lt_mul_of_gt_one_right {x y : Nat} (h : x > 0 := by nat_is_pos) : y > 1 → x < x * y := by
  intro hy
  cases y with
  | zero => contradiction
  | succ y =>
    rw [Nat.mul_succ]
    apply Nat.lt_add_left
    apply Nat.mul_pos
    · exact h
    · exact Nat.lt_of_succ_lt_succ hy

-- assert theorem mul_le_mul {x₁ x₂ y₁ y₂ : Nat} : x₁ ≤ x₂ → y₁ ≤ y₂ → x₁ * y₁ ≤ x₂ * y₂

-- assert theorem mul_le_mul_left {x y : Nat} (z : Nat) : x ≤ y → z * x ≤ z * y

-- assert theorem mul_le_mul_right {x y : Nat} (z : Nat) : x ≤ y → x * z ≤ y * z

-- assert theorem mul_lt_mul_of_pos_left {x y z : Nat} : x < y → z > 0 → z * x < z * y

-- assert theorem mul_lt_mul_of_pos_right {x y z : Nat} : x < y → z > 0 → x * z < y * z

protected theorem mul_lt_mul_left {x y z : Nat} : x < y → (h : z > 0 := by nat_is_pos) → z * x < z * y := Nat.mul_lt_mul_of_pos_left

protected theorem mul_lt_mul_right {x y z : Nat} : x < y → (h : z > 0 := by nat_is_pos) → x * z < y * z := Nat.mul_lt_mul_of_pos_right

protected theorem mul_lt_mul {x₁ x₂ y₁ y₂ : Nat} : x₁ < x₂ → y₁ < y₂ → x₁ * y₁ < x₂ * y₂ := by
  intro hx hy
  transitivity (x₂ * y₁) using LE.le, LT.lt
  · apply Nat.mul_le_mul_right
    exact Nat.le_of_lt hx
  · apply Nat.mul_lt_mul_of_pos_left
    · exact hy
    · transitivity x₁ using LE.le, LT.lt
      · apply Nat.zero_le
      · exact hx

protected theorem mul_lt_mul_of_le_of_lt {x₁ x₂ y₁ y₂ : Nat} : x₁ ≤ x₂ → y₁ < y₂ → (h : x₂ > 0 := by nat_is_pos) → x₁ * y₁ < x₂ * y₂ := by
  intro hx hy h
  transitivity (x₂ * y₁) using LE.le, LT.lt
  · exact Nat.mul_le_mul_right _ hx
  · exact Nat.mul_lt_mul_left hy

protected theorem mul_lt_mul_of_lt_of_le {x₁ x₂ y₁ y₂ : Nat} : x₁ < x₂ → y₁ ≤ y₂ → (h : y₂ > 0 := by nat_is_pos) → x₁ * y₁ < x₂ * y₂ := by
  intro hx hy h
  transitivity (x₁ * y₂) using LE.le, LT.lt
  · exact Nat.mul_le_mul_left _ hy
  · exact Nat.mul_lt_mul_right hx

protected theorem le_of_mul_le_mul_of_pos_left {x y z : Nat} : x > 0 → x * y ≤ x * z → y ≤ z := by
  intro hx hxyz
  by_cases y > z with
  | isTrue h =>
    absurd hxyz
    apply Nat.not_le_of_gt
    exact Nat.mul_lt_mul_left h
  | isFalse h =>
    exact Nat.le_of_not_gt h

protected theorem le_of_mul_le_mul_of_pos_right {x y z : Nat} : x > 0 → y * x ≤ z * x → y ≤ z := by
  intro hx hxyz
  by_cases y > z with
  | isTrue h =>
    absurd hxyz
    apply Nat.not_le_of_gt
    exact Nat.mul_lt_mul_right h
  | isFalse h =>
    exact Nat.le_of_not_gt h

protected theorem le_of_mul_le_mul_left' (x : Nat) {y z : Nat} : (h : x > 0 := by nat_is_pos) → x * y ≤ x * z → y ≤ z := Nat.le_of_mul_le_mul_of_pos_left

protected theorem le_of_mul_le_mul_right' (x : Nat) {y z : Nat} : (h : x > 0 := by nat_is_pos) → y * x ≤ z * x → y ≤ z := Nat.le_of_mul_le_mul_of_pos_right

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
