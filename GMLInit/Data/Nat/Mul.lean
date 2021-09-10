import GMLInit.Data.Nat.Basic
import GMLInit.Data.Nat.Order
import GMLInit.Data.Nat.Succ
import GMLInit.Data.Nat.Add
import GMLInit.Data.Nat.Sub

namespace Nat

-- assert theorem mul_zero (x : Nat) : x * 0 = 0

-- assert theorem zero_mul (x : Nat) : 0 * x = 0

-- assert theorem mul_one (x : Nat) : x * 1 = x

-- assert theorem one_mul (x : Nat) : 1 * x = x

-- assert theorem mul_succ (x y : Nat) : x * (y + 1) = x * y + x

-- assert theorem succ_mul (x y : Nat) : (x + 1) * y = x * y + y

protected theorem mul_pred (x y : Nat) : x * (y - 1) = x * y - x := by
  cases y using Nat.casesAuxOn with
  | zero => simp only [Nat.pred_zero, Nat.mul_zero, Nat.zero_sub, eq_self]
  | succ y => simp only [Nat.pred_succ, Nat.mul_succ, Nat.add_sub_cancel_right, eq_self]

protected theorem pred_mul (x y : Nat) : (x - 1) * y = x * y - y := by
  cases x using Nat.casesAuxOn with
  | zero => simp only [Nat.pred_zero, Nat.zero_mul, Nat.zero_sub, eq_self]
  | succ x => simp only [Nat.pred_succ, Nat.succ_mul, Nat.add_sub_cancel_right, eq_self]

-- assert theorem mul_comm (x y : Nat) : x * y = y * x

-- assert theorem mul_assoc (x y z : Nat) : (x * y) * z = x * (y * z)

-- assert theorem mul_left_comm (x y z : Nat) : x * (y * z) = y * (x * z)

protected theorem mul_right_comm (x y z : Nat) : (x * y) * z = (x * z) * y := calc
  _ = x * (y * z) := by rw [Nat.mul_assoc]
  _ = x * (z * y) := by rw [Nat.mul_comm y z]
  _ = (x * z) * y := by rw [Nat.mul_assoc]

protected theorem mul_cross_comm (x₁ x₂ y₁ y₂ : Nat) : (x₁ * x₂) * (y₁ * y₂) = (x₁ * y₁) * (x₂ * y₂) := calc
  _ = x₁ * (x₂ * (y₁ * y₂)) := by rw [Nat.mul_assoc]
  _ = x₁ * (y₁ * (x₂ * y₂)) := by rw [Nat.mul_left_comm x₂ y₁ y₂]
  _ = (x₁ * y₁) * (x₂ * y₂) := by rw [Nat.mul_assoc]

-- assert theorem mul_add (x y z : Nat) : x * (y + z) = x * y + x * z

-- assert theorem add_mul (x y z : Nat) : (x + y) * z = x * z + y * z

protected theorem mul_sub (x y z : Nat) : x * (y - z) = x * y - x * z := by
  induction y, z using Nat.recDiagAuxOn with
  | left y => simp only [Nat.sub_zero, Nat.mul_zero, eq_self]
  | right z => simp only [Nat.zero_sub, Nat.mul_zero, eq_self]
  | diag y z H => calc
    _ = x * (y - z) := by rw [Nat.succ_sub_succ]
    _ = x * y - x * z := by rw [H]
    _ = (x * y + x) - (x * z + x) := by rw [Nat.add_sub_add]
    _ = x * (y + 1) - x * (z + 1) := by rw [Nat.mul_succ, Nat.mul_succ]

protected theorem sub_mul (x y z : Nat) : (x - y) * z = x * z - y * z := by
  induction x, y using Nat.recDiagAuxOn with
  | left x => simp only [Nat.sub_zero, Nat.zero_mul, eq_self]
  | right y => simp only [Nat.zero_sub, Nat.zero_mul, eq_self]
  | diag x y H => calc
    _ = (x - y) * z := by rw [Nat.succ_sub_succ]
    _ = x * z - y * z := by rw [H]
    _ = (x * z + z) - (y * z + z) := by rw [Nat.add_sub_add]
    _ = (x + 1) * z - (y + 1) * z := by rw [Nat.succ_mul, Nat.succ_mul]

protected theorem le_mul_of_pos_left (x : Nat) {y : Nat} : y > 0 → x ≤ y * x := by
  cases y using Nat.casesAuxOn with
  | zero => intro; contradiction
  | succ y => intro; rw [Nat.succ_mul]; apply Nat.le_add_left

protected theorem le_mul_of_pos_right (x : Nat) {y : Nat} : y > 0 → x ≤ x * y := by
  induction y using Nat.recAuxOn with
  | zero => intro; contradiction
  | succ y H => intro; rw [Nat.mul_succ]; apply Nat.le_add_left

protected theorem lt_mul_of_gt_one_of_pos_left {x y : Nat} : x > 0 → y > 1 → x < y * x := by
  intro hx hy
  cases y using Nat.casesAuxOn with
  | zero => contradiction
  | succ y =>
    rw [Nat.succ_mul]
    apply Nat.lt_add_of_pos_left
    apply Nat.mul_pos
    · apply Nat.lt_of_succ_lt_succ
      exact hy
    · exact hx

protected theorem lt_mul_of_gt_one_of_pos_right {x y : Nat} : x > 0 → y > 1 → x < x * y := by
  intro hx hy
  cases y using Nat.casesAuxOn with
  | zero => contradiction
  | succ y =>
    rw [Nat.mul_succ]
    apply Nat.lt_add_of_pos_left
    apply Nat.mul_pos
    · exact hx
    · apply Nat.lt_of_succ_lt_succ
      exact hy

-- assert theorem mul_le_mul {x₁ x₂ y₁ y₂ : Nat} : x₁ ≤ x₂ → y₁ ≤ y₂ → x₁ * y₁ ≤ x₂ * y₂

-- assert theorem mul_le_mul_left {x y : Nat} (z : Nat) : x ≤ y → z * x ≤ z * y

-- assert theorem mul_le_mul_right {x y : Nat} (z : Nat) : x ≤ y → x * z ≤ y * z

-- assert theorem mul_lt_mul_of_pos_left {x y z : Nat} : x < y → z > 0 → z * x < z * y

-- assert theorem mul_lt_mul_of_pos_right {x y z : Nat} : x < y → z > 0 → z * x < z * y

protected theorem mul_lt_mul {x₁ x₂ y₁ y₂ : Nat} : x₁ < x₂ → y₁ < y₂ → x₁ * y₁ < x₂ * y₂ := by
  intro hx hy
  transitivity (x₂ * y₁) using LE.le, LT.lt
  · apply Nat.mul_le_mul_right
    apply Nat.le_of_lt
    exact hx
  · apply Nat.mul_lt_mul_of_pos_left
    · exact hy
    · transitivity x₁ using LE.le, LT.lt
      · apply Nat.zero_le
      · exact hx

protected theorem mul_lt_mul_of_le_of_lt_of_pos {x₁ x₂ y₁ y₂ : Nat} : x₁ ≤ x₂ → y₁ < y₂ → x₂ > 0 → x₁ * y₁ < x₂ * y₂ := by
  intro hx hy hpos
  transitivity (x₂ * y₁) using LE.le, LT.lt
  · apply Nat.mul_le_mul_right
    exact hx
  · apply Nat.mul_lt_mul_of_pos_left
    · exact hy
    · exact hpos

protected theorem mul_lt_mul_of_lt_of_le_of_pos {x₁ x₂ y₁ y₂ : Nat} : x₁ < x₂ → y₁ ≤ y₂ → y₂ > 0 → x₁ * y₁ < x₂ * y₂ := by
  intro hx hy hpos
  transitivity (x₁ * y₂) using LE.le, LT.lt
  · apply Nat.mul_le_mul_left
    exact hy
  · apply Nat.mul_lt_mul_of_pos_right
    · exact hx
    · exact hpos

protected theorem le_of_mul_le_mul_of_pos_left {x y z : Nat} : x > 0 → x * y ≤ x * z → y ≤ z := by
  intro hx hxyz
  by_cases y > z with
  | isTrue h =>
    absurd hxyz
    apply Nat.not_le_of_gt
    apply Nat.mul_lt_mul_of_pos_left
    · exact h
    · exact hx
  | isFalse h =>
    apply Nat.le_of_not_gt
    exact h

protected theorem le_of_mul_le_mul_of_pos_right {x y z} : x > 0 → y * x ≤ z * x → y ≤ z := by
  intro hx hxyz
  by_cases y > z with
  | isTrue h =>
    absurd hxyz
    apply Nat.not_le_of_gt
    apply Nat.mul_lt_mul_of_pos_right
    · exact h
    · exact hx
  | isFalse h =>
    apply Nat.le_of_not_gt
    exact h

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
