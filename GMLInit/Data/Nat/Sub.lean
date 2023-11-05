import GMLInit.Data.Nat.Basic
import GMLInit.Data.Nat.IsPos
import GMLInit.Data.Nat.Order
import GMLInit.Data.Nat.Add

namespace Nat

attribute [local eliminator] Nat.recDiagAux

-- assert theorem sub_zero (x : Nat) : x - 0 = x

protected theorem sub_succ' (x y : Nat) : x - (y + 1) = (x - y) - 1 := Nat.sub_succ ..

-- assert theorem zero_sub (x : Nat) : 0 - x = 0

-- assert theorem sub_self (x : Nat) : x - x = 0

protected theorem succ_sub_succ' (x y : Nat) : (x + 1) - (y + 1) = x - y := Nat.succ_sub_succ ..

@[deprecated Nat.add_sub_add_right]
protected theorem add_sub_add (x y z : Nat) : (x + z) - (y + z) = x - y := Nat.add_sub_add_right ..

@[deprecated Nat.sub_sub]
protected theorem sub_assoc (x y z : Nat) : (x - y) - z = x - (y + z) := Nat.sub_sub ..

-- assert theorem sub_right_comm (x y z : Nat) : (x - y) - z = (x - z) - y

-- assert theorem add_sub_cancel_left (x y : Nat) : (x + y) - x = y

-- assert theorem add_sub_cancel_right (x y : Nat) : (x + y) - y = x

protected theorem add_sub_comm (x y : Nat) : x + (y - x) = y + (x - y) := by
  rw [Nat.add_comm x, Nat.add_comm y, Nat.sub_add_eq_max, Nat.sub_add_eq_max, Nat.max_comm]

protected theorem sub_sub_comm (x y : Nat) : x - (x - y) = y - (y - x) := by
  rw [Nat.sub_sub_eq_min, Nat.sub_sub_eq_min, Nat.min_comm]

@[deprecated Nat.sub_eq_zero_iff_le]
protected theorem le_iff_sub_eq_zero (x y : Nat) : x - y = 0 ↔ x ≤ y := Nat.sub_eq_zero_iff_le

-- assert theorem le_of_sub_eq_zero {x y : Nat} : x - y = 0 → x ≤ y

-- assert theorem sub_eq_zero_of_le {x y : Nat} : x ≤ y → x - y = 0

-- assert theorem sub_pos_iff_lt (x y : Nat) : x > y ↔ x - y > 0 := sorry

-- assert theorem lt_of_sub_pos {x y : Nat} : x - y > 0 → x > y := (Nat.sub_pos_iff_lt _ _).2

@[deprecated Nat.sub_pos_of_lt]
protected theorem sub_pos_of_gt {x y : Nat} : x > y → x - y > 0 := Nat.sub_pos_of_lt

protected theorem sub_le_of_le_add' {x y z : Nat} : x ≤ y + z → x - y ≤ z := Nat.sub_le_iff_le_add'.2

protected theorem le_add_of_sub_le' {x y z : Nat} : x - y ≤ z → x ≤ y + z := Nat.sub_le_iff_le_add'.1


@[deprecated Nat.le_sub_iff_add_le]
protected theorem le_sub_iff_add_le_of_ge (x y z : Nat) (h : y ≥ z) : x ≤ y - z ↔ x + z ≤ y := Nat.le_sub_iff_add_le h

-- assert theorem le_sub_of_add_le {x y z : Nat} : x + y ≤ z → x ≤ z - y

@[deprecated Nat.add_le_of_le_sub]
protected theorem add_le_of_ge_of_le_sub {x y z : Nat} : y ≥ z → x ≤ y - z → x + z ≤ y := Nat.add_le_of_le_sub


protected theorem sub_lt_iff_lt_add_of_pos (x y z : Nat) (hz : z > 0) : x - y < z ↔ x < y + z := by
  induction x, y with
  | zero_right x =>
    rw [Nat.sub_zero, Nat.zero_add]
  | zero_left y =>
    rw [Nat.zero_sub]
    constructor
    · intro
      transitivity z using LT.lt, LE.le
      · exact hz
      · exact Nat.le_add_left ..
    · intro
      exact hz
  | succ_succ x y H =>
    rw [Nat.succ_sub_succ, Nat.succ_add, Nat.succ_eq, Nat.succ_lt_succ_iff]
    apply H

protected theorem sub_lt_of_pos_of_lt_add {x y z : Nat} (hpos : y > 0) : x < y + z → x - z < y := by
  intro h
  rw [Nat.sub_lt_iff_lt_add_of_pos]
  · rw [Nat.add_comm]
    exact h
  · exact hpos

protected theorem lt_add_of_sub_lt {x y z : Nat} : x - y < z → x < y + z := by
  cases z with
  | zero =>
    intro
    contradiction
  | succ z =>
    intro h
    rw [←Nat.sub_lt_iff_lt_add_of_pos]
    · exact h
    · exact Nat.zero_lt_succ ..

protected theorem lt_sub_iff_add_lt (x y z : Nat) : x < y - z ↔ x + z < y := by
  induction y, z with
  | zero_right y => rw [Nat.sub_zero, Nat.add_zero]
  | zero_left z => rw [Nat.zero_sub]; constructor <;> (intro; contradiction)
  | succ_succ y z H => rw [Nat.succ_sub_succ, Nat.add_succ, Nat.succ_eq, Nat.succ_lt_succ_iff]; exact H

theorem add_lt_of_lt_sub' {x y z : Nat} : x < y - z → x + z < y :=
  (Nat.lt_sub_iff_add_lt _ _ _).mp

theorem lt_sub_of_add_lt' {x y z : Nat} : x + y < z → x < z - y :=
  (Nat.lt_sub_iff_add_lt _ _ _).mpr

protected theorem sub_le_right (x y : Nat) : x - y ≤ x := by
  rw [Nat.sub_le_iff_le_add]
  exact Nat.le_add_right ..

protected theorem sub_lt_of_pos_of_pos_right {x y : Nat} : x > 0 → y > 0 → x - y < x := by
  intro hx hy
  rw [Nat.sub_lt_iff_lt_add_of_pos]
  · exact Nat.lt_add_of_pos_left hy
  · exact hx

-- assert theorem sub_le_sub_left {x y : Nat} (h : x ≤ y) (z : Nat) : x - z ≤ y - z

@[deprecated Nat.sub_le_sub_left]
protected theorem sub_le_sub_of_ge_right {x y : Nat} (h : x ≥ y) (z : Nat) : z - x ≤ z - y :=
  Nat.sub_le_sub_left h _

protected theorem sub_le_sub_of_le_of_ge {x₁ x₂ y₁ y₂ : Nat} : x₁ ≤ x₂ → y₁ ≥ y₂ → x₁ - y₁ ≤ x₂ - y₂ := by
  intro hx hy
  transitivity (x₂ - y₁)
  · exact Nat.sub_le_sub_right hx _
  · exact Nat.sub_le_sub_left hy _

protected theorem sub_lt_sub_of_lt_left {x y z : Nat} : x < y → z < y → x - z < y - z := by
  intro hx hz
  apply Nat.lt_sub_of_add_lt
  cases Nat.le_total x z with
  | inl h => rw [Nat.sub_eq_zero_of_le h, Nat.zero_add]; exact hz
  | inr h => rw [Nat.add_comm, Nat.add_sub_comm, Nat.sub_eq_zero_of_le h, Nat.add_zero]; exact hx

protected theorem sub_lt_sub_of_gt_of_lt_right {x y z : Nat} (hx : x > y) (hz : y < z) : z - x < z - y := by
  apply Nat.sub_lt_of_pos_of_lt_add
  · apply Nat.sub_pos_of_lt
    exact hz
  · transitivity (y + (z - y)) using LE.le, LT.lt
    · rw [Nat.add_sub_comm]
      exact Nat.le_add_right ..
    · rw [Nat.add_comm]
      exact Nat.add_lt_add_left hx ..

end Nat
