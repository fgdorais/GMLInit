import GMLInit.Data.Nat.Basic
import GMLInit.Data.Nat.IsPos
import GMLInit.Data.Nat.Order
import GMLInit.Data.Nat.Add

namespace Nat

attribute [local eliminator] Nat.recDiagAux

-- assert theorem sub_zero (x : Nat) : x - 0 = x

protected theorem sub_succ' (x y : Nat) : x - (y + 1) = (x - y) - 1 := Nat.sub_succ x y

-- assert theorem zero_sub (x : Nat) : 0 - x = 0

-- assert theorem sub_self (x : Nat) : x - x = 0

protected theorem succ_sub_succ' (x y : Nat) : (x + 1) - (y + 1) = x - y := Nat.succ_sub_succ x y

protected theorem add_sub_add (x y z : Nat) : (x + z) - (y + z) = x - y := by
  induction z with
  | zero => rfl
  | succ z H =>
    calc
    _ = (x + z + 1) - (y + z + 1) := rfl
    _ = (x + z) - (y + z) := by rw [Nat.succ_sub_succ']
    _ = x - y := by rw [H]

protected theorem sub_assoc (x y z : Nat) : (x - y) - z = x - (y + z) := by
  induction z with
  | zero => rfl
  | succ z H => 
    calc
    _ = x - y - z - 1  := by rw [Nat.sub_succ']
    _ = (x - (y + z)) - 1  := by rw [H]
    _ = x - (y + z + 1) := by rw [←Nat.sub_succ']

protected theorem sub_right_comm (x y z : Nat) : (x - y) - z = (x - z) - y := by
  rw [Nat.sub_assoc, Nat.add_comm, ←Nat.sub_assoc]

-- assert theorem add_sub_cancel_left (x y : Nat) : (x + y) - x = y := by

protected theorem add_sub_cancel_right (x y : Nat) : (x + y) - y = x := by
  induction y with
  | zero => rw [Nat.add_zero, Nat.sub_zero]
  | succ y H => 
    calc
    _ = ((x + y) + 1) - (y + 1) := by rw [Nat.add_assoc]
    _ = (x + y) - y := by rw [Nat.add_sub_add]
    _ = x := by rw [H]

protected theorem add_sub_comm (x y : Nat) : x + (y - x) = y + (x - y) := by
  induction x, y with
  | left x => 
    calc
    _ = x + 0 := by rw [Nat.zero_sub]
    _ = 0 + x := by rw [Nat.add_comm]
    _ = 0 + (x - 0) := by rw [Nat.sub_zero]
  | right y => 
    calc
    _ = 0 + y := by rw [Nat.sub_zero]
    _ = y + 0 := by rw [Nat.add_comm]
    _ = y + (0 - y) := by rw [Nat.zero_sub]
  | diag x y H =>
    calc
    _ = (x + 1) + (y - x) := by rw [Nat.succ_sub_succ']
    _ = (x + (y - x)) + 1 := by rw [Nat.succ_add']
    _ = (y + (x - y)) + 1 := by rw [H]
    _ = (y + 1) + (x - y) := by rw [Nat.succ_add']
    _ = (y + 1) + ((x + 1) - (y + 1)) := by rw [Nat.succ_sub_succ']

protected theorem sub_sub_comm (x y : Nat) : x - (x - y) = y - (y - x) :=
  Nat.add_left_cancel' (y + (x - y)) $
  calc
  _ = y + (x - y) + (x - (x - y)) := rfl
  _ = y + ((x - y) + (x - (x - y))) := by rw [Nat.add_assoc]
  _ = y + (x + ((x - y) - x)) := by rw [Nat.add_sub_comm]
  _ = y + (x + ((x - x) - y)) := by rw [Nat.sub_right_comm]
  _ = y + (x + (0 - y)) := by rw [Nat.sub_self]
  _ = y + (x + 0) := by rw [Nat.zero_sub]
  _ = y + x := by rw [Nat.add_zero]
  _ = x + y := by rw [Nat.add_comm]
  _ = x + (y + 0) := by rw [Nat.add_zero]
  _ = x + (y + (0 - x)) := by rw [Nat.zero_sub]
  _ = x + (y + ((y - y) - x)) := by rw [Nat.sub_self]
  _ = x + (y + ((y - x) - y)) := by rw [Nat.sub_right_comm]
  _ = x + ((y - x) + (y - (y - x))) := by rw [Nat.add_sub_comm]
  _ = (x + (y - x)) + (y - (y - x)) := by rw [Nat.add_assoc]
  _ = (y + (x - y)) + (y - (y - x)) := by rw [Nat.add_sub_comm]

protected theorem le_iff_sub_eq_zero (x y : Nat) : x - y = 0 ↔ x ≤ y := by
  induction x, y with
  | left x => rw [Nat.sub_zero, Nat.eq_zero_iff_le_zero]; reflexivity
  | right y => rw [Nat.zero_sub, Nat.eq_zero_iff_le_zero]; constr <;> (intro; apply Nat.zero_le)
  | diag x y H => rw [Nat.succ_sub_succ, Nat.succ_le_succ_iff_le]; exact H

protected theorem le_of_sub_eq_zero {x y : Nat} : x - y = 0 → x ≤ y :=
  (Nat.le_iff_sub_eq_zero x y).mp

-- assert theorem sub_eq_zero_of_le {x y : Nat} : x ≤ y → x - y = 0

protected theorem gt_iff_sub_pos (x y : Nat) : x > y ↔ x - y > 0 := by
  induction x, y with
  | left x => rw [Nat.sub_zero]; reflexivity
  | right y => rw [Nat.zero_sub]; constr <;> (intro; contradiction)
  | diag x y H => 
    calc
    _ ↔ y < x := Nat.succ_lt_succ_iff_lt y x
    _ ↔ x - y > 0 := H
    _ = ((x + 1) - (y + 1) > 0) := by rw [Nat.succ_sub_succ]

protected theorem gt_of_sub_pos {x y : Nat} : x - y > 0 → x > y :=
  (Nat.gt_iff_sub_pos x y).mpr

protected theorem sub_pos_of_gt {x y : Nat} : x > y → x - y > 0 :=
  (Nat.gt_iff_sub_pos x y).mp

protected theorem sub_le_iff_le_add (x y z : Nat) : x - y ≤ z ↔ x ≤ y + z := by
  induction x, y with
  | left x => rw [Nat.sub_zero, Nat.zero_add]; reflexivity
  | right y => rw [Nat.zero_sub]; constr <;> (intro; apply Nat.zero_le)
  | diag x y H => rw [Nat.succ_sub_succ, Nat.succ_add', Nat.succ_le_succ_iff_le]; exact H

protected theorem sub_le_of_le_add' {x y z : Nat} : x ≤ y + z → x - y ≤ z :=
  (Nat.sub_le_iff_le_add x y z).mpr

protected theorem le_add_of_sub_le' {x y z : Nat} : x - y ≤ z → x ≤ y + z :=
  (Nat.sub_le_iff_le_add x y z).mp

protected theorem le_sub_iff_add_le_of_ge (x y z : Nat) (h : y ≥ z) : x ≤ y - z ↔ x + z ≤ y := by
  induction y, z with
  | left y =>
    rw [Nat.sub_zero, Nat.add_zero]
    reflexivity
  | right z =>
    rw [Nat.zero_sub, Nat.eq_zero_of_le_zero h, Nat.add_zero]
    reflexivity
  | diag y z H =>
    rw [Nat.succ_sub_succ', Nat.add_succ', Nat.succ_le_succ_iff_le]
    apply H
    exact Nat.le_of_succ_le_succ' h

-- assert theorem le_sub_of_add_le {x y z : Nat} : x + y ≤ z → x ≤ z - y := by

protected theorem add_le_of_ge_of_le_sub {x y z : Nat} : y ≥ z → x ≤ y - z → x + z ≤ y := by
  intro hge h
  rw [←Nat.le_sub_iff_add_le_of_ge]
  · exact h
  · exact hge

protected theorem sub_lt_iff_lt_add_of_pos (x y z : Nat) (hz : z > 0) : x - y < z ↔ x < y + z := by
  induction x, y with
  | left x =>
    rw [Nat.sub_zero, Nat.zero_add]
    reflexivity
  | right y =>
    rw [Nat.zero_sub]
    constr
    · intro
      transitivity z using LT.lt, LE.le
      · exact hz
      · exact Nat.le_add_left ..
    · intro
      exact hz
  | diag x y H =>
    rw [Nat.succ_sub_succ, Nat.succ_add, Nat.succ_eq, Nat.succ_lt_succ_iff_lt]
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
  | left y => rw [Nat.sub_zero, Nat.add_zero]; reflexivity
  | right z => rw [Nat.zero_sub]; constr <;> (intro; contradiction)
  | diag y z H => rw [Nat.succ_sub_succ, Nat.add_succ, Nat.succ_eq, Nat.succ_lt_succ_iff_lt]; exact H

theorem add_lt_of_lt_sub' {x y z : Nat} : x < y - z → x + z < y :=
  (Nat.lt_sub_iff_add_lt _ _ _).mp

theorem lt_sub_of_add_lt' {x y z : Nat} : x + y < z → x < z - y :=
  (Nat.lt_sub_iff_add_lt _ _ _).mpr

protected theorem sub_le_right (x y : Nat) : x - y ≤ x := by
  rw [Nat.sub_le_iff_le_add]
  exact Nat.le_add_left ..

protected theorem sub_lt_of_pos_of_pos_right {x y : Nat} : x > 0 → y > 0 → x - y < x := by
  intro hx hy
  rw [Nat.sub_lt_iff_lt_add_of_pos]
  · exact Nat.lt_add_left _ _
  · exact hx

protected theorem sub_le_sub_left {x y : Nat} (h : x ≤ y) (z : Nat) : x - z ≤ y - z :=
  Nat.sub_le_of_le_add' $
  calc
  _ ≤ x + (z - y) := by apply Nat.le_add_right
  _ ≤ y + (z - y) := by apply Nat.add_le_add_right h
  _ = z + (y - z) := by rw [Nat.add_sub_comm]

protected theorem sub_le_sub_of_ge_right {x y : Nat} (h : x ≥ y) (z : Nat) : z - x ≤ z - y :=
  Nat.sub_le_of_le_add' $ 
  calc
  _ ≤ z + (y - z) := by apply Nat.le_add_right
  _ = y + (z - y) := by rw [Nat.add_sub_comm]
  _ ≤ x + (z - y) := by apply Nat.add_le_add_right h

protected theorem sub_le_sub_of_le_of_ge {x₁ x₂ y₁ y₂ : Nat} : x₁ ≤ x₂ → y₁ ≥ y₂ → x₁ - y₁ ≤ x₂ - y₂ := by
  intro hx hy
  transitivity (x₂ - y₁)
  · exact Nat.sub_le_sub_left hx ..
  · exact Nat.sub_le_sub_of_ge_right hy ..

protected theorem sub_lt_sub_of_lt_left {x y z : Nat} : x < y → z < y → x - z < y - z := by
  intro hx hz
  apply Nat.lt_sub_of_add_lt
  cases Nat.le_total x z with
  | inl h => rw [Nat.sub_eq_zero_of_le h, Nat.zero_add]; exact hz
  | inr h => rw [Nat.add_comm, Nat.add_sub_comm, Nat.sub_eq_zero_of_le h, Nat.add_zero]; exact hx

protected theorem sub_lt_sub_of_gt_of_lt_right {x y z : Nat} (hx : x > y) (hz : y < z) : z - x < z - y := by
  apply Nat.sub_lt_of_pos_of_lt_add
  · apply Nat.sub_pos_of_gt
    exact hz
  · transitivity (y + (z - y)) using LE.le, LT.lt
    · rw [Nat.add_sub_comm]
      exact Nat.le_add_right ..
    · rw [Nat.add_comm]
      exact Nat.add_lt_add_left hx ..

end Nat
