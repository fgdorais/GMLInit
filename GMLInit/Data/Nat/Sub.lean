import GMLInit.Data.Nat.Basic
import GMLInit.Data.Nat.Order
import GMLInit.Data.Nat.Add

namespace Nat

-- assert theorem sub_zero (x : Nat) : x - 0 = x

-- assert theorem sub_succ (x y : Nat) : x - (y + 1) = (x - y) - 1

protected theorem zero_sub (x : Nat) : 0 - x = 0 := by
  induction x using Nat.recAuxOn with
  | zero => rfl
  | succ x H => rw [Nat.sub_succ, H]; rfl

-- assert theorem sub_self (x : Nat) : x - x = 0

-- assert theorem succ_sub_succ (x y : Nat) : (x + 1) - (y + 1) = x - y

protected theorem add_sub_add (x y z : Nat) : (x + z) - (y + z) = x - y := by
  induction z with
  | zero => rfl
  | succ z H => simp only [Nat.add_succ, Nat.succ_sub_succ]; rw [H]

protected theorem sub_assoc (x y z : Nat) : (x - y) - z = x - (y + z) := by
  induction z with
  | zero => rfl
  | succ z H => simp only [Nat.add_succ, Nat.sub_succ]; rw [H]

protected theorem sub_right_comm (x y z : Nat) : (x - y) - z = (x - z) - y := by
  rw [Nat.sub_assoc, Nat.add_comm, ←Nat.sub_assoc]

protected theorem add_sub_cancel_left (x y : Nat) : (x + y) - x = y := by
  induction x using Nat.recAuxOn with
  | zero => simp only [Nat.zero_add, Nat.sub_zero, eq_self]
  | succ x H => calc
    _ = ((x + y) + 1) - (x + 1) := by rw [Nat.succ_add x y, Nat.simp_succ]
    _ = (x + y) - x := by rw [←Nat.simp_succ, ← Nat.simp_succ, Nat.succ_sub_succ]
    _ = y := by rw [H]

protected theorem add_sub_cancel_right (x y : Nat) : (x + y) - y = x := by
  induction y using Nat.recAuxOn with
  | zero => simp only [Nat.add_zero, Nat.sub_zero, eq_self]
  | succ y H => calc
    _ = ((x + y) + 1) - (y + 1) := by rw [Nat.add_succ x y, Nat.simp_succ]
    _ = (x + y) - y := by rw [←Nat.simp_succ, ←Nat.simp_succ, Nat.succ_sub_succ (x + y) y]
    _ = x := by rw [H]

protected theorem add_sub_comm (x y : Nat) : x + (y - x) = y + (x - y) := by
  induction x, y using Nat.recDiagAuxOn with
  | left x => simp only [Nat.sub_zero, Nat.zero_sub, Nat.add_zero, Nat.zero_add, eq_self]
  | right y => simp only [Nat.sub_zero, Nat.zero_sub, Nat.add_zero, Nat.zero_add, eq_self]
  | diag x y H => calc
    _ = (x + 1) + (y - x) := by rw [Nat.succ_sub_succ]
    _ = (x + (y - x)) + 1 := by rw [Nat.succ_add, Nat.simp_succ]
    _ = (y + (x - y)) + 1 := by rw [H]
    _ = (y + 1) + (x - y) := by rw [Nat.succ_add, Nat.simp_succ]
    _ = (y + 1) + ((x + 1) - (y + 1)) := by rw [Nat.succ_sub_succ]

protected theorem le_iff_sub_eq_zero (x y : Nat) : x - y = 0 ↔ x ≤ y := by
  induction x, y using Nat.recDiagAuxOn with
  | left x => rw [Nat.sub_zero, Nat.eq_zero_iff_le_zero]; reflexivity
  | right y => simp [Nat.zero_sub, Nat.zero_le]
  | diag x y H => rw [Nat.succ_sub_succ, Nat.succ_le_succ_iff_le]; exact H

protected theorem le_of_sub_eq_zero {x y : Nat} : x - y = 0 → x ≤ y :=
  (Nat.le_iff_sub_eq_zero x y).mp

protected theorem sub_eq_zero_of_le {x y : Nat} : x ≤ y → x - y = 0 :=
  (Nat.le_iff_sub_eq_zero x y).mpr

protected theorem gt_iff_sub_pos (x y : Nat) : x > y ↔ x - y > 0 := by
  induction x, y using Nat.recDiagAuxOn with
  | left x => rw [Nat.sub_zero]; reflexivity
  | right y => simp [Nat.zero_sub]; apply Nat.not_lt_zero
  | diag x y H => calc
    _ ↔ y < x := Nat.succ_lt_succ_iff_lt y x
    _ ↔ x - y > 0 := H
    _ = ((x + 1) - (y + 1) > 0) := by rw [Nat.succ_sub_succ]

protected theorem gt_of_sub_pos {x y : Nat} : x - y > 0 → x > y :=
  (Nat.gt_iff_sub_pos x y).mpr

protected theorem sub_pos_of_gt {x y : Nat} : x > y → x - y > 0 :=
  (Nat.gt_iff_sub_pos x y).mp

protected theorem sub_le_iff_le_add (x y z : Nat) : x - y ≤ z ↔ x ≤ y + z := by
  induction x, y using Nat.recDiagAuxOn with
  | left x => simp only [Nat.sub_zero, Nat.zero_add]; reflexivity
  | right y => simp only [Nat.zero_sub, Nat.zero_le]
  | diag x y H => simp only [Nat.succ_sub_succ, Nat.succ_add, Nat.succ_le_succ_iff_le, Nat.simp_succ]; exact H

protected theorem sub_le_of_le_add {x y z : Nat} : x ≤ y + z → x - y ≤ z := by
  intro h
  rw [Nat.sub_le_iff_le_add]
  exact h

protected theorem le_add_of_sub_le {x y z : Nat} : x - y ≤ z → x ≤ y + z := by
  intro h
  rw [←Nat.sub_le_iff_le_add]
  exact h

protected theorem le_sub_iff_add_le_of_ge (x y z : Nat) (h : y ≥ z) : x ≤ y - z ↔ x + z ≤ y := by
  induction y, z using Nat.recDiagAuxOn with
  | left y =>
    rw [Nat.sub_zero, Nat.add_zero]
    reflexivity
  | right z =>
    rw [Nat.zero_sub, Nat.eq_zero_of_le_zero h, Nat.add_zero]
    reflexivity
  | diag y z H =>
    rw [Nat.succ_sub_succ, Nat.add_succ, Nat.simp_succ, Nat.succ_le_succ_iff_le]
    apply H
    apply Nat.le_of_succ_le_succ
    exact h

protected theorem le_sub_of_add_le {x y z : Nat} : x + y ≤ z → x ≤ z - y := by
  cases Nat.le_total z y with
  | inl hle =>
    intro h
    rw [Nat.sub_eq_zero_of_le hle]
    apply Nat.le_of_add_le_add_right y
    rw [Nat.zero_add]
    transitivity z
    · exact h
    · exact hle
  | inr hge =>
    intro h
    rw [Nat.le_sub_iff_add_le_of_ge]
    exact h
    exact hge

protected theorem add_le_of_ge_of_le_sub {x y z : Nat} : y ≥ z → x ≤ y - z → x + z ≤ y := by
  intro hge h
  rw [←Nat.le_sub_iff_add_le_of_ge]
  · exact h
  · exact hge

protected theorem sub_lt_iff_lt_add_of_pos (x y z : Nat) (hz : z > 0) : x - y < z ↔ x < y + z := by
  induction x, y using Nat.recDiagAuxOn with
  | left x =>
    rw [Nat.sub_zero, Nat.zero_add]
    reflexivity
  | right y =>
    rw [Nat.zero_sub]
    constr
    · intro
      transitivity z using LT.lt, LE.le
      · exact hz
      · apply Nat.le_add_left
    · intro
      exact hz
  | diag x y H =>
    rw [Nat.succ_sub_succ, Nat.succ_add, Nat.simp_succ, Nat.succ_lt_succ_iff_lt]
    apply H

protected theorem sub_lt_of_pos_of_lt_add {x y z : Nat} (hpos : y > 0) : x < y + z → x - z < y := by
  intro h
  rw [Nat.sub_lt_iff_lt_add_of_pos]
  · rw [Nat.add_comm]
    exact h
  · exact hpos

protected theorem lt_add_of_sub_lt {x y z : Nat} : x - y < z → x < y + z := by
  cases z using Nat.recAuxOn with
  | zero =>
    intro
    contradiction
  | succ z =>
    intro h
    rw [←Nat.sub_lt_iff_lt_add_of_pos]
    · exact h
    · apply Nat.zero_lt_succ

protected theorem lt_sub_iff_add_lt (x y z : Nat) : x < y - z ↔ x + z < y := by
  induction y, z using Nat.recDiagAuxOn with
  | left y => rw [Nat.sub_zero, Nat.add_zero]; reflexivity
  | right z => simp only [Nat.zero_sub, Nat.not_lt_zero]
  | diag y z H => rw [Nat.succ_sub_succ, Nat.add_succ, Nat.simp_succ, Nat.succ_lt_succ_iff_lt]; exact H

protected theorem lt_sub_of_add_lt {x y z : Nat} : x + y < z → x < z - y := by
  intro h
  rw [Nat.lt_sub_iff_add_lt]
  exact h

protected theorem add_lt_of_lt_sub {x y z : Nat} : x < y - z → x + z < y := by
  intro h
  rw [←Nat.lt_sub_iff_add_lt]
  exact h

protected theorem sub_le_right (x y : Nat) : x - y ≤ x := by
  rw [Nat.sub_le_iff_le_add]
  apply Nat.le_add_left

protected theorem sub_lt_of_pos_of_pos_right {x y : Nat} : x > 0 → y > 0 → x - y < x := by
  intro hx hy
  rw [Nat.sub_lt_iff_lt_add_of_pos]
  · apply Nat.lt_add_of_pos_left
    exact hy
  · exact hx

protected theorem sub_le_sub_left {x y : Nat} (h : x ≤ y) (z : Nat) : x - z ≤ y - z :=
  Nat.sub_le_of_le_add $ calc
  _ ≤ x + (z - y) := by apply Nat.le_add_right
  _ ≤ y + (z - y) := by apply Nat.add_le_add_right h
  _ = z + (y - z) := by rw [Nat.add_sub_comm]

protected theorem sub_le_sub_of_ge_right {x y : Nat} (h : x ≥ y) (z : Nat) : z - x ≤ z - y :=
  Nat.sub_le_of_le_add $ calc
  _ ≤ z + (y - z) := by apply Nat.le_add_right
  _ = y + (z - y) := by rw [Nat.add_sub_comm]
  _ ≤ x + (z - y) := by apply Nat.add_le_add_right h

protected theorem sub_le_sub_of_le_of_ge {x₁ x₂ y₁ y₂ : Nat} : x₁ ≤ x₂ → y₁ ≥ y₂ → x₁ - y₁ ≤ x₂ - y₂ := by
  intro hx hy
  transitivity (x₂ - y₁)
  · apply Nat.sub_le_sub_left
    exact hx
  · apply Nat.sub_le_sub_of_ge_right
    exact hy

protected theorem sub_lt_sub_of_lt_left {x y z : Nat} : x < y → z < y → x - z < y - z :=
  λ hx hz => Nat.lt_sub_of_add_lt $ match Nat.le_total x z with
  | Or.inl h => by rw [Nat.sub_eq_zero_of_le h, Nat.zero_add]; exact hz
  | Or.inr h => by rw [Nat.add_comm, Nat.add_sub_comm, Nat.sub_eq_zero_of_le h, Nat.add_zero]; exact hx

protected theorem sub_lt_sub_of_gt_of_lt_right {x y z : Nat} (hx : x > y) (hz : y < z) : z - x < z - y := by
  apply Nat.sub_lt_of_pos_of_lt_add
  · apply Nat.sub_pos_of_gt
    exact hz
  · transitivity (y + (z - y)) using LE.le, LT.lt
    · rw [Nat.add_sub_comm]
      apply Nat.le_add_right
    · rw [Nat.add_comm]
      apply Nat.add_lt_add_left
      exact hx

end Nat
