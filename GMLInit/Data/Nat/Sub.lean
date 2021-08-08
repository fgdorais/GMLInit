import GMLInit.Data.Nat.Basic
import GMLInit.Data.Nat.Order
import GMLInit.Data.Nat.Add

namespace Nat

-- assert lemma sub_zero (x : Nat) : x - 0 = x

-- assert lemma sub_succ (x y : Nat) : x - (y + 1) = (x - y) - 1

protected lemma zero_sub (x : Nat) : 0 - x = 0 := by
  induction x using Nat.recAuxOn with
  | zero => rfl
  | succ x H => rw [Nat.sub_succ, H]; rfl

-- assert lemma sub_self (x : Nat) : x - x = 0

-- assert lemma succ_sub_succ (x y : Nat) : (x + 1) - (y + 1) = x - y

protected lemma add_sub_add (x y z : Nat) : (x + z) - (y + z) = x - y := by
  induction z with
  | zero => rfl
  | succ z H => simp only [Nat.add_succ, Nat.succ_sub_succ]; rw [H]

protected lemma sub_assoc (x y z : Nat) : (x - y) - z = x - (y + z) := by
  induction z with
  | zero => rfl
  | succ z H => simp only [Nat.add_succ, Nat.sub_succ]; rw [H]

protected lemma sub_right_comm (x y z : Nat) : (x - y) - z = (x - z) - y := by
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

protected lemma sub_le_iff_le_add : ∀ (x y z : Nat), x - y ≤ z ↔ x ≤ y + z
| 0, y, z => by simp only [Nat.zero_sub, Nat.zero_le]
| x, 0, z => by simp only [Nat.sub_zero, Nat.zero_add]; reflexivity
| x + 1, y + 1, z => by
  simp only [Nat.succ_sub_succ, Nat.succ_add]
  rw [Nat.sub_le_iff_le_add]
  split
  exact Nat.succ_le_succ
  exact Nat.le_of_succ_le_succ

protected lemma lt_sub_iff_add_lt (x y z : Nat) : z < x - y ↔ y + z < x := by
  rw [Nat.lt_iff_not_ge]
  rw [Nat.lt_iff_not_ge]
  apply Iff.mt
  symmetry
  exact Nat.sub_le_iff_le_add x y z

protected lemma le_sub_of_add_le : ∀ {x y z : Nat}, x ≥ y + z → x - y ≥ z
| 0, y, z => by
  simp only [Nat.zero_sub]
  intro h
  transitivity (y + z) using LE.le
  exact Nat.le_add_left z y
  exact h
| x, 0, z => by
  simp only [Nat.zero_add, Nat.sub_zero]
  exact id
| x + 1, y + 1, z => by
  simp only [Nat.succ_add, Nat.succ_sub_succ]
  intro h
  apply Nat.le_sub_of_add_le
  exact Nat.le_of_succ_le_succ h

end Nat
