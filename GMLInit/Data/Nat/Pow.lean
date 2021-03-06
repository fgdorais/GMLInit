import GMLInit.Data.Nat.Basic
import GMLInit.Data.Nat.IsPos
import GMLInit.Data.Nat.Order
import GMLInit.Data.Nat.Succ
import GMLInit.Data.Nat.Add
import GMLInit.Data.Nat.Sub
import GMLInit.Data.Nat.Mul

namespace Nat

attribute [local eliminator] Nat.recDiagAux

-- assert theorem pow_zero (x : Nat) : x ^ 0 = 1

protected theorem pow_succ' (x y : Nat) : x ^ (y + 1) = x ^ y * x := Nat.pow_succ x y

protected theorem pow_one (x : Nat) : x ^ 1 = x := 
  calc
  _ = x ^ 0 * x := by rw [Nat.pow_succ]
  _ = 1 * x := by rw [Nat.pow_zero]
  _ = x := by rw [Nat.one_mul]

protected theorem one_pow (x : Nat) : 1 ^ x = 1 := by
  induction x with
  | zero => rw [Nat.pow_zero]
  | succ x H => 
    calc
    _ = 1 ^ x * 1 := by rw [Nat.pow_succ]
    _ = 1 * 1 := by rw [H]
    _ = 1 := by rw [Nat.mul_one]

protected theorem zero_pow_succ (x : Nat) : 0 ^ (x + 1) = 0 := 
  calc
  _ = 0 ^ x * 0 := by rw [Nat.pow_succ]
  _ = 0 := by rw [Nat.mul_zero]

protected theorem zero_pow_of_nonzero {x : Nat} : x ≠ 0 → 0 ^ x = 0 := by
  cases x with
  | zero => intro; contradiction
  | succ x => intro; rw [Nat.zero_pow_succ]

protected theorem zero_pow (x : Nat) : (h : x ≠ 0 := by nat_is_nonzero) → 0 ^ x = 0 := Nat.zero_pow_of_nonzero

protected theorem pow_add (x y z : Nat) : x ^ (y + z) = x ^ y * x ^ z := by
  induction z with
  | zero => rw [Nat.pow_zero, Nat.add_zero, Nat.mul_one]
  | succ z H => rw [Nat.pow_succ, Nat.add_succ, Nat.pow_succ, H, Nat.mul_assoc]

protected theorem mul_pow (x y z : Nat) : (x * y) ^ z = x ^ z * y ^ z := by
  induction z with
  | zero => rw [Nat.pow_zero, Nat.pow_zero, Nat.pow_zero, Nat.mul_one]
  | succ z H => rw [Nat.pow_succ, Nat.pow_succ, Nat.pow_succ, H, Nat.mul_cross_comm]

protected theorem pow_assoc (x y z : Nat) : (x ^ y) ^ z = x ^ (y * z) := by
  induction z with
  | zero => rw [Nat.pow_zero, Nat.mul_zero, Nat.pow_zero]
  | succ z H => rw [Nat.pow_succ, Nat.mul_succ, Nat.pow_add, H]

protected theorem pow_right_comm (x y z : Nat) : (x ^ y) ^ z = (x ^ z) ^ y := by
  rw [Nat.pow_assoc, Nat.mul_comm, ←Nat.pow_assoc]

-- assert theorem pos_pow_of_pos {x : Nat} (y : Nat) : x > 0 → x ^ y > 0

protected theorem le_pow_right_of_pos {x y : Nat} : y > 0 → x ≤ x ^ y := by
  cases x, y with
  | left x => intro; contradiction
  | right y => intro; apply Nat.zero_le
  | diag x y =>
    intro
    transitivity (1 * (x + 1)) using Eq, LE.le
    · rw [Nat.one_mul]
    · rw [Nat.pow_succ]
      apply Nat.mul_le_mul_right
      apply Nat.succ_le_of_lt
      apply Nat.pos_pow_of_pos
      apply Nat.zero_lt_succ

protected theorem le_pow_right (x y : Nat) : (h : y > 0 := by nat_is_pos) → x ≤ x ^ y := Nat.le_pow_right_of_pos

protected theorem pow_le_pow_left {x y : Nat} (h : x ≤ y) (z : Nat) : x ^ z ≤ y ^ z :=
  Nat.pow_le_pow_of_le_left h z

protected theorem pow_le_pow_of_pos_left {x y : Nat} (h : x ≤ y) {z : Nat} : z > 0 → z ^ x ≤ z ^ y :=
  λ hz => Nat.pow_le_pow_of_le_right hz h

protected theorem pow_lt_pow_of_pos_right {x y : Nat} (h : x < y) {z : Nat} : z > 0 → x ^ z < y ^ z := by
  cases z with
  | zero => intro; contradiction
  | succ z =>
    intro
    rw [Nat.pow_succ, Nat.pow_succ]
    apply Nat.mul_lt_mul_of_le_of_lt
    · apply Nat.pow_le_pow_left
      apply Nat.le_of_lt
      exact h
    · exact h
    · apply Nat.pos_pow_of_pos
      transitivity x using LE.le, LT.lt
      · apply Nat.zero_le
      · exact h

protected theorem pow_lt_pow_of_gt_one_left {x y : Nat} (h : x < y) {z : Nat} : z > 1 → z ^ x < z ^ y := by
  induction x, y with
  | left x => intro; contradiction
  | right y =>
    intro hz
    transitivity z using LT.lt, LE.le
    · rw [Nat.pow_zero]
      exact hz
    · exact Nat.le_pow_right _ _
  | diag x y H =>
    intro hz
    rw [Nat.pow_succ, Nat.pow_succ]
    apply Nat.mul_lt_mul_of_pos_right
    apply H
    · exact Nat.lt_of_succ_lt_succ h
    · exact hz
    · transitivity 1 using LT.lt
      · exact Nat.zero_lt_one
      · exact hz

end Nat
