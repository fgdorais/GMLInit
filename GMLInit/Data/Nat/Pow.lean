import GMLInit.Data.Nat.Basic
import GMLInit.Data.Nat.IsPos
import GMLInit.Data.Nat.Order

namespace Nat

attribute [local induction_eliminator] Nat.recDiagAux

protected theorem zero_pow_succ (x : Nat) : 0 ^ (x + 1) = 0 :=
  calc
  _ = 0 ^ x * 0 := by rw [Nat.pow_succ]
  _ = 0 := by rw [Nat.mul_zero]

protected theorem zero_pow_of_nonzero {x : Nat} : x ≠ 0 → 0 ^ x = 0 := by
  cases x with
  | zero => intro; contradiction
  | succ x => intro; rw [Nat.zero_pow_succ]

protected theorem pow_assoc (x y z : Nat) : (x ^ y) ^ z = x ^ (y * z) := by
  induction z with
  | zero => rw [Nat.pow_zero, Nat.mul_zero, Nat.pow_zero]
  | succ z H => rw [Nat.pow_succ, Nat.mul_succ, Nat.pow_add, H]

protected theorem le_pow_right_of_pos {x y : Nat} : y > 0 → x ≤ x ^ y := by
  induction x, y with
  | zero_right x => intro; contradiction
  | zero_left y => intro; apply Nat.zero_le
  | succ_succ x y =>
    intro
    transitivity (1 * (x + 1)) using Eq, LE.le
    · rw [Nat.one_mul]
    · rw [Nat.pow_succ]
      apply Nat.mul_le_mul_right
      apply Nat.succ_le_of_lt
      apply Nat.pos_pow_of_pos
      apply Nat.zero_lt_succ

protected theorem le_pow_right (x y : Nat) : (h : y > 0 := by nat_is_pos) → x ≤ x ^ y := Nat.le_pow_right_of_pos

protected theorem pow_lt_pow_of_gt_one_left {x y : Nat} (h : x < y) {z : Nat} : z > 1 → z ^ x < z ^ y := by
  induction x, y with
  | zero_right x => intro; contradiction
  | zero_left y =>
    intro hz
    transitivity z using LT.lt, LE.le
    · rw [Nat.pow_zero]
      exact hz
    · exact Nat.le_pow_right _ _
  | succ_succ x y H =>
    intro hz
    rw [Nat.pow_succ, Nat.pow_succ]
    apply Nat.mul_lt_mul_of_pos_right
    apply H
    · exact Nat.lt_of_succ_lt_succ h
    · exact hz
    · transitivity 1 using LT.lt
      · exact Nat.zero_lt_one
      · exact hz
