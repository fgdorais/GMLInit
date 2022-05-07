import GMLInit.Meta.Stable
import GMLInit.Data.Nat.Basic
import GMLInit.Data.Nat.IsPos
import GMLInit.Data.Nat.Order

namespace Nat

protected theorem pred_zero' : 0 - 1 = 0 := rfl

protected theorem pred_succ' (x : Nat) : (x + 1) - 1 = x := rfl

protected theorem succ_pred' (x : Nat) (h : x > 0 := by nat_is_pos) : (x - 1) + 1 = x := by
  cases x using Nat.casesAuxOn with
  | zero => contradiction
  | succ x => rw [Nat.pred_succ']

-- assert theorem zero_lt_succ (x : Nat) : 0 < x + 1

-- assert theorem not_succ_le_zero (x : Nat) : ¬ x + 1 ≤ 0

-- assert theorem lt_succ_self (x : Nat) : x < x + 1

-- assert theorem not_succ_le_self (x : Nat) : ¬ x + 1 ≤ x

-- assert theorem succ_le_succ {x y : Nat} : x ≤ y → x + 1 ≤ y + 1

-- assert theorem le_of_succ_le_succ {x y : Nat} : x + 1 ≤ y + 1 → x ≤ y

-- assert theorem succ_lt_succ {x y : Nat} : x < y → x + 1 < y + 1

-- assert theorem lt_of_succ_lt_succ {x y : Nat} : x + 1 < y + 1 → x < y

-- assert theorem succ_le_of_lt {x y : Nat} : x + 1 ≤ y → x < y

-- assert theorem lt_of_succ_le {x y : Nat} : x + 1 ≤ y → x < y

-- assert theorem lt_succ_of_le {x y : Nat} : x ≤ y → x < y + 1

-- assert theorem le_of_lt_succ {x y : Nat} : x < y + 1 → x ≤ y

protected theorem succ_le_iff_lt (x y : Nat) : x + 1 ≤ y ↔ x < y :=
  ⟨Nat.lt_of_succ_le, Nat.succ_le_of_lt⟩

protected theorem lt_succ_iff_le (x y : Nat) : x < y + 1 ↔ x ≤ y :=
  ⟨Nat.le_of_lt_succ, Nat.lt_succ_of_le⟩

protected theorem succ_le_succ_iff_le (x y : Nat) : x + 1 ≤ y + 1 ↔ x ≤ y :=
  ⟨Nat.le_of_succ_le_succ, Nat.succ_le_succ⟩

protected theorem succ_lt_succ_iff_lt (x y : Nat) : x + 1 < y + 1 ↔ x < y :=
  ⟨Nat.lt_of_succ_lt_succ, Nat.succ_lt_succ⟩

protected theorem pred_le_iff_le_succ (x y : Nat) : x - 1 ≤ y ↔ x ≤ y + 1 := by
  cases x, y using Nat.casesDiagAuxOn with
  | left x =>
    cases x with
    | zero =>
      constr
      · intro
        apply Nat.zero_le
      · intro
        apply Nat.zero_le
    | succ x =>
      constr
      · exact Nat.succ_le_succ
      · exact Nat.le_of_succ_le_succ
  | right y =>
    constr
    · intro
      apply Nat.zero_le
    · intro
      apply Nat.zero_le
  | diag x y =>
    constr
    · exact Nat.succ_le_succ
    · exact Nat.le_of_succ_le_succ

protected theorem succ_lt_iff_lt_pred (x y : Nat) : x + 1 < y ↔ x < y - 1 := by
  rw [Nat.lt_iff_not_ge, Nat.lt_iff_not_ge]
  apply Iff.mt
  exact Nat.pred_le_iff_le_succ y x

protected theorem succ_le_or_eq_zero_iff_le_pred (x y : Nat) : x + 1 ≤ y ∨ x = 0 ↔ x ≤ y - 1 := by
  cases x, y using Nat.recDiagAuxOn with
  | left x =>
    constr
    · intro
      | Or.inl h => absurd h; apply Nat.not_succ_le_zero
      | Or.inr h => rw [h]; apply Nat.le_refl
    · intro h
      right
      antisymmetry using LE.le
      exact h
      exact Nat.zero_le x
  | right y =>
    constr
    · intro; apply Nat.zero_le
    · intro; right; reflexivity
  | diag x y =>
    constr
    · intro
      | Or.inl h => exact Nat.le_of_succ_le_succ h
      | Or.inr h => absurd h; apply Nat.succ_ne_zero
    · intro h
      left
      exact Nat.succ_le_succ h

protected theorem pred_lt_or_eq_zero_iff_lt_succ (x y : Nat) : x - 1 < y ∨ x = 0 ↔ x < y + 1 := by
  induction x, y using Nat.recDiagAuxOn with
  | left x =>
    constr
    · intro
      | Or.inl h => absurd h; apply Nat.not_lt_zero
      | Or.inr h => rw [h]; apply Nat.zero_lt_one
    · intro h
      right
      antisymmetry using LE.le
      exact Nat.le_of_lt_succ h
      exact Nat.zero_le x
  | right y =>
    constr
    · intro
      apply Nat.zero_lt_succ
    · intro
      right
      reflexivity
  | diag x y H =>
    constr
    · intro
      | Or.inl h => exact Nat.succ_lt_succ h
      | Or.inr h => absurd h; apply Nat.succ_ne_zero
    · intro h
      left
      exact Nat.lt_of_succ_lt_succ h

end Nat
