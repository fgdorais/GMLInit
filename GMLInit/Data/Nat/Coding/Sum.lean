import GMLInit.Data.Bool
import GMLInit.Data.Nat.Basic
import GMLInit.Data.Nat.Order

namespace Nat
open Logic

protected def recTwo {motive : Nat → Sort _} (zero : motive 0) (one : motive 1) (step : (n : Nat) → motive n → motive (n+2)) : (n : Nat) → motive n
| 0 => zero
| 1 => one
| n+2 => step n (Nat.recTwo zero one step n)

protected def recTwoOn {motive : Nat → Sort _} (n : Nat) (zero : motive 0) (one : motive 1) (step : (n : Nat) → motive n → motive (n+2)) : motive n :=
  Nat.recTwo zero one step n

protected def casesTwoOn {motive : Nat → Sort _} (n : Nat) (zero : motive 0) (one : motive 1) (step : (n : Nat) → motive (n+2)) : motive n :=
  Nat.recTwo zero one (λ n _ => step n) n

def isEven : Nat → Bool
| 0 => true
| 1 => false
| n + 2 => isEven n

abbrev isOdd (n : Nat) := !n.isEven

private abbrev isEvenImpl (n : Nat) : Bool := (n % 2) == 0

@[csimp] theorem isEven_eq_isEvenImpl : isEven = isEvenImpl := by
  funext n
  induction n using Nat.recTwo with
  | zero => rfl
  | one => rfl
  | step n ih =>
    unfold Nat.isEven Nat.add
    rw [isEvenImpl, Nat.add_mod_right, ih]

theorem isEven_or_isOdd (n : Nat) : n.isEven ∨ n.isOdd := by
  rw [←Bool.or_eq_true]
  exact Bool.or_not_self ..

theorem not_isOdd_eq_isEven (n : Nat) : (!n.isOdd) = n.isEven := by
  rw [Bool.not_not]

theorem not_isEven_eq_isOdd (n : Nat) : (!n.isEven) = n.isOdd := rfl

def half : Nat → Nat
| 0 | 1 => 0
| n + 2 => half n + 1

abbrev halfImpl (n : Nat) : Nat := n / 2

@[csimp] theorem half_eq_halfImpl : half = halfImpl := by
  funext n
  induction n using Nat.recTwo with
  | zero => rfl
  | one => rfl
  | step n ih =>
    unfold Nat.half Nat.add
    rw [halfImpl, Nat.add_div_right, ih]
    nat_is_pos

protected abbrev inl (n : Nat) := 2 * n

protected abbrev inr (n : Nat) := 2 * n + 1

theorem isEven_inl (n : Nat) : isEven n.inl := by
  induction n with
  | zero => rfl
  | succ n ih =>
    unfold Nat.inl at ih ⊢
    rw [Nat.mul_succ]
    exact ih

theorem isOdd_inr (n : Nat) : isOdd n.inr := by
  induction n with
  | zero => rfl
  | succ n ih =>
    unfold Nat.inr at ih ⊢
    rw [Nat.mul_succ]
    exact ih

theorem half_inl_eq (n : Nat) : half n.inl = n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    unfold Nat.inl at ih ⊢
    rw [Nat.mul_succ, Nat.half, ih]

theorem half_inr_eq (n : Nat) : half n.inr = n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    unfold Nat.inr at ih ⊢
    rw [Nat.mul_succ, Nat.half, ih]

theorem inl_half_eq_of_isEven {n : Nat} : isEven n → (half n).inl = n := by
  induction n using Nat.recTwo with
  | zero => intro; rfl
  | one => intro; contradiction
  | step n ih =>
    intro h
    unfold Nat.inl at ih ⊢
    unfold Nat.half Nat.add
    rw [Nat.mul_succ, ih h]

theorem inr_half_eq_of_isOdd {n : Nat} : isOdd n → (half n).inr = n := by
  induction n using Nat.recTwo with
  | zero => intro; contradiction
  | one => intro; rfl
  | step n ih =>
    intro h
    unfold Nat.inr at ih ⊢
    unfold Nat.half Nat.add
    rw [Nat.mul_succ, Nat.add_succ, Nat.add_succ, ih h]

theorem inl_half_eq_or_inr_half_eq (n : Nat) : (half n).inl = n ∨ (half n).inr = n := by
  match isEven_or_isOdd n with
  | .inl h => left; exact inl_half_eq_of_isEven h
  | .inr h => right; exact inr_half_eq_of_isOdd h

def encodeSum : Sum Nat Nat → Nat
| .inl n => n.inl
| .inr n => n.inr

def decodeSum (n : Nat) : Sum Nat Nat :=
  if n.isOdd
  then .inr (half n)
  else .inl (half n)

def equivSum : Equiv (Sum Nat Nat) Nat where
  fwd := encodeSum
  rev := decodeSum
  fwd_eq_iff_rev_eq := by intro
    | .inl m, n =>
      unfold encodeSum decodeSum
      split
      next h =>
        cases h
        constructor
        · intro
          | rfl =>
            rw [half_inl_eq]
            split
            next h =>
              rw [←not_isEven_eq_isOdd, isEven_inl] at h
              contradiction
            next h => rfl
        · intro hl
          split at hl
          next => contradiction
          next h =>
            cases hl
            rw [inl_half_eq_of_isEven]
            rw [Bool.not_eq_true] at h
            rw [←not_isOdd_eq_isEven, h]
            rfl
      next h => contradiction
    | .inr m, n =>
      unfold encodeSum decodeSum
      split
      next h => contradiction
      next h =>
        cases h
        constructor
        · intro | rfl => rw [if_pos (isOdd_inr _), half_inr_eq]
        · intro h
          split at h
          next hodd => cases h; rw [inr_half_eq_of_isOdd hodd]
          next => contradiction

end Nat
