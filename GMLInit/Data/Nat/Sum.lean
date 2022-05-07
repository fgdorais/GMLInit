import GMLInit.Data.Nat.Basic
import GMLInit.Data.Nat.Order

namespace Nat

protected def recTwo {motive : Nat → Sort _} (zero : motive 0) (one : motive 1) (step : (n : Nat) → motive n → motive (n+2)) : (n : Nat) → motive n
| 0 => zero
| 1 => one
| n+2 => step n (Nat.recTwo zero one step n)

protected def recTwoOn {motive : Nat → Sort _} (n : Nat) (zero : motive 0) (one : motive 1) (step : (n : Nat) → motive n → motive (n+2)) : motive n :=
  Nat.recTwo zero one step n

protected def casesTwoOn {motive : Nat → Sort _} (n : Nat) (zero : motive 0) (one : motive 1) (step : (n : Nat) → motive (n+2)) : motive n :=
  Nat.recTwo zero one (λ n _ => step n) n

def is_even : Nat → Bool
| 0 => true
| 1 => false
| n + 2 => is_even n

def is_odd : Nat → Bool
| 0 => false
| 1 => true
| n + 2 => is_odd n

theorem not_is_odd_eq_is_even : (n : Nat) → (!is_odd n) = is_even n
| 0 | 1 => rfl
| n + 2 => not_is_odd_eq_is_even n

theorem not_is_even_eq_is_odd : (n : Nat) → (!is_even n) = is_odd n
| 0 | 1 => rfl
| n + 2 => not_is_even_eq_is_odd n

def half : Nat → Nat
| 0 | 1 => 0
| n + 2 => half n + 1

protected def inl (n : Nat) := 2 * n

protected def inr (n : Nat) := 2 * n + 1

theorem is_even_inl (n : Nat) : is_even n.inl := by
  induction n using Nat.recAux with
  | zero => rfl
  | succ n ih =>
    unfold Nat.inl at ih ⊢
    rw [Nat.mul_succ]
    exact ih

theorem is_odd_inr (n : Nat) : is_odd n.inr := by
  induction n using Nat.recAux with
  | zero => rfl
  | succ n ih =>
    unfold Nat.inr at ih ⊢
    rw [Nat.mul_succ]
    exact ih

theorem half_inl_eq (n : Nat) : half n.inl = n := by
  induction n using Nat.recAux with
  | zero => rfl
  | succ n ih =>
    unfold Nat.inl at ih ⊢
    rw [Nat.mul_succ, Nat.half, ih]

theorem half_inr_eq (n : Nat) : half n.inr = n := by
  induction n using Nat.recAux with
  | zero => rfl
  | succ n ih =>
    unfold Nat.inr at ih ⊢
    rw [Nat.mul_succ, Nat.half, ih]

theorem inl_half_eq_or_inr_half_eq (n : Nat) : (half n).inl = n ∨ (half n).inr = n := by
  induction n using Nat.recTwo with
  | zero => left; rfl
  | one => right; rfl
  | step n ih =>
    cases ih with
    | inl ih =>
      left
      unfold Nat.inl Nat.half Nat.add at ih ⊢
      rw [Nat.mul_succ, ih]
    | inr ih =>
      right
      unfold Nat.inr Nat.half Nat.add at ih ⊢
      rw [Nat.mul_succ, Nat.add_succ, Nat.add_succ, ih]

theorem inl_half_eq_of_is_even (n : Nat) : is_even n → (half n).inl = n := by
  induction n using Nat.recTwo with
  | zero => intro; rfl
  | one => intro; contradiction
  | step n ih =>
    intro h
    unfold Nat.inl Nat.half Nat.add at ih ⊢
    rw [Nat.mul_succ, ih h]

theorem inr_half_eq_of_is_odd (n : Nat) : is_odd n → (half n).inr = n := by
  induction n using Nat.recTwo with
  | zero => intro; contradiction
  | one => intro; rfl
  | step n ih =>
    intro h
    unfold Nat.inr Nat.half Nat.add at ih ⊢
    rw [Nat.mul_succ, Nat.add_succ, Nat.add_succ, ih h]

def equivSum : Equiv Nat (Sum Nat Nat) where
  fwd n := if is_odd n then Sum.inr (half n) else Sum.inl (half n)
  rev
  | Sum.inl n => Nat.inl n
  | Sum.inr n => Nat.inr n
  spec := by intro
    | n, Sum.inl m =>
      clean
      split
      next h =>
        constr
        · intro
          contradiction
        · intro hl
          rw [←not_is_even_eq_is_odd, ←hl, is_even_inl] at h
          contradiction
      next h =>
        cases inl_half_eq_or_inr_half_eq n with
        | inl hl =>
          constr
          · intro heq
            cases heq
            exact hl
          · intro heq
            cases heq
            rw [half_inl_eq]
        | inr hr =>
          constr
          · intro heq
            cases heq
            rw [←hr,is_odd_inr] at h
            contradiction
          · intro heq
            cases heq
            rw [half_inl_eq]
    | n, Sum.inr m =>
      clean
      split
      next h =>
        cases inl_half_eq_or_inr_half_eq n with
        | inl hl =>
          constr
          · intro heq
            cases heq
            rw [←hl, ←not_is_even_eq_is_odd, is_even_inl] at h
            contradiction
          · intro heq
            cases heq
            rw [half_inr_eq]
        | inr hr =>
          constr
          · intro heq
            cases heq
            exact hr
          · intro heq
            cases heq
            rw [half_inr_eq]
      next h =>
        simp
        intro hl
        rw [←hl, is_odd_inr] at h
        contradiction

end Nat
