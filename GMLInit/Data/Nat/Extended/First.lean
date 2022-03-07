import GMLInit.Data.Nat.Extended.Basic
import GMLInit.Data.Nat.Extended.Finite

namespace ENat
variable (p : Nat → Bool)

private def first.isLEAux : Nat → Bool
| 0 => p 0
| x+1 => p (x+1) || isLEAux x

def first : ENat where
  isLE := first.isLEAux p
  step := by
    intro x hx
    unfold first.isLEAux
    simp [hx]

variable {p}
theorem first.isLE_of (x : Nat) : p x → (first p).isLE x := by
  match x with
  | 0 => intro h; exact h
  | x+1 => intro h; simp [first, first.isLEAux, h]

theorem first.exists_le_of_isLE (x : Nat) : (first p).isLE x → ∃ y, y ≤ x ∧ p y := by
  induction x using Nat.recAux with
  | zero =>
    intro h
    exists (0:Nat)
    constr
    · reflexivity
    · exact h
  | succ x H =>
    intro h
    unfold first first.isLEAux at h
    rw [Bool.or_eq_true] at h
    cases h with
    | inl h =>
      exists (x+1)
      constr
      · reflexivity
      · exact h
    | inr h =>
      match H h with
      | ⟨y, hle, hy⟩ =>
        exists y
        constr
        · transitivity x
          · exact hle
          · exact Nat.le_succ x
        · exact hy

@[simp] theorem first.isLE_iff_exists_le (x) : (first p).isLE x ↔ ∃ y, y ≤ x ∧ p y := by
  constr
  · exact first.exists_le_of_isLE x
  · intro ⟨y, hle, hy⟩
    apply mono _ hle
    exact first.isLE_of _ hy

theorem first.isFinite_of {x} : p x → Finite (first p) := by
  intro h
  exists x
  exact first.isLE_of _ h

theorem first.isFinite_of_exists : (∃ x, p x) → Finite (first p) := by
  intro ⟨_,h⟩
  exact first.isFinite_of h

end ENat
