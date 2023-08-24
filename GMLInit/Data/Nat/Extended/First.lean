import GMLInit.Data.Nat.Extended.Basic
import GMLInit.Data.Nat.Extended.Finite

namespace ENat
variable (p : Nat → Bool)

private def first.leNatAux : Nat → Bool
| 0 => p 0
| x+1 => p (x+1) || leNatAux x

def first : ENat where
  leNat := first.leNatAux p
  mono_step := by intro x hx; simp [first.leNatAux, hx]

variable {p}

theorem first.leNat_of (x : Nat) : p x → (first p).leNat x := by
  match x with
  | 0 => intro h; exact h
  | x+1 => intro h; simp [first, first.leNatAux, h]

theorem first.exists_le_of_leNat (x : Nat) : (first p).leNat x → ∃ y, y ≤ x ∧ p y := by
  induction x with
  | zero =>
    intro h
    exists 0
  | succ x H =>
    intro h
    simp [first, first.leNatAux] at h
    cases h with
    | inl h =>
      exists x+1
      constructor
      · exact Nat.le_refl ..
      · exact h
    | inr h =>
      match H h with
      | ⟨y, hle, hy⟩ =>
        exists y
        constructor
        · apply Nat.le_trans hle
          exact Nat.le_succ ..
        · exact hy

@[simp] theorem first.leNat_iff_exists_le (x) : (first p).leNat x ↔ ∃ y, y ≤ x ∧ p y := by
  constructor
  · exact first.exists_le_of_leNat x
  · intro ⟨y, hle, hy⟩
    apply mono hle
    exact first.leNat_of _ hy

theorem first.isFinite_of {x} : p x → Finite (first p) := by
  intro h
  exists x
  exact first.leNat_of _ h

theorem first.isFinite_of_exists : (∃ x, p x) → Finite (first p) := by
  intro ⟨_,h⟩
  exact first.isFinite_of h

end ENat
