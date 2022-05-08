import GMLInit.Data.Nat.Basic
import GMLInit.Data.Nat.Order

class Infinity (α) where
  infinity : α
notation "∞" => Infinity.infinity

structure ENat where
  isLE : Nat → Bool
  step (x : Nat) : isLE x → isLE (x + 1)

namespace ENat

protected theorem eq : {e₁ e₂ : ENat} → e₁.isLE = e₂.isLE → e₁ = e₂
| ⟨_,_⟩, ⟨_,_⟩, rfl => rfl

protected theorem ext {e₁ e₂ : ENat} : (∀ x, e₁.isLE x = e₂.isLE x) → e₁ = e₂
| h => ENat.eq $ funext h

theorem mono (e : ENat) {x y : Nat} : x ≤ y → e.isLE x → e.isLE y := by
  intro h hx
  match Nat.le.dest h with
  | ⟨z,hz⟩ =>
    cases hz
    induction z with
    | zero => exact hx
    | succ z H =>
      apply e.step
      apply H
      exact Nat.le_add_right x z

protected def zero : ENat where
  isLE _ := true
  step _ := id
instance : OfNat ENat (nat_lit 0) := ⟨ENat.zero⟩

@[simp] theorem isLE_zero (n) : ENat.isLE 0 n = true := rfl

protected def infinity : ENat where
  isLE _ := false
  step _ := Bool.noConfusion
instance : Infinity ENat := ⟨ENat.infinity⟩

@[simp] theorem isLE_infinity (n) : ENat.isLE ∞ n = false := rfl

protected def ofNat (n : Nat) : ENat where
  isLE := Nat.ble n
  step x := by
    intro h
    rw [Nat.ble_eq] at h ⊢
    transitivity x
    · exact h
    · exact Nat.le_add_right ..

instance : Coe Nat ENat := ⟨ENat.ofNat⟩

@[simp] theorem ofNat_isLE_iff_le (n m : Nat) : ENat.isLE n m ↔ n ≤ m := by
  unfold ENat.ofNat
  rw [Nat.ble_eq]
  reflexivity

theorem ofNat_isLE_self (n : Nat) : ENat.isLE n n := by
  rw [ofNat_isLE_iff_le]
  reflexivity

end ENat
