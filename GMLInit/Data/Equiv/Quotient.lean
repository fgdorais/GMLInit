import GMLInit.Data.Equiv.Basic

namespace Quotient

def equiv {α₁ α₂} {s₁ : Setoid α₁} {s₂ : Setoid α₂} (e : Equiv α₁ α₂) (H : ∀ x y : α₁, x ≈ y ↔ e.fwd x ≈ e.fwd y) : Equiv (Quotient s₁) (Quotient s₂) where
  fwd x := Quotient.liftOn x (fun x => Quotient.mk s₂ (e.fwd x)) $ by
    intro _ _ h
    apply Quotient.sound
    rw [←H]
    exact h
  rev y := Quotient.liftOn y (fun y => Quotient.mk s₁ (e.rev y)) $ by
    intro _ _ h
    apply Quotient.sound
    rw [H]
    rw [e.fwd_rev, e.fwd_rev]
    exact h
  spec {x y} := by
    induction x, y using Quotient.inductionOn₂ with
    | _ x y =>
      constr
      · intro h
        have h := Quotient.exact h
        transitivity (Quotient.mk s₁ (e.rev y))
        · rfl
        · apply Quotient.sound
          rw [H]
          rw [e.fwd_rev]
          symmetry
          exact h
      · intro h
        have h := Quotient.exact h
        transitivity (Quotient.mk s₂ (e.fwd x))
        · rfl
        · apply Quotient.sound
          rw [←e.fwd_rev y]
          rw [←H]
          symmetry
          exact h

end Quotient

