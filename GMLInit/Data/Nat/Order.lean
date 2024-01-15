import GMLInit.Data.Nat.Basic
import GMLInit.Logic.Ordering

namespace Nat

@[deprecated Nat.lt_or_ge]
protected theorem le_or_gt (x y : Nat) : x ≤ y ∨ x > y := (Nat.lt_or_ge y x).symm

protected theorem lt_compare {x y : Nat} : x < y → ∀ z, x < z ∨ z < y :=
  λ hlt z => Or.elim (Nat.lt_or_ge x z) Or.inl (λ hge => Or.inr (Nat.lt_of_le_of_lt hge hlt))

@[deprecated Nat.not_le_of_gt]
protected theorem not_ge_of_lt {x y : Nat} : x < y → ¬ x ≥ y := Nat.not_le_of_gt

@[deprecated Nat.not_lt_of_ge]
protected theorem not_gt_of_le {x y : Nat} : x ≤ y → ¬ x > y := Nat.not_lt_of_ge

@[deprecated Nat.not_le]
protected theorem not_le_iff_gt (x y : Nat) : ¬ x ≤ y ↔ x > y := Nat.not_le

@[deprecated Nat.not_le]
protected theorem lt_iff_not_ge (x y : Nat) : x < y ↔ ¬ x ≥ y := Nat.not_le.symm

@[deprecated Nat.not_lt]
protected theorem not_lt_iff_ge (x y : Nat) : ¬ x < y ↔ x ≥ y := Nat.not_lt

@[deprecated Nat.not_lt]
protected theorem le_iff_not_gt (x y : Nat) : x ≤ y ↔ ¬ x > y := Nat.not_lt.symm

protected theorem eq_zero_iff_le_zero (x : Nat) : x = 0 ↔ x ≤ 0 :=
  ⟨Nat.le_of_eq, Nat.eq_zero_of_le_zero⟩

open Relation

local instance : Logic.Reflexive (α:=Nat) (.≤.) := ⟨Nat.le_refl⟩
local instance : Logic.Transitive (α:=Nat) (.≤.) := ⟨Nat.le_trans⟩
local instance : Logic.Antisymmetric (α:=Nat) (.≤.) := ⟨Nat.le_antisymm⟩
local instance : Logic.Total (α:=Nat) (.≤.) := ⟨Nat.le_total⟩
instance : TotalOrder (α:=Nat) (.≤.) := TotalOrder.infer _
local instance : Logic.Irreflexive (α:=Nat) (.<.) := ⟨Nat.lt_irrefl⟩
local instance : Logic.Transitive (α:=Nat) (.<.) := ⟨Nat.lt_trans⟩
local instance : Logic.Connex (α:=Nat) (.<.) := ⟨Nat.lt_or_gt_of_ne⟩
local instance : Logic.Comparison (α:=Nat) (.<.) := ⟨Nat.lt_compare⟩
instance : LinearOrder (α:=Nat) (.<.) := LinearOrder.infer _
instance : Logic.HTransitive (α:=Nat) (β:=Nat) (γ:=Nat) (.≤.) (.<.) (.<.) := ⟨Nat.lt_of_le_of_lt⟩
instance : Logic.HTransitive (α:=Nat) (β:=Nat) (γ:=Nat) (.<.) (.≤.) (.<.) := ⟨Nat.lt_of_lt_of_le⟩

end Nat
