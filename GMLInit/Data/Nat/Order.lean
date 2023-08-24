import GMLInit.Data.Nat.Basic
import GMLInit.Data.Nat.IsPos
import GMLInit.Logic.Ordering

namespace Nat

-- assert theorem lt_or_ge (x y : Nat) : x < y ∨ x ≥ y

@[deprecated Nat.lt_or_ge]
protected theorem le_or_gt (x y : Nat) : x ≤ y ∨ x > y := (Nat.lt_or_ge y x).symm

-- assert theorem lt_or_eq_of_le {x y : Nat} : x ≤ y → x < y ∨ x = y

-- assert theorem le_iff_lt_or_eq (x y : Nat) : x ≤ y ↔ x < y ∨ x = y

-- assert theorem le_of_lt {x y : Nat} : x < y → x ≤ y

-- assert theorem ne_of_lt {x y : Nat} : x < y → x ≠ y | h, rfl => Nat.lt_irrefl x h

-- assert theorem lt_of_le_of_ne {x y : Nat} : x ≤ y → x ≠ y → x < y

-- assert theorem lt_iff_le_and_ne (x y : Nat) : x < y ↔ x ≤ y ∧ x ≠ y

-- assert theorem le_total (x y : Nat) : x ≤ y ∨ x ≥ y := Nat.leTotal x y

-- assert theorem lt_connex {x y : Nat} : x ≠ y → x < y ∨ x > y

protected theorem lt_compare {x y : Nat} : x < y → ∀ z, x < z ∨ z < y :=
  λ hlt z => Or.elim (Nat.lt_or_ge x z) Or.inl (λ hge => Or.inr (Nat.lt_of_le_of_lt hge hlt))

-- assert theorem ge_of_not_lt {x y : Nat} : ¬ x < y → x ≥ y := Or.mtp (Nat.le_or_gt y x)

-- assert theorem gt_of_not_le {x y : Nat} : ¬ x ≤ y → x > y

-- assert theorem le_of_not_gt {x y : Nat} : ¬ x > y → x ≤ y

-- assert theorem lt_of_not_ge {x y : Nat} : ¬ x ≥ y → x < y

@[deprecated Nat.not_le_of_gt]
protected theorem not_ge_of_lt {x y : Nat} : x < y → ¬ x ≥ y := Nat.not_le_of_gt

@[deprecated Nat.not_lt_of_ge]
protected theorem not_gt_of_le {x y : Nat} : x ≤ y → ¬ x > y := Nat.not_lt_of_ge

-- assert theorem not_le_of_gt {x y : Nat} : x > y → ¬ x ≤ y

-- assert theorem not_lt_of_ge {x y : Nat} : x ≥ y → ¬ x < y

@[deprecated Nat.not_le]
protected theorem not_le_iff_gt (x y : Nat) : ¬ x ≤ y ↔ x > y := Nat.not_le

@[deprecated Nat.not_le]
protected theorem lt_iff_not_ge (x y : Nat) : x < y ↔ ¬ x ≥ y := Nat.not_le.symm

@[deprecated Nat.not_lt]
protected theorem not_lt_iff_ge (x y : Nat) : ¬ x < y ↔ x ≥ y := Nat.not_lt

@[deprecated Nat.not_lt]
protected theorem le_iff_not_gt (x y : Nat) : x ≤ y ↔ ¬ x > y := Nat.not_lt.symm

-- assert theorem ne_iff_lt_or_gt (x y : Nat) : x ≠ y ↔ x < y ∨ x > y

-- assert theorem zero_le (x : Nat) : 0 ≤ x

-- assert theorem not_lt_zero (x : Nat) : ¬ x < 0

-- assert theorem eq_zero_of_le_zero {x : Nat} : x ≤ 0 → x = 0

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
local instance : Logic.Connex (α:=Nat) (.<.) := ⟨Nat.lt_connex⟩
local instance : Logic.Comparison (α:=Nat) (.<.) := ⟨Nat.lt_compare⟩
instance : LinearOrder (α:=Nat) (.<.) := LinearOrder.infer _
instance : Logic.HTransitive (α:=Nat) (β:=Nat) (γ:=Nat) (.≤.) (.<.) (.<.) := ⟨Nat.lt_of_le_of_lt⟩
instance : Logic.HTransitive (α:=Nat) (β:=Nat) (γ:=Nat) (.<.) (.≤.) (.<.) := ⟨Nat.lt_of_lt_of_le⟩

end Nat
