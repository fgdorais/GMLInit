import GMLInit.Data.Nat.Basic
import GMLInit.Data.Nat.IsPos
import GMLInit.Logic.Connectives
import GMLInit.Logic.Ordering
import GMLInit.Logic.Relation

namespace Nat

-- assert theorem lt_or_ge (x y : Nat) : x < y ∨ x ≥ y

protected theorem le_or_gt (x y : Nat) : x ≤ y ∨ x > y :=
  Or.elim (Nat.lt_or_ge y x) Or.inr Or.inl

protected theorem lt_or_eq_of_le {x y : Nat} : x ≤ y → x < y ∨ x = y :=
  λ hle => Or.elim (Nat.lt_or_ge x y) Or.inl λ hge => Or.inr (Nat.le_antisymm hle hge)

protected theorem le_iff_lt_or_eq (x y : Nat) : x ≤ y ↔ x < y ∨ x = y :=
  ⟨Nat.lt_or_eq_of_le, λ h => Or.elim h Nat.le_of_lt Nat.le_of_eq⟩

-- assert theorem le_of_lt {x y : Nat} : x < y → x ≤ y

-- assert theorem ne_of_lt {x y : Nat} : x < y → x ≠ y | h, rfl => Nat.lt_irrefl x h

-- assert theorem lt_of_le_of_ne {x y : Nat} : x ≤ y → x ≠ y → x < y

protected theorem lt_iff_le_and_ne (x y : Nat) : x < y ↔ x ≤ y ∧ x ≠ y :=
  ⟨λ hlt => ⟨Nat.le_of_lt hlt, Nat.ne_of_lt hlt⟩, λ ⟨hle, hne⟩ => Nat.lt_of_le_of_ne hle hne⟩

-- assert theorem le_total (x y : Nat) : x ≤ y ∨ x ≥ y := Nat.leTotal x y

protected theorem lt_connex {x y : Nat} : x ≠ y → x < y ∨ x > y :=
  λ hne => Or.elim (Nat.lt_or_ge x y) Or.inl λ h => Or.inr (Nat.lt_of_le_of_ne h hne.symm)

protected theorem lt_compare {x y : Nat} : x < y → ∀ z, x < z ∨ z < y :=
  λ hlt z => Or.elim (Nat.lt_or_ge x z) Or.inl (λ hge => Or.inr (Nat.lt_of_le_of_lt hge hlt))

-- assert theorem ge_of_not_lt {x y : Nat} : ¬ x < y → x ≥ y := Or.mtp (Nat.le_or_gt y x)

-- assert theorem gt_of_not_le {x y : Nat} : ¬ x ≤ y → x > y

protected theorem le_of_not_gt {x y : Nat} : ¬ x > y → x ≤ y := Or.mtp (Nat.le_or_gt x y)

protected theorem lt_of_not_ge {x y : Nat} : ¬ x ≥ y → x < y := Or.mtp (Nat.lt_or_ge x y)

protected theorem not_ge_of_lt {x y : Nat} : x < y → ¬ x ≥ y := Nat.not_le_of_gt

protected theorem not_gt_of_le {x y : Nat} : x ≤ y → ¬ x > y := λ hle hgt => Nat.not_ge_of_lt hgt hle

-- assert theorem not_le_of_gt {x y : Nat} : x > y → ¬ x ≤ y

protected theorem not_lt_of_ge {x y : Nat} : x ≥ y → ¬ x < y := λ hge hlt => Nat.not_gt_of_le hlt (Nat.succ_le_succ hge)

protected theorem not_le_iff_gt (x y : Nat) : ¬ x ≤ y ↔ x > y :=
  ⟨Nat.gt_of_not_le, Nat.not_ge_of_lt⟩

protected theorem lt_iff_not_ge (x y : Nat) : x < y ↔ ¬ x ≥ y :=
  ⟨Nat.not_ge_of_lt, Nat.gt_of_not_le⟩

protected theorem not_lt_iff_ge (x y : Nat) : ¬ x < y ↔ x ≥ y :=
  ⟨Nat.ge_of_not_lt, Nat.not_gt_of_le⟩

protected theorem le_iff_not_gt (x y : Nat) : x ≤ y ↔ ¬ x > y :=
  ⟨Nat.not_gt_of_le, Nat.ge_of_not_lt⟩

protected theorem ne_iff_lt_or_gt (x y : Nat) : x ≠ y ↔ x < y ∨ x > y :=
  ⟨Nat.lt_connex, λ h => Or.elim h Nat.ne_of_lt λ h => (Nat.ne_of_lt h).symm⟩

-- assert theorem zero_le (x : Nat) : 0 ≤ x

-- assert theorem not_lt_zero (x : Nat) : ¬ x < 0

-- assert theorem eq_zero_of_le_zero {x : Nat} : x ≤ 0 → x = 0

protected theorem eq_zero_iff_le_zero (x : Nat) : x = 0 ↔ x ≤ 0 :=
  ⟨Nat.le_of_eq, Nat.eq_zero_of_le_zero⟩

open Relation

local instance : Reflexive (α:=Nat) (.≤.) := ⟨Nat.le_refl⟩
local instance : Transitive (α:=Nat) (.≤.) := ⟨Nat.le_trans⟩
local instance : Antisymmetric (α:=Nat) (.≤.) := ⟨Nat.le_antisymm⟩
local instance : Total (α:=Nat) (.≤.) := ⟨Nat.le_total⟩
instance : TotalOrder (α:=Nat) (.≤.) := TotalOrder.infer _
local instance : Irreflexive (α:=Nat) (.<.) := ⟨Nat.lt_irrefl⟩
local instance : Transitive (α:=Nat) (.<.) := ⟨Nat.lt_trans⟩
local instance : Connex (α:=Nat) (.<.) := ⟨Nat.lt_connex⟩
local instance : Comparison (α:=Nat) (.<.) := ⟨Nat.lt_compare⟩
instance : LinearOrder (α:=Nat) (.<.) := LinearOrder.infer _
instance : HTransitive (α:=Nat) (β:=Nat) (γ:=Nat) (.≤.) (.<.) (.<.) := ⟨Nat.lt_of_le_of_lt⟩
instance : HTransitive (α:=Nat) (β:=Nat) (γ:=Nat) (.<.) (.≤.) (.<.) := ⟨Nat.lt_of_lt_of_le⟩

end Nat
