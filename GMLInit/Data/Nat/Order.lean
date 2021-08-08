import GMLInit.Data.Nat.Basic
import GMLInit.Logic.Connectives

namespace Nat

instance : Relation.Reflexive (α:=Nat) (.≤.) := ⟨Nat.le_refl⟩

instance : Relation.Irreflexive (α:=Nat) (.<.) := ⟨Nat.lt_irrefl⟩

instance : Relation.Transitive (α:=Nat) (.≤.) := ⟨Nat.le_trans⟩

instance : Relation.Transitive (α:=Nat) (.<.) := ⟨Nat.lt_trans⟩

instance : Relation.HTransitive (α:=Nat) (β:=Nat) (γ:=Nat) (.≤.) (.<.) (.<.) := ⟨Nat.lt_of_le_of_lt⟩

instance : Relation.HTransitive (α:=Nat) (β:=Nat) (γ:=Nat) (.<.) (.≤.) (.<.) := ⟨Nat.lt_of_lt_of_le⟩

instance : Relation.Antisymmetric (α:=Nat) (.≤.) := ⟨Nat.le_antisymm⟩

-- assert theorem lt_or_ge (x y : Nat) : x < y ∨ x ≥ y

protected theorem le_or_gt (x y : Nat) : x ≤ y ∨ x > y :=
  Or.elim (Nat.lt_or_ge y x) Or.inr Or.inl

protected theorem lt_or_eq_of_le {x y : Nat} : x ≤ y → x < y ∨ x = y :=
  λ hle => Or.elim (Nat.lt_or_ge x y) Or.inl λ hge => Or.inr (Nat.le_antisymm hle hge)

protected theorem le_iff_lt_or_eq (x y : Nat) : x ≤ y ↔ x < y ∨ x = y :=
  ⟨Nat.lt_or_eq_of_le, λ h => Or.elim h Nat.le_of_lt Nat.le_of_eq⟩

-- assert theorem le_of_lt {x y : Nat} : x < y → x ≤ y

protected theorem ne_of_lt {x y : Nat} : x < y → x ≠ y | h, rfl => Nat.lt_irrefl x h -- fix?

-- assert theorem lt_of_le_of_ne {x y : Nat} : x ≤ y → x ≠ y → x < y

protected theorem lt_iff_le_and_ne (x y : Nat) : x < y ↔ x ≤ y ∧ x ≠ y :=
  ⟨λ hlt => ⟨Nat.le_of_lt hlt, Nat.ne_of_lt hlt⟩, λ ⟨hle, hne⟩ => Nat.lt_of_le_of_ne hle hne⟩

-- assert theorem le_total (x y : Nat) : x ≤ y ∨ x ≥ y := Nat.leTotal x y

protected theorem lt_connex {x y : Nat} : x ≠ y → x < y ∨ x > y :=
  λ hne => Or.elim (Nat.lt_or_ge x y) Or.inl λ h => Or.inr (Nat.lt_of_le_of_ne h hne.symm)

protected theorem ge_of_not_lt {x y : Nat} : ¬ x < y → x ≥ y := Or.mtp (Nat.le_or_gt y x)

-- assert theorem gt_of_not_le {x y : Nat} : ¬ x ≤ y → x > y

protected theorem le_of_not_gt {x y : Nat} : ¬ x > y → x ≤ y := Or.mtp (Nat.le_or_gt x y)

protected theorem lt_of_not_ge {x y : Nat} : ¬ x ≥ y → x < y := Or.mtp (Nat.lt_or_ge x y)

protected theorem not_ge_of_lt {x y : Nat} : x < y → ¬ x ≥ y := Nat.not_le_of_gt

protected theorem not_gt_of_le {x y : Nat} : x ≤ y → ¬ x > y := λ hle hgt => Nat.not_ge_of_lt hgt hle

-- assert theorem not_le_of_gt {x y : Nat} : x > y → ¬ x ≤ y

protected theorem not_lt_of_ge {x y : Nat} : x ≥ y → ¬ x < y := λ hge hlt => Nat.not_gt_of_le hlt hge

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

end Nat