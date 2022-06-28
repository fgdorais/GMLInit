import GMLInit.Data.Basic
import GMLInit.Logic.Relation
import GMLInit.Meta.Decidable

variable (α) [Ord α]

open Ordering (lt eq gt)

class TransOrd : Prop where
  eq_refl (x : α) : compare x x = eq
  eq_subst {x y z : α} : compare x y = eq → compare x z = compare y z
  lt_trans {x y z : α} : compare x y = lt → compare y z = lt → compare x z = lt
  gt_trans {x y z : α} : compare x y = gt → compare y z = gt → compare x z = gt
export TransOrd (eq_refl eq_subst lt_trans gt_trans)

class LawfulOrd : Prop where
  eq_refl (x : α) : compare x x = eq
  eq_tight {x y : α} : compare x y = eq → x = y
  lt_trans {x y z : α} : compare x y = lt → compare y z = lt → compare x z = lt
  gt_trans {x y z : α} : compare x y = gt → compare y z = gt → compare x z = gt
export LawfulOrd (eq_tight)

instance [LawfulOrd α] : TransOrd α where
  eq_refl := LawfulOrd.eq_refl 
  eq_subst h := (eq_tight h) ▸ rfl
  lt_trans := LawfulOrd.lt_trans
  gt_trans := LawfulOrd.gt_trans

namespace Ord

section TransOrd
variable {α} [Ord α] [TransOrd α]

theorem lt_irrefl (x : α) : compare x x ≠ lt := eq_refl x ▸ Ordering.noConfusion

theorem gt_irrefl (x : α) : compare x x ≠ gt := eq_refl x ▸ Ordering.noConfusion

theorem eq_trans {x y z : α} (hxy : compare x y = eq) (hyz : compare y z = eq) : compare x z = eq := by
  rw [eq_subst hxy, hyz]

theorem symm (x y : α) : compare x y = (compare y x).opp := by
  rw [Ordering.opp]
  match hxy : compare x y, hyx : compare y x with
  | lt, lt => 
    have h : compare x x = lt := by
      exact lt_trans hxy hyx
    rw [eq_refl] at h
    contradiction
  | lt, eq => 
    have h : compare y y = lt := by
      rw [eq_subst hyx]
      exact hxy
    rw [eq_refl] at h
    contradiction
  | lt, gt => rfl
  | eq, lt => 
    have h : compare x x = lt := by
      rw [eq_subst hxy]
      exact hyx
    rw [eq_refl] at h
    contradiction
  | eq, eq => rfl
  | eq, gt => 
    have h : compare x x = gt := by 
      rw [eq_subst hxy]
      exact hyx
    rw [eq_refl] at h
    contradiction
  | gt, lt => rfl
  | gt, eq => 
    have h : compare y y = gt := by 
      rw [eq_subst hyx]
      exact hxy
    rw [eq_refl] at h
    contradiction
  | gt, gt => 
    have h : compare y y = gt := by 
      exact gt_trans hyx hxy
    rw [eq_refl] at h
    contradiction

theorem eq_symm {x y : α} : compare x y = eq → compare y x = eq := by
  intro h; rw [symm, h]; rfl

theorem lt_of_gt_symm {x y : α} : compare x y = gt → compare y x = lt := by
  intro h; rw [symm, h]; rfl

theorem gt_of_lt_symm {x y : α} : compare x y = lt → compare y x = gt := by
  intro h; rw [symm, h]; rfl

theorem eq_of_eq_of_eq {x y z : α} : compare x y = eq → compare y z = eq → compare x z = eq := by exact eq_trans

theorem lt_of_lt_of_lt {x y z : α} : compare x y = lt → compare y z = lt → compare x z = lt := by exact lt_trans

theorem gt_of_gt_of_gt {x y z : α} : compare x y = gt → compare y z = gt → compare x z = gt := by exact gt_trans

theorem lt_of_eq_of_lt {x y z : α} : compare x y = eq → compare y z = lt → compare x z = lt := by intro h hyz; rw [eq_subst h, hyz]

theorem gt_of_eq_of_gt {x y z : α} : compare x y = eq → compare y z = gt → compare x z = gt := by intro h hyz; rw [eq_subst h, hyz]

theorem lt_of_lt_of_eq {x y z : α} : compare x y = lt → compare y z = eq → compare x z = lt := by 
  intro hxy hyz 
  rw [symm, Ordering.eq_opp_iff_opp_eq] at hxy hyz ⊢
  exact gt_of_eq_of_gt hyz hxy

theorem gt_of_gt_of_eq {x y z : α} : compare x y = gt → compare y z = eq → compare x z = gt := by
  intro hxy hyz 
  rw [symm, Ordering.eq_opp_iff_opp_eq] at hxy hyz ⊢
  exact lt_of_eq_of_lt hyz hxy

end TransOrd

section LawfulOrd
variable {α} [Ord α] [LawfulOrd α]

theorem connex {x y : α} : x ≠ y → compare x y = lt ∨ compare x y = gt := by
  intro hne
  match hxy : compare x y with
  | lt => left; rfl
  | eq => absurd hne; exact eq_tight hxy
  | gt => right; rfl

theorem antisymm {x y : α} : compare x y ≠ lt → compare x y ≠ gt → x = y := by
  intro nlt ngt
  match hxy : compare x y with
  | lt => absurd nlt; exact hxy
  | eq => exact eq_tight hxy
  | gt => absurd ngt; exact hxy

end LawfulOrd

section LELT
variable {α} [Ord α]

scoped instance (priority:=low) instLT (α) [Ord α] : LT α := ⟨λ x y => Ord.compare x y = lt⟩
scoped instance (priority:=low) instLE (α) [Ord α] : LE α := ⟨λ x y => Ord.compare x y ≠ gt⟩

instance : DecidableRel (instLT α).lt := λ x y => inferDecidable (Ord.compare x y = lt)
instance : DecidableRel (instLE α).le := λ x y => inferDecidable (Ord.compare x y ≠ gt)

theorem lt_iff_compare_eq_lt (x y : α) : x < y ↔ compare x y = lt := Iff.rfl

theorem le_iff_compare_ne_gt (x y : α) : x ≤ y ↔ compare x y ≠ gt := Iff.rfl

theorem gt_iff_compare_eq_gt [TransOrd α] (x y : α) : x > y ↔ compare x y = gt := by
  rw [symm, Ordering.eq_opp_iff_opp_eq]; exact Iff.rfl

theorem ge_iff_compare_ne_lt [TransOrd α] (x y : α) : x ≥ y ↔ compare x y ≠ lt :=
  show compare y x ≠ gt ↔ compare x y ≠ lt by
  apply Iff.mt; rw [symm, Ordering.eq_opp_iff_opp_eq]; exact Iff.rfl

theorem eq_iff_compare_eq_eq [LawfulOrd α] (x y : α) : x = y ↔ compare x y = eq :=
  ⟨fun | rfl => eq_refl x, eq_tight⟩

theorem ne_iff_compare_ne_eq [LawfulOrd α] (x y : α) : x ≠ y ↔ compare x y ≠ eq := by
  apply Iff.mt; apply Iff.symm; exact eq_iff_compare_eq_eq ..

theorem le_trans [TransOrd α] {x y z : α} : x ≤ y → y ≤ z → x ≤ z := by
  intro hxy hyz cxz
  rw [le_iff_compare_ne_gt] at hxy hyz
  match cxy : compare x y, cyz : compare y z with
  | lt, lt => rw [lt_of_lt_of_lt cxy cyz] at cxz; contradiction
  | lt, eq => rw [lt_of_lt_of_eq cxy cyz] at cxz; contradiction
  | eq, lt => rw [lt_of_eq_of_lt cxy cyz] at cxz; contradiction
  | eq, eq => rw [eq_of_eq_of_eq cxy cyz] at cxz; contradiction
  | gt, _ => contradiction
  | _, gt => contradiction

theorem lt_of_le_of_lt [TransOrd α] {x y z : α} : x < y → y ≤ z → x < z := by
  intro cxy hyz
  rw [lt_iff_compare_eq_lt] at cxy ⊢
  rw [le_iff_compare_ne_gt] at hyz
  match cyz : compare y z with
  | lt => rw [lt_of_lt_of_lt cxy cyz]
  | eq => rw [lt_of_lt_of_eq cxy cyz]
  | gt => contradiction

theorem lt_of_lt_of_le [TransOrd α] {x y z : α} : x ≤ y → y < z → x < z := by
  intro hxy cyz
  rw [le_iff_compare_ne_gt] at hxy
  rw [lt_iff_compare_eq_lt] at cyz ⊢
  match cxy : compare x y with
  | lt => rw [lt_of_lt_of_lt cxy cyz]
  | eq => rw [lt_of_eq_of_lt cxy cyz]
  | gt => contradiction

theorem le_antisymm [LawfulOrd α] {x y : α} : x ≤ y → y ≤ x → x = y := by
  intro hxy hyx
  rw [le_iff_compare_ne_gt] at hxy hyx
  rw [symm] at hyx
  match cxy : compare x y with
  | lt => absurd hyx; rw [cxy]; rfl
  | eq => exact eq_tight cxy
  | gt => absurd hxy; rw [cxy]

theorem le_total [TransOrd α] (x y : α) : x ≤ y ∨ y ≤ x := by
  rw [le_iff_compare_ne_gt, le_iff_compare_ne_gt]
  match cxy : compare x y with
  | lt => left; trivial
  | eq => left; trivial
  | gt => right; rw [symm, cxy]; trivial

theorem lt_connex [LawfulOrd α] {x y : α} : x ≠ y → x < y ∨ y < x := by
  intro hne
  rw [lt_iff_compare_eq_lt, lt_iff_compare_eq_lt]
  match cxy : compare x y with
  | lt => left; rfl
  | eq => absurd hne; exact eq_tight cxy
  | gt => right; rw [symm, cxy]; rfl

theorem lt_comparison [TransOrd α] {x y : α} : x < y → (z : α) → x < z ∨ z < y := by
  intro hxy z
  rw [lt_iff_compare_eq_lt] at hxy
  rw [lt_iff_compare_eq_lt, lt_iff_compare_eq_lt]
  match cxz : compare x z, czy : compare z y with
  | lt, _ => left; rfl
  | _, lt =>  right; rfl
  | eq, eq => rw [eq_of_eq_of_eq cxz czy] at hxy; contradiction
  | eq, gt => rw [gt_of_eq_of_gt cxz czy] at hxy; contradiction
  | gt, eq => rw [gt_of_gt_of_eq cxz czy] at hxy; contradiction
  | gt, gt => rw [gt_of_gt_of_gt cxz czy] at hxy; contradiction

end LELT

open Relation

instance [TransOrd α] : Irreflexive (α:=α) (.<.) := ⟨lt_irrefl⟩
instance [TransOrd α] : Transitive (α:=α) (.<.) := ⟨lt_trans⟩
instance [TransOrd α] : Reflexive (α:=α) (.≤.) := ⟨gt_irrefl⟩
instance [TransOrd α] : Transitive (α:=α) (.<.) := ⟨lt_trans⟩
instance [TransOrd α] : HTransitive (α:=α) (β:=α) (γ:=α) (.<.) (.≤.) (.<.) := ⟨lt_of_le_of_lt⟩
instance [TransOrd α] : HTransitive (α:=α) (β:=α) (γ:=α) (.≤.) (.<.) (.<.) := ⟨lt_of_lt_of_le⟩
instance [TransOrd α] : Total (α:=α) (.≤.) := ⟨le_total⟩
instance [TransOrd α] : Comparison (α:=α) (.<.) := ⟨lt_comparison⟩
instance [LawfulOrd α] : Antisymmetric (α:=α) (.≤.) := ⟨le_antisymm⟩
instance [LawfulOrd α] : Connex (α:=α) (.<.) := ⟨lt_connex⟩

end Ord

