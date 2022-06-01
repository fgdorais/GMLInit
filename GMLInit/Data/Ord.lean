import GMLInit.Data.Basic
import GMLInit.Logic.Relation

namespace Ord
variable (α) [Ord α]

open Ordering (lt eq gt)

scoped instance instOrdLT : LT α := ⟨λ x y => Ord.compare x y = lt⟩

scoped instance instOrdLE : LE α := ⟨λ x y => Ord.compare x y ≠ gt⟩

scoped instance instOrdBEq : BEq α := ⟨λ x y => Ord.compare x y = eq⟩

instance : DecidableRel (instOrdLT α).lt := λ x y => inferDecidable (Ord.compare x y = lt)

instance : DecidableRel (instOrdLE α).le := λ x y => inferDecidable (Ord.compare x y ≠ gt)

theorem lt_def {x y : α} : x < y ↔ Ord.compare x y = lt := Iff.rfl

theorem le_def {x y : α} : x ≤ y ↔ Ord.compare x y ≠ gt := Iff.rfl

class TransOrd : Prop where
  eq_refl (x : α) : compare x x = eq
  lt_trans {x y z : α} : compare x y = lt → compare y z = lt → compare x z = lt
  gt_trans {x y z : α} : compare x y = gt → compare y z = gt → compare x z = gt
  lt_of_lt_of_eq {x y z : α} : compare x y = lt → compare y z = eq → compare x z = lt
  lt_of_eq_of_lt {x y z : α} : compare x y = eq → compare y z = lt → compare x z = lt
  gt_of_gt_of_eq {x y z : α} : compare x y = gt → compare y z = eq → compare x z = gt
  gt_of_eq_of_gt {x y z : α} : compare x y = eq → compare y z = gt → compare x z = gt
export TransOrd (eq_refl lt_trans gt_trans lt_of_lt_of_eq lt_of_eq_of_lt gt_of_gt_of_eq gt_of_eq_of_gt)

class LawfulOrd : Prop where
  eq_refl (x : α) : compare x x = eq
  eq_tight {x y : α} : compare x y = eq → x = y
  lt_trans {x y z : α} : compare x y = lt → compare y z = lt → compare x z = lt
  gt_trans {x y z : α} : compare x y = gt → compare y z = gt → compare x z = gt
export LawfulOrd (eq_tight)

section TransOrd
variable {α} [ord : Ord α] [TransOrd α]

theorem lt_of_lt_of_lt {x y z : α} : compare x y = lt → compare y z = lt → compare x z = lt := lt_trans

theorem gt_of_gt_of_gt {x y z : α} : compare x y = gt → compare y z = gt → compare x z = gt := gt_trans

theorem lt_irrefl (x : α) : compare x x ≠ lt := eq_refl x ▸ Ordering.noConfusion

theorem gt_irrefl (x : α) : compare x x ≠ gt := eq_refl x ▸ Ordering.noConfusion

theorem lt_of_gt_symm {x y : α} (hyx : compare y x = gt) : compare x y = lt :=
  match hxy : compare x y with
  | lt => rfl
  | eq => absurd (gt_of_eq_of_gt hxy hyx) (eq_refl x ▸ Ordering.noConfusion)
  | gt => absurd (gt_of_gt_of_gt hxy hyx) (eq_refl x ▸ Ordering.noConfusion)

theorem gt_of_lt_symm {x y : α} (hyx : compare y x = lt) : compare x y = gt :=
  match hxy : compare x y with
  | lt => absurd (lt_of_lt_of_lt hxy hyx) (eq_refl x ▸ Ordering.noConfusion)
  | eq => absurd (lt_of_eq_of_lt hxy hyx) (eq_refl x ▸ Ordering.noConfusion)
  | gt => rfl

theorem eq_symm {x y : α} (hyx : compare y x = eq) : compare x y = eq :=
  match hxy : compare x y with
  | lt => absurd (lt_of_lt_of_eq hxy hyx) (eq_refl x ▸ Ordering.noConfusion)
  | eq => rfl
  | gt => absurd (gt_of_gt_of_eq hxy hyx) (eq_refl x ▸ Ordering.noConfusion)

theorem eq_trans {x y z : α} (hxy : compare x y = eq) (hyz : compare y z = eq) : compare x z = eq :=
  match hzx : compare z x with
  | lt => absurd (lt_of_eq_of_lt hyz hzx) (eq_symm hxy ▸ Ordering.noConfusion)
  | eq => eq_symm hzx
  | gt => absurd (gt_of_gt_of_eq hzx hxy) (eq_symm hyz ▸ Ordering.noConfusion)

theorem le_refl (x : α) : x ≤ x := fun h => absurd h (eq_refl x ▸ Ordering.noConfusion)

theorem le_trans {x y z : α} : x ≤ y → y ≤ z → x ≤ z :=
  fun (nxy : compare x y ≠ gt) (nyz : compare y z ≠ gt) hxz =>
  match hxy : compare x y, hyz : compare y z with
  | _, gt => absurd hyz nyz
  | gt, _ => absurd hxy nxy
  | lt, lt => absurd (lt_trans hxy hyz) (hxz ▸ Ordering.noConfusion)
  | lt, eq => absurd (lt_of_lt_of_eq hxy hyz) (hxz ▸ Ordering.noConfusion)
  | eq, lt => absurd (lt_of_eq_of_lt hxy hyz) (hxz ▸ Ordering.noConfusion)
  | eq, eq => absurd (eq_trans hxy hyz) (hxz ▸ Ordering.noConfusion)

theorem lt_of_le_of_lt {x y z : α} : x ≤ y → y < z → x < z := by
  intro nxy hyz
  match hxy : compare x y with
  | lt => exact lt_trans hxy hyz
  | eq => exact lt_of_eq_of_lt hxy hyz
  | gt => absurd hxy; exact nxy

theorem lt_of_lt_of_le {x y z : α} : x < y → y ≤ z → x < z := by
  intro hxy nyz
  match hyz : compare y z with
  | lt => exact lt_trans hxy hyz
  | eq => exact lt_of_lt_of_eq hxy hyz
  | gt => absurd hyz; exact nyz

instance : Relation.Reflexive (α:=α) (.≤.) := ⟨le_refl⟩
instance : Relation.Irreflexive (α:=α) (.<.) := ⟨lt_irrefl⟩
instance : Relation.Transitive (α:=α) (.≤.) := ⟨le_trans⟩
instance : Relation.Transitive (α:=α) (.<.) := ⟨lt_trans⟩
instance : Relation.HTransitive (α:=α) (.<.) (.≤.) (.<.) := ⟨lt_of_lt_of_le⟩
instance : Relation.HTransitive (α:=α) (.≤.) (.<.) (.<.) := ⟨lt_of_le_of_lt⟩

end TransOrd

section LawfulOrd
variable {α} [Ord α] [LawfulOrd α]

theorem eq_iff_eq (x y : α) : compare x y = eq ↔ x = y := ⟨eq_tight, fun | rfl => LawfulOrd.eq_refl _⟩

instance : TransOrd α where
  eq_refl := LawfulOrd.eq_refl
  lt_trans := LawfulOrd.lt_trans
  gt_trans := LawfulOrd.gt_trans
  lt_of_lt_of_eq {x y z : α} (hxy : compare x y = lt) (hyz : compare y z = eq) := match eq_tight hyz with | rfl => hxy
  lt_of_eq_of_lt {x y z : α} (hxy : compare x y = eq) (hyz : compare y z = lt) := match eq_tight hxy with | rfl => hyz
  gt_of_gt_of_eq {x y z : α} (hxy : compare x y = gt) (hyz : compare y z = eq) := match eq_tight hyz with | rfl => hxy
  gt_of_eq_of_gt {x y z : α} (hxy : compare x y = eq) (hyz : compare y z = gt) := match eq_tight hxy with | rfl => hyz

theorem le_antisymm {x y : α} (nxy : x ≤ y) (nyx : x ≥ y) : x = y :=
  eq_tight $ match hxy : compare x y with
  | lt => absurd (gt_of_lt_symm hxy) nyx
  | eq => rfl
  | gt => absurd hxy nxy

instance : Relation.Antisymmetric (α:=α) (.≤.) := ⟨le_antisymm⟩

instance : DecidableEq α := fun x y =>
  match h : compare x y with
  | lt => isFalse fun | rfl => Ordering.noConfusion (eq_refl x ▸ h)
  | eq => isTrue (eq_tight h)
  | gt => isFalse fun | rfl => Ordering.noConfusion (eq_refl x ▸ h)

end LawfulOrd

end Ord
