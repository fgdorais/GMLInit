import GMLInit.Data.Basic
import GMLInit.Logic.Relation
import GMLInit.Meta.Decidable

open Ordering (lt eq gt)

class Std.LinearCmp {α} (cmp : α → α → Ordering) extends TransCmp cmp : Prop where
  eq_strict {x y : α} : cmp x y = eq → x = y

class abbrev OrientedOrd (α) [Ord α] : Prop := Std.OrientedCmp (α:=α) Ord.compare

class abbrev TransOrd (α) [Ord α] : Prop := Std.TransCmp (α:=α) Ord.compare

class abbrev LinearOrd (α) [Ord α] : Prop := Std.LinearCmp (α:=α) Ord.compare

namespace Ord
variable {α} [Ord α]

theorem eq_refl [OrientedOrd α] (x : α) : compare x x = eq := Std.OrientedCmp.cmp_refl

theorem lt_irrefl [OrientedOrd α] (x : α) : compare x x ≠ lt := eq_refl x ▸ Ordering.noConfusion

theorem gt_irrefl [OrientedOrd α] (x : α) : compare x x ≠ gt := eq_refl x ▸ Ordering.noConfusion

theorem ne_irrefl [OrientedOrd α] (x : α) : ¬(compare x x ≠ eq) := absurd (eq_refl x)

theorem le_refl [OrientedOrd α] (x : α) : compare x x ≠ gt := gt_irrefl x

theorem ge_refl [OrientedOrd α] (x : α) : compare x x ≠ lt := lt_irrefl x

theorem eq_symm [OrientedOrd α] {x y : α} : compare x y = eq → compare y x = eq := Std.OrientedCmp.cmp_eq_eq_symm.mp

theorem gt_of_lt_opp [OrientedOrd α] {x y : α} : compare x y = lt → compare y x = gt := Std.OrientedCmp.cmp_eq_gt.mpr

theorem lt_of_gt_opp [OrientedOrd α] {x y : α} : compare x y = gt → compare y x = lt := Std.OrientedCmp.cmp_eq_gt.mp

theorem lt_asymm [OrientedOrd α] {x y : α} : compare x y = lt → compare y x ≠ lt := fun hxy => gt_of_lt_opp hxy ▸ Ordering.noConfusion

theorem gt_asymm [OrientedOrd α] {x y : α} : compare x y = gt → compare y x ≠ gt := fun hxy => lt_of_gt_opp hxy ▸ Ordering.noConfusion

theorem eq_subst_left [TransOrd α] {x y z : α} : compare x y = eq → compare x z = compare y z := Std.TransCmp.cmp_congr_left

theorem eq_subst_right [TransOrd α] {x y z : α} : compare x y = eq → compare z x = compare z y := Std.TransCmp.cmp_congr_right

theorem eq_trans [TransOrd α] {x y z : α} : compare x y = eq → compare y z = eq → compare x z = eq := fun hxy hyz => eq_subst_left hxy ▸ hyz

theorem lt_trans [TransOrd α] {x y z : α} : compare x y = lt → compare y z = lt → compare x z = lt := Std.TransCmp.lt_trans

theorem gt_trans [TransOrd α] {x y z : α} : compare x y = gt → compare y z = gt → compare x z = gt := Std.TransCmp.gt_trans

theorem le_trans [TransOrd α] {x y z : α} : compare x y ≠ gt → compare y z ≠ gt → compare x z ≠ gt := Std.TransCmp.le_trans

theorem ge_trans [TransOrd α] {x y z : α} : compare x y ≠ lt → compare y z ≠ lt → compare x z ≠ lt := Std.TransCmp.ge_trans

theorem lt_of_lt_of_le [TransOrd α] {x y z : α} : compare x y = lt → compare y z ≠ gt → compare x z = lt :=
  fun hxy nyz => match hyz : compare y z with
  | lt => lt_trans hxy hyz
  | eq => eq_subst_right hyz ▸ hxy
  | gt => absurd hyz nyz

theorem lt_of_le_of_lt [TransOrd α] {x y z : α} : compare x y ≠ gt → compare y z = lt → compare x z = lt :=
  fun nxy hyz => match hxy : compare x y with
  | lt => lt_trans hxy hyz
  | eq => eq_subst_left hxy ▸ hyz
  | gt => absurd hxy nxy

theorem gt_of_gt_of_ge [TransOrd α] {x y z : α} : compare x y = gt → compare y z ≠ lt → compare x z = gt :=
  fun hxy nyz => match hyz : compare y z with
  | gt => gt_trans hxy hyz
  | eq => eq_subst_right hyz ▸ hxy
  | lt => absurd hyz nyz

theorem gt_of_ge_of_gt [TransOrd α] {x y z : α} : compare x y ≠ lt → compare y z = gt → compare x z = gt :=
  fun nxy hyz => match hxy : compare x y with
  | gt => gt_trans hxy hyz
  | eq => eq_subst_left hxy ▸ hyz
  | lt => absurd hxy nxy

theorem le_or_ge [TransOrd α] (x y : α) : compare x y ≠ gt ∨ compare x y ≠ lt :=
  match compare x y with
  | lt => Or.inl Ordering.noConfusion
  | eq => Or.inl Ordering.noConfusion
  | gt => Or.inr Ordering.noConfusion

theorem eq_strict [LinearOrd α] {x y : α} : compare x y = eq → x = y := Std.LinearCmp.eq_strict

theorem connex [LinearOrd α] {x y : α} : x ≠ y → compare x y = lt ∨ compare x y = gt :=
  fun hne => match hxy : compare x y with
  | lt => Or.inl rfl
  | eq => absurd (eq_strict hxy) hne
  | gt => Or.inr rfl

theorem antisymm [LinearOrd α] {x y : α} : compare x y ≠ lt → compare x y ≠ gt → x = y :=
  fun nlt ngt => match hxy : compare x y with
  | lt => absurd hxy nlt
  | eq => eq_strict hxy
  | gt => absurd hxy ngt

namespace Notation
set_option quotPrecheck false
scoped infix:50 (priority:=high) " < " => fun x y => Ord.compare x y = lt
scoped infix:50 (priority:=high) " <= " => fun x y => Ord.compare x y ≠ gt
scoped infix:50 (priority:=high) " > " => fun x y => Ord.compare x y = gt
scoped infix:50 (priority:=high) " >= " => fun x y => Ord.compare x y ≠ lt
scoped infix:50 (priority:=high) " == " => fun x y => Ord.compare x y = eq
scoped infix:50 (priority:=high) " != " => fun x y => Ord.compare x y ≠ eq
end Notation

section
variable (α) [Ord α]
open Notation Relation

instance [OrientedOrd α] : Reflexive (α:=α) (.==.) := ⟨eq_refl⟩
instance [OrientedOrd α] : Reflexive (α:=α) (.<=.) := ⟨le_refl⟩
instance [OrientedOrd α] : Reflexive (α:=α) (.>=.) := ⟨ge_refl⟩
instance [OrientedOrd α] : Irreflexive (α:=α) (.!=.) := ⟨ne_irrefl⟩
instance [OrientedOrd α] : Irreflexive (α:=α) (.<.) := ⟨lt_irrefl⟩
instance [OrientedOrd α] : Irreflexive (α:=α) (.>.) := ⟨gt_irrefl⟩
instance [TransOrd α] : Transitive (α:=α) (.==.) := ⟨eq_trans⟩
instance [TransOrd α] : Transitive (α:=α) (.<.) := ⟨lt_trans⟩
instance [TransOrd α] : Transitive (α:=α) (.<=.) := ⟨le_trans⟩
instance [TransOrd α] : Transitive (α:=α) (.>.) := ⟨gt_trans⟩
instance [TransOrd α] : Transitive (α:=α) (.>=.) := ⟨ge_trans⟩
instance [TransOrd α] : HTransitive (α:=α) (β:=α) (γ:=α) (.<.) (.<=.) (.<.) := ⟨lt_of_lt_of_le⟩
instance [TransOrd α] : HTransitive (α:=α) (β:=α) (γ:=α) (.<=.) (.<.) (.<.) := ⟨lt_of_le_of_lt⟩
instance [TransOrd α] : HTransitive (α:=α) (β:=α) (γ:=α) (.>.) (.>=.) (.>.) := ⟨gt_of_gt_of_ge⟩
instance [TransOrd α] : HTransitive (α:=α) (β:=α) (γ:=α) (.>=.) (.>.) (.>.) := ⟨gt_of_ge_of_gt⟩

end

end Ord
