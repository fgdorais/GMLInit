import GMLInit.Data.Basic
import GMLInit.Meta.Basic

open Ordering (lt eq gt)

class Batteries.LinearCmp {α} (cmp : α → α → Ordering) extends TransCmp cmp : Prop where
  eq_strict {x y : α} : cmp x y = eq → x = y

class abbrev Batteries.LinearOrd (α) [Ord α] : Prop := Batteries.LinearCmp (α:=α) Ord.compare

namespace Ord
open Batteries
variable {α} [Ord α]

theorem eq_refl [OrientedOrd α] (x : α) : compare x x = eq := OrientedCmp.cmp_refl

theorem lt_irrefl [OrientedOrd α] (x : α) : compare x x ≠ lt := eq_refl x ▸ Ordering.noConfusion

theorem gt_irrefl [OrientedOrd α] (x : α) : compare x x ≠ gt := eq_refl x ▸ Ordering.noConfusion

theorem ne_irrefl [OrientedOrd α] (x : α) : ¬(compare x x ≠ eq) := absurd (eq_refl x)

theorem le_refl [OrientedOrd α] (x : α) : compare x x ≠ gt := gt_irrefl x

theorem ge_refl [OrientedOrd α] (x : α) : compare x x ≠ lt := lt_irrefl x

theorem eq_symm [OrientedOrd α] {x y : α} : compare x y = eq → compare y x = eq := OrientedCmp.cmp_eq_eq_symm.mp

theorem gt_of_lt_opp [OrientedOrd α] {x y : α} : compare x y = lt → compare y x = gt := OrientedCmp.cmp_eq_gt.mpr

theorem lt_of_gt_opp [OrientedOrd α] {x y : α} : compare x y = gt → compare y x = lt := OrientedCmp.cmp_eq_gt.mp

theorem ge_of_le_opp [OrientedOrd α] {x y : α} : compare x y ≠ gt → compare y x ≠ lt := mt gt_of_lt_opp

theorem le_of_ge_opp [OrientedOrd α] {x y : α} : compare x y ≠ lt → compare y x ≠ gt := mt lt_of_gt_opp

theorem le_total [OrientedOrd α] (x y : α) : compare x y ≠ gt ∨ compare y x ≠ gt :=
  match hxy : compare x y with
  | lt => Or.inl Ordering.noConfusion
  | eq => Or.inl Ordering.noConfusion
  | gt => Or.inr fun h => Ordering.noConfusion (Eq.trans (lt_of_gt_opp h).symm hxy)

theorem ge_total [OrientedOrd α] (x y : α) : compare x y ≠ lt ∨ compare y x ≠ lt :=
  match hxy : compare x y with
  | lt => Or.inr fun h => Ordering.noConfusion (Eq.trans (gt_of_lt_opp h).symm hxy)
  | eq => Or.inl Ordering.noConfusion
  | gt => Or.inl Ordering.noConfusion

theorem lt_asymm [OrientedOrd α] {x y : α} : compare x y = lt → compare y x ≠ lt := fun hxy => gt_of_lt_opp hxy ▸ Ordering.noConfusion

theorem gt_asymm [OrientedOrd α] {x y : α} : compare x y = gt → compare y x ≠ gt := fun hxy => lt_of_gt_opp hxy ▸ Ordering.noConfusion

theorem eq_subst_left [TransOrd α] {x y z : α} : compare x y = eq → compare x z = compare y z := TransCmp.cmp_congr_left

theorem eq_subst_right [TransOrd α] {x y z : α} : compare x y = eq → compare z x = compare z y := TransCmp.cmp_congr_right

theorem eq_trans [TransOrd α] {x y z : α} : compare x y = eq → compare y z = eq → compare x z = eq := fun hxy hyz => eq_subst_left hxy ▸ hyz

theorem lt_trans [TransOrd α] {x y z : α} : compare x y = lt → compare y z = lt → compare x z = lt := TransCmp.lt_trans

theorem gt_trans [TransOrd α] {x y z : α} : compare x y = gt → compare y z = gt → compare x z = gt := TransCmp.gt_trans

theorem le_trans [TransOrd α] {x y z : α} : compare x y ≠ gt → compare y z ≠ gt → compare x z ≠ gt := TransCmp.le_trans

theorem ge_trans [TransOrd α] {x y z : α} : compare x y ≠ lt → compare y z ≠ lt → compare x z ≠ lt := TransCmp.ge_trans

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

theorem eq_strict [LinearOrd α] {x y : α} : compare x y = eq → x = y := LinearCmp.eq_strict

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

theorem le_antisymm [LinearOrd α] {x y : α} : compare x y ≠ gt → compare y x ≠ gt → x = y :=
  fun nxy nyx => antisymm (ge_of_le_opp nyx) nxy

theorem ge_antisymm [LinearOrd α] {x y : α} : compare x y ≠ lt → compare y x ≠ lt → x = y :=
  fun nxy nyx => antisymm nxy (le_of_ge_opp nyx)

theorem lt_or_gt_of_ne {x y : α} : compare x y ≠ eq → compare x y = lt ∨ compare x y = gt :=
  fun hne => match h : compare x y with
  | lt => .inl rfl
  | eq => absurd h hne
  | gt => .inr rfl

theorem lt_connex [LinearOrd α] {x y : α} : x ≠ y → compare x y = lt ∨ compare y x = lt :=
  fun hne => match lt_or_gt_of_ne (mt eq_strict hne) with
  | .inl h => .inl h
  | .inr h => .inr (lt_of_gt_opp h)

theorem gt_connex [LinearOrd α] {x y : α} : x ≠ y → compare x y = gt ∨ compare y x = gt :=
  fun hne => match lt_or_gt_of_ne (mt eq_strict hne) with
  | .inr h => .inl h
  | .inl h => .inr (gt_of_lt_opp h)

section LELT
open Logic

local instance instLE : LE α := ⟨fun x y => compare x y ≠ gt⟩
local instance instLT : LT α := ⟨fun x y => compare x y = lt⟩

instance [OrientedOrd α] : Reflexive (α:=α) (.≤.) := ⟨le_refl⟩
instance [OrientedOrd α] : Irreflexive (α:=α) (.<.) := ⟨lt_irrefl⟩
instance [OrientedOrd α] : Total (α:=α) (.≤.) := ⟨le_total⟩
instance [TransOrd α] : Transitive (α:=α) (.≤.) := ⟨le_trans⟩
instance [TransOrd α] : Transitive (α:=α) (.<.) := ⟨lt_trans⟩
instance [TransOrd α] : HTransitive (α:=α) (β:=α) (γ:=α) (.≤.) (.<.) (.<.) := ⟨lt_of_le_of_lt⟩
instance [TransOrd α] : HTransitive (α:=α) (β:=α) (γ:=α) (.<.) (.≤.) (.<.) := ⟨lt_of_lt_of_le⟩
instance [LinearOrd α] : Antisymmetric (α:=α) (.≤.) := ⟨le_antisymm⟩
instance [LinearOrd α] : Connex (α:=α) (.<.) := ⟨lt_connex⟩

end LELT

end Ord
