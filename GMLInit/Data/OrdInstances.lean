import GMLInit.Data.Basic
import GMLInit.Data.Ord
import GMLInit.Data.Nat
import GMLInit.Data.Int
import GMLInit.Logic.Ordering
import GMLInit.Logic.Relation

open Relation
open Ordering (lt eq gt)

def compareOfLE {α} [LE α] [DecidableRel (α:=α) (.≤.)] (x y : α) : Ordering :=
  if x ≤ y then if y ≤ x then eq else lt else gt

namespace compareOfLE
variable {α} [LE α] [DecidableRel (α:=α) (.≤.)]

theorem eq_refl [Reflexive (α:=α) (.≤.)] (x : α) : compareOfLE x x = eq := by
  rw [compareOfLE]
  rw [if_pos (Reflexive.refl x)]
  rw [if_pos (Reflexive.refl x)]

theorem eq_subst [Transitive (α:=α) (.≤.)] {x y z : α} : compareOfLE x y = eq → compareOfLE x z = compareOfLE y z := by
  unfold compareOfLE
  intro h
  by_cases x ≤ y, y ≤ x with
  | isFalse nxy, _ => rw [if_neg nxy] at h; contradiction
  | _, isFalse nyx => rw [if_neg nyx] at h; split at h <;> contradiction
  | isTrue hxy, isTrue hyx =>
    by_cases x ≤ z, y ≤ z with
    | isFalse nxz, isFalse nyz => rw [if_neg nxz, if_neg nyz]
    | isTrue hxz, _ => 
      rw [if_pos hxz, if_pos (Transitive.trans hyx hxz)]
      by_cases z ≤ x, z ≤ y with
      | isFalse nzx, isFalse nzy => rw [if_neg nzx, if_neg nzy]
      | isTrue hzx, _ => rw [if_pos hzx, if_pos (Transitive.trans hzx hxy)]
      | _, isTrue hzy => rw [if_pos hzy, if_pos (Transitive.trans hzy hyx)]
    | _, isTrue hyz => 
      rw [if_pos hyz, if_pos (Transitive.trans hxy hyz)]
      by_cases z ≤ x, z ≤ y with
      | isFalse nzx, isFalse nzy => rw [if_neg nzx, if_neg nzy]
      | isTrue hzx, _ => rw [if_pos hzx, if_pos (Transitive.trans hzx hxy)]
      | _, isTrue hzy => rw [if_pos hzy, if_pos (Transitive.trans hzy hyx)]

theorem eq_tight [Antisymmetric (α:=α) (.≤.)] {x y : α} : compareOfLE x y = eq → x = y := by
  unfold compareOfLE
  intro h
  by_cases x ≤ y, y ≤ x with
  | isFalse nxy, _ => rw [if_neg nxy] at h; contradiction
  | _, isFalse nyx => rw [if_neg nyx] at h; split at h <;> contradiction
  | isTrue hxy, isTrue hyx => 
    exact Antisymmetric.antisymm hxy hyx

theorem gt_trans [Transitive (α:=α) (.≤.)] [Total (α:=α) (.≤.)] {x y z : α} : compareOfLE x y = gt → compareOfLE y z = gt → compareOfLE x z = gt := by
  unfold compareOfLE
  intro cxy cyz
  by_cases x ≤ y, y ≤ z, x ≤ z with
  | isTrue hxy, _, _ => rw [if_pos hxy] at cxy; split at cxy <;> contradiction
  | _, isTrue hyz, _ => rw [if_pos hyz] at cyz; split at cyz <;> contradiction
  | _, _, isFalse nxz => rw [if_neg nxz]
  | isFalse nxy, isFalse nyz, isTrue hxz =>
    cases Total.total (r:=(.≤.)) x y with
    | inl hxy => absurd hxy; exact nxy
    | inr hyx => 
      rw [if_pos (Transitive.trans hyx hxz)] at cyz
      split at cyz <;> contradiction

theorem lt_trans [Transitive (α:=α) (.≤.)] [Total (α:=α) (.≤.)] {x y z : α} : compareOfLE x y = lt → compareOfLE y z = lt → compareOfLE x z = lt := by
  unfold compareOfLE
  intro cxy cyz
  cases Total.total (r:=(.≤.)) x y with
  | inr hyx => rw [if_pos hyx] at cxy; split at cxy <;> contradiction
  | inl hxy =>
    cases Total.total (r:=(.≤.)) y z with
    | inr hzy => rw [if_pos hzy] at cyz; split at cyz <;> contradiction
    | inl hyz => 
      rw [if_pos (Transitive.trans hxy hyz)]
      by_cases z ≤ x with
      | isFalse nzx => rw [if_neg nzx]
      | isTrue hzx => 
        rw [if_pos (Transitive.trans hzx hxy)] at cyz
        split at cyz <;> contradiction

variable (α) [LE α] [DecidableRel (α:=α) (.≤.)]

scoped instance instOrd : Ord α := ⟨compareOfLE⟩

instance instTransOrd [TotalPreorder (α:=α) (.≤.)] : TransOrd α where
  eq_refl := eq_refl
  eq_subst := eq_subst
  lt_trans := lt_trans
  gt_trans := gt_trans

instance instLawfulOrd [TotalOrder (α:=α) (.≤.)] : LawfulOrd α where
  eq_refl := eq_refl
  eq_tight := eq_tight
  lt_trans := lt_trans
  gt_trans := gt_trans

end compareOfLE

def compareOfLT {α} [LT α] [DecidableRel (α:=α) (.<.)] (x y : α) : Ordering :=
  if x < y then lt else if y < x then gt else eq

namespace compareOfLT
variable {α} [inst : LT α] [DecidableRel (α:=α) (.<.)]

theorem eq_refl [Irreflexive (α:=α) (.<.)] (x : α) : compareOfLT x x = eq := by
  unfold compareOfLT
  rw [if_neg (Irreflexive.irrefl x)]
  rw [if_neg (Irreflexive.irrefl x)]

theorem eq_subst {x y z : α} [Transitive (α:=α) (.<.)] [Comparison (α:=α) (.<.)] : compareOfLT x y = eq → compareOfLT x z = compareOfLT y z := by
  unfold compareOfLT
  intro heq
  by_cases x < y, y < x with
  | isTrue hxy, _ => rw [if_pos hxy] at heq; contradiction
  | isFalse nxy, isTrue hyx => rw [if_neg nxy, if_pos hyx] at heq; contradiction
  | isFalse nxy, isFalse nyx =>
    by_cases x < z, y < z with
    | isTrue hxz, isTrue hyz => 
      rw [if_pos hxz, if_pos hyz]
    | isTrue hxz, isFalse nyz => 
      cases Comparison.compare hxz y with
      | inl hxy => absurd hxy; exact nxy
      | inr hyz => absurd hyz; exact nyz
    | isFalse nxz, isTrue hyz =>
      cases Comparison.compare hyz x with
      | inl hyx => absurd hyx; exact nyx
      | inr hxz => absurd hxz; exact nxz
    | isFalse nxz, isFalse nyz =>
      rw [if_neg nxz, if_neg nyz]
      by_cases z < x, z < y with
      | isTrue hzx, isTrue hzy =>
        rw [if_pos hzx, if_pos hzy]
      | isTrue hzx, isFalse nzy =>
        cases Comparison.compare hzx y with
        | inl hzy => absurd hzy; exact nzy
        | inr hyx => absurd hyx; exact nyx
      | isFalse nzx, isTrue hzy =>
        cases Comparison.compare hzy x with
        | inl hzx => absurd hzx; exact nzx
        | inr hxy => absurd hxy; exact nxy
      | isFalse nzx, isFalse nzy =>
        rw [if_neg nzx, if_neg nzy]

theorem eq_tight {x y : α} [StableEq α] [Connex (α:=α) (.<.)] : compareOfLT x y = eq → x = y := by
  unfold compareOfLT
  intro heq
  by_contradiction
  | assuming hne =>
    cases Connex.connex (r:=(.<.)) hne with
    | inl => 
      split at heq
      next => contradiction
      next => contradiction
    | inr => 
      split at heq
      next => contradiction
      next => contradiction

theorem lt_trans [Transitive (α:=α) (.<.)] {x y z : α} : compareOfLT x y = lt → compareOfLT y z = lt → compareOfLT x z = lt := by
  unfold compareOfLT
  intro cxy cyz
  by_cases x < z, x < y, y < z with
  | isTrue hxz, _, _ =>
    rw [if_pos hxz]
  | isFalse nxz, isTrue hxy, isTrue hyz =>
    absurd nxz
    exact Transitive.trans hxy hyz
  | _, _, isFalse nyz =>
    rw [if_neg nyz] at cyz 
    split at cyz <;> contradiction
  | _, isFalse nxy, _ => 
    rw [if_neg nxy] at cxy
    split at cxy <;> contradiction

theorem gt_trans [Irreflexive (α:=α) (.<.)] [Transitive (α:=α) (.<.)] {x y z : α} : compareOfLT x y = gt → compareOfLT y z = gt → compareOfLT x z = gt := by
  unfold compareOfLT
  intro cxy cyz
  by_cases z < x, y < x, z < y with
  | isTrue hzx, _, _ =>
    have nxz : ¬ x < z := by
      intro hxz
      absurd (Transitive.trans hxz hzx)
      exact Irreflexive.irrfl
    rw [if_pos hzx, if_neg nxz]
  | isFalse nzx, isTrue hyx, isTrue hzy =>
    absurd nzx
    exact Transitive.trans hzy hyx
  | _, isFalse nyx, _ => 
    rw [if_neg nyx] at cxy
    split at cxy <;> contradiction
  | _, _, isFalse nzy =>
    rw [if_neg nzy] at cyz
    split at cyz <;> contradiction

variable (α) [LT α] [DecidableRel (α:=α) (.<.)]

scoped instance instOrd : Ord α := ⟨compareOfLT⟩

instance instTransOrd [LinearQuasiorder (α:=α) (.<.)] : TransOrd α where
  eq_refl := eq_refl
  eq_subst := eq_subst
  lt_trans := lt_trans
  gt_trans := gt_trans

instance instLawfulOrd [StableEq α] [LinearOrder (α:=α) (.<.)] : LawfulOrd α where
  eq_refl := eq_refl
  eq_tight := eq_tight
  lt_trans := lt_trans
  gt_trans := gt_trans

end compareOfLT

namespace compareOfLessAndEq
variable {α} [LT α] [DecidableRel (α:=α) (.<.)] [DecidableEq α]

theorem eq_refl [Irreflexive (α:=α) (.<.)] (x : α) : compareOfLessAndEq x x = eq := by
  rw [compareOfLessAndEq]
  rw [if_neg Irreflexive.irrfl]
  rw [if_pos rfl]

theorem eq_tight {x y : α} : compareOfLessAndEq x y = eq → x = y := by
  unfold compareOfLessAndEq
  intro cxy
  by_cases x = y with
  | isTrue rfl => rfl
  | isFalse hne => 
    rw [if_neg hne] at cxy
    split at cxy <;> contradiction

theorem lt_trans [Transitive (α:=α) (.<.)] {x y z : α} : compareOfLessAndEq x y = lt → compareOfLessAndEq y z = lt → compareOfLessAndEq x z = lt := by
  unfold compareOfLessAndEq
  intro cxy cyz
  split at cxy
  next hxy => 
    split at cyz
    next hyz => rw [if_pos (Transitive.trans hxy hyz)]
    next nyz => split at cyz <;> contradiction
  next nxy => split at cxy <;> contradiction

theorem gt_trans [Irreflexive (α:=α) (.<.)] [Transitive (α:=α) (.<.)] [Connex (α:=α) (.<.)] {x y z : α} : compareOfLessAndEq x y = gt → compareOfLessAndEq y z = gt → compareOfLessAndEq x z = gt := by
  unfold compareOfLessAndEq
  intro cxy cyz
  by_cases x = y, y = z with
  | isTrue hxy, _ => rw [if_pos hxy] at cxy; split at cxy <;> contradiction
  | _, isTrue hyz => rw [if_pos hyz] at cyz; split at cyz <;> contradiction
  | isFalse hxy, isFalse hyz => 
    match Connex.connex (r:=(.<.)) hxy, Connex.connex (r:=(.<.)) hyz with
    | .inl lxy, _ => rw [if_pos lxy] at cxy; contradiction
    | _, .inl lyz => rw [if_pos lyz] at cyz; contradiction
    | .inr lyx, .inr lzy =>
      have lzx : z < x := Transitive.trans lzy lyx
      rw [if_neg (Asymmetric.asymm lzx)]
      rw [if_neg (Irreflexive.ne_of lzx).symm]

variable (α) [LT α] [DecidableRel (α:=α) (.<.)] [DecidableEq α]

scoped instance instOrd : Ord α := ⟨fun x y => compareOfLessAndEq x y⟩

instance [Irreflexive (α:=α) (.<.)] [Transitive (α:=α) (.<.)] [Connex (α:=α) (.<.)] : LawfulOrd α where
  eq_refl := eq_refl
  eq_tight := eq_tight
  lt_trans := lt_trans
  gt_trans := gt_trans

end compareOfLessAndEq

instance : LawfulOrd Nat where
  eq_refl := compareOfLessAndEq.eq_refl
  eq_tight := compareOfLessAndEq.eq_tight
  lt_trans := compareOfLessAndEq.lt_trans
  gt_trans := compareOfLessAndEq.gt_trans

instance : LawfulOrd Int where
  eq_refl := compareOfLessAndEq.eq_refl
  eq_tight := compareOfLessAndEq.eq_tight
  lt_trans := compareOfLessAndEq.lt_trans
  gt_trans := compareOfLessAndEq.gt_trans
