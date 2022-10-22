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

theorem symm [Total (α:=α) (.≤.)] (x y : α) : (compareOfLE x y).swap = compareOfLE y x := by
  unfold compareOfLE
  split
  next =>
    split
    next => rfl
    next => rfl
  next =>
    split
    next => rfl
    next nxy nyx =>
      cases Total.total (r:=(.≤.)) x y with
      | inl hxy => contradiction
      | inr hyx => contradiction

theorem le_trans [Transitive (α:=α) (.≤.)] {x y z : α} : compareOfLE x y ≠ gt → compareOfLE y z ≠ gt → compareOfLE x z ≠ gt := by
  unfold compareOfLE
  intro cxy cyz
  split
  next =>
    split
    next => intro; contradiction
    next => intro; contradiction
  next nxz =>
    split at cxy
    next hxy =>
      split at cyz
      next hyz =>
        absurd nxz
        transitivity y
        · exact hxy
        · exact hyz
      next => contradiction
    next => contradiction

theorem eq_strict [Antisymmetric (α:=α) (.≤.)] {x y : α} : compareOfLE x y = eq → x = y := by
  unfold compareOfLE
  intro cxy
  split at cxy
  next hxy =>
    split at cxy
    next hyx =>
      antisymmetry using (.≤.)
      · exact hxy
      · exact hyx
    next => contradiction
  next => contradiction

variable (α) [LE α] [DecidableRel (α:=α) (.≤.)]

scoped instance instOrd : Ord α := ⟨compareOfLE⟩

scoped instance instOrientedOrd [Total (α:=α) (.≤.)] : OrientedOrd α where
  symm := symm

scoped instance instTransOrd [Total (α:=α) (.≤.)] [Transitive (α:=α) (.≤.)] : TransOrd α where
  symm := symm
  le_trans := le_trans

scoped instance instLinearOrd [Total (α:=α) (.≤.)] [Transitive (α:=α) (.≤.)] [Antisymmetric (α:=α) (.≤.)] : LinearOrd α where
  symm := symm
  le_trans := le_trans
  eq_strict := eq_strict

end compareOfLE

def compareOfLT {α} [LT α] [DecidableRel (α:=α) (.<.)] (x y : α) : Ordering :=
  if x < y then lt else if y < x then gt else eq

namespace compareOfLT
variable {α} [inst : LT α] [DecidableRel (α:=α) (.<.)]

theorem symm [Asymmetric (α:=α) (.<.)] (x y : α) : (compareOfLT x y).swap = compareOfLT y x := by
  unfold compareOfLT
  split
  next hxy =>
    split
    next hyx  =>
      absurd hxy
      exact Asymmetric.asymm hyx
    next => rfl
  next =>
    split
    next => rfl
    next => rfl

theorem le_trans {x y z : α} [Transitive (α:=α) (.<.)] [Comparison (α:=α) (.<.)] : compareOfLT x y ≠ gt → compareOfLT y z ≠ gt → compareOfLT x z ≠ gt := by
  unfold compareOfLT
  intro cxy cyz
  split
  next => intro; contradiction
  next nxz =>
    split
    next hzx =>
      split at cxy
      next =>
        split at cyz
        next =>
          absurd nxz
          transitivity y
          · assumption
          · assumption
        next =>
          split at cyz
          next => contradiction
          next nzy =>
            absurd nzy
            transitivity x
            · assumption
            . assumption
      next =>
        split at cxy
        next => contradiction
        next nyx =>
          split at cyz
          next =>
            absurd nyx
            transitivity z
            · assumption
            . assumption
          next =>
            split at cyz
            next => contradiction
            next =>
              cases Comparison.compare hzx y with
              | inl _ => contradiction
              | inr _ => contradiction
    next => intro; contradiction

theorem eq_strict {x y : α} [StableEq α] [Connex (α:=α) (.<.)] : compareOfLT x y = eq → x = y := by
  unfold compareOfLT
  intro cxy
  split at cxy
  next => contradiction
  next =>
    split at cxy
    next => contradiction
    next =>
      by_contradiction
      | assuming hne =>
        cases Connex.connex (r:=(.<.)) hne with
        | inl _ => contradiction
        | inr _ => contradiction

variable (α) [LT α] [DecidableRel (α:=α) (.<.)]

scoped instance instOrd : Ord α := ⟨compareOfLT⟩

scoped instance instOrientedOrd [Asymmetric (α:=α) (.<.)] : OrientedOrd α where
  symm := symm

scoped instance instTransOrd [Asymmetric (α:=α) (.<.)] [Transitive (α:=α) (.<.)] [Comparison (α:=α) (.<.)] : TransOrd α where
  symm := symm
  le_trans := le_trans

scoped instance instLinearOrd [StableEq α] [Asymmetric (α:=α) (.<.)] [Transitive (α:=α) (.<.)] [Comparison (α:=α) (.<.)] [Connex (α:=α) (.<.)] : LinearOrd α where
  symm := symm
  le_trans := le_trans
  eq_strict := eq_strict

end compareOfLT

namespace compareOfLessAndEq
variable {α} [LT α] [DecidableRel (α:=α) (.<.)] [DecidableEq α]

theorem symm [Irreflexive (α:=α) (.<.)] [Transitive (α:=α) (.<.)] [Connex (α:=α) (.<.)] (x y : α) : (compareOfLessAndEq x y).swap = compareOfLessAndEq y x := by
  unfold compareOfLessAndEq
  split
  next hlt =>
    split
    next =>
      absurd Irreflexive.irrefl (r:=(.<.)) x
      transitivity y
      · assumption
      · assumption
    next =>
      split
      next heq =>
        absurd hlt
        rw [heq]
        exact Irreflexive.irrfl
      next => rfl
  next =>
    split
    next heq =>
      split
      next hlt =>
        absurd hlt
        rw [heq]
        exact Irreflexive.irrfl
      next =>
        split
        next => rfl
        next hne =>
          absurd hne
          symmetry
          assumption
    next hne =>
      split
      next => rfl
      next =>
        split
        next =>
          absurd hne
          symmetry
          assumption
        next =>
          cases Connex.connex (r:=(.<.)) hne with
          | inl _ => contradiction
          | inr _ => contradiction

theorem le_trans [Transitive (α:=α) (.<.)] [Connex (α:=α) (.<.)]  {x y z : α} : compareOfLessAndEq x y ≠ gt → compareOfLessAndEq y z ≠ gt → compareOfLessAndEq x z ≠ gt := by
  unfold compareOfLessAndEq
  intro cxy cyz
  split
  next => intro; contradiction
  next nxz =>
    split
    next => intro; contradiction
    next hne =>
      split at cxy
      next =>
        split at cyz
        next =>
          absurd nxz
          transitivity y
          · assumption
          · assumption
        next =>
          split at cyz
          next heq =>
            absurd nxz
            rw [←heq]
            assumption
          next => contradiction
      next =>
        split at cxy
        next heq =>
          split at cyz
          next =>
            absurd nxz
            rw [heq]
            assumption
          next =>
            split at cyz
            next =>
              absurd hne
              transitivity y
              · assumption
              · assumption
            next =>
              cases Connex.connex (r:=(.<.)) hne with
              | inl _ => contradiction
              | inr _ => contradiction
        next => contradiction

theorem eq_strict {x y : α} : compareOfLessAndEq x y = eq → x = y := by
  unfold compareOfLessAndEq
  intro cxy
  split at cxy
  next => contradiction
  next =>
    split at cxy
    next => assumption
    next => contradiction

variable (α) [LT α] [DecidableRel (α:=α) (.<.)] [DecidableEq α]

scoped instance instOrd : Ord α := ⟨fun x y => compareOfLessAndEq x y⟩

scoped instance instOrientedOrd [Irreflexive (α:=α) (.<.)] [Transitive (α:=α) (.<.)] [Connex (α:=α) (.<.)] : OrientedOrd α where
  symm := symm

scoped instance instTransOrd [Irreflexive (α:=α) (.<.)] [Transitive (α:=α) (.<.)] [Connex (α:=α) (.<.)] : TransOrd α where
  symm := symm
  le_trans := le_trans

scoped instance instLinearOrd [Irreflexive (α:=α) (.<.)] [Transitive (α:=α) (.<.)] [Connex (α:=α) (.<.)] : LinearOrd α where
  symm := symm
  le_trans := le_trans
  eq_strict := eq_strict

end compareOfLessAndEq

instance : LinearOrd Nat := compareOfLessAndEq.instLinearOrd Nat
instance : LinearOrd Int := compareOfLessAndEq.instLinearOrd Int
