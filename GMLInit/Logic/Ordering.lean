import GMLInit.Logic.Basic
import GMLInit.Logic.Relation
import GMLInit.Logic.Equivalence

namespace Relation
variable {α} (r : α → α → Prop)

abbrev coRel (x y) := ¬ r y x
abbrev reflRel (x y) := r x y ∨ x = y
abbrev asymRel (x y) := r x y ∧ coRel r x y
abbrev symmRel (x y) := r x y ∧ r y x

class Preorder extends Reflexive r, Transitive r : Prop

def Preorder.infer [Reflexive r] [Transitive r] : Preorder r where
  refl := Reflexive.refl
  trans := Transitive.trans

class PartialOrder extends Preorder r, Antisymmetric r : Prop

def PartialOrder.infer [Reflexive r] [Transitive r] [Antisymmetric r] : PartialOrder r where
  refl := Reflexive.refl
  trans := Transitive.trans
  antisymm := Antisymmetric.antisymm

class TotalPreorder extends Preorder r, Total r : Prop

def TotalPreorder.infer [Reflexive r] [Transitive r] [Total r] : TotalPreorder r where
  refl := Reflexive.refl
  trans := Transitive.trans
  total := Total.total

class TotalOrder extends PartialOrder r, TotalPreorder r : Prop

def TotalOrder.infer [Reflexive r] [Transitive r] [Antisymmetric r] [Total r] : TotalOrder r where
  refl := Reflexive.refl
  trans := Transitive.trans
  antisymm := Antisymmetric.antisymm
  total := Total.total

class Quasiorder extends Transitive r : Prop where
  protected irrefl (x) : ¬ r x x

def Quasiorder.infer [Transitive r] [Irreflexive r] : Quasiorder r where
  trans := Transitive.trans
  irrefl := Irreflexive.irrefl

namespace Quasiorder
variable {r} [self : Quasiorder r]

protected theorem asymm {x y} : r x y → ¬ r y x := by
  intro hxy hyx
  apply self.irrefl x
  exact self.trans hxy hyx

end Quasiorder

instance [self : Quasiorder r] : Irreflexive r := ⟨self.irrefl⟩
instance [self : Quasiorder r] : Asymmetric r := ⟨self.asymm⟩

class LinearQuasiorder extends Quasiorder r, Comparison r : Prop

def LinearQuasiorder.infer [Transitive r] [Irreflexive r] [Comparison r] : LinearQuasiorder r where
  trans := Transitive.trans
  irrefl := Irreflexive.irrefl
  compare := Comparison.compare

class LinearOrder extends LinearQuasiorder r, Connex r : Prop

def LinearOrder.infer [Transitive r] [Irreflexive r] [Comparison r] [Connex r] : LinearOrder r where
  trans := Transitive.trans
  irrefl := Irreflexive.irrefl
  compare := Comparison.compare
  connex := Connex.connex

namespace Preorder
variable {r} [self : Preorder r]

theorem co_irrefl (x) : ¬coRel r x x := by
  exact not_not_intro Reflexive.rfl

theorem co_compare [WeaklyComplementedRel r] {x y} : coRel r x y → ∀ z, coRel r x z ∨ coRel r z y := by
  intro cxy z
  rw [←And.deMorgan]
  intro ⟨hzx, hyz⟩
  absurd cxy
  exact Transitive.trans hyz hzx
  
theorem as_irrefl (x) : ¬asymRel r x x := by
  intro ⟨_, cxx⟩
  exact co_irrefl x cxx

theorem as_trans {x y z} : asymRel r x y → asymRel r y z → asymRel r x z := by
  intro ⟨hxy, cxy⟩ ⟨hyz, _⟩
  constr
  · exact Transitive.trans hxy hyz
  · intro hzx
    absurd cxy
    exact Transitive.trans hyz hzx

instance : Quasiorder (asymRel r) where
  irrefl := Preorder.as_irrefl
  trans := Preorder.as_trans

end Preorder

namespace PartialOrder
variable {r} [self : PartialOrder r]

theorem co_connex [WeaklyComplementedRel r] {x y} : x ≠ y → coRel r x y ∨ coRel r y x := by
  intro hne
  rw [←And.deMorgan]
  intro ⟨hyx, hxy⟩
  absurd hne
  exact Antisymmetric.antisymm hxy hyx

end PartialOrder

namespace TotalPreorder
variable {r} [self : TotalPreorder r]

theorem coRel_iff_asymRel (x y) : coRel r x y ↔ asymRel r x y := by
  constr
  · intro cxy
    constr
    · cases Total.total (r:=r) x y with
      | inl hxy => exact hxy
      | inr hyx => absurd cxy; exact hyx
    · exact cxy
  · exact And.right
  
theorem co_trans {x y z} : coRel r x y → coRel r y z → coRel r x z := by
  repeat rw [coRel_iff_asymRel]
  exact Preorder.as_trans

theorem as_compare [WeaklyComplementedRel r] {x y} : asymRel r x y → ∀ z, asymRel r x z ∨ asymRel r z y := by
  intro h z
  rw [←coRel_iff_asymRel] at h
  repeat rw [←coRel_iff_asymRel]
  exact Preorder.co_compare h z

instance : Quasiorder (coRel r) where
  irrefl := Preorder.co_irrefl
  trans := TotalPreorder.co_trans

instance [WeaklyComplementedRel r] : LinearQuasiorder (coRel r) where
  toQuasiorder := inferInstance
  compare := Preorder.co_compare

instance [WeaklyComplementedRel r] : LinearQuasiorder (asymRel r) where
  toQuasiorder := inferInstance
  compare := TotalPreorder.as_compare

end TotalPreorder

namespace TotalOrder
variable {r} [self : TotalOrder r]

theorem coRel_iff_rel_and_ne (x y) : coRel r x y ↔ r x y ∧ x ≠ y := by
  constr
  · intro cxy
    constr
    · cases Total.total (r:=r) x y with
      | inl hxy => exact hxy
      | inr hyx => absurd cxy; exact hyx
    · intro | rfl => absurd cxy; exact Reflexive.rfl
  · intro ⟨hxy, hne⟩ hyx
    absurd hne
    exact Antisymmetric.antisymm hxy hyx

instance [WeaklyComplementedRel r] : LinearOrder (coRel r) where
  toLinearQuasiorder := inferInstance
  connex := PartialOrder.co_connex

end TotalOrder

namespace Quasiorder
variable {r} [self : Quasiorder r]

theorem co_refl (x) : coRel r x x := Irreflexive.irrfl

theorem rc_refl (x) : reflRel r x x := by right; rfl

theorem rc_trans {x y z} : reflRel r x y → reflRel r y z → reflRel r x z := by
  intro hxy hyz
  match hxy, hyz with
  | Or.inr rfl, Or.inr rfl => right; rfl
  | Or.inr rfl, Or.inl hyz => left; exact hyz
  | Or.inl hxy, Or.inr rfl => left; exact hxy
  | Or.inl hxy, Or.inl hyz => left; exact Transitive.trans hxy hyz

theorem rc_antisymm {x y} : reflRel r x y → reflRel r y x → x = y := by
  intro hxy hyx
  match hxy, hyx with
  | Or.inr rfl, _ => rfl
  | _, Or.inr rfl => rfl
  | Or.inl hxy, Or.inl hyx => 
    absurd hxy
    exact Asymmetric.asymm hyx

instance : PartialOrder (reflRel r) where
  refl := Quasiorder.rc_refl
  trans := Quasiorder.rc_trans
  antisymm := Quasiorder.rc_antisymm

end Quasiorder

namespace LinearQuasiorder
variable {r} [self : LinearQuasiorder r]

theorem co_trans {x y z} : coRel r x y → coRel r y z → coRel r x z := by
  intro cxy cyz rzx
  cases Comparison.compare rzx y with
  | inl rzy => exact cyz rzy
  | inr ryx => exact cxy ryx

theorem co_total [ComplementedRel r] (x y) : coRel r x y ∨ coRel r y x := by
  match inferComplemented (r x y) with
  | .isTrue hxy => left; exact Asymmetric.asymm hxy
  | .isFalse nxy => right; exact nxy

instance : Preorder (coRel r) where
  refl := Quasiorder.co_refl
  trans := LinearQuasiorder.co_trans

instance [ComplementedRel r] : TotalPreorder (coRel r) where
  refl := Quasiorder.co_refl
  trans := LinearQuasiorder.co_trans
  total := LinearQuasiorder.co_total

end LinearQuasiorder

namespace LinearOrder
variable {r} [self : LinearOrder r]

theorem co_antisymm [StableEq α] {x y} : coRel r x y → coRel r y x → x = y := by
  intro cxy cyx
  by_contradiction
  | assuming hne =>
    cases Connex.connex (r:=r) hne with
    | inl hxy => absurd hxy; exact cyx
    | inr hyx => absurd hyx; exact cxy

theorem coRel_iff_reflRel [StableEq α] [ComplementedRel r] (x y) : coRel r x y ↔ reflRel r x y := by
  constr
  · intro cxy
    match inferComplemented (r x y) with
    | .isTrue hxy => left; exact hxy
    | .isFalse cyx =>
      right
      by_contradiction
      | assuming hne =>
        cases Connex.connex (r:=r) hne with
        | inl hxy => absurd cyx; exact hxy
        | inr hyx => absurd cxy; exact hyx
  · intro
    | .inr rfl => exact Quasiorder.co_refl x
    | .inl hxy => exact Asymmetric.asymm hxy

theorem rc_total [ComplementedEq α] (x y) : reflRel r x y ∨ reflRel r y x := by
  match inferComplemented (x = y) with
  | .isTrue rfl => left; right; rfl
  | .isFalse hne => 
    cases Connex.connex (r:=r) hne with
    | inl hxy => left; left; exact hxy
    | inr hyx => right; left; exact hyx

instance [StableEq α] : PartialOrder (coRel r) where
  toPreorder := inferInstance
  antisymm := co_antisymm

instance [ComplementedRel r] [StableEq α] : TotalOrder (coRel r) where
  toPartialOrder := inferInstance
  total := LinearQuasiorder.co_total

instance [ComplementedEq α] : TotalOrder (reflRel r) where
  toPartialOrder := inferInstance
  total := LinearOrder.rc_total

end LinearOrder

end Relation
