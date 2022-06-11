import GMLInit.Logic.Basic
import GMLInit.Logic.Relation
import GMLInit.Meta.Decidable
import GMLInit.Meta.Relation

namespace Relation

class PartialEquivalence {α} (r : α → α → Prop) : Prop where
  protected symm {x y} : r x y → r y x
  protected eucl {x y z} : r x y → r x z → r y z

namespace PartialEquivalence

protected def infer {α} (r : α → α → Prop) [Symmetric r] [Euclidean r] : PartialEquivalence r where
  symm := Symmetric.symm
  eucl := Euclidean.eucl

variable {α} {r : α → α → Prop} [PartialEquivalence r]

instance : Symmetric r := ⟨PartialEquivalence.symm⟩
instance : Euclidean r := ⟨PartialEquivalence.eucl⟩
instance : Transitive r := Euclidean.toTransitive r

protected theorem trans {x y z} : r x y → r y z → r x z := Transitive.trans

instance {α} (r : α → α → Prop) [Symmetric r] : PartialEquivalence (TC r) := PartialEquivalence.infer _

end PartialEquivalence

class Equivalence {α} (r : α → α → Prop) : Prop where
  protected refl (x) : r x x
  protected eucl {x y z} : r x y → r x z → r y z

protected def Equivalence.infer {α} (r : α → α → Prop) [Reflexive r] [Euclidean r] : Equivalence r where
  refl := Reflexive.refl
  eucl := Euclidean.eucl

namespace Equivalence
variable {α} {r : α → α → Prop} [Equivalence r]

instance : Reflexive r := ⟨Equivalence.refl⟩
instance : Euclidean r := ⟨Equivalence.eucl⟩
instance : Symmetric r := inferInstance
instance : Transitive r := Euclidean.toTransitive r

protected theorem symm {x y} : r x y → r y x := Symmetric.symm

protected theorem trans {x y z} : r x y → r y z → r x z := Transitive.trans

instance : PartialEquivalence r := PartialEquivalence.infer r

instance (α) : Equivalence (α:=α) (.=.) := Equivalence.infer _
instance (α) [Setoid α] : Equivalence (α:=α) (.≈.) := Equivalence.infer _
instance (α) [Setoid α] : Equivalence (α:=α) Setoid.r := Equivalence.infer _

instance {α} (r : α → α → Prop) [Reflexive r] [Symmetric r] : Equivalence (TC r) := Equivalence.infer _

protected def to_eqv : _root_.Equivalence r where
  refl := Reflexive.refl
  symm := Symmetric.symm
  trans := Transitive.trans

end Equivalence

namespace PartialEquivalence
variable {α} (r : α → α → Prop) [PartialEquivalence r]

abbrev toSubtype : { x // r x x } → { x // r x x } → Prop
| ⟨x,_⟩, ⟨y,_⟩ => r x y

instance : Equivalence (toSubtype r) where
  refl := Subtype.property
  eucl := Euclidean.eucl (r:=r)

end PartialEquivalence

class Apartness {α} (r : α → α → Prop) : Prop where
  protected irrefl (x) : ¬ r x x
  protected symm {x y} : r x y → r y x
  protected compare {x y} : r x y → (z : α) → r x z ∨ r z y

protected def Apartness.infer {α} (r : α → α → Prop) [Irreflexive r] [Symmetric r] [Comparison r] : Apartness r where
  irrefl := Irreflexive.irrefl
  symm := Symmetric.symm
  compare := Comparison.compare

namespace Apartness
variable {α} {r : α → α → Prop} [Apartness r]

instance : Irreflexive r := ⟨Apartness.irrefl⟩
instance : Symmetric r := ⟨Apartness.symm⟩
instance : Comparison r := ⟨Apartness.compare⟩

instance : Equivalence (λ x y => ¬ r x y) where
  refl := Irreflexive.irrefl
  eucl {x _ _} (nxy nxz hyz) :=
    match Comparison.compare hyz x with
    | .inl hyx => nxy (Symmetric.symm hyx)
    | .inr hxz => nxz hxz

end Apartness

namespace Equivalence
variable {α} (r : α → α → Prop) [Equivalence r]

def toApartness [ComplementedRel r] : Apartness (λ x y => ¬ r x y) where
  irrefl x h := h (Reflexive.refl x)
  symm nxy hyx := nxy (Symmetric.symm hyx)
  compare {x y} (nxy z) := by
    by_cases r x z, r z y using Complemented with
    | .isFalse nxz, _ =>
      left
      exact nxz
    | _, .isFalse nzy =>
      right
      exact nzy
    | .isTrue hxz, .isTrue hzy =>
      absurd nxy
      transitivity z
      exact hxz
      exact hzy

end Equivalence

class TightApartness {α} (r : α → α → Prop) extends Apartness r : Prop where
  protected tight {x y} : ¬ r x y → x = y

namespace TightApartness
variable {α} (r : α → α → Prop) [TightApartness r]

theorem eq_iff_not_apart : x = y ↔ ¬ r x y := ⟨λ | rfl => Irreflexive.irrefl _, TightApartness.tight⟩

instance : StableEq α := λ _ _ => Iff.subst (eq_iff_not_apart r).symm inferInstance

instance [WeaklyComplementedEq α] : TightApartness (α:=α) (.≠.) where
  irrefl := Irreflexive.irrefl
  symm := Symmetric.symm
  tight := Stable.by_contradiction
  compare := by
    intro x y h z
    by_cases x = z using WeaklyComplemented with
    | .isIrrefutable _ => right; intro | rfl => contradiction
    | .isFalse _ => left; assumption

end TightApartness

end Relation
