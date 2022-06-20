import GMLInit.Logic.Basic
import GMLInit.Logic.Relation
import GMLInit.Meta.Decidable
import GMLInit.Meta.Relation

namespace Relation
variable {α} (r : α → α → Prop)

class PartialEquivalence extends Symmetric r, Euclidean r : Prop

instance [PartialEquivalence r] : Transitive r := Euclidean.toTransitive r

protected def PartialEquivalence.infer [Symmetric r] [Euclidean r] : PartialEquivalence r where
  symm := Symmetric.symm
  eucl := Euclidean.eucl

instance [Symmetric r] : PartialEquivalence (TC r) := PartialEquivalence.infer _

namespace PartialEquivalence
variable {r} [PartialEquivalence r]

protected theorem trans {x y z} : r x y → r y z → r x z := Transitive.trans

end PartialEquivalence

class Equivalence extends Reflexive r, Euclidean r : Prop

instance [Equivalence r] : PartialEquivalence r := PartialEquivalence.infer r

protected def Equivalence.infer {α} (r : α → α → Prop) [Reflexive r] [Euclidean r] : Equivalence r where
  refl := Reflexive.refl
  eucl := Euclidean.eucl

namespace Equivalence
variable {r} [Equivalence r]

protected theorem symm {x y} : r x y → r y x := Symmetric.symm
protected theorem trans {x y z} : r x y → r y z → r x z := Transitive.trans

end Equivalence

protected def Equivalence.to_eqv [Equivalence r] : _root_.Equivalence r where
  refl := Reflexive.refl
  symm := Symmetric.symm
  trans := Transitive.trans

instance (α) : Equivalence (α:=α) (.=.) := Equivalence.infer _
instance (α) [Setoid α] : Equivalence (α:=α) (.≈.) := Equivalence.infer _
instance (α) [Setoid α] : Equivalence (α:=α) Setoid.r := Equivalence.infer _

instance [Reflexive r] [Symmetric r] : Equivalence (TC r) := Equivalence.infer _

abbrev PartialEquivalence.toSubtype [PartialEquivalence r] : { x // r x x } → { x // r x x } → Prop
| ⟨x,_⟩, ⟨y,_⟩ => r x y

instance [PartialEquivalence r] : Equivalence (PartialEquivalence.toSubtype r) where
  refl := Subtype.property
  eucl := Euclidean.eucl (r:=r)

class Apartness extends Symmetric r, Comparison r : Prop where
  protected irrefl (x) : ¬ r x x

instance [self : Apartness r] : Irreflexive r := ⟨self.irrefl⟩

protected def Apartness.infer [Irreflexive r] [Symmetric r] [Comparison r] : Apartness r where
  irrefl := Irreflexive.irrefl
  symm := Symmetric.symm
  compare := Comparison.compare

instance [Apartness r] : Equivalence (¬ r . .) where
  refl := Irreflexive.irrefl
  eucl {x _ _} nxy nxz hyz :=
    match Comparison.compare hyz x with
    | .inl hyx => nxy (Symmetric.symm hyx)
    | .inr hxz => nxz hxz

def Equivalence.toApartness [Equivalence r] [ComplementedRel r] : Apartness (¬ r . .) where
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

class TightApartness {α} (r : α → α → Prop) extends Apartness r : Prop where
  protected tight {x y} : ¬ r x y → x = y

namespace TightApartness
variable [TightApartness r] 

theorem eq_iff_not_apart : x = y ↔ ¬ r x y := by
  constr
  · intro | rfl => irreflexivity
  · exact TightApartness.tight

instance : StableEq α := λ _ _ => Iff.subst (TightApartness.eq_iff_not_apart r).symm inferInstance

end TightApartness

instance [ComplementedEq α] : TightApartness (α:=α) (.≠.) where
  toApartness := Equivalence.toApartness _
  tight := Stable.by_contradiction

end Relation
