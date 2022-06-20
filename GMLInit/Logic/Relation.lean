import GMLInit.Meta.Stable
import GMLInit.Meta.Decidable

namespace Relation

section Reflexive

class Reflexive {α} (r : α → α → Prop) : Prop where
  protected refl (x) : r x x

protected abbrev Reflexive.rfl {α} {r : α → α → Prop} [Reflexive r] {x : α} := Reflexive.refl (r:=r) x

theorem Reflexive.of_eq {α} (r : α → α → Prop) [Reflexive r] : {x y : α} → x = y → r x y
| _, _, rfl => Reflexive.rfl

instance (α) [Setoid α] : Reflexive (α:=α) (.≈.) := ⟨Setoid.refl⟩
instance (α) [Setoid α] : Reflexive (α:=α) Setoid.r := ⟨Setoid.refl⟩
instance (α) : Reflexive (α:=α) (.≅.) := ⟨HEq.refl⟩
instance (α) : Reflexive (α:=α) (.=.) := ⟨Eq.refl⟩
instance : Reflexive (.→.) := ⟨@id⟩
instance : Reflexive (.↔.) := ⟨Iff.refl⟩

instance {α} (r : α → α → Prop) [Reflexive r] : Reflexive (TC r) where
  refl x := TC.base _ _ (Reflexive.refl x)

end Reflexive

section Irreflexive

abbrev Irreflexive {α} (r : α → α → Prop) : Prop := Reflexive (¬ r . .)

protected abbrev Irreflexive.irrefl {α} {r : α → α → Prop} [Irreflexive r] (x : α) := Reflexive.refl (r:=(¬ r . .)) x

protected abbrev Irreflexive.irrfl {α} {r : α → α → Prop} [Irreflexive r] {x : α} := Irreflexive.irrefl (r:=r) x

theorem Irreflexive.ne_of {α} {r : α → α → Prop} [Irreflexive r] : {x y : α} → r x y → x ≠ y
| _, _, h, rfl => Irreflexive.irrfl h

instance (α) : Irreflexive (α:=α) (.≠.) := ⟨λ x h => h (Eq.refl x)⟩

end Irreflexive

section Symmetric

class HSymmetric (r : α → β → Prop) (s : β → α → Prop) : Prop where
  protected symm {x y} : r x y → s y x

class Symmetric (r : α → α → Prop) : Prop where
  protected symm {x y} : r y x → r x y

@[defaultInstance]
instance {α} (r : α → α → Prop) [Symmetric r] : HSymmetric r r := ⟨Symmetric.symm⟩

class Asymmetric (r : α → α → Prop) : Prop where
  protected asymm {x y} : r x y → ¬r y x

instance {α} (r : α → α → Prop) [Asymmetric r] : HSymmetric r (λ x y => ¬r x y) := ⟨Asymmetric.asymm⟩

instance (α) : Symmetric (α:=α) (.=.) := ⟨Eq.symm⟩
instance (α) : Symmetric (α:=α) (.≠.) := ⟨Ne.symm⟩
instance (α) [Setoid α] : Symmetric (α:=α) (.≈.) := ⟨Setoid.symm⟩
instance (α) [Setoid α] : Symmetric (α:=α) Setoid.r := ⟨Setoid.symm⟩
instance (α β) : HSymmetric (α:=α) (β:=β) (.≅.) (.≅.) := ⟨HEq.symm⟩
instance (α) [LE α] : HSymmetric (α:=α) (.≤.) (.≥.) := ⟨id⟩
instance (α) [LE α] : HSymmetric (α:=α) (.≥.) (.≤.) := ⟨id⟩
instance (α) [LT α] : HSymmetric (α:=α) (.<.) (.>.) := ⟨id⟩
instance (α) [LT α] : HSymmetric (α:=α) (.>.) (.<.) := ⟨id⟩
instance : Symmetric (.↔.) := ⟨Iff.symm⟩

instance {α} (r : α → α → Prop) [Symmetric r] : Symmetric (TC r) where
  symm := by
    intros x y hxy
    induction hxy with
    | base x y h =>
      apply TC.base
      exact Symmetric.symm h
    | trans x y z _ _ hyx hzy =>
      apply TC.trans
      exact hzy
      exact hyx

end Symmetric

section Antisymmetric

class HAntisymmetric {α} (r : α → α → Prop) (s : outParam (α → α → Prop)) : Prop where
  protected antisymm {x y} : r x y → r y x → s x y

class Antisymmetric {α} (r : α → α → Prop) : Prop where
  protected antisymm {x y} : r x y → r y x → x = y

@[defaultInstance]
instance {α} (r : α → α → Prop) [Antisymmetric r] : HAntisymmetric r Eq where
  antisymm := Antisymmetric.antisymm

instance : HAntisymmetric (.→.) (.↔.) := ⟨Iff.intro⟩

abbrev WeaklyConnex {α} (r : α → α → Prop) := Antisymmetric (λ x y => ¬ r y x)

abbrev WeaklyConnex.connex {α} {r : α → α → Prop} [WeaklyConnex r] {x y} : ¬ r y x → ¬ r x y → x = y := 
  Antisymmetric.antisymm (r := λ x y => ¬ r y x)

end Antisymmetric

section Transitive

class HTransitive {α β γ} (r : α → β → Prop) (s : β → γ → Prop) (t : outParam (α → γ → Prop)) : Prop where
  protected trans {x y z} : (left : r x y) → (right : s y z) → t x z

instance {α β γ} (r : α → β → Prop) (s : β → γ → Prop) (t : α → γ → Prop) [HTransitive r s t] : Trans r s t where
  trans := HTransitive.trans

class Transitive {α} (r : α → α → Prop) : Prop where
  protected trans {x y z} : (left : r x y) → (right : r y z) → r x z

@[defaultInstance]
instance {α} (r : α → α → Prop) [Transitive r] : HTransitive r r r := ⟨Transitive.trans⟩

instance (α) : Transitive (α:=α) (.=.) := ⟨Eq.trans⟩
instance (α β γ) : HTransitive (α:=α) (β:=β) (γ:=γ) (.≅.) (.≅.) (.≅.) := ⟨HEq.trans⟩
instance {α β} (r : α → β → Prop) : HTransitive (.=.) r r := ⟨λ he hr => he ▸ hr⟩
instance {α β} (r : α → β → Prop) : HTransitive r (.=.) r := ⟨λ hr he => he ▸ hr⟩
instance (α) [Setoid α] : Transitive (α:=α) (.≈.) := ⟨Setoid.trans⟩
instance (α) [Setoid α] : Transitive (α:=α) Setoid.r := ⟨Setoid.trans⟩
instance : Transitive (.→.) := ⟨λ h₁ h₂ h => h₂ (h₁ h)⟩
instance : Transitive (.↔.) := ⟨Iff.trans⟩

instance {α} (r : α → α → Prop) : Transitive (TC r) where
  trans := TC.trans _ _ _

end Transitive

section Euclidean

class HEuclidean {α β γ} (r : α → β → Prop) (s : α → γ → Prop) (t : outParam (β → γ → Prop)) : Prop where
  protected eucl {x y z} : (left : r x y) → (right : s x z) → t y z

class Euclidean {α} (r : α → α → Prop) : Prop where
  protected eucl {x y z} : (left : r x y) → (right : r x z) → r y z

@[defaultInstance]
instance {α} (r : α → α → Prop) [Euclidean r] : HEuclidean r r r := ⟨Euclidean.eucl⟩

instance [Reflexive r] [Euclidean r] : Symmetric r where
  symm hxy := Euclidean.eucl hxy (Reflexive.refl _)

instance [Symmetric r] [Transitive r] : Euclidean r where
  eucl hxy hxz := Transitive.trans (Symmetric.symm hxy) hxz

def Euclidean.toSymmetric {α} (r : α → α → Prop) [Reflexive r] [Euclidean r] : Symmetric r where
  symm hxy := Euclidean.eucl hxy Reflexive.rfl

def Euclidean.toTransitive {α} (r : α → α → Prop) [Symmetric r] [Euclidean r] : Transitive r where
  trans hxy hyz := Euclidean.eucl (Symmetric.symm hxy) hyz

end Euclidean

section Total

class HTotal {α β} (r : α → β → Prop) (s : β → α → Prop) : Prop where
  protected total (x y) : (r x y) ∨ (s y x)

class Total {α} (r : α → α → Prop) : Prop where
  protected total (x y) : (r x y) ∨ (r y x)

@[defaultInstance]
instance {α} (r : α → α → Prop) [Total r] : HTotal r r := ⟨Total.total⟩

end Total

section Comparison

class HComparison {α} (r : α → α → Prop) (s : α → α → Prop) : Prop where
  protected compare {x y} : s x y → (z : α) → r x z ∨ r z y

class Comparison {α} (r : α → α → Prop) : Prop where
  protected compare {x y} : r x y → (z : α) → r x z ∨ r z y

@[defaultInstance]
instance {α} (r : α → α → Prop) [Comparison r] : HComparison r r := ⟨Comparison.compare⟩

def Transitive.toComparison {α} (r : α → α → Prop) [ComplementedRel r] [Transitive r] : Comparison (λ x y => ¬ r y x) where
  compare := by
    intro x y nxy z
    by_cases r z x using Complemented with
    | .isFalse nxz =>
      left
      exact nxz
    | .isTrue hxz =>
      right
      intro hzy
      apply nxy
      exact Transitive.trans hzy hxz

instance Comparison.toTransitive {α} (r : α → α → Prop) [Comparison r] : Transitive (λ x y => ¬ r y x) where
  trans := by
    intros x y z nxy nyz hxz
    cases Comparison.compare hxz y with
    | inl hyz => exact nyz hyz
    | inr hxy => exact nxy hxy

end Comparison

section Connex

class HConnex {α} (r : α → α → Prop) (s : α → α → Prop) : Prop where
  protected connex {x y} : s x y → r x y ∨ r y x

class Connex {α} (r : α → α → Prop) : Prop where
  protected connex {x y} : x ≠ y → r x y ∨ r y x

@[defaultInstance]
instance {α} (r : α → α → Prop) [Connex r] : HConnex r (.≠.) := ⟨Connex.connex⟩

def Connex.toAntisymmetric {α} (r : α → α → Prop) [StableEq α] [Connex r] : Antisymmetric (λ x y => ¬ r y x) where
  antisymm := by
    intro x y nxy nyx
    by_contradiction
    | assuming hne =>
      cases Connex.connex (r:=r) hne with
      | inl hyx => exact nyx hyx
      | inr hxy => exact nxy hxy

def Antisymmetric.toConnex {α} (r : α → α → Prop) [WeaklyComplementedRel r] [Antisymmetric r] : Connex fun x y => ¬ r y x where
  connex := by
    intro x y hne
    rw [←And.deMorgan]
    intro ⟨hyx, hxy⟩
    absurd hne
    exact Antisymmetric.antisymm hxy hyx

end Connex

end Relation
