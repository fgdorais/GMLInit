import GMLInit.Data.Basic
import GMLInit.Meta.Basic
import GMLInit.Meta.Relation

class EquivBEq (α) [BEq α] extends PartialEquivBEq α : Prop where
  protected refl (x : α) : (x == x) = true

instance (α) [BEq α] [LawfulBEq α] : EquivBEq α where
  refl _ := LawfulBEq.rfl
  symm h := eq_of_beq h ▸ LawfulBEq.rfl
  trans h₁ h₂ := eq_of_beq h₁ ▸ h₂

namespace BEq
variable {α} [BEq α] 

protected theorem refl [EquivBEq α] (x : α) : x == x := EquivBEq.refl x

protected theorem rfl [EquivBEq α] {x : α} : x == x := EquivBEq.refl x

protected theorem symm [PartialEquivBEq α] {x y : α} : x == y → y == x := PartialEquivBEq.symm

protected theorem trans [PartialEquivBEq α] {x y z : α} : x == y → y == z → x == z := PartialEquivBEq.trans

protected theorem comm [PartialEquivBEq α] (x y : α) : (x == y) = (y == x) := by
  match hxy : x == y, hyx : y == x with
  | true, true => rfl
  | true, false => rw [BEq.symm hxy] at hyx; contradiction
  | false, true => rw [BEq.symm hyx] at hxy; contradiction
  | false, false => rfl

theorem subst_left [PartialEquivBEq α] {x y z : α} : (x == y) = true → (x == z) = (y == z) := by
  intro hxy 
  match hxz : x == z, hyz : y == z with
  | true, true => rfl
  | true, false => rw [BEq.trans (BEq.symm hxy) hxz] at hyz; contradiction
  | false, true => rw [BEq.trans hxy hyz] at hxz; contradiction
  | false, false => rfl

theorem subst_right [PartialEquivBEq α] {x y z : α} : (x == y) = true → (z == x) = (z == y) := by
  intro hxy 
  match hzx : z == x, hzy : z == y with
  | true, true => rfl
  | true, false => rw [BEq.trans hzx hxy] at hzy; contradiction
  | false, true => rw [BEq.trans hzy (BEq.symm hxy)] at hzx; contradiction
  | false, false => rfl

theorem beq_of_eq [EquivBEq α] {x y : α} : x = y → (x == y) = true := fun | rfl => BEq.rfl

theorem eq_of_beq [LawfulBEq α] {x y : α} : (x == y) = true → x = y := LawfulBEq.eq_of_beq

theorem comp [PartialEquivBEq α] {x y : α} : (x != y) = true → ∀ z, (x != z) = true ∨ (z != y) = true := by
  clean unfold bne
  intro hxy z
  match hxz : x == z, hyz : z == y with
  | true, true => rw [BEq.subst_right hyz] at hxz; rw [hxz] at hxy; contradiction
  | false, _ => left; rfl
  | _, false => right; rfl

instance (α) [BEq α] [EquivBEq α] : Relation.Reflexive (α:=α) (.==.) := ⟨BEq.refl⟩
instance (α) [BEq α] [PartialEquivBEq α] : Relation.Symmetric (α:=α) (.==.) := ⟨BEq.symm⟩
instance (α) [BEq α] [PartialEquivBEq α] : Relation.Transitive (α:=α) (.==.) := ⟨BEq.trans⟩

end BEq
