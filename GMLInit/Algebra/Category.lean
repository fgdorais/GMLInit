import GMLInit.Algebra.Basic
import GMLInit.Algebra.Group

namespace Algebra
variable {α} {β : α → α → Sort _}

class Semicategory (s : SemicategorySig β) : Prop where
  protected dop_assoc {{a b c d}} (x : β c d) (y : β b c) (z : β a b) : s.op (s.op x y) z = s.op x (s.op y z)

protected def Semicategory.infer (s : SemicategorySig β) [DOpAssoc s.op] : Semicategory s where
  dop_assoc := dop_assoc _

namespace Semicategory
variable {s : SemicategorySig β} [Semicategory s]

instance : DOpAssoc (no_index s.op) := ⟨Semicategory.dop_assoc⟩

instance (a : α) : OpAssoc (no_index (s.toSemigroupSig a).op) := ⟨dop_assoc _ (a:=a) (b:=a) (c:=a) (d:=a)⟩

instance (a : α) : Semigroup (no_index s.toSemigroupSig a) := Semigroup.infer _

end Semicategory

class CancelSemicategory (s : SemicategorySig β) extends Semicategory (no_index s) : Prop where
  protected dop_left_cancel {{a b c}} (x : β b c) {y z : β a b} : s.op x y = s.op x z → y = z
  protected dop_right_cancel {{a b c}} (x : β a b) {y z : β b c} : s.op y x = s.op z x → y = z

namespace CancelSemicategory
variable {s : SemicategorySig β} [CancelSemicategory s]

instance : DOpLeftCancel (no_index s.op) := ⟨CancelSemicategory.dop_left_cancel⟩
instance : DOpRightCancel (no_index s.op) := ⟨CancelSemicategory.dop_right_cancel⟩

local instance (a : α) : OpLeftCancel (no_index (s.toSemigroupSig a).op) := ⟨dop_left_cancel _ (a:=a) (b:=a) (c:=a)⟩
local instance (a : α) : OpRightCancel (no_index (s.toSemigroupSig a).op) := ⟨dop_right_cancel _ (a:=a) (b:=a) (c:=a)⟩

instance (a : α) : CancelSemigroup (no_index s.toSemigroupSig a) := CancelSemigroup.infer _

end CancelSemicategory

class Category (s : CategorySig β) extends Semicategory (no_index s.toSemicategorySig): Prop where
  protected dop_left_id {{a b}} (x : β a b) : s.op s.id x = x
  protected dop_right_id {{a b}} (x : β a b) : s.op x s.id = x

protected def Category.infer (s : CategorySig β) [DOpAssoc s.op] [DOpLeftId s.op s.id] [DOpRightId s.op s.id] : Category s where
  dop_assoc := dop_assoc _
  dop_left_id := dop_left_id _
  dop_right_id := dop_right_id _

namespace Category
variable {s : CategorySig β} [Category s]

instance : DOpLeftId (no_index s.op) (no_index s.id) := ⟨Category.dop_left_id⟩
instance : DOpRightId (no_index s.op) (no_index s.id) := ⟨Category.dop_right_id⟩

instance (a : α) : OpLeftId (no_index (s.toMonoidSig a).op) (no_index (s.toMonoidSig a).id) := ⟨dop_left_id (a:=a) (b:=a) _⟩
instance (a : α) : OpRightId (no_index (s.toMonoidSig a).op) (no_index (s.toMonoidSig a).id) := ⟨dop_right_id (a:=a) (b:=a) _⟩

instance (a : α) : Monoid (no_index s.toMonoidSig a) := Monoid.infer _

end Category

class CancelCategory (s : CategorySig β) extends Category (no_index s), CancelSemicategory (no_index s.toSemicategorySig) : Prop

protected def CancelCategory.infer (s : CategorySig β) [DOpAssoc s.op] [DOpLeftId s.op s.id] [DOpRightId s.op s.id] [DOpLeftCancel s.op] [DOpRightCancel s.op] : CancelCategory s where
  dop_assoc := dop_assoc _
  dop_left_id := dop_left_id _
  dop_right_id := dop_right_id _
  dop_left_cancel := dop_left_cancel _
  dop_right_cancel := dop_right_cancel _

namespace CancelCategory
variable {s : CategorySig β} [CancelCategory s]

instance (a : α) : OpLeftCancel (no_index (s.toMonoidSig a).op) := ⟨dop_left_cancel (a:=a) (b:=a) (c:=a) _⟩
instance (a : α) : OpRightCancel (no_index (s.toMonoidSig a).op) := ⟨dop_right_cancel (a:=a) (b:=a) (c:=a) _⟩

instance (a : α) : CancelMonoid (no_index s.toMonoidSig a) := CancelMonoid.infer _

end CancelCategory

class Groupoid (s : GroupoidSig β) : Prop where
  protected dop_assoc {{a b c d}} (x : β c d) (y : β b c) (z : β a b) : s.op (s.op x y) z = s.op x (s.op y z)
  protected dop_right_id {{a b}} (x : β a b) : s.op x s.id = x
  protected dop_right_inv {{a b}} (x : β a b) : s.op x (s.inv x) = s.id

protected def Groupoid.infer (s : GroupoidSig β) [DOpAssoc s.op] [DOpRightId s.op s.id] [DOpRightInv s.op s.inv s.id] : Groupoid s where
  dop_assoc := dop_assoc _
  dop_right_id := dop_right_id _
  dop_right_inv := dop_right_inv _

namespace Groupoid
variable {s : GroupoidSig β} [Groupoid s]

local infixr:60 " ⋆ " => s.op
local postfix:max "⁻¹" => s.inv
local notation "e" => s.id

local instance : DOpAssoc (no_index s.op) := ⟨Groupoid.dop_assoc⟩
local instance : DOpRightId (no_index s.op) (no_index s.id) := ⟨Groupoid.dop_right_id⟩
instance : DOpRightInv (no_index s.op) (no_index s.inv) (no_index s.id) := ⟨Groupoid.dop_right_inv⟩

protected theorem dop_right_cancel {{a b c}} (x : β a b) {y z : β b c} (h : s.op y x = s.op z x) : y = z := calc
  _ = y ⋆ e := by rw [dop_right_id s.op]
  _ = y ⋆ (x ⋆ x⁻¹) := by rw [dop_right_inv s.op]
  _ = (y ⋆ x) ⋆ x⁻¹ := by rw [dop_assoc s.op]
  _ = (z ⋆ x) ⋆ x⁻¹ := by rw [h]
  _ = z ⋆ (x ⋆ x⁻¹) := by rw [dop_assoc s.op]
  _ = z ⋆ e := by rw [dop_right_inv s.op]
  _ = z := by rw [dop_right_id s.op]
local instance : DOpRightCancel (no_index s.op) := ⟨Groupoid.dop_right_cancel⟩

protected theorem dop_left_id {{a b}} (x : β a b) : e ⋆ x = x :=
  dop_right_cancel s.op x⁻¹ $ calc
  _ = e ⋆ (x ⋆ x⁻¹) := by rw [dop_assoc s.op]
  _ = e ⋆ e := by rw [dop_right_inv s.op]
  _ = e := by rw [dop_right_id s.op]
  _ = x ⋆ x⁻¹ := by rw [dop_right_inv s.op]
local instance : DOpLeftId (no_index s.op) (no_index s.id) := ⟨Groupoid.dop_left_id⟩

protected theorem dop_left_inv {{a b}} (x : β a b) : x⁻¹ ⋆ x = e :=
  dop_right_cancel s.op x⁻¹ $ calc
  _ = x⁻¹ ⋆ (x ⋆ x⁻¹) := by rw [dop_assoc s.op]
  _ = x⁻¹ ⋆ e := by rw [dop_right_inv s.op]
  _ = x⁻¹ := by rw [dop_right_id s.op]
  _ = e ⋆ x⁻¹ := by rw [dop_left_id s.op]
instance : DOpLeftInv (no_index s.op) (no_index s.inv) (no_index s.id) := ⟨Groupoid.dop_left_inv⟩

protected theorem dop_left_cancel {{a b c}} (x : β b c) {y z : β a b} (h : x ⋆ y = x ⋆ z) : y = z := calc
  _ = e ⋆ y := by rw [dop_left_id s.op]
  _ = (x⁻¹ ⋆ x) ⋆ y := by rw [dop_left_inv s.op]
  _ = x⁻¹ ⋆ (x ⋆ y) := by rw [dop_assoc s.op]
  _ = x⁻¹ ⋆ (x ⋆ z) := by rw [h]
  _ = (x⁻¹ ⋆ x) ⋆ z := by rw [dop_assoc s.op]
  _ = e ⋆ z := by rw [dop_left_inv s.op]
  _ = z := by rw [dop_left_id s.op]
local instance : DOpLeftCancel (no_index s.op) := ⟨Groupoid.dop_left_cancel⟩

instance : CancelCategory (no_index s.toCategorySig) := CancelCategory.infer _

instance : OpLeftInv (no_index (s.toGroupSig a).op) (no_index (s.toGroupSig a).inv) (no_index (s.toGroupSig a).id) := ⟨dop_left_inv _ (a:=a) (b:=a)⟩
instance : OpRightInv (no_index (s.toGroupSig a).op) (no_index (s.toGroupSig a).inv) (no_index (s.toGroupSig a).id) := ⟨dop_right_inv _ (a:=a) (b:=a)⟩

instance : Group (no_index s.toGroupSig a) := Group.infer _

end Groupoid

end Algebra
