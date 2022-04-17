import GMLInit.Algebra.Basic

namespace Algebra
variable {α} (s : SemigroupSig α)

local infixr:70 " ⋆ " => s.op

class Semigroup : Prop where
  protected op_assoc (x y z) : (x ⋆ y) ⋆ z = x ⋆ (y ⋆ z)

protected def Semigroup.infer [OpAssoc s.op] : Semigroup s where
  op_assoc := op_assoc _

namespace Semigroup
variable {s} [self : Semigroup s]

instance : OpAssoc (no_index s.op) := ⟨Semigroup.op_assoc⟩

end Semigroup

class CommSemigroup extends Semigroup s : Prop where
  protected op_comm (x y) : x ⋆ y = y ⋆ x

protected def CommSemigroup.infer [OpAssoc s.op] [OpComm s.op] : CommSemigroup s where
  op_assoc := op_assoc _
  op_comm := op_comm _

namespace CommSemigroup
variable {s} [self : CommSemigroup s]

instance : OpComm (no_index s.op) := ⟨CommSemigroup.op_comm⟩

protected theorem op_left_comm (x y z) : x ⋆ (y ⋆ z) = y ⋆ (x ⋆ z) := calc
  _ = (x ⋆ y) ⋆ z := by rw [op_assoc (.⋆.) x y z]
  _ = (y ⋆ x) ⋆ z := by rw [op_comm (.⋆.) x y]
  _ = y ⋆ (x ⋆ z) := by rw [op_assoc (.⋆.) y x z]
instance : OpLeftComm (no_index s.op) := ⟨CommSemigroup.op_left_comm⟩

protected theorem op_right_comm (x y z) : (x ⋆ y) ⋆ z = (x ⋆ z) ⋆ y := calc
  _ = x ⋆ (y ⋆ z) := by rw [op_assoc (.⋆.) x y z]
  _ = x ⋆ (z ⋆ y) := by rw [op_comm (.⋆.) y z]
  _ = (x ⋆ z) ⋆ y := by rw [op_assoc (.⋆.) x z y]
instance : OpRightComm (no_index s.op) := ⟨CommSemigroup.op_right_comm⟩

theorem op_cross_comm (x₁ x₂ y₁ y₂) : (x₁ ⋆ x₂) ⋆ (y₁ ⋆ y₂) = (x₁ ⋆ y₁) ⋆ (x₂ ⋆ y₂) := calc
  _ = x₁ ⋆ (x₂ ⋆ (y₁ ⋆ y₂)) := by rw [op_assoc (.⋆.) x₁ x₂ (y₁ ⋆ y₂)]
  _ = x₁ ⋆ (y₁ ⋆ (x₂ ⋆ y₂)) := by rw [op_left_comm (.⋆.) x₂ y₁ y₂]
  _ = (x₁ ⋆ y₁) ⋆ (x₂ ⋆ y₂) := by rw [op_assoc (.⋆.) x₁ y₁ (x₂ ⋆ y₂)]
instance : OpCrossComm (no_index s.op) := ⟨CommSemigroup.op_cross_comm⟩

end CommSemigroup

class CancelSemigroup extends Semigroup s where
  protected op_left_cancel (x) {y z} : x ⋆ y = x ⋆ z → y = z
  protected op_right_cancel (x) {y z} : y ⋆ x = z ⋆ x → y = z

protected def CancelSemigroup.infer [OpAssoc s.op] [OpLeftCancel s.op] [OpRightCancel s.op] : CancelSemigroup s where
  op_assoc := op_assoc _
  op_left_cancel := op_left_cancel _
  op_right_cancel := op_right_cancel _

namespace CancelSemigroup
variable {s} [self : CancelSemigroup s]

instance : OpLeftCancel (no_index s.op) := ⟨CancelSemigroup.op_left_cancel⟩
instance : OpRightCancel (no_index s.op) := ⟨CancelSemigroup.op_right_cancel⟩

end CancelSemigroup

class CancelCommSemigroup extends CommSemigroup s where
  protected op_right_cancel (x) {y z} : y ⋆ x = z ⋆ x → y = z

protected def CancelCommSemigroup.infer [OpAssoc s.op] [OpComm s.op] [OpRightCancel s.op] : CancelCommSemigroup s where
  op_assoc := op_assoc _
  op_comm := op_comm _
  op_right_cancel := op_right_cancel _

namespace CancelCommSemigroup
variable {s} [self : CancelCommSemigroup s]

local instance : OpRightCancel (no_index s.op) := ⟨CancelCommSemigroup.op_right_cancel⟩

protected theorem op_left_cancel (x) {y z} (h : x ⋆ y = x ⋆ z) : y = z :=
  op_right_cancel (.⋆.) x $ calc
  _ = x ⋆ y := by rw [op_comm (.⋆.) x y]
  _ = x ⋆ z := by rw [h]
  _ = z ⋆ x := by rw [op_comm (.⋆.) x z]
local instance : OpLeftCancel (no_index s.op) := ⟨CancelCommSemigroup.op_left_cancel⟩

instance toCancelSemigroup : CancelSemigroup s := CancelSemigroup.infer s

end CancelCommSemigroup

end Algebra
