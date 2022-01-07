import GMLInit.Algebra.Basic
import GMLInit.Algebra.Monoid
import GMLInit.Algebra.Semigroup

namespace Algebra
variable {α} (s : GroupSig α)

local infixr:70 " ⋆ " => s.op
local postfix:max "⁻¹" => s.inv
local notation "e" => s.id

class Group extends Semigroup (no_index s.toSemigroupSig) : Prop where
  protected op_right_id (x) : x ⋆ e = x
  protected op_right_inv (x) : x ⋆ x⁻¹ = e

def Group.infer [OpAssoc s.op] [OpRightInv s.op s.inv s.id] [OpRightId s.op s.id] : Group s where
  op_assoc := op_assoc
  op_right_id := op_right_id
  op_right_inv := op_right_inv

namespace Group
variable {s} [self : Group s]

local instance : OpRightId (no_index s.op) (no_index s.id) := ⟨Group.op_right_id⟩
instance : OpRightInv (no_index s.op) (no_index s.inv) (no_index s.id) := ⟨Group.op_right_inv⟩

protected theorem op_right_cancel (x) {y z} (h : y ⋆ x = z ⋆ x) : y = z := calc
  _ = y ⋆ e := by rw [op_right_id (op:=s.op) y]
  _ = y ⋆ (x ⋆ x⁻¹) := by rw [op_right_inv (op:=s.op) x]
  _ = (y ⋆ x) ⋆ x⁻¹ := by rw [op_assoc (op:=s.op) y x x⁻¹]
  _ = (z ⋆ x) ⋆ x⁻¹ := by rw [h]
  _ = z ⋆ (x ⋆ x⁻¹) := by rw [op_assoc (op:=s.op) z x x⁻¹]
  _ = z ⋆ e := by rw [op_right_inv (op:=s.op) x]
  _ = z := by rw [op_right_id (op:=s.op) z]
local instance : OpRightCancel (no_index s.op) := ⟨Group.op_right_cancel⟩

protected theorem op_left_id (x) : e ⋆ x = x :=
  op_right_cancel (op:=s.op) x⁻¹ $ calc
  _ = e ⋆ (x ⋆ x⁻¹) := by rw [op_assoc (op:=s.op) e x x⁻¹]
  _ = e ⋆ e := by rw [op_right_inv (op:=s.op) x]
  _ = e := by rw [op_right_id (op:=s.op) e]
  _ = x ⋆ x⁻¹ := by rw [op_right_inv (op:=s.op) x]
local instance : OpLeftId (no_index s.op) (no_index s.id) := ⟨Group.op_left_id⟩

protected theorem op_left_inv (x) : x⁻¹ ⋆ x = e :=
  op_right_cancel (op:=s.op) x⁻¹ $ calc
  _ = x⁻¹ ⋆ (x ⋆ x⁻¹) := by rw [op_assoc (op:=s.op) x⁻¹ x x⁻¹]
  _ = x⁻¹ ⋆ e := by rw [op_right_inv (op:=s.op) x]
  _ = x⁻¹ := by rw [op_right_id (op:=s.op) x⁻¹]
  _ = e ⋆ x⁻¹ := by rw [op_left_id (op:=s.op) x⁻¹]
instance : OpLeftInv (no_index s.op) (no_index s.inv) (no_index s.id) := ⟨Group.op_left_inv⟩

protected theorem op_left_cancel (x) {y z} (h : x ⋆ y = x ⋆ z) : y = z := calc
  _ = e ⋆ y := by rw [op_left_id (op:=s.op) y]
  _ = (x⁻¹ ⋆ x) ⋆ y := by rw [op_left_inv (op:=s.op) x]
  _ = x⁻¹ ⋆ (x ⋆ y) := by rw [op_assoc (op:=s.op) x⁻¹ x y]
  _ = x⁻¹ ⋆ (x ⋆ z) := by rw [h]
  _ = (x⁻¹ ⋆ x) ⋆ z := by rw [op_assoc (op:=s.op) x⁻¹ x z]
  _ = e ⋆ z := by rw [op_left_inv (op:=s.op) x]
  _ = z := by rw [op_left_id (op:=s.op) z]
local instance : OpLeftCancel (no_index s.op) := ⟨Group.op_left_cancel⟩

protected theorem inv_op (x y) : (x ⋆ y)⁻¹ = y⁻¹ ⋆ x⁻¹ :=
  op_right_cancel (op:=s.op) (x ⋆ y) $ calc
  _ = e := by rw [op_left_inv (op:=s.op) (x ⋆ y)]
  _ = y⁻¹ ⋆ y := by rw [op_left_inv (op:=s.op) y]
  _ = y⁻¹ ⋆ (e ⋆ y) := by rw [op_left_id (op:=s.op) y]
  _ = y⁻¹ ⋆ (x⁻¹ ⋆ x) ⋆ y := by rw [op_left_inv (op:=s.op) x]
  _ = y⁻¹ ⋆ x⁻¹ ⋆ (x ⋆ y) := by rw [op_assoc (op:=s.op) x⁻¹ x y]
  _ = (y⁻¹ ⋆ x⁻¹) ⋆ (x ⋆ y) := by rw [op_assoc (op:=s.op) y⁻¹ x⁻¹ (x ⋆ y)]
instance : InvOp (no_index s.inv) (no_index s.op) := ⟨Group.inv_op⟩

protected theorem inv_inv (x) : x⁻¹⁻¹ = x :=
  op_right_cancel (op:=s.op) x⁻¹ $ calc
  _ = e := by rw [op_left_inv (op:=s.op) x⁻¹]
  _ = x ⋆ x⁻¹ := by rw [op_right_inv (op:=s.op) x]
instance : InvInv (no_index s.inv) := ⟨Group.inv_inv⟩

protected theorem inv_id : e⁻¹ = e :=
  op_right_cancel (op:=s.op) e $ calc
  _ = e := by rw [op_left_inv (op:=s.op) e]
  _ = e ⋆ e := by rw [op_right_id (op:=s.op) e]
instance : InvId (no_index s.inv) (no_index s.id) := ⟨Group.inv_id⟩

instance toCancelMonoid : CancelMonoid (no_index s.toMonoidSig) := CancelMonoid.infer s.toMonoidSig

end Group

class CommGroup extends Group s, CommMonoid (no_index s.toMonoidSig) : Prop where

def CommGroup.infer [OpAssoc s.op] [OpComm s.op] [OpRightId s.op s.id] [OpRightInv s.op s.inv s.id] : CommGroup s where
  op_assoc := op_assoc
  op_comm := op_comm
  op_right_id := op_right_id
  op_right_inv := op_right_inv

namespace CommGroup
variable {s} [self : CommGroup s]

protected theorem inv_hom (x y) : (x ⋆ y)⁻¹ = x⁻¹ ⋆ y⁻¹ := calc
  _ = y⁻¹ ⋆ x⁻¹ := by rw [inv_op (inv:=s.inv) x y]
  _ = x⁻¹ ⋆ y⁻¹ := by rw [op_comm (op:=s.op) x⁻¹ y⁻¹]
instance : InvHom (no_index s.inv) (no_index s.op) := ⟨CommGroup.inv_hom⟩

instance toCancelCommMonoid : CancelCommMonoid (no_index s.toMonoidSig) := CancelCommMonoid.infer s.toMonoidSig

end CommGroup

end Algebra
