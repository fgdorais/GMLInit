import GMLInit.Prelude

namespace Algebra

section Signatures

structure SemigroupSig (α) where
  op : α → α → α

structure MonoidSig (α) extends SemigroupSig α where
  id : α

structure GroupSig (α) extends MonoidSig α where
  inv : α → α

structure SemiringSig (α) where
  add : α → α → α
  mul : α → α → α

def SemiringSig.toAddSemigroupSig {α} (s : SemiringSig α) : SemigroupSig α where
  op := s.add

def SemiringSig.toMulSemigroupSig {α} (s : SemiringSig α) : SemigroupSig α where
  op := s.mul

structure RigSig (α) extends SemiringSig α where
  zero : α

def RigSig.toAddMonoidSig {α} (s : RigSig α) : MonoidSig α where
  toSemigroupSig := s.toSemiringSig.toAddSemigroupSig
  id := s.zero

unif_hint {α} (s : SemigroupSig α) (t : RigSig α) where
  s =?= t.toAddMonoidSig.toSemigroupSig ⊢ s =?= t.toSemiringSig.toAddSemigroupSig

structure RingSig (α) extends RigSig α where
  neg : α → α

def RingSig.toAddGroupSig {α} (s : RingSig α) : GroupSig α where
  toMonoidSig := s.toRigSig.toAddMonoidSig
  inv := s.neg

unif_hint {α} (s : MonoidSig α) (t : RingSig α) where
  s =?= t.toAddGroupSig.toMonoidSig ⊢ s =?= t.toRigSig.toAddMonoidSig

structure UnitalSemiringSig (α) extends SemiringSig α where
  one : α

def UnitalSemiringSig.toMulMonoidSig {α} (s : UnitalSemiringSig α) : MonoidSig α where
  toSemigroupSig := s.toSemiringSig.toMulSemigroupSig
  id := s.one

unif_hint {α} (s : SemigroupSig α) (t : UnitalSemiringSig α) where
  s =?= t.toMulMonoidSig.toSemigroupSig ⊢ s =?= t.toSemiringSig.toMulSemigroupSig

structure UnitalRigSig (α) extends RigSig α, UnitalSemiringSig α

structure UnitalRingSig (α) extends RingSig α, UnitalRigSig α

unif_hint {α} (s : SemigroupSig α) (t : MonoidSig α) where
  s =?= t.toSemigroupSig ⊢ s.op =?= t.op

unif_hint {α} (s : MonoidSig α) (t : GroupSig α) where
  s =?= t.toMonoidSig ⊢ s.op =?= t.op

unif_hint {α} (s : SemigroupSig α) (t : GroupSig α) where
  s =?= t.toMonoidSig.toSemigroupSig ⊢ s.op =?= t.op

unif_hint {α} (s : MonoidSig α) (t : GroupSig α) where
  s =?= t.toMonoidSig ⊢ s.id =?= t.id

unif_hint {α} (s : SemigroupSig α) (t : SemiringSig α) where
  s =?= t.toAddSemigroupSig ⊢ s.op =?= t.add

unif_hint {α} (s : SemigroupSig α) (t : SemiringSig α) where
  s =?= t.toMulSemigroupSig ⊢ s.op =?= t.mul

unif_hint {α} (s : MonoidSig α) (t : UnitalSemiringSig α) where
  s =?= t.toMulMonoidSig ⊢ s.op =?= t.mul

unif_hint {α} (s : MonoidSig α) (t : UnitalSemiringSig α) where
  s =?= t.toMulMonoidSig ⊢ s.id =?= t.one

unif_hint {α} (s : MonoidSig α) (t : RigSig α) where
  s =?= t.toAddMonoidSig ⊢ s.op =?= t.add

unif_hint {α} (s : MonoidSig α) (t : RigSig α) where
  s =?= t.toAddMonoidSig ⊢ s.id =?= t.zero

unif_hint {α} (s : MonoidSig α) (t : UnitalRigSig α) where
  s =?= t.toUnitalSemiringSig.toMulMonoidSig ⊢ s.op =?= t.mul

unif_hint {α} (s : MonoidSig α) (t : UnitalRigSig α) where
  s =?= t.toUnitalSemiringSig.toMulMonoidSig ⊢ s.id =?= t.one

unif_hint {α} (s : GroupSig α) (t : RingSig α) where
  s =?= t.toAddGroupSig ⊢ s.op =?= t.add

unif_hint {α} (s : GroupSig α) (t : RingSig α) where
  s =?= t.toAddGroupSig ⊢ s.inv =?= t.neg

unif_hint {α} (s : GroupSig α) (t : RingSig α) where
  s =?= t.toAddGroupSig ⊢ s.id =?= t.zero

unif_hint {α} (s : MonoidSig α) (t : UnitalRingSig α) where
  s =?= t.toUnitalRigSig.toUnitalSemiringSig.toMulMonoidSig ⊢ s.op =?= t.mul

unif_hint {α} (s : MonoidSig α) (t : UnitalRingSig α) where
  s =?= t.toUnitalRigSig.toUnitalSemiringSig.toMulMonoidSig ⊢ s.id =?= t.one

end Signatures

section Identities
variable {α} (op : α → α → α) (op' : outParam (α → α → α)) (inv : outParam (α → α)) (id : outParam α) (nil : outParam α)

local infix:70 " ⋆ " => op
local infix:65 " ⊹ " => op'
local postfix:max "⁻¹" => inv
local notation "e" => id

class OpAssoc : Prop where
  op_assoc {} (x y z) : (x ⋆ y) ⋆ z = x ⋆ (y ⋆ z)
export OpAssoc (op_assoc)

class OpComm : Prop where
  op_comm {} (x y) : x ⋆ y = y ⋆ x
export OpComm (op_comm)

class OpLeftComm : Prop where
  op_left_comm {} (x y z) : x ⋆ (y ⋆ z) = y ⋆ (x ⋆ z)
export OpLeftComm (op_left_comm)

class OpRightComm : Prop where
  op_right_comm {} (x y z) : (x ⋆ y) ⋆ z = (x ⋆ z) ⋆ y
export OpRightComm (op_right_comm)

class OpCrossComm : Prop where
  op_cross_comm {} (x₁ x₂ y₁ y₂) : (x₁ ⋆ x₂) ⋆ (y₁ ⋆ y₂) = (x₁ ⋆ y₁) ⋆ (x₂ ⋆ y₂)
export OpCrossComm (op_cross_comm)

class OpLeftId : Prop where
  op_left_id {} (x) : e ⋆ x = x
export OpLeftId (op_left_id)

class OpRightId : Prop where
  op_right_id {} (x) : x ⋆ e = x
export OpRightId (op_right_id)

class OpLeftInv : Prop where
  op_left_inv {} (x) : x⁻¹ ⋆ x = e
export OpLeftInv (op_left_inv)

class OpRightInv : Prop where
  op_right_inv {} (x) : x ⋆ x⁻¹ = e
export OpRightInv (op_right_inv)

class OpLeftNil : Prop where
  op_left_nil {} (x) : nil ⋆ x = nil
  export OpLeftNil (op_left_nil)

class OpRightNil : Prop where
  op_right_nil {} (x) : x ⋆ nil = nil
export OpRightNil (op_right_nil)

class InvOp (inv : α → α) (op : outParam (α → α → α)) : Prop where
  inv_op {} (x y) : inv (op x y) = op (inv y) (inv x)
export InvOp (inv_op)

class InvHom (inv : α → α) (op : outParam (α → α → α)) : Prop where
  inv_hom {} (x y) : inv (op x y) = op (inv x) (inv y)
export InvHom (inv_hom)

class InvInv (inv : α → α) : Prop where
  inv_inv {} (x) : inv (inv x) = x
export InvInv (inv_inv)

class InvId (inv : α → α) (id : outParam α): Prop where
  inv_id {} : inv id = id
export InvId (inv_id)

class OpLeftCancel : Prop where
  op_left_cancel {} (x) {y z} : x ⋆ y = x ⋆ z → y = z
abbrev op_left_cancel (op : α → α → α) [self : OpLeftCancel op] (x) {y z} : op x y = op x z → y = z := self.op_left_cancel x

class OpRightCancel : Prop where
  op_right_cancel {} (x) {y z} : y ⋆ x = z ⋆ x → y = z
abbrev op_right_cancel (op : α → α → α) [self : OpRightCancel op] (x) {y z} : op y x = op z x → y = z := self.op_right_cancel x

class OpLeftDistrib : Prop where
  op_left_distrib {} (x y z) : x ⋆ (y ⊹ z) = x ⋆ y ⊹ x ⋆ z
export OpLeftDistrib (op_left_distrib)

class OpRightDistrib : Prop where
  op_right_distrib {} (x y z) : (x ⊹ y) ⋆ z = x ⋆ z ⊹ y ⋆ z
export OpRightDistrib (op_right_distrib)

end Identities

section Notation
variable (α)
  [HAdd α α α] [Neg α] [OfNat α 0]
  [HMul α α α] [Inv α] [OfNat α 1]

abbrev add_assoc [self : OpAssoc (.+.:α→α→α)] := self.op_assoc
abbrev add_comm [self : OpComm (.+.:α→α→α)] := self.op_comm
abbrev add_left_comm [self : OpLeftComm (.+.:α→α→α)] := self.op_left_comm
abbrev add_right_comm [self : OpRightComm (.+.:α→α→α)] := self.op_right_comm
abbrev add_cross_comm [self : OpCrossComm (.+.:α→α→α)] := self.op_cross_comm
abbrev add_zero_left [self : OpLeftId (.+.:α→α→α) 0] := self.op_left_id
abbrev add_zero_right [self : OpRightId (.+.:α→α→α) 0] := self.op_right_id
abbrev add_neg_left [self : OpLeftInv (.+.:α→α→α) (-.) 0] := self.op_left_inv
abbrev add_neg_right [self : OpRightInv (.+.:α→α→α) (-.) 0] := self.op_right_inv

abbrev neg_add [self : InvHom (-.:α→α) (.+.)] := self.inv_hom
abbrev neg_neg [self : InvInv (-.:α→α)] := self.inv_inv
abbrev neg_zero [self : InvId (-.:α→α) 0] := self.inv_id

abbrev mul_assoc [self : OpAssoc (.*.:α→α→α)] := self.op_assoc
abbrev mul_comm [self : OpComm (.*.:α→α→α)] := self.op_comm
abbrev mul_left_comm [self : OpLeftComm (.*.:α→α→α)] := self.op_left_comm
abbrev mul_right_comm [self : OpRightComm (.*.:α→α→α)] := self.op_right_comm
abbrev mul_cross_comm [self : OpCrossComm (.*.:α→α→α)] := self.op_cross_comm
abbrev mul_one_left [self : OpLeftId (.*.:α→α→α) 1] := self.op_left_id
abbrev mul_one_right [self : OpRightId (.*.:α→α→α) 1] := self.op_right_id
abbrev mul_left_distrib [self : OpLeftDistrib (.*.:α→α→α) (.+.)] := self.op_left_distrib
abbrev mul_right_distrib [self : OpRightDistrib (.*.:α→α→α) (.+.)] := self.op_right_distrib
abbrev mul_inv_left [self : OpLeftInv (.*.:α→α→α) (.⁻¹) 1] := self.op_left_inv
abbrev mul_inv_right [self : OpRightInv (.*.:α→α→α) (.⁻¹) 1] := self.op_right_inv
abbrev mul_zero_left [self : OpLeftNil (.*.:α→α→α) 0] := self.op_left_nil
abbrev mul_zero_right [self : OpRightNil (.*.:α→α→α) 0] := self.op_right_nil

abbrev inv_mul [self : InvOp (.⁻¹:α→α) (.*.)] := self.inv_op
abbrev inv_inv [self : InvInv (.⁻¹:α→α)] := self.inv_inv
abbrev inv_one [self : InvId (.⁻¹:α→α) 1] := self.inv_id

end Notation

end Algebra
