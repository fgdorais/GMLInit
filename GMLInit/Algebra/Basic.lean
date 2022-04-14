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
  protected op_assoc (x y z) : (x ⋆ y) ⋆ z = x ⋆ (y ⋆ z)
def op_assoc (op : α → α → α) [self : OpAssoc op] := self.op_assoc

class OpComm : Prop where
  protected op_comm (x y) : x ⋆ y = y ⋆ x
def op_comm (op : α → α → α) [self : OpComm op] := self.op_comm

class OpLeftComm : Prop where
  protected op_left_comm (x y z) : x ⋆ (y ⋆ z) = y ⋆ (x ⋆ z)
def op_left_comm (op : α → α → α) [self : OpLeftComm op] := self.op_left_comm

class OpRightComm : Prop where
  protected op_right_comm (x y z) : (x ⋆ y) ⋆ z = (x ⋆ z) ⋆ y
export OpRightComm (op_right_comm)
def op_right_comm (op : α → α → α) [self : OpRightComm op] := self.op_right_comm

class OpCrossComm : Prop where
  protected op_cross_comm (x₁ x₂ y₁ y₂) : (x₁ ⋆ x₂) ⋆ (y₁ ⋆ y₂) = (x₁ ⋆ y₁) ⋆ (x₂ ⋆ y₂)
def op_cross_comm (op : α → α → α) [self : OpCrossComm op] := self.op_cross_comm

class OpLeftId : Prop where
  op_left_id (x) : e ⋆ x = x
def op_left_id (op : α → α → α) {id : α} [self : OpLeftId op id] := self.op_left_id

class OpRightId : Prop where
  protected op_right_id (x) : x ⋆ e = x
def op_right_id (op : α → α → α) {id : α} [self : OpRightId op id] := self.op_right_id

class OpLeftInv : Prop where
  protected op_left_inv (x) : x⁻¹ ⋆ x = e
def op_left_inv (op : α → α → α) {inv : α → α} {id : α} [self : OpLeftInv op inv id] := self.op_left_inv

class OpRightInv : Prop where
  protected op_right_inv (x) : x ⋆ x⁻¹ = e
def op_right_inv (op : α → α → α) {inv : α → α} {id : α} [self : OpRightInv op inv id] := self.op_right_inv

class OpLeftNil : Prop where
  protected op_left_nil (x) : nil ⋆ x = nil
def op_left_nil (op : α → α → α) {nil : α} [self : OpLeftNil op nil] := self.op_left_nil

class OpRightNil : Prop where
  protected op_right_nil (x) : x ⋆ nil = nil
def op_right_nil (op : α → α → α) {nil : α} [self : OpRightNil op nil] := self.op_right_nil

class InvOp (inv : α → α) (op : outParam (α → α → α)) : Prop where
  protected inv_op (x y) : inv (op x y) = op (inv y) (inv x)
def inv_op (inv : α → α) {op : α → α → α} [self : InvOp inv op] := self.inv_op

class InvHom (inv : α → α) (op : outParam (α → α → α)) : Prop where
  protected inv_hom (x y) : inv (op x y) = op (inv x) (inv y)
def inv_hom (inv : α → α) {op : α → α → α} [self : InvHom inv op] := self.inv_hom

class InvInv (inv : α → α) : Prop where
  protected inv_inv (x) : inv (inv x) = x
def inv_inv (inv : α → α) [self : InvInv inv] := self.inv_inv

class InvId (inv : α → α) (id : outParam α): Prop where
  protected inv_id : inv id = id
def inv_id (inv : α → α) {id : α} [self : InvId inv id] := self.inv_id

class OpLeftCancel : Prop where
  protected op_left_cancel (x) {y z} : x ⋆ y = x ⋆ z → y = z
def op_left_cancel (op : α → α → α) [self : OpLeftCancel op] := self.op_left_cancel

class OpRightCancel : Prop where
  protected op_right_cancel (x) {y z} : y ⋆ x = z ⋆ x → y = z
def op_right_cancel (op : α → α → α) [self : OpRightCancel op] := self.op_right_cancel

class OpLeftDistrib : Prop where
  protected op_left_distrib (x y z) : x ⋆ (y ⊹ z) = x ⋆ y ⊹ x ⋆ z
def op_left_distrib (op : α → α → α) {op' : α → α → α} [self : OpLeftDistrib op op'] := self.op_left_distrib

class OpRightDistrib : Prop where
  protected op_right_distrib (x y z) : (x ⊹ y) ⋆ z = x ⋆ z ⊹ y ⋆ z
def op_right_distrib (op : α → α → α) {op' : α → α → α} [self : OpRightDistrib op op'] := self.op_right_distrib

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
-- abbrev inv_inv [self : InvInv (.⁻¹:α→α)] := self.inv_inv
abbrev inv_one [self : InvId (.⁻¹:α→α) 1] := self.inv_id

end Notation

end Algebra
