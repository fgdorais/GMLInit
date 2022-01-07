import GMLInit.Algebra.Basic
import GMLInit.Algebra.Group
import GMLInit.Algebra.Semiring
import GMLInit.Algebra.Ring
import GMLInit.Algebra.UnitalSemiring

namespace Algebra
variable {α} (s : UnitalRingSig α)

local infixr:65 " ⊹ " => s.add
local prefix:100 "∼" => s.neg
local notation "𝟘" => s.zero
local infixr:70 " ⋆ " => s.mul
local notation "𝟙" => s.one

class UnitalRing extends Ring (no_index s.toRingSig), UnitalSemiring (no_index s.toUnitalSemiringSig) : Prop

def UnitalRing.infer [OpAssoc s.add] [OpComm s.add] [OpRightInv s.add s.neg s.zero] [OpRightId s.add s.zero] [OpAssoc s.mul] [OpLeftDistrib s.mul s.add] [OpRightDistrib s.mul s.add] [OpLeftId s.mul s.one] [OpRightId s.mul s.one] : UnitalRing s where
  add_assoc := op_assoc
  add_comm := op_comm
  add_right_inv := op_right_inv
  add_right_id := op_right_id
  mul_assoc := op_assoc
  mul_left_distrib := op_left_distrib
  mul_right_distrib := op_right_distrib
  mul_left_id := op_left_id
  mul_right_id := op_right_id

namespace UnitalRing
variable {s} [self : UnitalRing s]

end UnitalRing

class UnitalCommRing extends CommRing (no_index s.toRingSig), UnitalCommSemiring (no_index s.toUnitalSemiringSig) : Prop

def UnitalCommRing.infer [OpAssoc s.add] [OpComm s.add] [OpRightInv s.add s.neg s.zero] [OpRightId s.add s.zero] [OpAssoc s.mul] [OpComm s.mul] [OpRightDistrib s.mul s.add] [OpRightId s.mul s.one] : UnitalCommRing s where
  add_assoc := op_assoc
  add_comm := op_comm
  add_right_inv := op_right_inv
  add_right_id := op_right_id
  mul_assoc := op_assoc
  mul_comm := op_comm
  mul_right_distrib := op_right_distrib
  mul_right_id := op_right_id

namespace UnitalCommRing
variable {s} [self : UnitalCommRing s]

end UnitalCommRing
