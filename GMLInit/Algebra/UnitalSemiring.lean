import GMLInit.Algebra.Basic
import GMLInit.Algebra.Monoid
import GMLInit.Algebra.Semigroup
import GMLInit.Algebra.Semiring

namespace Algebra
variable {α} (s : UnitalSemiringSig α)

local infixr:70 " ⋆ " => s.mul
local infixr:65 " ⊹ " => s.add
local notation "e" => s.one

class UnitalSemiring extends Semiring (no_index s.toSemiringSig) : Prop where
  protected mul_left_id (x) : e ⋆ x = x
  protected mul_right_id (x) : x ⋆ e = x

def UnitalSemiring.infer [OpAssoc s.add] [OpComm s.add] [OpAssoc s.mul] [OpLeftDistrib s.mul s.add] [OpRightDistrib s.mul s.add] [OpLeftId s.mul s.one] [OpRightId s.mul s.one] : UnitalSemiring s where
  add_assoc := op_assoc
  add_comm := op_comm
  mul_assoc := op_assoc
  mul_left_distrib := op_left_distrib
  mul_right_distrib := op_right_distrib
  mul_left_id := op_left_id
  mul_right_id := op_right_id

namespace UnitalSemiring
variable {s} [self : UnitalSemiring s]

local instance : OpLeftId (no_index s.mul) (no_index s.one) := ⟨UnitalSemiring.mul_left_id⟩
local instance : OpRightId (no_index s.mul) (no_index s.one) := ⟨UnitalSemiring.mul_right_id⟩

instance toMulMonoid : Monoid (no_index s.toMulMonoidSig) := Monoid.infer s.toMulMonoidSig

end UnitalSemiring

class UnitalCommSemiring extends CommSemiring (no_index s.toSemiringSig) : Prop where
  protected mul_right_id (x) : x ⋆ e = x

def UnitalCommSemiring.infer [OpAssoc s.add] [OpComm s.add] [OpAssoc s.mul] [OpComm s.mul] [OpRightDistrib s.mul s.add] [OpRightId s.mul s.one] : UnitalCommSemiring s where
  add_assoc := op_assoc
  add_comm := op_comm
  mul_assoc := op_assoc
  mul_comm := op_comm
  mul_right_distrib := op_right_distrib
  mul_right_id := op_right_id

namespace UnitalCommSemiring
variable {s} [self : UnitalCommSemiring s]

local instance : OpRightId (no_index s.mul) (no_index s.one) := ⟨UnitalCommSemiring.mul_right_id⟩

protected theorem mul_left_id (x) : e ⋆ x = x := calc
  _ = x ⋆ e := by rw [op_comm (op:=s.mul) e x]
  _ = x := by rw [op_right_id (op:=s.mul) x]
local instance : OpLeftId (no_index s.mul) (no_index s.one) := ⟨UnitalCommSemiring.mul_left_id⟩

instance toUnitalSemiring : UnitalSemiring s :=
  set_option synthInstance.maxHeartbeats 0 in
  UnitalSemiring.infer s

instance toMulCommMonoid : CommMonoid (no_index s.toMulMonoidSig) := CommMonoid.infer s.toMulMonoidSig

end UnitalCommSemiring
