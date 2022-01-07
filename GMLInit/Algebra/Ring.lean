import GMLInit.Algebra.Basic
import GMLInit.Algebra.Group
import GMLInit.Algebra.Monoid
import GMLInit.Algebra.Semigroup
import GMLInit.Algebra.UnitalRig

namespace Algebra
variable {α} (s : RingSig α)

local infixr:70 " ⋆ " => s.mul
local infixr:65 " ⊹ " => s.add
local prefix:100 "∼" => s.neg
local notation "𝟘" => s.zero

class Ring extends Semiring (no_index s.toSemiringSig) : Prop where
  protected add_right_id (x) : x ⊹ 𝟘 = x
  protected add_right_inv (x) : x ⊹ ∼x = 𝟘

def Ring.infer [OpAssoc s.add] [OpComm s.add] [OpRightInv s.add s.neg s.zero] [OpRightId s.add s.zero] [OpAssoc s.mul] [OpLeftDistrib s.mul s.add] [OpRightDistrib s.mul s.add] : Ring s where
  add_assoc := op_assoc
  add_comm := op_comm
  add_right_id := op_right_id
  add_right_inv := op_right_inv
  mul_assoc := op_assoc
  mul_left_distrib := op_left_distrib
  mul_right_distrib := op_right_distrib

namespace Ring
variable {s} [self : Ring s]

local instance : OpRightId (no_index s.add) (no_index s.zero) := ⟨Ring.add_right_id⟩
local instance : OpRightInv (no_index s.add) (no_index s.neg) (no_index s.zero) := ⟨Ring.add_right_inv⟩

instance toAddCommGroup : CommGroup (no_index s.toAddGroupSig) := CommGroup.infer s.toAddGroupSig

instance toCancelRig : CancelRig (no_index s.toRigSig) :=
  set_option synthInstance.maxHeartbeats 0 in
  CancelRig.infer s.toRigSig

end Ring

class CommRing extends CommSemiring (no_index s.toSemiringSig): Prop where
  protected add_right_id (x) : x ⊹ 𝟘 = x
  protected add_right_inv (x) : x ⊹ ∼x = 𝟘

def CommRing.infer [OpAssoc s.add] [OpComm s.add] [OpRightInv s.add s.neg s.zero] [OpRightId s.add s.zero] [OpAssoc s.mul] [OpComm s.mul] [OpRightDistrib s.mul s.add] : CommRing s where
  add_assoc := op_assoc
  add_comm := op_comm
  add_right_id := op_right_id
  add_right_inv := op_right_inv
  mul_assoc := op_assoc
  mul_comm := op_comm
  mul_right_distrib := op_right_distrib

namespace CommRing
variable {s} [self : CommRing s]

local instance : OpRightId (no_index s.add) (no_index s.zero) := ⟨CommRing.add_right_id⟩
local instance : OpRightInv (no_index s.add) (no_index s.neg) (no_index s.zero) := ⟨CommRing.add_right_inv⟩

instance toRing : Ring s :=
  set_option synthInstance.maxHeartbeats 0 in
  Ring.infer s

instance toCancelCommRig : CancelCommRig (no_index s.toRigSig) :=
  set_option synthInstance.maxHeartbeats 0 in
  CancelCommRig.infer s.toRigSig

end CommRing

end Algebra
