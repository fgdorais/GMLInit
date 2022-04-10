import GMLInit.Algebra.Basic
import GMLInit.Algebra.Group
import GMLInit.Algebra.Monoid
import GMLInit.Algebra.Semigroup
import GMLInit.Algebra.UnitalSemiring

namespace Algebra
variable {α} (s : RigSig α)

local infixr:70 " ⋆ " => s.mul
local infixr:65 " ⊹ " => s.add
local notation "𝟘" => s.zero

class Rig extends Semiring (no_index s.toSemiringSig) : Prop where
  protected add_right_id (x) : x ⊹ 𝟘 = x
  protected mul_left_zero (x) : 𝟘 ⋆ x = 𝟘
  protected mul_right_zero (x) : x ⋆ 𝟘 = 𝟘

def Rig.infer [OpAssoc s.add] [OpComm s.add] [OpRightId s.add s.zero] [OpAssoc s.mul] [OpLeftDistrib s.mul s.add] [OpRightDistrib s.mul s.add] [OpLeftNil s.mul s.zero] [OpRightNil s.mul s.zero] : Rig s where
  add_assoc := op_assoc _
  add_comm := op_comm _
  add_right_id := op_right_id _
  mul_assoc := op_assoc _
  mul_left_distrib := op_left_distrib _
  mul_right_distrib := op_right_distrib _
  mul_left_zero := op_left_nil _
  mul_right_zero := op_right_nil _

namespace Rig
variable {s} [self : Rig s]

local instance : OpRightId (no_index s.add) (no_index s.zero) := ⟨Rig.add_right_id⟩
instance : OpLeftNil (no_index s.mul) (no_index s.zero) := ⟨Rig.mul_left_zero⟩
instance : OpRightNil (no_index s.mul) (no_index s.zero) := ⟨Rig.mul_right_zero⟩

instance toAddCommMonoid : CommMonoid (no_index s.toAddMonoidSig) := CommMonoid.infer _

end Rig

class CommRig extends CommSemiring (no_index s.toSemiringSig): Prop where
  protected add_right_id (x) : x ⊹ 𝟘 = x
  protected mul_right_zero (x) : x ⋆ 𝟘 = 𝟘

def CommRig.infer [OpAssoc s.add] [OpComm s.add] [OpRightId s.add s.zero] [OpAssoc s.mul] [OpComm s.mul] [OpRightDistrib s.mul s.add] [OpRightNil s.mul s.zero] : CommRig s where
  add_assoc := op_assoc _
  add_comm := op_comm _
  add_right_id := op_right_id _
  mul_assoc := op_assoc _
  mul_comm := op_comm _
  mul_right_distrib := op_right_distrib _
  mul_right_zero := op_right_nil _

namespace CommRig
variable {s} [self : CommRig s]

local instance : OpRightId (no_index s.add) (no_index s.zero) := ⟨CommRig.add_right_id⟩
local instance : OpRightNil (no_index s.mul) (no_index s.zero) := ⟨CommRig.mul_right_zero⟩

protected theorem mul_left_zero (x) : 𝟘 ⋆ x = 𝟘 := calc
  _ = x ⋆ 𝟘 := by rw [op_comm (.⋆.) x 𝟘]
  _ = 𝟘 := by rw [op_right_nil (.⋆.) x]
local instance : OpLeftNil (no_index s.mul) (no_index s.zero) := ⟨CommRig.mul_left_zero⟩

instance toRig : Rig s := Rig.infer s

end CommRig

class CancelRig extends Semiring (no_index s.toSemiringSig) : Prop where
  protected add_right_id (x) : x ⊹ 𝟘 = x
  protected add_right_cancel (x) {y z} : y ⊹ x = z ⊹ x → y = z

def CancelRig.infer [OpAssoc s.add] [OpComm s.add] [OpRightId s.add s.zero] [OpRightCancel s.add] [OpAssoc s.mul] [OpLeftDistrib s.mul s.add] [OpRightDistrib s.mul s.add] : CancelRig s where
  add_assoc := op_assoc _
  add_comm := op_comm _
  add_right_id := op_right_id _
  add_right_cancel := op_right_cancel _
  mul_assoc := op_assoc _
  mul_left_distrib := op_left_distrib _
  mul_right_distrib := op_right_distrib _

namespace CancelRig
variable {s} [self : CancelRig s]

local instance : OpRightId (no_index s.add) (no_index s.zero) := ⟨CancelRig.add_right_id⟩
local instance : OpRightCancel (no_index s.add) := ⟨CancelRig.add_right_cancel⟩

instance toAddCancelCommMonoid : CancelCommMonoid (no_index s.toAddMonoidSig) := CancelCommMonoid.infer _

protected theorem mul_left_zero (x) : 𝟘 ⋆ x = 𝟘 :=
  op_right_cancel (.⊹.) (𝟘 ⋆ x) $ calc
  _ = (𝟘 ⊹ 𝟘) ⋆ x := by rw [op_right_distrib (.⋆.) 𝟘 𝟘 x]
  _ = 𝟘 ⋆ x := by rw [op_right_id (.⊹.) 𝟘]
  _ = 𝟘 ⊹ 𝟘 ⋆ x := by rw [op_left_id (.⊹.)]
local instance : OpLeftNil (no_index s.mul) (no_index s.zero) := ⟨CancelRig.mul_left_zero⟩

protected theorem mul_right_zero (x) : x ⋆ 𝟘 = 𝟘 :=
  op_right_cancel (.⊹.) (x ⋆ 𝟘) $ calc
  _ = x ⋆ (𝟘 ⊹ 𝟘) := by rw [op_left_distrib (.⋆.) x 𝟘 𝟘]
  _ = x ⋆ 𝟘 := by rw [op_right_id (.⊹.) 𝟘]
  _ = 𝟘 ⊹ x ⋆ 𝟘 := by rw [op_left_id (.⊹.)]
local instance : OpRightNil (no_index s.mul) (no_index s.zero) := ⟨CancelRig.mul_right_zero⟩

instance toRig : Rig s := Rig.infer s

end CancelRig

class CancelCommRig extends CommSemiring (no_index s.toSemiringSig) : Prop where
  protected add_right_id (x) : x ⊹ 𝟘 = x
  protected add_right_cancel (x) {y z} : y ⊹ x = z ⊹ x → y = z

def CancelCommRig.infer [OpAssoc s.add] [OpComm s.add] [OpRightId s.add s.zero] [OpRightCancel s.add] [OpAssoc s.mul] [OpComm s.mul] [OpRightDistrib s.mul s.add] : CancelCommRig s where
  add_assoc := op_assoc _
  add_comm := op_comm _
  add_right_id := op_right_id _
  add_right_cancel := op_right_cancel _
  mul_assoc := op_assoc _
  mul_comm := op_comm _
  mul_right_distrib := op_right_distrib _

namespace CancelCommRig
variable {s} [self : CancelCommRig s]

local instance : OpRightId (no_index s.add) (no_index s.zero) := ⟨CancelCommRig.add_right_id⟩
local instance : OpRightCancel (no_index s.add) := ⟨CancelCommRig.add_right_cancel⟩

instance toCancelRig : CancelRig s := CancelRig.infer s

instance toCommRig : CommRig s := CommRig.infer s

end CancelCommRig

end Algebra
