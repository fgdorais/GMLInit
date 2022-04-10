import GMLInit.Algebra.Basic
import GMLInit.Algebra.Group

namespace Algebra
variable {α} (s : SemiringSig α)

local infixr:70 " ⋆ " => s.mul
local infixr:65 " ⊹ " => s.add

class Semiring : Prop where
  protected add_assoc (x y z) : (x ⊹ y) ⊹ z = x ⊹ (y ⊹ z)
  protected add_comm (x y) : x ⊹ y = y ⊹ x
  protected mul_assoc (x y z) : (x ⋆ y) ⋆ z = x ⋆ (y ⋆ z)
  protected mul_left_distrib (x y z) : x ⋆ (y ⊹ z) = x ⋆ y ⊹ x ⋆ z
  protected mul_right_distrib (x y z) : (x ⊹ y) ⋆ z = x ⋆ z ⊹ y ⋆ z

def Semiring.infer [OpAssoc s.add] [OpComm s.add] [OpAssoc s.mul] [OpLeftDistrib s.mul s.add] [OpRightDistrib s.mul s.add] : Semiring s where
  add_assoc := op_assoc _
  add_comm := op_comm _
  mul_assoc := op_assoc _
  mul_left_distrib := op_left_distrib _
  mul_right_distrib := op_right_distrib _

namespace Semiring
variable {s} [self : Semiring s]

local instance : OpAssoc (no_index s.add) := ⟨Semiring.add_assoc⟩
local instance : OpComm (no_index s.add) := ⟨Semiring.add_comm⟩
local instance : OpAssoc (no_index s.mul) := ⟨Semiring.mul_assoc⟩
instance : OpLeftDistrib (no_index s.mul) (no_index s.add) := ⟨Semiring.mul_left_distrib⟩
instance : OpRightDistrib (no_index s.mul) (no_index s.add) := ⟨Semiring.mul_right_distrib⟩

instance toAddCommSemigroup : CommSemigroup (no_index s.toAddSemigroupSig) := CommSemigroup.infer _

instance toMulSemigroup : Semigroup (no_index s.toMulSemigroupSig) := Semigroup.infer _

end Semiring

class CommSemiring : Prop where
  protected add_assoc (x y z) : (x ⊹ y) ⊹ z = x ⊹ (y ⊹ z)
  protected add_comm (x y) : x ⊹ y = y ⊹ x
  protected mul_assoc (x y z) : (x ⋆ y) ⋆ z = x ⋆ (y ⋆ z)
  protected mul_comm (x y) : x ⋆ y = y ⋆ x
  protected mul_right_distrib (x y z) : (x ⊹ y) ⋆ z = x ⋆ z ⊹ y ⋆ z

def CommSemiring.infer [OpAssoc s.add] [OpComm s.add] [OpAssoc s.mul] [OpComm s.mul] [OpRightDistrib s.mul s.add] : CommSemiring s where
  add_assoc := op_assoc _
  add_comm := op_comm _
  mul_assoc := op_assoc _
  mul_comm := op_comm _
  mul_right_distrib := op_right_distrib _

namespace CommSemiring
variable {s} [self : CommSemiring s]

local instance : OpAssoc (no_index s.add) := ⟨CommSemiring.add_assoc⟩
local instance : OpComm (no_index s.add) := ⟨CommSemiring.add_comm⟩
local instance : OpAssoc (no_index s.mul) := ⟨CommSemiring.mul_assoc⟩
local instance : OpComm (no_index s.mul) := ⟨CommSemiring.mul_comm⟩
local instance : OpRightDistrib (no_index s.mul) (no_index s.add) := ⟨CommSemiring.mul_right_distrib⟩

protected theorem mul_left_distrib (x y z) : x ⋆ (y ⊹ z) = x ⋆ y ⊹ x ⋆ z := calc
  _ = (y ⊹ z) ⋆ x := by rw [op_comm (.⋆.) x (y ⊹ z)]
  _ = y ⋆ x ⊹ z ⋆ x := by rw [op_right_distrib (.⋆.) y z x]
  _ = x ⋆ y ⊹ z ⋆ x := by rw [op_comm (.⋆.) x y]
  _ = x ⋆ y ⊹ x ⋆ z := by rw [op_comm (.⋆.) x z]
local instance : OpLeftDistrib (no_index s.mul) (no_index s.add) := ⟨CommSemiring.mul_left_distrib⟩

instance toSemiring : Semiring s := Semiring.infer s

instance toMulCommSemigroup : CommSemigroup (no_index s.toMulSemigroupSig) := CommSemigroup.infer _

end CommSemiring
