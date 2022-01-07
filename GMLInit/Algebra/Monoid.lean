import GMLInit.Algebra.Basic
import GMLInit.Algebra.Semigroup

namespace Algebra
variable {α} (s : MonoidSig α)

local infixr:70 " ⋆ " => s.op
local notation "e" => s.id

class Monoid extends Semigroup (no_index s.toSemigroupSig) : Prop where
  protected op_left_id (x) : e ⋆ x = x
  protected op_right_id (x) : x ⋆ e = x

def Monoid.infer [OpAssoc s.op] [OpLeftId s.op s.id] [OpRightId s.op s.id] : Monoid s where
  op_assoc := op_assoc
  op_left_id := op_left_id
  op_right_id := op_right_id

namespace Monoid
variable {s} [self : Monoid s]

instance : OpLeftId (no_index s.op) (no_index s.id) := ⟨Monoid.op_left_id⟩
instance : OpRightId (no_index s.op) (no_index s.id) := ⟨Monoid.op_right_id⟩

end Monoid

class CommMonoid extends CommSemigroup (no_index s.toSemigroupSig) : Prop where
  protected op_right_id (x) : x ⋆ e = x

def CommMonoid.infer [OpAssoc s.op] [OpComm s.op] [OpRightId s.op s.id] : CommMonoid s where
  op_assoc := op_assoc
  op_comm := op_comm
  op_right_id := op_right_id

namespace CommMonoid
variable {s} [self : CommMonoid s]

local instance : OpRightId (no_index s.op) (no_index s.id) := ⟨CommMonoid.op_right_id⟩

protected theorem op_left_id (x) : e ⋆ x = x := calc
  _ = x ⋆ e := by rw [op_comm (op:=s.op) x e]
  _ = x := by rw [op_right_id (op:=s.op) x]
local instance : OpLeftId (no_index s.op) (no_index s.id) := ⟨CommMonoid.op_left_id⟩

instance : Monoid s := Monoid.infer s

end CommMonoid

class CancelMonoid extends Monoid s, CancelSemigroup (no_index s.toSemigroupSig) : Prop

def CancelMonoid.infer [OpAssoc s.op] [OpLeftId s.op s.id] [OpRightId s.op s.id] [OpLeftCancel s.op] [OpRightCancel s.op] : CancelMonoid s where
  op_assoc := op_assoc
  op_left_id := op_left_id
  op_right_id := op_right_id
  op_left_cancel := op_left_cancel
  op_right_cancel := op_right_cancel

class CancelCommMonoid extends CommMonoid s, CancelCommSemigroup (no_index s.toSemigroupSig) : Prop

def CancelCommMonoid.infer [OpAssoc s.op] [OpComm s.op] [OpRightId s.op s.id] [OpRightCancel s.op] : CancelCommMonoid s where
  op_assoc := op_assoc
  op_comm := op_comm
  op_right_id := op_right_id
  op_right_cancel := op_right_cancel

end Algebra
