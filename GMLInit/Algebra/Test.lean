import GMLInit.Algebra.Basic
import GMLInit.Algebra.Group
import GMLInit.Algebra.Monoid
import GMLInit.Algebra.Semigroup
import GMLInit.Algebra.Semiring
import GMLInit.Algebra.UnitalRing

open Algebra

--abbrev Algebra.add_right_comm {α} [HAdd α α α] [OpRightComm (HAdd.hAdd:α→α→α)] (x y z : α) := op_right_comm (op:=HAdd.hAdd) x y z

def Nat.unitalRigSig : UnitalRigSig Nat where
  add := Nat.add
  mul := Nat.mul
  one := Nat.succ Nat.zero
  zero := Nat.zero

unif_hint (s : UnitalRigSig Nat) where
  s =?= Nat.unitalRigSig ⊢ s.add =?= HAdd.hAdd

unif_hint (s : UnitalRigSig Nat) where
  s =?= Nat.unitalRigSig ⊢ s.mul =?= HMul.hMul

unif_hint (s : SemiringSig Nat) where
  s =?= Nat.unitalRigSig.toSemiringSig ⊢ s.add =?= HAdd.hAdd

unif_hint (s : SemiringSig Nat) where
  s =?= Nat.unitalRigSig.toSemiringSig ⊢ s.mul =?= HMul.hMul

unif_hint (s : SemigroupSig Nat) where
  s =?= Nat.unitalRigSig.toAddSemigroupSig ⊢ s.op =?= HAdd.hAdd

unif_hint (s : MonoidSig Nat) where
  s =?= Nat.unitalRigSig.toUnitalSemiringSig.toMulMonoidSig ⊢ s.op =?= HMul.hMul

unif_hint (s : MonoidSig Nat) where
  s =?= Nat.unitalRigSig.toUnitalSemiringSig.toMulMonoidSig ⊢ s.id =?= 1

instance : CancelUnitalCommRig (no_index Nat.unitalRigSig) where
  add_assoc := Nat.add_assoc
  add_comm := Nat.add_comm
  add_right_id := Nat.add_zero
  add_right_cancel _ := Nat.add_right_cancel
  mul_assoc := Nat.mul_assoc
  mul_comm := Nat.mul_comm
  mul_right_id := Nat.mul_one
  mul_right_distrib := Nat.add_mul

set_option synthInstance.maxHeartbeats 0

example (x y : Nat) : x * (y + 1) = x * y + x := calc
  _ = x * y + x * 1 := by rw [mul_left_distrib Nat x y 1]
  _ = x * y + x := by rw [mul_one_right Nat x]

def Nat.addMonoidSig : MonoidSig Nat where
  op := Nat.add
  id := Nat.zero

unif_hint (s : MonoidSig Nat) where
  s =?= Nat.addMonoidSig ⊢ s.op =?= (.+.)

unif_hint (s : MonoidSig Nat) where
  s =?= Nat.addMonoidSig ⊢ s.id =?= 0

example (x y z : Nat) : (x + y) + z = (x + z) + y :=
  op_right_comm x y z

example (x y z : Nat) : (x + y) + z = (x + z) + y := by
  rw [add_right_comm Nat x y z]

instance Nat.addCommMonoid : CommMonoid addMonoidSig where
  op_assoc := Nat.add_assoc
  op_comm := Nat.add_comm
  op_right_id := Nat.add_zero

example (x y z : Nat) : (0 + y) + z = z + y := by
  rw [add_zero_left Nat y]
  rw [add_comm Nat y z]
