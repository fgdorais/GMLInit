import GMLInit.Algebra.Basic

namespace Algebra

class SemigroupHom (s : SemigroupSig α) (t : SemigroupSig β) (h : α → β) : Prop where
  op_hom (x y) : h (s.op x y) = t.op (h x) (h y)
export SemigroupHom (op_hom)

class MonoidHom (s : MonoidSig α) (t : MonoidSig β) (h : α → β) extends SemigroupHom (no_index s.toSemigroupSig) (no_index t.toSemigroupSig) h where
  id_hom : h s.id = t.id
export MonoidHom (id_hom)

class GroupHom (s : GroupSig α) (t : GroupSig β) (h : α → β) extends MonoidHom (no_index s.toMonoidSig) (no_index t.toMonoidSig) h where
  inv_hom (x) : h (s.inv x) = t.inv (h x)
export GroupHom (inv_hom)

class SemiringHom (s : SemiringSig α) (t : SemiringSig β) (h : α → β) where
  add_hom (x y) : h (s.add x y) = t.add (h x) (h y)
  mul_hom (x y) : h (s.mul x y) = t.mul (h x) (h y)
export SemiringHom (add_hom)
export SemiringHom (mul_hom)

instance SemiringHom.toAddSemigroupHom (s : SemiringSig α) (t : SemiringSig β) (h : α → β) [self : SemiringHom s t h] : SemigroupHom (no_index s.toAddSemigroupSig) (no_index t.toAddSemigroupSig) h where
  op_hom := add_hom

instance SemiringHom.toMulSemigroupHom (s : SemiringSig α) (t : SemiringSig β) (h : α → β) [self : SemiringHom s t h] : SemigroupHom (no_index s.toMulSemigroupSig) (no_index t.toMulSemigroupSig) h where
  op_hom := mul_hom

class RigHom (s : RigSig α) (t : RigSig β) (h : α → β) extends SemiringHom (no_index s.toSemiringSig) (no_index t.toSemiringSig) h where
  zero_hom : h s.zero = t.zero
export RigHom (zero_hom)

instance RigHom.toAddMonoidHom (s : RigSig α) (t : RigSig β) (h : α → β) [self : RigHom s t h] : MonoidHom (no_index s.toAddMonoidSig) (no_index t.toAddMonoidSig) h where
  id_hom := zero_hom

class RingHom (s : RingSig α) (t : RingSig β) (h : α → β) extends RigHom (no_index s.toRigSig) (no_index t.toRigSig) h where
  neg_hom (x) : h (s.neg x) = t.neg (h x)
export RingHom (neg_hom)

instance RingHom.toAddMonoidHom (s : RingSig α) (t : RingSig β) (h : α → β) [self : RingHom s t h] : GroupHom (no_index s.toAddGroupSig) (no_index t.toAddGroupSig) h where
  inv_hom := neg_hom

class UnitalSemiringHom (s : UnitalSemiringSig α) (t : UnitalSemiringSig β) (h : α → β) extends SemiringHom (no_index s.toSemiringSig) (no_index t.toSemiringSig) h where
  one_hom : h s.one = t.one
export UnitalSemiringHom (one_hom)

instance UnitalSemiringHom.toMulMonoidHom (s : UnitalSemiringSig α) (t : UnitalSemiringSig β) (h : α → β) [self : UnitalSemiringHom s t h] : MonoidHom (no_index s.toMulMonoidSig) (no_index t.toMulMonoidSig) h where
  id_hom := one_hom

class UnitalRigHom (s : UnitalRigSig α) (t : UnitalRigSig β) (h : α → β) extends RigHom (no_index s.toRigSig) (no_index t.toRigSig) h, UnitalSemiringHom (no_index s.toUnitalSemiringSig) (no_index t.toUnitalSemiringSig) h

class UnitalRingHom (s : UnitalRingSig α) (t : UnitalRingSig β) (h : α → β) extends RingHom (no_index s.toRingSig) (no_index t.toRingSig) h, UnitalRigHom (no_index s.toUnitalRigSig) (no_index t.toUnitalRigSig) h

end Algebra
