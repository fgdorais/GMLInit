import GMLInit.Algebra.Basic

namespace Algebra

class SemigroupHom (s : SemigroupSig α) (t : SemigroupSig β) (f : α → β) : Prop where
  op_hom (x y) : f (s.op x y) = t.op (f x) (f y)

class MonoidHom (s : MonoidSig α) (t : MonoidSig β) (f : α → β) extends SemigroupHom (no_index s.toSemigroupSig) (no_index t.toSemigroupSig) f where
  id_hom : f s.id = t.id

class GroupHom (s : GroupSig α) (t : GroupSig β) (f : α → β) extends MonoidHom (no_index s.toMonoidSig) (no_index t.toMonoidSig) f where
  inv_hom (x) : f (s.inv x) = t.inv (f x)

class SemiringHom (s : SemiringSig α) (t : SemiringSig β) (f : α → β) where
  add_hom (x y) : f (s.add x y) = t.add (f x) (f y)
  mul_hom (x y) : f (s.mul x y) = t.mul (f x) (f y)

instance SemiringHom.toAddSemigroupHom (s : SemiringSig α) (t : SemiringSig β) (f : α → β) [self : SemiringHom s t f] : SemigroupHom (no_index s.toAddSemigroupSig) (no_index t.toAddSemigroupSig) f where
  op_hom := add_hom

instance SemiringHom.toMulSemigroupHom (s : SemiringSig α) (t : SemiringSig β) (f : α → β) [self : SemiringHom s t f] : SemigroupHom (no_index s.toMulSemigroupSig) (no_index t.toMulSemigroupSig) f where
  op_hom := mul_hom

class RigHom (s : RigSig α) (t : RigSig β) (f : α → β) extends SemiringHom (no_index s.toSemiringSig) (no_index t.toSemiringSig) f where
  zero_hom : f s.zero = t.zero

instance RigHom.toAddMonoidHom (s : RigSig α) (t : RigSig β) (f : α → β) [self : RigHom s t f] : MonoidHom (no_index s.toAddMonoidSig) (no_index t.toAddMonoidSig) f where
  id_hom := zero_hom

class RingHom (s : RingSig α) (t : RingSig β) (f : α → β) extends RigHom (no_index s.toRigSig) (no_index t.toRigSig) f where
  neg_hom (x) : f (s.neg x) = t.neg (f x)

instance RingHom.toAddMonoidHom (s : RingSig α) (t : RingSig β) (f : α → β) [self : RingHom s t f] : GroupHom (no_index s.toAddGroupSig) (no_index t.toAddGroupSig) f where
  inv_hom := neg_hom

class UnitalSemiringHom (s : UnitalSemiringSig α) (t : UnitalSemiringSig β) (f : α → β) extends SemiringHom (no_index s.toSemiringSig) (no_index t.toSemiringSig) f where
  one_hom : f s.one = t.one

instance UnitalSemiringHom.toMulMonoidHom (s : UnitalSemiringSig α) (t : UnitalSemiringSig β) (f : α → β) [self : UnitalSemiringHom s t f] : MonoidHom (no_index s.toMulMonoidSig) (no_index t.toMulMonoidSig) f where
  id_hom := one_hom

class UnitalRigHom (s : UnitalRigSig α) (t : UnitalRigSig β) (f : α → β) extends RigHom (no_index s.toRigSig) (no_index t.toRigSig) f, UnitalSemiringHom (no_index s.toUnitalSemiringSig) (no_index t.toUnitalSemiringSig) f

class UnitalRingHom (s : UnitalRingSig α) (t : UnitalRingSig β) (f : α → β) extends RingHom (no_index s.toRingSig) (no_index t.toRingSig) f, UnitalRigHom (no_index s.toUnitalRigSig) (no_index t.toUnitalRigSig) f

end Algebra
