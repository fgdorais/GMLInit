import GMLInit.Prelude

namespace Algebra

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

structure SemicategorySig {α} (β : α → α → Sort _) where
  op {{a b c}} : β b c → β a b → β a c

def SemicategorySig.toSemigroupSig {α} {β : α → α → Sort _} (s : SemicategorySig β) (a : α) : SemigroupSig (β a a) where
  op := s.op (a:=a) (b:=a) (c:=a)

structure CategorySig {α} (β : α → α → Sort _) extends SemicategorySig β where
  id {a} : β a a

def CategorySig.toMonoidSig {α} {β : α → α → Sort _} (s : CategorySig β) (a : α) : MonoidSig (β a a) where
  op := s.op (a:=a) (b:=a) (c:=a)
  id := s.id (a:=a)

unif_hint {α} {β : α → α → Sort _} (a : α) (s : SemicategorySig β) (t : CategorySig β) where
  s =?= t.toSemicategorySig ⊢ s.toSemigroupSig a =?= (t.toMonoidSig a).toSemigroupSig

structure GroupoidSig {α} (β : α → α → Sort _) extends CategorySig β where
  inv {{a b}} : β a b → β b a

def GroupoidSig.toGroupSig {α} {β : α → α → Sort _} (s : GroupoidSig β) (a : α) : GroupSig (β a a) where
  op := s.op (a:=a) (b:=a) (c:=a)
  inv := s.inv (a:=a) (b:=a)
  id := s.id (a:=a)

unif_hint {α} {β : α → α → Sort _} (a : α) (s : SemicategorySig β) (t : GroupoidSig β) where
  s =?= t.toSemicategorySig ⊢ s.toSemigroupSig a =?= (t.toGroupSig a).toSemigroupSig

unif_hint {α} {β : α → α → Sort _} (a : α) (s : CategorySig β) (t : GroupoidSig β) where
  s =?= t.toCategorySig ⊢ s.toMonoidSig a =?= (t.toGroupSig a).toMonoidSig

def SemigroupSig.toSemicategorySig {α} (s : SemigroupSig α) : SemicategorySig (λ _ _ : Unit => α) where
  op _ _ _ := s.op

def MonoidSig.toCategorySig {α} (s : MonoidSig α) : CategorySig (λ _ _ : Unit => α) where
  op _ _ _ := s.op
  id := s.id

def GroupSig.toGroupoidSig {α} (s : GroupSig α) : GroupoidSig (λ _ _ : Unit => α) where
  op _ _ _ := s.op
  inv _ _ := s.inv
  id := s.id

end Algebra
