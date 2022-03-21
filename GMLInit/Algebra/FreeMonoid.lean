import GMLInit.Algebra.Hom
import GMLInit.Algebra.Monoid
import GMLInit.Algebra.FreeSemigroup

namespace Algebra

inductive Semigroup.ToMonoid (α)
| id : ToMonoid α
| inj : α → ToMonoid α

section
variable {α} (s : SemigroupSig α)
open Semigroup (ToMonoid)

def SemigroupSig.toMonoidSig : MonoidSig (ToMonoid α) where
  id := ToMonoid.id
  op
  | ToMonoid.id, ToMonoid.id => ToMonoid.id
  | ToMonoid.id, ToMonoid.inj y => ToMonoid.inj y
  | ToMonoid.inj x, ToMonoid.id => ToMonoid.inj x
  | ToMonoid.inj x, ToMonoid.inj y => ToMonoid.inj (s.op x y)

private theorem id_op_id : s.toMonoidSig.toSemigroupSig.op ToMonoid.id ToMonoid.id = ToMonoid.id := rfl
private theorem id_op_inj (y) : s.toMonoidSig.toSemigroupSig.op ToMonoid.id (ToMonoid.inj y) = ToMonoid.inj y := rfl
private theorem inj_op_id (x) : s.toMonoidSig.toSemigroupSig.op (ToMonoid.inj x) ToMonoid.id = ToMonoid.inj x := rfl
private theorem inj_op_inj (x y) : s.toMonoidSig.toSemigroupSig.op (ToMonoid.inj x) (ToMonoid.inj y) = ToMonoid.inj (s.op x y) := rfl

instance Semigroup.toMonoid [Semigroup s] : Monoid (no_index s.toMonoidSig) where
  op_assoc
  | ToMonoid.id, ToMonoid.id, ToMonoid.id => rfl
  | ToMonoid.id, ToMonoid.id, ToMonoid.inj z => rfl
  | ToMonoid.id, ToMonoid.inj y, ToMonoid.id => rfl
  | ToMonoid.id, ToMonoid.inj y, ToMonoid.inj z => rfl
  | ToMonoid.inj x, ToMonoid.id, ToMonoid.id => rfl
  | ToMonoid.inj x, ToMonoid.id, ToMonoid.inj z => rfl
  | ToMonoid.inj x, ToMonoid.inj y, ToMonoid.id => rfl
  | ToMonoid.inj x, ToMonoid.inj y, ToMonoid.inj z => congrArg ToMonoid.inj (op_assoc x y z)
  op_left_id
  | ToMonoid.id => rfl
  | ToMonoid.inj x => rfl
  op_right_id
  | ToMonoid.id => rfl
  | ToMonoid.inj x => rfl

instance CommSemigroup.toCommMonoid [CommSemigroup s] : CommMonoid (no_index s.toMonoidSig) where
  op_assoc := op_assoc
  op_right_id := op_right_id
  op_comm
  | ToMonoid.id, ToMonoid.id => rfl
  | ToMonoid.id, ToMonoid.inj y => rfl
  | ToMonoid.inj x, ToMonoid.id => rfl
  | ToMonoid.inj x, ToMonoid.inj y => congrArg ToMonoid.inj (op_comm x y)

def CancelSemigroup.toCancelMonoid [CancelSemigroup s] (H : (x y : α) → s.op x y ≠ x ∧ s.op x y ≠ y) : CancelMonoid (no_index s.toMonoidSig) where
  op_left_cancel
  | ToMonoid.id, ToMonoid.id, ToMonoid.id, _ => rfl
  | ToMonoid.id, ToMonoid.id, ToMonoid.inj _, h => ToMonoid.noConfusion h
  | ToMonoid.id, ToMonoid.inj _, ToMonoid.id, h => ToMonoid.noConfusion h
  | ToMonoid.id, ToMonoid.inj _, ToMonoid.inj _, rfl => rfl
  | ToMonoid.inj x, ToMonoid.id, ToMonoid.id, h => rfl
  | ToMonoid.inj x, ToMonoid.id, ToMonoid.inj z, h => False.elim $ by injection h with h; exact (H x z).left.symm h
  | ToMonoid.inj x, ToMonoid.inj y, ToMonoid.id, h => False.elim $ by injection h with h; exact (H x y).left h
  | ToMonoid.inj x, ToMonoid.inj y, ToMonoid.inj z, h =>
    congrArg ToMonoid.inj $ op_left_cancel (op:=s.op) x $ by injection h with h; exact h
  op_right_cancel
  | ToMonoid.id, ToMonoid.id, ToMonoid.id, _ => rfl
  | ToMonoid.id, ToMonoid.id, ToMonoid.inj _, h => ToMonoid.noConfusion h
  | ToMonoid.id, ToMonoid.inj _, ToMonoid.id, h => ToMonoid.noConfusion h
  | ToMonoid.id, ToMonoid.inj _, ToMonoid.inj _, rfl => rfl
  | ToMonoid.inj x, ToMonoid.id, ToMonoid.id, h => rfl
  | ToMonoid.inj x, ToMonoid.id, ToMonoid.inj z, h => False.elim $ by injection h with h; exact (H z x).right.symm h
  | ToMonoid.inj x, ToMonoid.inj y, ToMonoid.id, h => False.elim $ by injection h with h; exact (H y x).right h
  | ToMonoid.inj x, ToMonoid.inj y, ToMonoid.inj z, h =>
    congrArg ToMonoid.inj $ op_right_cancel (op:=s.op) x $ by injection h with h; exact h

def CancelCommSemigroup.toCancelCommMonoid [CancelCommSemigroup s] (H : (x y : α) → s.op x y ≠ x ∧ s.op x y ≠ y) : CancelCommMonoid (no_index s.toMonoidSig) where
  op_right_cancel := (CancelSemigroup.toCancelMonoid s H).op_right_cancel

end

namespace Monoid
open Semigroup (ToMonoid)

abbrev Free (α) := ToMonoid (Semigroup.Free α)

protected abbrev Free.sig (α) : MonoidSig (Free α) := (Semigroup.Free.sig α).toMonoidSig

instance (α) : CancelMonoid (Free.sig α) :=
  CancelSemigroup.toCancelMonoid (Semigroup.Free.sig α) $
  λ as bs => ⟨Semigroup.Free.op_ne_left as bs, Semigroup.Free.op_ne_right as bs⟩

abbrev Free.gen (a : α) : Free α := ToMonoid.inj (Semigroup.Free.gen a)

namespace Free
variable {α β} (s : MonoidSig β) (f : α → β)

def eval : Free α → β
| ToMonoid.id => s.id
| ToMonoid.inj as => as.eval s.toSemigroupSig f

private theorem eval_id : eval s f ToMonoid.id = s.id := rfl
private theorem eval_inj (as) : eval s f (ToMonoid.inj as) = as.eval s.toSemigroupSig f := rfl

instance evalHom [Monoid s] : MonoidHom (Free.sig α) s (eval s f) where
  id_hom := eval_id s f
  op_hom
  | ToMonoid.id, ToMonoid.id => by rw [id_op_id, eval_id, op_right_id (op:=s.op)]
  | ToMonoid.id, ToMonoid.inj bs => by rw [id_op_inj, eval_id, op_left_id (op:=s.op)]
  | ToMonoid.inj as, ToMonoid.id => by rw [inj_op_id, eval_id, op_right_id (op:=s.op)]
  | ToMonoid.inj as, ToMonoid.inj bs => by rw [inj_op_inj, eval_inj, eval_inj, eval_inj, op_hom (t:=s.toSemigroupSig) (h:=Semigroup.Free.eval s.toSemigroupSig f)]

end Free

#exit

def Free.ofList : List α → Free α := List.foldr (λ a => (Free.sig α).op (Free.gen a)) (Free.sig α).id

theorem Free.ofList_nil {α} : Free.ofList [] = (Free.sig α).id := rfl

theorem Free.ofList_cons {α} (a : α) (as : List α) : Free.ofList (a :: as) = (Free.sig α).op (Free.gen a) (Free.ofList as) := rfl

theorem Free.ofList_append {α} (as bs : List α) : Free.ofList (as ++ bs) = (Free.sig α).op (Free.ofList as) (Free.ofList bs) := by
  induction as with
  | nil => rw [List.nil_append, ofList_nil, op_left_id (op:=(Free.sig α).op)]
  | cons a as H => rw [List.cons_append, ofList_cons, ofList_cons, H, op_assoc (op:=(Free.sig α).op)]

def Free.toList (as : Free α) : List α :=
  let rec aux : Semigroup.Free α → List α
  | Semigroup.Free.gen a => [a]
  | Semigroup.Free.app a as => a :: aux as
  match as with
  | ToMonoid.id => []
  | ToMonoid.inj as => aux as

end Monoid

#exit

inductive Free (α)
| gen : α → Free α
| app : α → Free α → Free α

namespace Free
variable {α}

protected def op : Free α → Free α → Free α
| gen a, bs => app a bs
| app a as, bs => app a (Free.op as bs)

protected def sig (α) : SemigroupSig (Free α) where
  op := Free.op

local infixr:65 " ⋆ " => SemigroupSig.op (Free.sig α)

theorem gen_op (a : α) (bs : Free α) : gen a ⋆ bs = app a bs := rfl

theorem app_op (a : α) (as bs : Free α) : app a as ⋆ bs = app a (as ⋆ bs) := rfl

protected theorem op_assoc (as bs cs : Free α) : (as ⋆ bs) ⋆ cs = as ⋆ (bs ⋆ cs) := by
  induction as with
  | gen a => rfl
  | app a as H => rw [app_op, app_op, app_op, H]

instance : Semigroup (Free.sig α) where
  op_assoc := Free.op_assoc

def eval (s : SemigroupSig β) (f : α → β) : Free α → β
| gen a => f a
| app a as => s.op (f a) (eval s f as)

theorem eval_gen (s : SemigroupSig β) (f : α → β) (a) : eval s f (gen a) = f a := rfl

theorem eval_app (s : SemigroupSig β) (f : α → β) (a as) : eval s f (app a as) = s.op (f a) (eval s f as) := rfl

instance evalHom (s : SemigroupSig β) [Semigroup s] (f : α → β) : SemigroupHom (Free.sig α) s (eval s f) where
  op_hom := by
    intro as bs
    induction as with
    | gen a => rw [gen_op, eval_gen, eval_app]
    | app a as H => rw [app_op, eval_app, eval_app, H, op_assoc (op:=s.op)]

abbrev eval_op (s : SemigroupSig β) [Semigroup s] (f : α → β) (as bs) : eval s f (as ⋆ bs) = s.op (eval s f as) (eval s f bs) := op_hom as bs

abbrev map (f : α → β) : Free α → Free β := eval (Free.sig β) (λ a => gen (f a))

end Free

end Algebra.Semigroup
