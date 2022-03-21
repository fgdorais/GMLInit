import GMLInit.Algebra.Hom
import GMLInit.Algebra.Semigroup
import GMLInit.Data.Basic

namespace Algebra.Semigroup

inductive Free (α)
| gen : α → Free α
| app : α → Free α → Free α

namespace Free
variable {α}

def op : Free α → Free α → Free α
| gen a, bs => app a bs
| app a as, bs => app a (op as bs)

theorem gen_op (a : α) (bs : Free α) : op (gen a) bs = app a bs := rfl

theorem app_op (a : α) (as bs : Free α) : op (app a as) bs = app a (op as bs) := rfl

theorem op_assoc (as bs cs : Free α) : op (op as bs) cs = op as (op bs cs) := by
  induction as with
  | gen a => rfl
  | app a as H => rw [app_op, app_op, app_op, H]

def rev : Free α → Free α
| gen a => gen a
| app a as => Free.op (rev as) (gen a)

theorem rev_gen (a : α) : rev (gen a) = gen a := rfl

theorem rev_app (a : α) (as : Free α) : rev (app a as) = op (rev as) (gen a) := rfl

theorem rev_op (as bs : Free α) : (op as bs).rev = op bs.rev as.rev := by
  induction as generalizing bs with
  | gen a => rw [gen_op, rev_app, rev_gen]
  | app a as H => rw [app_op, rev_app, rev_app, H, op_assoc]

theorem rev_rev (as : Free α) : as.rev.rev = as := by
  induction as with
  | gen a => rw [rev_gen, rev_gen]
  | app a as H => rw [rev_app, rev_op, rev_gen, gen_op, H]

theorem rev_inj {as bs : Free α} : as.rev = bs.rev → as = bs := by
  intro h
  rw [←rev_rev as, ←rev_rev bs, h]

theorem op_left_cancel (as : Free α) {bs cs : Free α} : op as bs = op as cs → bs = cs := by
  induction as with
  | gen a => intro h; rw [gen_op] at h; injection h with _ h; exact h
  | app a as H => intro h; rw [app_op, app_op] at h; injection h with _ h; apply H; exact h

theorem op_right_cancel (as : Free α) {bs cs : Free α} : op bs as = op cs as → bs = cs := by
  intro h
  apply rev_inj
  apply op_left_cancel as.rev
  rw [←rev_op, ←rev_op, h]

theorem op_ne_left (as bs : Free α) : op as bs ≠ as := by
  induction as with
  | gen a =>
    rw [gen_op]
    intro h
    contradiction
  | app a as H =>
    intro h
    rw [app_op] at h
    injection h with _ h
    apply H
    exact h

theorem op_ne_right (as bs : Free α) : op as bs ≠ bs := by
  intro h
  apply op_ne_left bs.rev as.rev
  rw [←rev_op, h]

protected def sig (α) : SemigroupSig (Free α) where
  op := Free.op

unif_hint {α} (s : SemigroupSig (Free α)) where
  s =?= Free.sig α ⊢ s.op =?= Free.op

instance : CancelSemigroup (Free.sig α) where
  op_assoc := op_assoc
  op_left_cancel := op_left_cancel
  op_right_cancel := op_right_cancel

section eval
variable (s : SemigroupSig β) (f : α → β)

def eval : Free α → β
| gen a => f a
| app a as => s.op (f a) (eval as)

theorem eval_gen (a : α) : eval s f (gen a) = f a := rfl

theorem eval_app (a : α) (as : Free α) : eval s f (app a as) = s.op (f a) (eval s f as) := rfl

instance evalHom [Semigroup s] : SemigroupHom (Free.sig α) s (eval s f) where
  op_hom := by
    intro as bs
    simp only [Free.sig]
    induction as with
    | gen a => rw [gen_op, eval_gen, eval_app]
    | app a as H => rw [app_op, eval_app, eval_app, H, Algebra.op_assoc (op:=s.op)]

abbrev eval_op [Semigroup s] (as bs : Free α) : eval s f (op as bs) = s.op (eval s f as) (eval s f bs) :=
  op_hom (s:=Free.sig α) as bs

end eval

end Free

end Algebra.Semigroup
