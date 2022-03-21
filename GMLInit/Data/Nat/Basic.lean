import GMLInit.Meta.Basic
import GMLInit.Meta.Decidable
import GMLInit.Meta.Relation
import GMLInit.Algebra.UnitalRig

namespace Nat

protected def recAux.{u} {motive : Nat → Sort u} (zero : motive 0) (succ : (n : Nat) → motive n → motive (n+1)) : (t : Nat) → motive t
| 0 => zero
| n+1 => succ n (Nat.recAux zero succ n)

protected def recAuxOn.{u} {motive : Nat → Sort u} (t : Nat) (zero : motive 0) (succ : (n : Nat) → motive n → motive (n+1)) : motive t :=
  Nat.recAux zero succ t

protected def casesAuxOn.{u} {motive : Nat → Sort u} (t : Nat) (zero : motive 0) (succ : (n : Nat) → motive (n+1)) : motive t :=
  Nat.recAux zero (λ n _ => succ n) t

protected def recDiagAux.{u} {motive : Nat → Nat → Sort u}
  (left : (x : Nat) → motive x 0)
  (right : (y : Nat) → motive 0 y)
  (diag : (x y : Nat) → motive x y → motive (x + 1) (y + 1)) :
  (x y : Nat) → motive x y
| x, 0 => left x
| 0, y => right y
| x + 1, y + 1 => diag x y (Nat.recDiagAux left right diag x y)

protected def recDiagAuxOn.{u} {motive : Nat → Nat → Sort u} (x y : Nat)
  (left : (x : Nat) → motive x 0)
  (right : (y : Nat) → motive 0 y)
  (diag : (x y : Nat) → motive x y → motive (x + 1) (y + 1)) :
  motive x y :=
  Nat.recDiagAux left right diag x y

protected def casesDiagAuxOn.{u} {motive : Nat → Nat → Sort u} (x y : Nat)
  (left : (x : Nat) → motive x 0)
  (right : (y : Nat) → motive 0 y)
  (diag : (x y : Nat) → motive (x + 1) (y + 1)) :
  motive x y :=
  Nat.recDiagAuxOn x y left right (λ x y _ => diag x y)

protected def recDiag.{u} {motive : Nat → Nat → Sort u}
  (zero_zero : motive 0 0)
  (succ_zero : (x : Nat) → motive x 0 → motive (x + 1) 0)
  (zero_succ : (y : Nat) → motive 0 y → motive 0 (y + 1))
  (succ_succ : (x y : Nat) → motive x y → motive (x + 1) (y + 1)) :
  (x y : Nat) → motive x y :=
  Nat.recDiagAux left right succ_succ where
  left : (x : Nat) → motive x 0
  | 0 => zero_zero
  | x+1 => succ_zero x (left x)
  right : (y : Nat) → motive 0 y
  | 0 => zero_zero
  | y+1 => zero_succ y (right y)

protected def recDiagOn.{u} {motive : Nat → Nat → Sort u} (x y : Nat)
  (zero_zero : motive 0 0)
  (succ_zero : (x : Nat) → motive x 0 → motive (x + 1) 0)
  (zero_succ : (y : Nat) → motive 0 y → motive 0 (y + 1))
  (succ_succ : (x y : Nat) → motive x y → motive (x + 1) (y + 1)) :
  motive x y :=
  Nat.recDiag zero_zero succ_zero zero_succ succ_succ x y

protected def casesDiagOn.{u} {motive : Nat → Nat → Sort u} (x y : Nat)
  (zero_zero : motive 0 0)
  (succ_zero : (x : Nat) → motive (x + 1) 0)
  (zero_succ : (y : Nat) → motive 0 (y + 1))
  (succ_succ : (x y : Nat) → motive (x + 1) (y + 1)) :
  motive x y :=
  Nat.recDiagOn x y zero_zero (λ x _ => succ_zero x) (λ y _ => zero_succ y) (λ x y _ => succ_succ x y)

@[simp] protected lemma simp_zero : Nat.zero = 0 := rfl

@[simp] protected lemma simp_succ (x : Nat) : Nat.succ x = x + 1 := rfl

@[simp] protected lemma simp_pred (x : Nat) : Nat.pred x = x - 1 := rfl

@[simp] protected lemma simp_add (x y : Nat) : Nat.add x y = x + y := rfl

@[simp] protected lemma simp_sub (x y : Nat) : Nat.sub x y = x - y := rfl

@[simp] protected lemma simp_mul (x y : Nat) : Nat.mul x y = x * y := rfl

@[simp] protected lemma simp_div (x y : Nat) : Nat.div x y = x / y := rfl

@[simp] protected lemma simp_mod (x y : Nat) : Nat.mod x y = x % y := rfl

@[simp] protected lemma simp_pow (x y : Nat) : Nat.pow x y = x ^ y := rfl

@[simp] protected theorem simp_one_add (x : Nat) : 1 + x = x + 1 := by
  rw [Nat.succ_add, Nat.zero_add]

protected theorem le_succ_self (x : Nat) : x ≤ x.succ := Nat.le_succ x -- fix

protected theorem Nat.pred_zero : 0 - 1 = 0 := rfl

protected theorem Nat.pred_succ (x : Nat) : (x + 1) - 1 = x := rfl

protected theorem Nat.succ_pred_of_nonzero {x : Nat} : x ≠ 0 → (x - 1) + 1 = x := by
  cases x using Nat.casesAuxOn with
  | zero => intro; contradiction
  | succ x => intro; rw [Nat.pred_succ]

protected def rigSig : Algebra.UnitalRigSig Nat where
  add := (.+.)
  mul := Nat.mul
  zero := Nat.zero
  one := Nat.succ Nat.zero

unif_hint (s : Algebra.UnitalRigSig Nat) where
  s =?= Nat.rigSig ⊢ s.toSemiringSig.add =?= Nat.add

unif_hint (s : Algebra.UnitalRigSig Nat) where
  s =?= Nat.rigSig ⊢ s.toSemiringSig.mul =?= (.*.)

unif_hint (s : Algebra.UnitalRigSig Nat) where
  s =?= Nat.rigSig ⊢ s.toRigSig.zero =?= 0

unif_hint (s : Algebra.UnitalRigSig Nat) where
  s =?= Nat.rigSig ⊢ s.toUnitalSemiringSig.one =?= 1

protected def addSig : Algebra.MonoidSig Nat where
  op := (.+.)
  id := Nat.zero

unif_hint (s : Algebra.MonoidSig Nat) where
  s =?= Nat.addSig ⊢ s.toSemigroupSig.op =?= Nat.add

unif_hint (s : Algebra.MonoidSig Nat) where
  s =?= Nat.addSig ⊢ s.toSemigroupSig.op =?= (.+.)

unif_hint (s : Algebra.MonoidSig Nat) where
  s =?= Nat.addSig ⊢ s.toSemigroupSig.op =?= Nat.rigSig.add

unif_hint (s : Algebra.UnitalRigSig Nat) (t : Algebra.MonoidSig Nat) where
  s =?= Nat.rigSig, t =?= Nat.addSig ⊢ s.add =?= t.op

instance : Algebra.CancelUnitalCommRig Nat.rigSig where
  add_assoc := Nat.add_assoc
  add_comm := Nat.add_comm
  add_right_id := Nat.add_zero
  add_right_cancel _ := Nat.add_right_cancel
  mul_assoc := Nat.mul_assoc
  mul_comm := Nat.mul_comm
  mul_right_distrib := Nat.add_mul
  mul_right_id := Nat.mul_one

instance : Algebra.CancelCommMonoid Nat.addSig where
  op_assoc := Nat.add_assoc
  op_comm := Nat.add_comm
  op_right_id := Nat.add_zero
  op_right_cancel _ := Nat.add_right_cancel

instance : Algebra.CommMonoid Nat.rigSig.toUnitalSemiringSig.toMulMonoidSig :=
  Algebra.CommMonoid.infer _

end Nat
