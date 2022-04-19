import GMLInit.Data
import GMLInit.Algebra.Semigroup

namespace Algebra

namespace Semigroup

inductive Expr {α} (xs : List α)
| var : Index xs → Expr xs
| app : Expr xs → Index xs → Expr xs

namespace Expr
variable {α} {xs : List α}

instance instDecidableEq : DecidableEq (Expr xs)
| var i, var j => if h: i = j
  then Decidable.isTrue (by rw [h])
  else Decidable.isFalse (by intro H; injection H; apply h; assumption)
| app a i, app b j =>
  match instDecidableEq a b with
  | Decidable.isTrue h => if h': i = j
    then Decidable.isTrue (by rw [h, h'])
    else Decidable.isFalse (by intro H; injection H; apply h'; assumption)
  | Decidable.isFalse h => Decidable.isFalse (by intro H; injection H; apply h; assumption)
| app _ _, var _ => Decidable.isFalse (by intro H; injection H)
| var _, app _ _ => Decidable.isFalse (by intro H; injection H)

def lift (x : α) : Expr xs → Expr (x :: xs)
| var i => var (Index.tail i)
| app a i => app (lift x a) (Index.tail i)

def op : Expr xs → Expr xs → Expr xs
| a, var i => app a i
| a, app b i => app (op a b) i

section Eval
variable {α} (s : SemigroupSig α)

def eval {xs : List α} : Expr xs → α
| var i => i.val
| app a i => s.op (eval a) i.val

variable [Semigroup s]

@[simp] theorem eval_lift (x) {xs} : ∀ (a : Expr xs), eval s (lift x a) = eval s a
| var i => by simp [lift, eval]
| app a i => by simp [lift, eval, eval_lift x a]

@[simp] theorem eval_app {xs} (a : Expr xs) (i : Index xs) : eval s (app a i) = s.op (eval s a) i.val := rfl

@[simp] theorem eval_var {xs} (i : Index xs) : eval s (var i) = i.val := rfl

@[simp] theorem eval_op {xs} : ∀ (a b : Expr xs), eval s (op a b) = s.op (eval s a) (eval s b)
| a, var i => rfl
| a, app b i => by simp [eval, eval_op a b, Algebra.op_assoc s.op]

end Eval

section Completeness
variable {α} (xs : List α)

def sig : SemigroupSig (Expr xs) where
  op := Expr.op

protected theorem op_assoc : ∀ (a b c : Expr xs), op (op a b) c = op a (op b c)
| _, _, var _ => rfl
| a, b, app c k => by simp [op, Expr.op_assoc a b c]

instance : Semigroup (Expr.sig xs) where
  op_assoc := Expr.op_assoc xs

end Completeness

end Expr

class Reflect (s : SemigroupSig α) (x : α) (xs : List α) where
  expr : Expr xs
  eval_eq : expr.eval s = x

namespace Reflect
variable {α} (s : SemigroupSig α)

variable [Semigroup s]

@[simp] instance instLift (y x : α) {xs : List α} [Reflect s y xs] : Reflect s y (x :: xs) where
  expr := Expr.lift x (expr s y)
  eval_eq := by simp [eval_eq]

@[simp] instance instVar (x : α) {xs : List α} : Reflect s x (x :: xs) where
  expr := Expr.var Index.head
  eval_eq := by simp

@[simp] instance instOp (x y : α) {xs : List α} [Reflect s x xs] [Reflect s y xs] : Reflect s (no_index s.op x y) xs where
  expr := Expr.op (expr s x) (expr s y)
  eval_eq := by simp [eval_eq]

end Reflect

theorem reflect {α} (s : SemigroupSig α) [Semigroup s] (xs : List α) {a b : α} [Reflect s a xs] [Reflect s b xs] : Reflect.expr s a (xs:=xs) = Reflect.expr s b (xs:=xs) → a = b := by
  intro h
  rw [← Reflect.eval_eq (s:=s) (x:=a) (xs:=xs), ← Reflect.eval_eq (s:=s) (x:=b) (xs:=xs), h]

end Semigroup

end Algebra

section Example
open Algebra
variable {α} (s : SemigroupSig α) [Semigroup s] (a b c d : α)

local infix:70 " ⋆ " => s.op

example : (a ⋆ b) ⋆ (c ⋆ d) = a ⋆ ((b ⋆ c) ⋆ d) :=
  Semigroup.reflect s [a,b,c,d] rfl

end Example
