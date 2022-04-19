import GMLInit.Data
import GMLInit.Algebra.Monoid

namespace Algebra.CommMonoid
open Algebra

inductive Expr {α : Type _} : List α → Type _
| nil : Expr []
| cons (n : Nat) {x : α} {xs : List α} : Expr xs → Expr (x :: xs)

namespace Expr

instance instDecidableEq {α} : {xs : List α} → DecidableEq (Expr xs)
| [], nil, nil => Decidable.isTrue rfl
| _::_, cons m a, cons n b => match instDecidableEq a b with
  | Decidable.isTrue h => if h': m = n
    then Decidable.isTrue (by rw [h, h'])
    else Decidable.isFalse (by intro H; injection H; apply h'; assumption)
  | Decidable.isFalse h => Decidable.isFalse (by intro H; injection H; apply h; assumption)

abbrev lift {α} (x : α) {xs : List α} : Expr xs → Expr (x :: xs) := cons 0

protected def id {α} : {xs : List α} → Expr xs
| [] => nil
| x :: xs => cons 0 Expr.id

protected def op {α} : {xs : List α} → Expr xs → Expr xs → Expr xs
| [], _, _ => nil
| _::_, cons m a, cons n b => cons (m + n) (Expr.op a b)

section Eval
variable {α} (s : MonoidSig α)

def eval : {xs : List α} → Expr xs → α
| [], _ => s.id
| _::_, cons 0 a => eval a
| x::xs, cons (n+1) a => s.op x (eval (xs:=x::xs) (cons n a))

variable [CommMonoid s]

@[simp] theorem eval_lift {x : α} {xs : List α} (a : Expr xs) : eval s (Expr.lift x a) = eval s a := by
  unfold eval

@[simp] theorem eval_cons_zero {x : α} {xs : List α} (a : Expr xs) : eval s (Expr.cons (x:=x) 0 a) = eval s a := by
  unfold eval

@[simp] theorem eval_cons_succ {x : α} {xs : List α} (a : Expr xs) : eval s (Expr.cons (x:=x) (n+1) a) = s.op x (eval s (cons (x:=x) n a)) := by
  unfold eval

@[simp] theorem eval_id : ∀ {xs : List α}, eval s (Expr.id (xs:=xs)) = s.id
| [] => rfl
| _::_ => by unfold eval Expr.id; exact eval_id

@[simp] theorem eval_op {xs : List α} (a b : Expr xs) : eval s (Expr.op a b) = s.op (eval s a) (eval s b) := by
  induction xs with
  | nil =>
    match a, b with
    | nil, nil =>
      unfold eval
      rw [Algebra.op_left_id s.op]
  | cons x xs ihxs =>
    match a, b with
    | cons m a, cons n b =>
      induction m, n using Nat.recDiagOn with
      | zero_zero => calc
        _ = eval s (Expr.op (cons 0 a) (cons 0 b)) := rfl
        _ = eval s (cons 0 (Expr.op a b)) := by rw [Expr.op]
        _ = eval s (Expr.op a b) := by rw [eval_cons_zero]
        _ = s.op (eval s a) (eval s b) := by rw [ihxs a b]
        _ = s.op (eval s (cons 0 a)) (eval s b) := by rw [eval_cons_zero s a (x:=x)]
        _ = s.op (eval s (cons 0 a)) (eval s (cons 0 b)) := by rw [eval_cons_zero s b (x:=x)]
      | zero_succ n ih => calc
        _ = eval s (Expr.op (cons 0 a) (cons (n + 1) b)) := rfl
        _ = eval s (cons (n + 1) (Expr.op a b)) := by rw [Expr.op, Nat.zero_add]
        _ = s.op x (eval s (cons n (Expr.op a b))) := by rw [eval_cons_succ]
        _ = s.op x (eval s ((Expr.op (cons 0 a) (cons n b)))) := by rw [Expr.op, Nat.zero_add]
        _ = s.op x (s.op (eval s (cons 0 a)) (eval s (cons n b))) := by rw [ih]
        _ = s.op (eval s (cons 0 a)) (s.op x (eval s (cons n b))) := by rw [Algebra.op_left_comm s.op]
        _ = s.op (eval s (cons 0 a)) (eval s (cons (n + 1) b)) := by rw [eval_cons_succ]
      | succ_zero m ih => calc
        _ = eval s (Expr.op (cons (m + 1) a) (cons 0 b)) := rfl
        _ = eval s (cons (m + 1) (Expr.op a b)) := by rw [Expr.op]
        _ = s.op x (eval s (cons (m + 0) (Expr.op a b))) := by rw [eval_cons_succ, Nat.add_zero]
        _ = s.op x (eval s (Expr.op (cons m a) (cons 0 b))) := by rw [Expr.op]
        _ = s.op x (s.op (eval s (cons m a)) (eval s (cons 0 b))) := by rw [ih]
        _ = s.op (s.op x (eval s (cons m a))) (eval s (cons 0 b)) := by rw [Algebra.op_assoc s.op]
        _ = s.op (eval s (cons (m + 1) a)) (eval s (cons 0 b)) := by rw [eval_cons_succ]
      | succ_succ m n ih => calc
        _ = eval s (Expr.op (cons (m + 1) a) (cons (n + 1) b)) := rfl
        _ = eval s (cons ((m + 1) + (n + 1)) (Expr.op a b)) := by rw [Expr.op]
        _ = eval s (cons (m + n + 1 + 1) (Expr.op a b)) := by rw [Nat.add_succ, Nat.succ_add]; rfl
        _ = s.op x (s.op x (eval s (cons (m + n) (Expr.op a b)))) := by rw [eval_cons_succ, eval_cons_succ]
        _ = s.op x (s.op x (eval s (Expr.op (cons m a) (cons n b)))) := by rw [Expr.op]
        _ = s.op x (s.op x (s.op (eval s (cons m a)) (eval s (cons n b)))) := by rw [ih]
        _ = s.op (s.op x x) (s.op (eval s (cons m a)) (eval s (cons n b))) := by rw [Algebra.op_assoc s.op]
        _ = s.op (s.op x (eval s (cons m a))) (s.op x (eval s (cons n b))) := by rw [Algebra.op_cross_comm s.op]
        _ = s.op (eval s (cons (m + 1) a)) (eval s (cons (n + 1) b)) := by rw [eval_cons_succ, eval_cons_succ]

end Eval

section Completeness

theorem op_assoc {α} : ∀ {xs : List α} (a b c : Expr xs), Expr.op (Expr.op a b) c = Expr.op a (Expr.op b c)
| [], _, _, _ => by unfold Expr.op
| _::_, cons l a, cons m b, cons n c => by simp only [Expr.op, Nat.add_assoc l m n, op_assoc a b c]

theorem op_comm {α} : ∀ {xs : List α} (a b : Expr xs), Expr.op a b = Expr.op b a
| [], _, _ => by unfold Expr.op
| _::_, cons m a, cons n b => by simp only [Expr.op, Nat.add_comm m n, op_comm a b]

theorem op_right_id {α} : ∀ {xs : List α} (a : Expr xs), Expr.op a Expr.id = a
| [], nil => by unfold Expr.op
| _::_, cons n a => by simp only [Expr.op, Nat.add_zero n, op_right_id a]

def sig {α} (xs : List α) : MonoidSig (Expr xs) where
  op := Expr.op
  id := Expr.id

instance {α} (xs : List α) : CommMonoid (sig xs) where
  op_assoc := op_assoc
  op_comm := op_comm
  op_right_id := op_right_id

end Completeness

end Expr

class Reflect {α} (s : MonoidSig α) (x : α) (xs : List α) where
  expr : Expr xs
  eval_eq : expr.eval s = x

protected def Reflect.eq {α} (s : MonoidSig α) (x xs) [inst : Reflect s x xs] : inst.expr.eval s = x := inst.eval_eq

namespace Reflect
variable {α} (s : MonoidSig α) [CommMonoid s]

instance instLift (y x : α) {xs : List α} [Reflect s y xs] : Reflect s y (x :: xs) where
  expr := Expr.lift x (expr s y)
  eval_eq := by simp [eval_eq]

instance instVar (x : α) {xs : List α} : Reflect s x (x :: xs) where
  expr := Expr.cons 1 Expr.id
  eval_eq := by simp; rw [Algebra.op_right_id s.op]

instance instOp (x y : α) {xs : List α} [Reflect s x xs] [Reflect s y xs] : Reflect s (no_index (s.op x y)) xs where
  expr := Expr.op (expr s x) (expr s y)
  eval_eq := by simp [eval_eq]

instance instId {xs : List α} : Reflect s (no_index (s.id)) xs where
  expr := Expr.id
  eval_eq := by simp

end Reflect

theorem reflect {α} (s : MonoidSig α) [CommMonoid s] (xs : List α) {a b : α} [Reflect s a xs] [Reflect s b xs] : Reflect.expr s a (xs:=xs) = Reflect.expr s b → a = b := by
  intro h
  rw [←Reflect.eq s a xs, ←Reflect.eq s b xs, h]

end Algebra.CommMonoid
