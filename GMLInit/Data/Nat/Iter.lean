import GMLInit.Data.Nat.Basic

namespace Nat
variable {α} (f : α → α)

/-- `iter (f : α → α) (n : Nat)` calculates the `n`th iterate of the function `f` -/
@[specialize, inline] def iter : (n : Nat) → α → α
| 0, r => r
| n+1, r => iter n (f r)

theorem iter_zero (a : α) : iter f 0 a = a := rfl

theorem iter_one (a : α) : iter f 1 a = f a := rfl

theorem iter_succ (n : Nat) (a : α) : iter f (n + 1) a = iter f n (f a) := rfl

theorem iter_add (m n : Nat) (a : α) : iter f (m + n) a = iter f m (iter f n a) := by
  induction n generalizing a with
  | zero => rfl
  | succ n ih =>
    calc
    _ = iter f (m + n + 1) a := rfl
    _ = iter f (m + n) (f a) := by rw [iter_succ]
    _ = iter f m (iter f n (f a)) := by rw [ih]
    _ = iter f m (iter f (n + 1) a) := by rw [iter_succ]

theorem iter_mul (m n : Nat) (a : α) : iter f (m * n) a = iter (iter f m) n a := by
  induction n generalizing a with
  | zero => rfl
  | succ n ih =>
    calc
    _ = iter f (m * n + m) a := rfl
    _ = iter f (m * n) (iter f m a) := by rw [iter_add]
    _ = iter (iter f m) n (iter f m a) := by rw [ih]
    _ = iter (iter f m) (n + 1) a := by rw [iter_succ]

theorem iter_zero_eq_id : iter f 0 = id := rfl

theorem iter_one_eq_self : iter f 1 = f := rfl

theorem iter_succ_eq_iter_comp_self (n : Nat) : iter f (n + 1) = iter f n ∘ f := rfl

theorem iter_add_eq_iter_comp_iter (m n : Nat) : iter f (m + n) = iter f m ∘ iter f n := funext (iter_add f m n)

theorem iter_mul_eq_iter_iter (m n : Nat) : iter f (m * n) = iter (iter f m) n := funext (iter_mul f m n)

end Nat
