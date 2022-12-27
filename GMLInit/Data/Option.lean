import GMLInit.Data.Basic

namespace Option

@[simp] theorem failure_eq_none : (failure : Option α) = none := rfl

@[simp] theorem orElse_none_left (x : Option α) : (none <|> x) = x := by
  rfl

@[simp] theorem orElse_none_right (x : Option α) : (x <|> none) = x := by
  cases x <;> rfl

theorem orElse_assoc (x y z : Option α) : ((x <|> y) <|> z) = (x <|> (y <|> z)) := by
  cases x <;> cases y <;> cases z <;> rfl

def first : List (Option α) → Option α
| [] => none
| x@(some _) :: _ => x
| none :: xs => first xs

@[simp] theorem first_nil : first ([] : List (Option α)) = none := rfl

@[simp] theorem first_cons (x : Option α) (xs : List (Option α)) : first (x :: xs) = (x <|> first xs) := by
  cases x <;> rfl

@[simp] theorem first_pure (x : Option α) : first [x] = x := by
  cases x <;> rfl

theorem first_append (xs ys : List (Option α)) : first (xs ++ ys) = (first xs <|> first ys) := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [orElse_assoc, ih]

end Option
