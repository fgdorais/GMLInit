import GMLInit.Data.Basic

namespace Option

def first : List (Option α) → Option α
| [] => none
| x@(some _) :: _ => x
| none :: xs => first xs

@[simp] theorem first_nil : first ([] : List (Option α)) = none := rfl

@[simp] theorem first_cons (x : Option α) (xs : List (Option α)) : first (x :: xs) = (x <|> first xs) := by
  cases x <;> rfl

end Option
