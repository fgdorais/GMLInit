import GMLInit.Data.List

namespace Data

structure List1 (α : Type _) where
  toList : List α
  nonnil : toList ≠ []

namespace List1
variable {α}

@[matchPattern]
def cons (x : α) (xs : List α) : List1 α := ⟨x::xs, List.noConfusion⟩

def head : List1 α → α | cons x _ => x

def tail : List1 α → List α | cons _ xs => xs

@[scoped simp]
theorem head_cons (x : α) (xs : List α) : (cons x xs).head = x := rfl

@[scoped simp]
theorem tail_cons (x : α) (xs : List α) : (cons x xs).tail = xs := rfl

@[scoped simp]
theorem cons_head_tail (xs : List1 α) : cons xs.head xs.tail = xs :=
  match xs with | cons _ _ => rfl

@[scoped simp]
theorem cons_toList (x : α) (xs : List α) : (cons x xs).toList = x :: xs := rfl

def ofList? : List α → Option (List1 α)
| [] => none
| x::xs => some (cons x xs)

abbrev append : List1 α → List α → List1 α
| cons x xs, ys => cons x (xs ++ ys)

@[scoped simp] theorem append_toList (xs : List1 α) (ys : List α) : (append xs ys).toList = xs.toList ++ ys :=
  match xs with | cons x xs => rfl

@[scoped simp] theorem append_nil (xs : List1 α) : append xs [] = xs :=
  match xs with
  | cons x xs => congrArg (cons x) (List.append_nil xs)

theorem append_append (xs : List1 α) (ys zs : List α) : append (append xs ys) zs = append xs (ys ++ zs) :=
  match xs with
  | cons x xs => congrArg (cons x) (List.append_assoc xs ys zs)

abbrev pure (x : α) := cons x []

def map : (α → β) → List1 α → List1 β
| f, cons x xs => cons (f x) (xs.map f)

def bind : List1 α → (α → List1 β) → List1 β
| cons x xs, f => append (f x) (xs.bind (λ x => (f x).toList))

end List1

end Data
