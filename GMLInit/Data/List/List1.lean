import GMLInit.Data.List.Basic

structure List1 (α : Type _) where
  toList : List α
  nonnil : toList ≠ []

namespace List1
variable {α}

@[matchPattern]
def cons (x : α) (xs : List α) : List1 α := ⟨x::xs, List.noConfusion⟩

def head : List1 α → α
| cons x _ => x

def tail : List1 α → List α
| cons _ xs => xs

def last : List1 α → α
| cons x xs => if h : xs = [] then x else last ⟨xs,h⟩

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
instance (α) : HAppend (List1 α) (List α) (List1 α) := ⟨List1.append⟩
instance (α) : Append (List1 α) := ⟨λ xs ys => List1.append xs ys.toList⟩

@[scoped simp] theorem append_toList_left (xs : List1 α) (ys : List α) : (xs ++ ys).toList = xs.toList ++ ys :=
  match xs with | cons _ _ => rfl

@[scoped simp] theorem append_toList (xs ys : List1 α) : (xs ++ ys).toList = xs.toList ++ ys.toList :=
  append_toList_left xs (ys.toList)

@[scoped simp] theorem append_nil (xs : List1 α) : append xs [] = xs :=
  match xs with
  | cons x xs => congrArg (cons x) (List.append_nil xs)

theorem append_compat_right (xs : List1 α) (ys zs : List α) : (xs ++ ys) ++ zs = xs ++ (ys ++ zs) :=
  match xs with
  | cons x xs => congrArg (cons x) (List.append_assoc xs ys zs)

theorem append_compat_left (xs ys : List1 α) (zs : List α) : (xs ++ ys) ++ zs = xs ++ (ys ++ zs) :=
  match xs with
  | cons x xs => congrArg (cons x) $ by rw [append_toList_left, List.append_assoc]

theorem append_assoc (xs ys zs : List1 α) : xs ++ (ys ++ zs) = (xs ++ ys) ++ zs :=
  match xs with
  | cons x xs => congrArg (cons x) $ by rw [append_toList, List.append_assoc]

abbrev pure (x : α) := cons x []

def map : (α → β) → List1 α → List1 β
| f, cons x xs => cons (f x) (xs.map f)

def bind : List1 α → (α → List1 β) → List1 β
| cons x xs, f => append (f x) (xs.bind (λ x => (f x).toList))

abbrev join (xss : List1 (List1 α)) : List1 α := xss.bind id

end List1
