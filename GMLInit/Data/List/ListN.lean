import GMLInit.Data.List.Basic

structure ListN (α : Type _) (n : Nat) where
  toList : List α
  length_eq : toList.length = n

namespace ListN

protected theorem eq {α n} : {xs ys : ListN α n} → xs.toList = ys.toList → xs = ys
| ⟨_,_⟩, ⟨_,_⟩, rfl => rfl

protected theorem heq {α β m n} : {xs : ListN α m} → {ys : ListN β n} → α = β → m = n → xs.toList ≅ ys.toList → xs ≅ ys
| ⟨_,_⟩, ⟨_,_⟩, rfl, rfl, HEq.rfl => HEq.rfl

def ofList (xs : List α) : ListN α xs.length := ⟨xs, rfl⟩

@[matchPattern] def nil {α} : ListN α 0 := ⟨[], rfl⟩

@[matchPattern] def cons {α n} (x : α) : ListN α n → ListN α (n+1)
| ⟨xs, hxs⟩ => ⟨x :: xs, congrArgs Nat.succ hxs⟩

def append {α m n} : ListN α m → ListN α n → ListN α (n + m)
| ⟨xs, hxs⟩, ⟨ys, hys⟩ => ⟨xs ++ ys, by rw [List.length_append, Nat.add_comm, hxs, hys]⟩
instance (α m n) : HAppend (ListN α m) (ListN α n) (ListN α (n + m)) := ⟨ListN.append⟩

theorem nil_append {α n} (xs : ListN α n) : append nil xs = xs := rfl

theorem cons_append {α m n} (x : α) (xs : ListN α m) (ys : ListN α n) : append (cons x xs) ys = cons x (append xs ys) := rfl

theorem append_nil {α n} (xs : ListN α n) : append xs nil ≅ xs := by
  cases xs
  apply ListN.heq
  · rfl
  · rw [Nat.zero_add]
  · clean unfold ListN.append
    rw [List.append_nil]
    reflexivity using (.≅.)

theorem append_assoc {α l m n} (xs : ListN α l) (ys : ListN α m) (zs : ListN α n) : append (append xs ys) zs ≅ append xs (append ys zs) := by
  _

#exit
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
