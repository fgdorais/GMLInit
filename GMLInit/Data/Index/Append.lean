import GMLInit.Data.Index.Basic

open Sum (inl inr)

namespace Index
variable {α} {xs ys : List α}

def append : {xs ys : List α} → Sum (Index xs) (Index ys) → Index (xs ++ ys)
| [], _, inr i => i
| _::_, _, inr i => tail (append (inr i))
| _::_, _, inl head => head
| _::_, _, inl (tail i) => tail (append (inl i))

abbrev append_inl (i : Index xs) : Index (xs ++ ys) := append (inl i)

abbrev append_inr (j : Index ys) : Index (xs ++ ys) := append (inr j)

def unappend : {xs ys : List α} → Index (xs ++ ys) → Sum (Index xs) (Index ys)
| [], _, i => inr i
| x::xs, ys, i =>
  match (i : Index (x :: (xs ++ ys))) with
  | head => inl head
  | tail i =>
    match unappend i with
    | inl i => inl (tail i)
    | inr i => inr i

theorem unappend_append (i : Sum (Index xs) (Index ys)) : unappend (append i) = i := by
  induction xs generalizing ys with
  | nil =>
    match i with
    | .inl i => contradiction
    | .inr j => rfl
  | cons x xs ih =>
    match i with
    | .inl .head => rfl
    | .inl (.tail i) => rw [append, unappend]; clean; rw [ih]
    | .inr j => rw [append, unappend]; clean; rw [ih]

theorem append_unappend (k : Index (xs ++ ys)) : append (unappend k) = k := by
  induction xs generalizing ys with
  | nil => rfl
  | cons x xs ih =>
    match k with
    | .head => rfl
    | .tail k =>
      rw [unappend]
      clean
      split
      next h => rw [append, ←h, ih]
      next h => rw [append, ←h, ih]

theorem append_eq_iff_eq_unappend (i : Sum (Index xs) (Index ys)) (j : Index (xs ++ ys)) : append i = j ↔ i = unappend j := by
  constr
  · intro h; rw [←h, unappend_append]
  · intro h; rw [h, append_unappend]

theorem unappend_eq_iff_eq_append (i : Index (xs ++ ys)) (j : Sum (Index xs) (Index ys)) : unappend i = j ↔ i = append j := by
  constr
  · intro h; rw [←h, append_unappend]
  · intro h; rw [h, unappend_append]

def appendEquiv (xs ys : List α) : Equiv (Sum (Index xs) (Index ys)) (Index (xs ++ ys)) where
  fwd := append
  rev := unappend
  spec := by
    intros
    constr
    · intro | rfl => exact unappend_append ..
    · intro | rfl => exact append_unappend ..

theorem val_append_inl (i : Index xs) : (append_inl (ys:=ys) i).val = i.val := by
  induction i with
  | head => rfl
  | tail _ ih => exact ih

theorem val_append_inr (j : Index ys) : (append_inr (xs:=xs) j).val = j.val := by
  induction xs with
  | nil => rfl
  | cons _ _ ih => exact ih

theorem val_append (i : Sum (Index xs) (Index ys)) : (append i).val = match i with | inl i => i.val | inr j => j.val := by
  match i with
  | inl _ => exact val_append_inl ..
  | inr _ => exact val_append_inr ..

theorem val_unappend (k : Index (xs ++ ys)) : (match unappend k with | inl i => i.val | inr j => j.val) = k.val := by
  rw [←append_unappend k, val_append, unappend_append]

end Index
