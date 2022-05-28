import GMLInit.Data.Index.Basic
import GMLInit.Data.Index.Append
import GMLInit.Data.Index.Map

open Sum (inl inr)

protected abbrev List.sum {α β} (xs : List α) (ys : List β) : List (Sum α β) := xs.map inl ++ ys.map inr

namespace Index
variable {α β} {xs : List α} {ys : List β}

def sum : Sum (Index xs) (Index ys) → Index (List.sum xs ys)
| inl i => append (inl (i.map inl))
| inr j => append (inr (j.map inr))

def unsum (k : Index (List.sum xs ys)) : Sum (Index xs) (Index ys) :=
  match unappend k with
  | inl i => inl (i.unmap inl)
  | inr j => inr (j.unmap inr)

theorem unsum_sum : (i : Sum (Index xs) (Index ys)) → unsum (sum i) = i
| inl _ => by unfold unsum sum; rw [unappend_append]; clean; rw [unmap_map]
| inr _ => by unfold unsum sum; rw [unappend_append]; clean; rw [unmap_map]

theorem sum_unsum (k : Index (List.sum xs ys)) : sum (unsum k) = k := by
  match h : unappend k with
  | inl i => rw [unappend_eq_iff_eq_append] at h; cases h; rw [unsum, unappend_append, sum]; clean; rw [map_unmap]
  | inr j => rw [unappend_eq_iff_eq_append] at h; cases h; rw [unsum, unappend_append, sum]; clean; rw [map_unmap]

theorem sum_eq_iff_eq_unsum (i : Sum (Index xs) (Index ys)) (k : Index (List.sum xs ys)) : sum i = k ↔ i = unsum k := by
  constr
  · intro h; cases h; rw [unsum_sum]
  · intro h; cases h; rw [sum_unsum]

theorem unsum_eq_iff_eq_sum (k : Index (List.sum xs ys)) (i : Sum (Index xs) (Index ys)) : unsum k = i ↔ k = sum i := by
  constr
  · intro h; cases h; rw [sum_unsum]
  · intro h; cases h; rw [unsum_sum]

def sumEquiv (xs : List α) (ys : List β) : Equiv (Sum (Index xs) (Index ys)) (Index (List.sum xs ys)) where
  fwd := sum
  rev := unsum
  spec := by
    intros
    constr
    · intro | rfl => exact unsum_sum ..
    · intro | rfl => exact sum_unsum ..

theorem val_sum (i : Sum (Index xs) (Index ys)) : (match i with | inl i => inl i.val | inr j => inr j.val) = (sum i).val := by
  match i with
  | inl i => unfold sum; rw [val_append]; clean; rw [val_map]
  | inr j => unfold sum; rw [val_append]; clean; rw [val_map]

theorem val_unsum (k : Index (List.sum xs ys)) : k.val = (match k.unsum with | inl i => inl i.val | inr j => inr j.val) := by
  rw [←sum_unsum k, val_sum, unsum_sum]

end Index
