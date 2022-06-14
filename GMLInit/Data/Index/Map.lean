import GMLInit.Data.Index.Basic

namespace Index
variable {α β} (f : α → β)

def map : {xs : List α} → Index xs → Index (xs.map f)
| _, Index.head => Index.head
| _, Index.tail i => Index.tail (map i)

def unmap : {xs : List α} → Index (xs.map f) → Index xs
| _::_, Index.head => Index.head
| _::_, Index.tail i => Index.tail (unmap i)

theorem unmap_map {xs : List α} (i : Index xs) : (i.map f).unmap f = i := by
  induction i with
  | head => rfl
  | tail i ih => exact congrArg tail ih

theorem map_unmap {xs : List α} (i : Index (xs.map f)) : (i.unmap f).map f = i := by
  induction xs with
  | nil => contradiction
  | cons x xs ih =>
    match i with
    | head => rfl
    | tail i => exact congrArg tail (ih i)

theorem map_eq_iff_eq_unmap {xs : List α} (i : Index xs) (j : Index (xs.map f)) : i.map f = j ↔ i = j.unmap f := by
  constr
  · intro h; rw [←h, unmap_map]
  · intro h; rw [h, map_unmap]

theorem unmap_eq_iff_eq_map {xs : List α} (i : Index (xs.map f)) (j : Index xs) : i.unmap f = j ↔ i = j.map f := by
  constr
  · intro h; rw [←h, map_unmap]
  · intro h; rw [h, unmap_map]

def mapEquiv (xs : List α) : Equiv (Index xs) (Index (xs.map f)) where
  fwd := map f
  rev := unmap f
  spec := by
    intros
    constr
    · intro | rfl => exact unmap_map ..
    · intro | rfl => exact map_unmap ..

theorem val_map {xs : List α} (i : Index xs) : (i.map f).val = f i.val := by
  induction i with
  | head => rfl
  | tail _ ih => exact ih

theorem val_unmap {xs : List α} (i : Index (xs.map f)) : i.val = f (i.unmap f).val := by
  rw [←map_unmap f i, val_map, unmap_map]

end Index
