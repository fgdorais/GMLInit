import GMLInit.Data.Index.Basic
import GMLInit.Data.Index.Map

def List.indexIota {α} : (xs : List α) → List (Index xs)
| [] => []
| _::xs => Index.head :: (indexIota xs).map Index.tail

namespace Index
variable {α} {xs : List α}

def iota : {xs : List α} → Index xs → Index xs.indexIota
| _::_, Index.head => Index.head
| _::_, Index.tail i => Index.tail ((iota i).map Index.tail)

theorem val_iota (i : Index xs) : val (iota i) = i := by
  induction i with
  | head => rfl
  | tail i ih => rw [iota, val_tail, val_map, ih]

theorem iota_val (i : Index xs.indexIota) : iota (val i) = i := by
  induction xs with
  | nil => contradiction
  | cons x xs ih =>
    match i with
    | head => rfl
    | tail i => rw [←map_unmap Index.tail i, val_tail, val_unmap Index.tail, iota, ih, map_unmap]

def iotaEquiv (xs : List α) : Equiv (Index xs) (Index xs.indexIota) where
  fwd := iota
  rev := val
  spec := by
    intros
    constr
    · intro | rfl => exact val_iota ..
    · intro | rfl => exact iota_val ..

end Index
