import GMLInit.Data.Index.Basic
import GMLInit.Data.Index.Bind
import GMLInit.Data.Index.Map
import GMLInit.Data.Index.Pi

protected abbrev List.arr {α β} (xs : List α) (ys : List β) : List (Index xs → β) :=
  xs.pi (β := fun _ => β) fun _ => ys

namespace Index
variable {α β} {xs : List α} {ys : List β}

def arr : (Index xs → Index ys) → Index (List.arr xs ys) := pi (β := fun _ => β) (f := fun _ => ys)

def unarr : Index (List.arr xs ys) → Index xs → Index ys := unpi (β := fun _ => β) (f := fun _ => ys)

theorem unarr_arr (h : Index xs → Index ys) : unarr (arr h) = h := by
  rw [arr, unarr, unpi_pi]

theorem arr_unarr (k : Index (List.arr xs ys)) : arr (unarr k) = k := by
  rw [arr, unarr, pi_unpi]

theorem arr_eq_iff_eq_unarr (h : Index xs → Index ys) (k : Index (List.arr xs ys)) : arr h = k ↔ h = unarr k := by
  constr
  · intro h; rw [←h, unarr_arr]
  · intro h; rw [h, arr_unarr]

theorem unarr_eq_iff_eq_arr (k : Index (List.arr xs ys)) (h : Index xs → Index ys) : unarr k = h ↔ k = arr h := by
  constr
  · intro h; rw [←h, arr_unarr]
  · intro h; rw [h, unarr_arr]

def arrEquiv (xs : List α) (ys : List β) : Equiv (Index xs → Index ys) (Index (List.arr xs ys)) where
  fwd := arr
  rev := unarr
  spec := by
    intros
    constr
    · intro | rfl => exact unarr_arr ..
    · intro | rfl => exact arr_unarr ..

end Index
