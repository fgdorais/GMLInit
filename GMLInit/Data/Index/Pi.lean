import GMLInit.Data.Index.Basic
import GMLInit.Data.Index.Bind
import GMLInit.Data.Index.Map

protected def List.pi {α} {β : α → Type _} : (xs : List α) → (f : (i : Index xs) → List (β i.val)) → List ((i : Index xs) → β i.val)
| [], _ => [(nomatch .)]
| _::xs, f => (List.pi xs fun i => f i.tail).bind (λ ys => (f .head).map (λ y i => match i with | .head => y | .tail i => ys i))

namespace Index
variable {α} {β : α → Type _} {xs : List α} {f : (i : Index xs) → List (β i.val)}

def pi : {xs : List α} → {f : (i : Index xs) → List (β i.val)} → ((i : Index xs) → Index (f i)) → Index (xs.pi f)
| [], _, _ => head
| _::_, _, y => bind _ ⟨pi fun i => y i.tail, map _ (y head)⟩

def unpi : {xs : List α} → {f : (i : Index xs) → List (β i.val)} → (Index (xs.pi f)) → (i : Index xs) → Index (f i)
| _::_, _, k, head =>
  match unbind _ k with | ⟨_, k⟩ => unmap _ k
| _::_, _, k, tail i =>
  match unbind _ k with | ⟨k, _⟩ => unpi k i

theorem unpi_pi (h : (i : Index xs) → Index (f i)) : unpi (pi h) = h := by
  funext i
  induction i with
  | head => unfold pi unpi; rw [unbind_bind, unmap_map]
  | tail i ih => unfold pi unpi; rw [unbind_bind, ih]

theorem pi_unpi (k : Index (xs.pi f)) : pi (unpi k) = k := by
  induction xs with
  | nil => cases k; unfold pi unpi; contradiction
  | cons x xs ih =>
    match h : unbind _ k with
    | ⟨k₁,k₂⟩ =>
      rw [unbind_eq_iff_eq_bind] at h
      cases h
      unfold pi unpi
      rw [unbind_bind, ih, map_unmap]

theorem pi_eq_iff_eq_unpi (h : (i : Index xs) → Index (f i)) (k : Index (xs.pi f)) : pi h = k ↔ h = unpi k := by
  constr
  · intro h; cases h; rw [unpi_pi]
  · intro h; cases h; rw [pi_unpi]

theorem unpi_eq_iff_eq_pi (k : Index (xs.pi f)) (h : (i : Index xs) → Index (f i)) : unpi k = h ↔ k = pi h := by
  constr
  · intro h; cases h; rw [pi_unpi]
  · intro h; cases h; rw [unpi_pi]

def piEquiv (xs : List α) (f : (i : Index xs) → List (β i.val)) : Equiv ((i : Index xs) → Index (f i)) (Index (xs.pi f)) where
  fwd := pi
  rev := unpi
  spec := by
    intros
    constr
    · intro | rfl => exact unpi_pi ..
    · intro | rfl => exact pi_unpi ..

end Index
