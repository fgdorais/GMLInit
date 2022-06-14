import GMLInit.Data.Index.Basic
import GMLInit.Data.Index.Append

namespace Index
variable {α β} (f : α → List β)

def bind : {xs : List α} → (i : Index xs) × (Index (f i.val)) → Index (xs.bind f)
| _::_, ⟨head, j⟩ => append_inl j
| _::_, ⟨tail i, j⟩ => append_inr (bind ⟨i, j⟩)

def unbind : {xs : List α} → (k : Index (xs.bind f)) → (i : Index xs) × (Index (f i.val))
| _::_, k =>
  match unappend k with
  | .inl j => ⟨head, j⟩
  | .inr k => ⟨tail (unbind k).fst, (unbind k).snd⟩

theorem unbind_bind {xs : List α} (i : Index xs) (j : Index (f i.val)) : unbind f (bind f ⟨i, j⟩) = ⟨i, j⟩ := by
  induction i with
  | head => rw [bind, unbind, unappend_append]
  | tail i ih =>
    rw [bind, unbind, unappend_append]
    clean
    rw [ih]

theorem bind_unbind {xs : List α} (k : Index (xs.bind f)) : bind f (unbind f k) = k := by
  induction xs with
  | nil => contradiction
  | cons x xs ih =>
    rw [unbind]
    split
    next h => rw [bind, append_inl, ←h, append_unappend]
    next h => rw [bind, append_inr, ih, ←h, append_unappend]

theorem bind_eq_iff_eq_unbind {xs} (i : (i : Index xs) × Index (f i.val)) (j : Index (xs.bind f)) : bind f i = j ↔ i = unbind f j := by
  constr
  · intro h; rw [←h, unbind_bind]
  · intro h; rw [h, bind_unbind]

theorem unbind_eq_iff_eq_bind {xs} (i : Index (xs.bind f)) (j : (i : Index xs) × Index (f i.val)) : unbind f i = j ↔ i = bind f j := by
  constr
  · intro h; rw [←h, bind_unbind]
  · intro h; rw [h, unbind_bind]

def bindEquiv (xs : List α) : Equiv ((i : Index xs) × Index (f i.val)) (Index (xs.bind f)) where
  fwd := bind f
  rev := unbind f
  spec := by
    intros
    constr
    · intro | rfl => exact unbind_bind ..
    · intro | rfl => exact bind_unbind ..

theorem val_bind {xs : List α} (i : (i : Index xs) × Index (f i.val)) : (bind f i).val = i.snd.val := by
  induction xs with
  | nil => cases i; contradiction
  | cons x xs ih =>
    match i with
    | ⟨head, j⟩ => rw [bind, val_append_inl]
    | ⟨tail i, j⟩ => rw [bind, val_append_inr, ih]

theorem val_unbind {xs : List α} (i : Index (xs.bind f)) : (unbind f i).snd.val = i.val := by
  rw [←bind_unbind f i, val_bind, unbind_bind]

end Index
