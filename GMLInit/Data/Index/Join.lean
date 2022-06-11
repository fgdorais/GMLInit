import GMLInit.Data.Index.Basic
import GMLInit.Data.Index.Append

namespace Index
variable {α} {xss : List (List α)}

def join : {xss : List (List α)} → (i : Index xss) × (Index i.val) → Index xss.join
| _, ⟨head, j⟩ => append (.inl j)
| _, ⟨tail i, j⟩ => append (.inr (join ⟨i, j⟩))

def unjoin : {xss : List (List α)} → Index xss.join → (i : Index xss) × (Index i.val)
| _::_, k =>
  match unappend k with
  | .inl j => ⟨head, j⟩
  | .inr k => ⟨tail (unjoin k).fst, (unjoin k).snd⟩

theorem unjoin_join (i : (i : Index xss) × (Index i.val)) : unjoin (join i) = i := by
  induction xss with
  | nil => cases i; contradiction
  | cons xs xss ih =>
    match i with
    | ⟨head, j⟩ => unfold join unjoin; rw [unappend_append]
    | ⟨tail i, j⟩ => unfold join unjoin; rw [unappend_append]; clean; rw [ih]

theorem join_unjoin (k : Index xss.join) : join (unjoin k) = k := by
  induction xss with
  | nil => contradiction
  | cons xs xss ih =>
    match h : unappend k with
    | .inl j => rw [unappend_eq_iff_eq_append] at h; cases h; rw [unjoin, unappend_append, join]
    | .inr k => rw [unappend_eq_iff_eq_append] at h; cases h; rw [unjoin, unappend_append, join, ih]

theorem join_eq_iff_eq_unjoin (i : (i : Index xss) × (Index i.val)) (k : Index xss.join) : join i = k ↔ i = unjoin k := by
  constr
  · intro h; cases h; rw [unjoin_join]
  · intro h; cases h; rw [join_unjoin]

theorem unjoin_eq_iff_eq_join (k : Index xss.join) (i : (i : Index xss) × (Index i.val)) : unjoin k = i ↔ k = join i := by
  constr
  · intro h; cases h; rw [join_unjoin]
  · intro h; cases h; rw [unjoin_join]

def joinEquiv (xss : List (List α)) : Equiv ((i : Index xss) × Index i.val) (Index xss.join) where
  fwd := join
  rev := unjoin
  spec := by
    intros
    constr
    · intro | rfl => exact unjoin_join ..
    · intro | rfl => exact join_unjoin ..

theorem val_join (i : (i : Index xss) × Index i.val) : (join i).val = i.snd.val := by
  induction xss with
  | nil => cases i; contradiction
  | cons xs xss ih =>
    match i with
    | ⟨head, j⟩ => unfold join; rw [val_append_inl]
    | ⟨tail i, j⟩ => unfold join; rw [val_append_inr, ih]

theorem val_unjoin (k : Index xss.join) : (unjoin k).snd.val = k.val := by
  rw [←join_unjoin k, val_join, unjoin_join]

end Index
