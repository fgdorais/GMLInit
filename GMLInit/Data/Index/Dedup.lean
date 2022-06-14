import GMLInit.Data.Index.Basic
import GMLInit.Data.Index.Bind
import GMLInit.Data.Index.Map
import GMLInit.Logic.Decidable
import GMLInit.Logic.ListConnectives

namespace Any

protected def get : {ps : List Prop} → [DecidableList ps] → Any ps → Index ps
| _, .cons (isTrue _) _, _ => .head
| _::ps, .cons (isFalse fh) inst, h =>
  have : Any ps :=
    match h with
    | .head hh => absurd hh fh
    | .tail ht => ht
  .tail (@Any.get ps inst this)

theorem get_prop : {ps : List Prop} → [DecidableList ps] → (h : Any ps) → h.get.val
| _, .cons (isTrue hh) _, _ => hh
| _, .cons (isFalse fh) _, h =>
  get_prop $ match h with
    | .head hh => absurd hh fh
    | .tail ht => ht

end Any

namespace List

def dedup {α} (s : Setoid α) [DecidableRel s.r] : List α → List α
| [] => []
| x :: xs =>
  if Any (xs.map (s.r x))
  then dedup s xs
  else x :: dedup s xs

end List

namespace Index
variable {α} (s : Setoid α) [DecidableRel s.r] {xs : List α}

def dedup : {xs : List α} → Index xs → Index (xs.dedup s)
| x :: xs, head =>
  if h : Any (xs.map (s.r x))
  then
    have : (x :: xs).dedup s = xs.dedup s := if_pos h
    this ▸ dedup (h.get.unmap _)
  else
    have : (x :: xs).dedup s = x :: xs.dedup s := if_neg h
    this ▸ head
| x :: xs, tail i =>
  if h : Any (xs.map (s.r x))
  then
    have : (x :: xs).dedup s = xs.dedup s := if_pos h
    this ▸ dedup i
  else
    have : (x :: xs).dedup s = x :: xs.dedup s := if_neg h
    this ▸ tail (dedup i)

theorem val_dedup (i : Index xs) : s.r i.val (i.dedup s).val := by
  induction xs with
  | nil => contradiction
  | cons x xs ih =>
    match i with
    | head =>
      unfold dedup
      split
      next h =>
        rw [val_ndrec]
        transitivity (h.get.unmap (s.r x)).val using s.r
        · rw [val_head, ←val_unmap (s.r x)]
          exact Any.get_prop ..
        · exact ih ..
      next => rw [val_ndrec]; reflexivity using s.r
    | tail i =>
      unfold dedup
      split
      next => rw [val_ndrec]; exact ih ..
      next => rw [val_ndrec]; exact ih ..

def undedup : {xs : List α} → Index (xs.dedup s) → Index xs
| x :: xs, i =>
  if h : Any (xs.map (s.r x))
  then
    have : (x :: xs).dedup s = xs.dedup s := if_pos h
    tail (undedup (this ▸ i))
  else
    have : (x :: xs).dedup s = x :: xs.dedup s := if_neg h
    match this ▸ i with
    | head => head
    | tail i => tail (undedup i)

theorem val_undedup (i : Index (xs.dedup s)) : (i.undedup s).val = i.val := by
  induction xs with
  | nil => contradiction
  | cons x xs ih =>
    unfold undedup
    split
    next ha =>
      have : (x :: xs).dedup s = xs.dedup s := if_pos ha
      rw [val_tail]
      transitivity (this ▸ i).val
      · exact ih ..
      · exact val_ndrec ..
    next ha =>
      split
      next h =>
        rw [eqNdrec_symm] at h
        rw [h, val_ndrec]
      next h =>
        rw [eqNdrec_symm] at h
        rw [h, val_ndrec, val_tail, val_tail, ih]

theorem dedup_undedup {xs : List α} (i : Index (xs.dedup s)) : (i.undedup s).dedup s = i := by
  induction xs with
  | nil => contradiction
  | cons x xs ih =>
    unfold undedup
    split
    next ha => rw [dedup, dif_pos ha, ih, eqNdrec_symm]; rfl
    next ha =>
      split
      next h => rw [dedup, dif_neg ha, eqNdrec_symm, ←h]; rfl
      next h => rw [dedup, dif_neg ha, eqNdrec_symm, ih, ←h]; rfl

theorem undedup_dedup {xs : List α} (i : Index xs) : s.r ((i.dedup s).undedup s).val i.val := by
  symmetry
  rw [val_undedup]
  exact val_dedup ..

theorem dedup_eq_of_rel {xs : List α} {i : Index xs} {j : Index (xs.dedup s)} (h : s.r i.val j.val) : i.dedup s = j := by
  induction xs with
  | nil => contradiction
  | cons x xs ih =>
    match i with
    | head =>
      rw [val_head] at h
      rw [dedup]
      split
      next ha =>
        rw [eqNdrec_symm]
        apply ih
        rw [val_ndrec]
        transitivity x
        · symmetry
          rw [←val_unmap (s.r x)]
          exact Any.get_prop ..
        · exact h
      next ha =>
        have : (x :: xs).dedup s = x :: xs.dedup s := if_neg ha
        rw [eqNdrec_symm]
        match hj : this ▸ j with
        | head =>
          rw [←hj]
        | tail j =>
          rw [eqNdrec_symm] at hj
          rw [hj, val_ndrec, val_tail] at h
          absurd ha
          apply Any.introIdx ((j.undedup s).map (s.r x))
          rw [val_map, val_undedup]
          exact h
    | tail i =>
      rw [val_tail] at h
      rw [dedup]
      split
      next ha =>
        rw [eqNdrec_symm]
        apply ih
        rw [val_ndrec]
        exact h
      next ha =>
        have : (x :: xs).dedup s = x :: xs.dedup s := if_neg ha
        rw [eqNdrec_symm]
        match hj : this ▸ j with
        | head =>
          rw [eqNdrec_symm] at hj
          rw [hj, val_ndrec, val_head] at h
          absurd ha
          apply Any.introIdx (i.map (s.r x))
          rw [val_map]
          symmetry
          exact h
        | tail j =>
          rw [eqNdrec_symm] at hj
          rw [hj, val_ndrec, val_tail] at h
          rw [hj, ih h]
          elim_casts

theorem dedup_eq_iff_rel {xs : List α} (i : Index xs) (j : Index (xs.dedup s)) : i.dedup s = j ↔ s.r i.val j.val := by
  constr
  · intro | rfl => exact val_dedup ..
  · exact dedup_eq_of_rel s

theorem dedup_eq_dedup_of_rel {xs : List α} {i j : Index xs} (h : s.r i.val j.val) : i.dedup s = j.dedup s := by
  apply dedup_eq_of_rel
  transitivity j.val
  · exact h
  · exact val_dedup ..

end Index
