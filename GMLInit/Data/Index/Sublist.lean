import GMLInit.Data.Index.Basic
import GMLInit.Data.Index.Bind
import GMLInit.Data.Index.Map

namespace List
variable {α} (p : α → Prop) [DecidablePred p]

protected def sublist : List α → List { x // p x}
| [] => []
| x :: xs => if h: p x then ⟨x,h⟩ :: List.sublist xs else List.sublist xs

theorem sublist_pos {α} {p : α → Prop} [DecidablePred p] {x : α} {xs : List α} (h : p x) : (x :: xs).sublist p = ⟨x,h⟩ :: xs.sublist p := dif_pos h

theorem sublist_neg {α} {p : α → Prop} [DecidablePred p] {x : α} {xs : List α} (h : ¬ p x) : (x :: xs).sublist p = xs.sublist p := dif_neg h

end List

namespace Index
variable {α} (p : α → Prop) [DecidablePred p]

def sublist : {xs : List α} → (i : Index xs) → p i.val → Index (xs.sublist p)
| x :: xs, i, hi =>
  if hh : p x then
    have : (x :: xs).sublist p = ⟨x,hh⟩ :: xs.sublist p := dif_pos hh
    match i with
    | head => this ▸ head
    | tail i => this ▸ tail (sublist i hi)
  else
    have : (x :: xs).sublist p = xs.sublist p := dif_neg hh
    match i with
    | head => absurd hi hh
    | tail i => this ▸ sublist i hi

section
variable {p}

theorem sublist_pos_head {x : α} {xs : List α} (h : p x) : (head:Index (x::xs)).sublist p h = ((List.sublist_pos h).symm ▸ head) := dif_pos h

theorem sublist_pos_tail {x : α} {xs : List α} (h : p x) (i : Index xs) (hi : p i.val) : (tail i:Index (x::xs)).sublist p hi = ((List.sublist_pos h).symm ▸ tail (i.sublist p hi)) := dif_pos h

theorem sublist_neg_tail {x : α} {xs : List α} (h : ¬ p x) (i : Index xs) (hi : p i.val) : (tail i:Index (x::xs)).sublist p hi = ((List.sublist_neg h).symm ▸ i.sublist p hi) := dif_neg h

end

def unsublist : {xs : List α} → (i : Index (xs.sublist p)) → Index xs
| x :: xs, i =>
  if hh : p x then
    have : (x :: xs).sublist p = ⟨x,hh⟩ :: xs.sublist p := dif_pos hh
    match ((List.sublist_pos hh).symm ▸ i : Index (⟨x,hh⟩ :: xs.sublist p)) with
    | head => head
    | tail i => tail (unsublist i)
  else
    have : (x :: xs).sublist p = xs.sublist p := dif_neg hh
    tail (unsublist (this ▸ i))

section
variable {p}

theorem unsublist_pos_head {x : α} {xs : List α} (h : p x) : ((List.sublist_pos h) ▸ (head : Index (⟨x,h⟩ :: xs.sublist p)) : Index ((x :: xs).sublist p)).unsublist p = head := by
  unfold unsublist
  rw [dif_pos h]
  split
  next => rfl
  next i hh => elim_casts at hh; contradiction

theorem unsublist_pos_tail {x : α} {xs : List α} (h : p x) (i : Index (xs.sublist p)) : ((List.sublist_pos h) ▸ (tail i : Index (⟨x,h⟩ :: xs.sublist p)) : Index ((x :: xs).sublist p)).unsublist p = tail (i.unsublist p) := by
  unfold unsublist
  rw [dif_pos h]
  split
  next i hh => elim_casts at hh; contradiction
  next i hh => elim_casts at hh; cases hh; rfl

theorem unsublist_neg_tail {x : α} {xs : List α} (h : ¬ p x) (i : Index (xs.sublist p)) : ((List.sublist_neg h).symm ▸ i : Index ((x :: xs).sublist p)).unsublist p = tail (i.unsublist p) := by
  unfold unsublist
  rw [dif_neg h]
  apply congrArg tail
  apply congrArg (unsublist p)
  elim_casts

end

theorem sublist_eq_iff_eq_unsublist {xs : List α} (i : Index xs) (hi : p i.val) (j : Index (xs.sublist p)) :
  i.sublist p hi = j ↔ i = j.unsublist := by
  induction xs with
  | nil => contradiction
  | cons x xs ih =>
    by_cases p x with
    | isTrue hx =>
      cases i with
      | head =>
        rw [sublist_pos_head hx]
        constr
        · intro heq
          cases heq
          rw [unsublist_pos_head]
        · intro heq
          simp [unsublist, hx] at heq
          split at heq
          next h => rw [←h, eqNdrec_symm]
          next => contradiction
      | tail i =>
        rw [sublist_pos_tail hx]
        constr
        · intro heq
          cases heq
          rw [unsublist_pos_tail]
          apply congrArg
          rw [←ih]
        · intro heq
          simp [unsublist, hx] at heq
          split at heq
          next => contradiction
          next j h =>
            cases heq
            rw [eqNdrec_symm] at h
            cases h
            elim_casts
            apply congrArg
            rw [ih]
    | isFalse hx =>
      cases i with
      | head => absurd hx; exact hi
      | tail i =>
        rw [sublist_neg_tail hx]
        constr
        · intro heq
          cases heq
          rw [unsublist_neg_tail hx]
          apply congrArg
          rw [←ih]
        · intro heq
          simp [unsublist, hx] at heq
          cases heq
          rw [eqNdrec_symm]
          rw [ih]
          rfl

theorem unsublist_sublist {xs : List α} (i : Index xs) (hi : p i.val) : (i.sublist p hi).unsublist p = i := by
  induction i with
  | head =>
    rw [sublist_pos_head]
    rw [unsublist_pos_head]
  | @tail x xs i ih =>
    by_cases p x with
    | isTrue hh =>
      rw [sublist_pos_tail hh]
      rw [unsublist_pos_tail hh]
      rw [ih]
    | isFalse hh =>
      rw [sublist_neg_tail hh]
      rw [unsublist_neg_tail hh]
      rw [ih]

theorem sublist_unsublist {xs : List α} (i : Index (xs.sublist p)) (hi : p (i.unsublist p).val) : (i.unsublist p).sublist p hi = i := by
  rw [sublist_eq_iff_eq_unsublist]

theorem val_unsublist_eq_val_val {xs : List α} (i : Index (xs.sublist p)) : (i.unsublist p).val = i.val.val := by
  induction xs with
  | nil => contradiction
  | cons x xs ih =>
    by_cases p x with
    | isTrue hx =>
      unfold unsublist
      rw [dif_pos hx]
      split
      next h =>
        rw [eqNdrec_symm] at h
        cases h
        rw [val_ndrec _ (List.sublist_pos hx).symm.symm.symm]
      next h =>
        rw [eqNdrec_symm] at h
        cases h
        rw [val_ndrec _ (List.sublist_pos hx).symm.symm.symm]
        rw [val_tail, val_tail]
        apply ih
    | isFalse hx =>
      unfold unsublist
      rw [dif_neg hx]
      rw [val_tail]
      rw [ih]
      apply congrArg
      rw [val_ndrec]

def sublistEquiv (xs : List α) : Equiv { i : Index xs // p i.val } (Index (xs.sublist p)) where
  fwd | ⟨i,hi⟩ => sublist p i hi
  rev i := ⟨unsublist p i, val_unsublist_eq_val_val p i ▸ i.val.property⟩
  spec := by
    intros i j
    clean
    rw [sublist_eq_iff_eq_unsublist]
    constr
    · intro h
      apply Subtype.eq
      rw [h]
    · intro h
      rw [←h]

end Index
