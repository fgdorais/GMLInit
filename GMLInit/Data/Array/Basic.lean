import GMLInit.Data.Fin
import GMLInit.Data.List.Basic

namespace Array

/- set -/

theorem get_set_of_eq (as : Array α) {i : Fin as.size} {j : Nat} {x : α} {hj : j < (as.set i x).size} : i.val = j → (as.set i x)[j]'hj = x := by
  intro h
  have hj' : j < as.size := as.size_set i x ▸ hj
  rw [as.get_set i j hj']
  rw [if_pos h]

theorem get_set_of_ne (as : Array α) {i : Fin as.size} {j : Nat} {x : α} {hj : j < (as.set i x).size} : i.val ≠ j → (as.set i x)[j]'hj = as[j]'(as.size_set i x ▸ hj) := by
  intro h;
  have hj' : j < as.size := as.size_set i x ▸ hj
  rw [as.get_set i j hj']
  rw [if_neg h]

/- pop -/

theorem get_pop.aux (as : Array α) {i : Nat} : i < as.pop.size → i < as.size :=
  fun h => Nat.lt_of_lt_of_le h (as.size_pop ▸ Nat.pred_le as.size)

theorem get_pop (as : Array α) (i : Nat) (hi : i < as.pop.size) :
  as.pop[i] = as[i]'(get_pop.aux as hi) := by
  rw [←as.get_eq_getElem ⟨i, get_pop.aux as hi⟩]
  rw [←as.pop.get_eq_getElem ⟨i, hi⟩]
  rw [get, get]
  unfold pop
  rw [List.get_dropLast]

/- swap -/

theorem get_swap.aux (as : Array α) (i j : Fin as.size) {k : Nat} : k < (as.swap i j).size → k < as.size :=
  fun h => as.size_swap i j ▸ h

theorem get_swap_fst (as : Array α) (i j : Fin as.size) :
  (as.swap i j)[i.val]'(by simp [i.isLt]) = as[j.val] := by
    simp only [swap]
    rw [get_set]
    split
    next heq =>
      have : j.val = i.val := by
        rw [←heq]
        apply Fin.val_eq_val_of_heq
        rw [size_set]
        elim_casts
        reflexivity
      simp [get_eq_getElem, this]
    next =>
      rw [get_set_eq, get_eq_getElem]

theorem get_swap_snd (as : Array α) (i j : Fin as.size) :
  (as.swap i j)[j.val]'(by simp [j.isLt]) = as[i.val] := by
    simp only [swap]
    rw [get_set_of_eq]
    rw [get_eq_getElem]
    apply Fin.val_eq_val_of_heq
    rw [size_set]
    elim_casts
    reflexivity

theorem get_swap_other (as : Array α) {i j : Fin as.size} (k : Nat) (hk : k < (as.swap i j).size) :
  i.val ≠ k → j.val ≠ k → (as.swap i j)[k]'(hk) = as[k]'(as.size_swap i j ▸ hk) := by
  intro hik hjk
  have hjk : ((size_set as i (get as j)).symm ▸ j).val ≠ k := by
    intro h
    cases h
    apply hjk
    apply Fin.val_eq_val_of_heq
    rw [size_set]
    elim_casts
    reflexivity
  simp only [swap]
  rw [get_set_of_ne]
  rw [get_set_of_ne as hik]
  exact hjk

theorem get_swap (as : Array α) (i j : Fin as.size) (k : Nat) (hk : k < (as.swap i j).size) :
  (as.swap i j)[k]'(hk) = if j.val = k then as[i] else if i.val = k then as[j] else as[k]'(get_swap.aux as i j hk) := by
  split
  next hkj => cases hkj; rw [get_swap_snd]; rfl
  next hkj =>
    split
    next hki => cases hki; rw [get_swap_fst]; rfl
    next hki => rw [get_swap_other as k hk hki hkj]

/- del -/

def del (as : Array α) (k : Fin as.size) : Array α :=
  have : as.size ≠ 0 := Nat.not_eq_zero_of_lt k.isLt
  let last : Fin as.size := ⟨as.size-1, Nat.pred_lt this⟩
  (as.swap k last).pop

theorem size_del (as : Array α) (k : Fin as.size) : (as.del k).size = as.size-1 := by simp [del]

theorem get_del.aux0 (as : Array α) (k : Fin as.size) : as.size ≠ 0 :=
  Nat.not_eq_zero_of_lt k.isLt

theorem get_del.aux1 (as : Array α) (k : Fin as.size) : as.size-1 < as.size :=
  Nat.pred_lt (aux0 as k)

theorem get_del.aux2 (as : Array α) (k : Fin as.size) {i : Nat} : i < (as.del k).size → i < as.size :=
  fun h => Nat.lt_of_lt_of_le (as.size_del k ▸ h : i < as.size-1) (Nat.pred_le as.size)

theorem get_del (as : Array α) (k : Fin as.size) (i : Nat) (hi : i < (as.del k).size) :
  (as.del k)[i] = if k.val = i then as[as.size-1]'(get_del.aux1 as k) else as[i]'(get_del.aux2 as k hi) := by
  have hi' : as.size - 1 ≠ i := Ne.symm <| Nat.ne_of_lt <| size_del as k ▸ hi
  simp only [del]
  rw [get_pop]
  rw [get_swap]
  rw [if_neg hi']
  rfl

end Array
