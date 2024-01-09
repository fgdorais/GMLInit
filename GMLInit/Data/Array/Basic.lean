import GMLInit.Data.BEq
import GMLInit.Data.Fin
import GMLInit.Data.List.Basic

namespace Array

@[deprecated Array.ext']
protected alias eq := Array.ext'

@[simp] theorem data_nil {α} : #[].data = ([] : List α) := rfl

/- get -/

theorem get_fin_eq_data_get_fin {α} (as : Array α) (i : Fin as.size) : as.get i = as.data.get i := rfl

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
  rw [Fin.castLE_mk]

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

section foldlM
variable {m} [Monad m] (f : β → α → m β) (b : β)

theorem foldlM_stop (as : Array α) (stop : Nat) (hstop : stop ≤ as.size) : as.foldlM f b stop stop = pure b := by
  simp only [Array.foldlM]
  rw [dif_pos hstop]
  rw [Array.foldlM.loop]
  rw [dif_neg (by irreflexivity)]

theorem foldlM_step (as : Array α) (start stop : Nat) (hstart : start < stop) (hstop : stop ≤ as.size) :
  have : start < as.size := Nat.lt_of_lt_of_le hstart hstop
  as.foldlM f b start stop = f b as[start] >>= fun b => as.foldlM f b (start+1) stop := by
  simp only [Array.foldlM]
  rw [dif_pos hstop]
  rw [Array.foldlM.loop]
  rw [dif_pos hstart]
  split
  next heq =>
    absurd heq
    apply Nat.sub_ne_zero_of_lt hstart
  next heq =>
    simp
    congr
    funext b
    rw [dif_pos hstop]
    rw [Nat.sub_succ, heq, Nat.pred_succ]

end foldlM

section foldl
variable (f : β → α → β) (b : β)

theorem foldl_stop (as : Array α) (stop : Nat) (hstop : stop ≤ as.size) : as.foldl f b stop stop = b := by
  apply foldlM_stop; assumption

theorem foldl_step (as : Array α) (start stop : Nat) (hstart : start < stop) (hstop : stop ≤ as.size) :
  have : start < as.size := Nat.lt_of_lt_of_le hstart hstop
  as.foldl f b start stop = as.foldl f (f b as[start]) (start+1) stop := by
  apply foldlM_step; assumption; assumption

variable (h : α → α → α) [Lean.IsAssociative h]

theorem foldl_assoc (as : Array α) (b c : α) (start stop : Nat) (hstart : start ≤ stop) (hstop : stop ≤ as.size) :
  as.foldl h (h b c) start stop = h b (as.foldl h c start stop) := by
  by_cases start = stop with
  | isTrue heq =>
    cases heq
    rw [foldl_stop] <;> try (exact hstop)
    rw [foldl_stop]; exact hstop
  | isFalse hne =>
    have hstart' : start < stop := Nat.lt_of_le_of_ne hstart hne
    have : start < as.size := Nat.lt_of_lt_of_le hstart' hstop
    rw [foldl_step h (h b c)] <;> try (first | exact hstop | exact hstart')
    rw [foldl_step h c] <;> try (first | exact hstop | exact hstart')
    rw [Lean.IsAssociative.assoc (op:=h)]
    rw [foldl_assoc as b (h c as[start]) (start+1) stop hstart' hstop]
termination_by foldl_assoc => stop - start

end foldl

section foldrM
variable {m} [Monad m] (f : α → β → m β) (b : β)

theorem foldrM_stop (as : Array α) (stop : Nat) (hstop : stop ≤ as.size) : as.foldrM f b stop stop = pure b := by
  simp only [Array.foldrM]
  rw [dif_pos hstop]
  rw [if_neg (by irreflexivity)]

theorem foldrM_step (as : Array α) (start stop : Nat) (hstop : stop ≤ start) (hstart : start < as.size) :
  as.foldrM f b (start+1) stop = f as[start] b >>= fun b => as.foldrM f b start stop := by
  simp only [Array.foldrM]
  rw [dif_pos (Nat.succ_le_of_lt hstart)]
  rw [if_pos (Nat.lt_succ_of_le hstop)]
  simp only [foldrM.fold]
  split
  next heq =>
    absurd (eq_of_beq heq)
    apply Nat.ne_of_gt
    apply Nat.lt_succ_of_le
    exact hstop
  next hne =>
    congr
    funext b
    rw [dif_pos (Nat.le_of_lt hstart)]
    split
    next => rfl
    next hge =>
      have : stop = start := by
        antisymmetry using LE.le
        · exact hstop
        · exact Nat.le_of_not_gt hge
      simp [this]
      unfold foldrM.fold
      rw [BEq.rfl, if_pos rfl]

end foldrM

section foldr
variable (f : α → β → β) (b : β)

theorem foldr_stop (as : Array α) (stop : Nat) (hstop : stop ≤ as.size) : as.foldr f b stop stop = b := by
  apply foldrM_stop; assumption

theorem foldr_step (as : Array α) (start stop : Nat) (hstop : stop ≤ start) (hstart : start < as.size) :
  as.foldr f b (start+1) stop = as.foldr f (f as[start] b) start stop := by
  apply foldrM_step; assumption

end foldr

section append

theorem size_append_aux {as bs : Array α} (start stop : Nat) (hstart : start ≤ stop) (hstop : stop ≤ bs.size) :
  (foldl push as bs start stop).size = as.size + (stop - start) := by
  by_cases start = stop with
  | isTrue heq =>
    rw [heq]
    rw [foldl_stop]
    rw [Nat.sub_self]
    rw [Nat.add_zero]
    exact hstop
  | isFalse hne =>
    have hstart' : start < stop := Nat.lt_of_le_of_ne hstart hne
    rw [foldl_step push as bs start stop hstart' hstop]
    rw [size_append_aux (start+1) stop hstart' hstop]
    rw [size_push]
    rw [Nat.sub_succ']
    rw [Nat.add_assoc]
    congr
    rw [Nat.add_comm]
    have : 1 ≤ stop - start := by
      rw [Nat.le_sub_iff_add_le hstart]
      rw [Nat.add_comm]
      exact hstart'
    rw [Nat.sub_add_cancel this]
termination_by size_append_aux => stop - start

theorem get_append_aux_lo {as bs : Array α} (start stop i : Nat) (hstart : start ≤ stop) (hstop : stop ≤ bs.size) (hi : i < as.size)
  (h : i < (foldl push as bs start stop).size := by simp_arith [*]) :
  (foldl push as bs start stop)[i] = as[i] := by
  simp only [autoParam] at h
  by_cases start = stop with
  | isTrue heq =>
    congr
    rw [heq]
    rw [foldl_stop]
    exact hstop
  | isFalse hne =>
    have hstart' : start < stop := Nat.lt_of_le_of_ne hstart hne
    have : start < bs.size := Nat.lt_of_lt_of_le hstart' hstop
    have : i < (foldl push (as.push bs[start]) bs (start+1) stop).size := by
      rw [←foldl_step]
      exact h
      exact hstart'
      exact hstop
    transitivity (foldl push (as.push bs[start]) bs (start+1) stop)[i]
    · congr 1
      rw [foldl_step]
      exact hstart'
      exact hstop
    · rw [get_append_aux_lo (start+1) stop i hstart' hstop]
      rw [get_push_lt]
termination_by get_append_aux_lo => stop - start

theorem get_append_aux_hi {as bs : Array α} (start stop i : Nat) (hstart : start ≤ stop) (hstop : stop ≤ bs.size) (hi : i < stop - start)
  (ha : as.size + i < (foldl push as bs start stop).size := by simp_arith [*])
  (hb : start + i < bs.size := by simp_arith [*]):
  (foldl push as bs start stop)[as.size + i] = bs[start + i] := by
  simp only [autoParam] at ha hb
  by_cases start = stop with
  | isTrue heq =>
    rw [heq, Nat.sub_self] at hi
    contradiction
  | isFalse hne =>
    have hstart' : start < stop := Nat.lt_of_le_of_ne hstart hne
    have : start < bs.size := Nat.lt_of_lt_of_le hstart' hstop
    have : as.size + i < (foldl push (as.push bs[start]) bs (start+1) stop).size := by
      rw [size_append_aux (start+1) stop (Nat.succ_le_of_lt hstart') hstop]
      rw [size_push]
      rw [Nat.add_assoc]
      apply Nat.add_lt_add_left
      rw [Nat.add_comm]
      rw [Nat.sub_succ']
      rw [Nat.sub_add_cancel]
      exact hi
      rw [Nat.le_sub_iff_add_le hstart]
      rw [Nat.add_comm]
      exact Nat.succ_le_of_lt hstart'
    transitivity (foldl push (as.push bs[start]) bs (start+1) stop)[as.size + i]
    · congr 1
      rw [foldl_step]
      exact hstart'
      exact hstop
    · match i with
      | 0 =>
        transitivity (as.push bs[start])[as.size]
        · have h : as.size < (as.push bs[start]).size := by simp; done
          exact get_append_aux_lo (start+1) stop as.size (Nat.succ_le_of_lt hstart') hstop h _
        · rw [get_push_eq]; rfl
      | i+1 =>
        have : (as.push bs[start]).size + i < (foldl push (as.push bs[start]) bs (start+1) stop).size := by
          rw [size_append_aux (start+1) stop (Nat.succ_le_of_lt hstart') hstop]
          rw [size_push]
          apply Nat.add_lt_add_left
          rw [Nat.sub_succ']
          rw [Nat.lt_sub_iff_add_lt]
          exact hi
        transitivity (foldl push (as.push bs[start]) bs (start+1) stop)[(as.push bs[start]).size + i]
        · congr 1
          rw [size_push]
          rw [Nat.add_right_comm, Nat.add_assoc]
        · have hi' : i < stop - (start+1) := by
            rw [Nat.sub_succ']
            rw [Nat.lt_sub_iff_add_lt]
            exact hi
          have : start + 1 + i < bs.size := by rw [Nat.add_assoc, Nat.add_comm 1]; exact hb
          rw [get_append_aux_hi (start+1) stop i (Nat.succ_le_of_lt hstart') hstop hi' _ _]
          congr 1
          rw [Nat.add_right_comm, Nat.add_assoc]
          assumption

theorem data_append_aux {as bs : Array α} (start stop : Nat) (hstart : start ≤ stop) (hstop : stop ≤ bs.size) :
  (foldl push as bs start stop).data = as.data ++ bs.data.extract start stop := by
  by_cases start = stop with
  | isTrue heq =>
    cases heq
    rw [foldl_stop] <;> try assumption
    rw [List.extract_stop]
    rw [List.append_nil]
  | isFalse hne =>
    have hstart' : start < stop := Nat.lt_of_le_of_ne hstart hne
    have : start < bs.size := Nat.lt_of_lt_of_le hstart' hstop
    rw [foldl_step] <;> try assumption
    rw [List.extract_step]
    rw [data_append_aux (start+1) stop] <;> try assumption
    rw [push_data]
    rw [getElem_eq_data_get]
    rw [List.append_assoc]
    rw [List.singleton_append]
termination_by data_append_aux => stop - start
end append

section sum

local instance : Lean.IsAssociative (α:=Nat) (.+.) where
  assoc := Nat.add_assoc

def sum (ns : Array Nat) (start := 0) (stop := ns.size) : Nat :=
  ns.foldl (.+.) 0 start stop

theorem sum_stop (ns : Array Nat) (stop : Nat) (hstop : stop ≤ ns.size) :
  ns.sum stop stop = 0 := by
  simp only [sum]
  rw [foldl_stop]
  exact hstop

theorem sum_step (ns : Array Nat) (start stop : Nat) (hstart : start < stop) (hstop : stop ≤ ns.size) :
  have : start < ns.size := Nat.lt_of_lt_of_le hstart hstop
  ns.sum start stop = ns[start] + ns.sum (start+1) stop := by
  have : start < ns.size := Nat.lt_of_lt_of_le hstart hstop
  simp only [sum]
  rw [foldl_step] <;> try assumption
  rw [Nat.add_comm 0 ns[start]]
  rw [ns.foldl_assoc (.+.) ns[start] 0 (start+1) stop (Nat.succ_le_of_lt hstart) hstop]

end sum

@[deprecated Array.ofFn]
protected def ofFun (f : Fin n → α) : Array α := ofFn f

theorem get_ofFn (f : Fin n → α) (i : Fin (ofFn f).size) : (ofFn f).get i = f (size_ofFn f ▸ i) := by
  rw [get_eq_getElem, getElem_ofFn]
  congr 1
  ext
  simp only
  apply Fin.val_eq_val_of_heq (size_ofFn ..)
  elim_casts; rfl

end Array
