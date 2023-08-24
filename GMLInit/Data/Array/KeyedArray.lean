import GMLInit.Data.BEq
import GMLInit.Data.Array.Basic

structure KeyedArray {α : Type _} [BEq α] (β : Type _) (p : β → α) extends Array β where
  uniq (i j : Fin toArray.size) : (p (toArray.get i) == p (toArray.get j)) = (i.val == j.val)

namespace KeyedArray
variable {α} [BEq α] {β} {p : β → α} (a : KeyedArray β p)

theorem uniq' {i j} (hi : i < a.size) (hj : j < a.size) : (p a.toArray[i] == p a.toArray[j]) = (i == j) := by
  rw [←a.toArray.get_eq_getElem ⟨i, hi⟩]
  rw [←a.toArray.get_eq_getElem ⟨j, hj⟩]
  rw [a.uniq]

def empty : KeyedArray β p where
  toArray := #[]
  uniq := (nomatch .)

def locate? (key : α) : Option (Fin a.size) :=
  Fin.find? fun i => p (a.get i) == key

theorem locate?_some (key : α) (i : Fin a.size) : a.locate? key = some i → p (a.get i) == key := by
  intro h; rw [Fin.find?_some i h]

theorem locate?_none (key : α) (i : Fin a.size) : a.locate? key = none → p (a.get i) != key := by
  intro h; rw [bne, Fin.find?_none i h]; rfl

theorem locate?_some_iff [EquivBEq α] (key : α) (i : Fin a.size) : a.locate? key = some i ↔ p (a.get i) == key := by
  constructor
  · exact locate?_some a key i
  · intro h
    match hloc : a.locate? key with
    | some j =>
      have := a.locate?_some key j hloc
      rw [BEq.subst_right (BEq.symm h)] at this
      rw [a.uniq] at this
      congr
      apply Fin.eq_of_val_eq
      exact eq_of_beq this
    | none =>
      have := a.locate?_none key i hloc
      rw [bne, h] at this
      contradiction

def find? (key : α) : Option β :=
  match a.locate? key with
  | none => none
  | some i => some (a.get i)

theorem find?_some (key : α) (value : β) : a.find? key = some value → p value == key := by
  intro h
  simp only [find?] at h
  split at h
  next => contradiction
  next heq =>
    injection h with h
    cases h
    apply locate?_some
    exact heq

def replace [EquivBEq α] (value : β) : KeyedArray β p where
  toArray :=
    match a.locate? (p value) with
    | some k => a.set k value
    | none => a.toArray
  uniq :=
    match hk : a.locate? (p value) with
    | some k => fun
      | ⟨i, (hi : i < (a.set k value).size)⟩,
        ⟨j, (hj : j < (a.set k value).size)⟩ => by
        have seq : (a.set k value).size = a.size := Array.size_set ..
        let hi' : i < a.size := seq ▸ hi
        let hj' : j < a.size := seq ▸ hj
        simp only [Array.get_eq_getElem]
        have heqi : p ((a.set k value)[i]) == p a.toArray[i] := by
          by_cases k.val = i with
          | isTrue h =>
            rw [Array.get_set a.toArray k i hi', if_pos h]
            symmetry using (.==.)
            apply locate?_some
            rw [hk]
            congr
            apply Fin.eq_of_val_eq
            exact h
          | isFalse h =>
            rw [Array.get_set a.toArray k i hi', if_neg h]
            exact BEq.refl ..
        have heqj : p ((a.set k value)[j]) == p a.toArray[j] := by
          by_cases k.val = j with
          | isTrue h =>
            rw [Array.get_set a.toArray k j hj', if_pos h]
            symmetry using (.==.)
            apply locate?_some
            rw [hk]
            congr
            apply Fin.eq_of_val_eq
            exact h
          | isFalse h =>
            rw [Array.get_set a.toArray k j hj', if_neg h]
            exact BEq.refl ..
        rw [BEq.subst_left heqi, BEq.subst_right heqj]
        rw [←a.get_eq_getElem ⟨i,hi'⟩, ←a.get_eq_getElem ⟨j,hj'⟩]
        exact a.uniq ..
    | none => a.uniq

def insert [EquivBEq α] (value : β) : KeyedArray β p where
  toArray :=
    match a.locate? (p value) with
    | some k => a.set k value
    | none => a.toArray.push value
  uniq :=
    match hk : a.locate? (p value) with
    | some k => fun
      | ⟨i, (hi : i < (a.set k value).size)⟩,
        ⟨j, (hj : j < (a.set k value).size)⟩ => by
        have seq : (a.set k value).size = a.size := Array.size_set ..
        have hi' : i < a.size := seq ▸ hi
        have hj' : j < a.size := seq ▸ hj
        simp only [Array.get_eq_getElem]
        have heqi : p ((a.set k value)[i]) == p a.toArray[i] := by
          by_cases k.val = i with
          | isTrue h =>
            rw [a.toArray.get_set k i hi', if_pos h]
            symmetry using (.==.)
            apply locate?_some
            rw [hk]
            congr
            apply Fin.eq_of_val_eq
            exact h
          | isFalse h =>
            rw [a.toArray.get_set k i hi', if_neg h]
            exact BEq.refl ..
        have heqj : p ((a.set k value)[j]) == p a.toArray[j] := by
          by_cases k.val = j with
          | isTrue h =>
            rw [a.toArray.get_set k j hj', if_pos h]
            symmetry using (.==.)
            apply locate?_some
            rw [hk]
            congr
            apply Fin.eq_of_val_eq
            exact h
          | isFalse h =>
            rw [Array.get_set a.toArray k j hj', if_neg h]
            exact BEq.refl ..
        rw [BEq.subst_left heqi, BEq.subst_right heqj]
        rw [←a.get_eq_getElem ⟨i,hi'⟩, ←a.get_eq_getElem ⟨j,hj'⟩]
        exact a.uniq ..
    | none => fun
      | ⟨i, (hi : i < (a.push value).size)⟩,
        ⟨j, (hj : j < (a.push value).size)⟩ => by
        simp only [Array.get_eq_getElem]
        have hsz : (a.push value).size = a.size + 1 := Array.size_push ..
        by_cases i = a.size, j = a.size with
        | isTrue heqi, isTrue heqj => simp only [heqi, heqj, BEq.refl]
        | isTrue heqi, isFalse hnej =>
          simp [heqi]
          rw [Bool.eq_iff_iff]
          constructor
          · intro h
            have h := BEq.symm h
            have hj' : j < a.size := by
              rw [hsz] at hj
              apply Nat.lt_of_le_of_ne
              · exact Nat.le_of_lt_succ hj
              · exact hnej
            rw [a.toArray.get_push_lt _ j hj'] at h
            rw [←a.toArray.get_eq_getElem ⟨j,hj'⟩] at h
            have h' := locate?_none a (p value) ⟨j, hj'⟩ hk
            rw [bne, h] at h'
            contradiction
          · intro h
            rw [BEq.eq_of_beq h] at hnej
            contradiction
        | isFalse hnei, isTrue heqj =>
          simp [heqj]
          rw [Bool.eq_iff_iff]
          constructor
          · intro h
            have hi' : i < a.size := by
              rw [hsz] at hi
              apply Nat.lt_of_le_of_ne
              · exact Nat.le_of_lt_succ hi
              · exact hnei
            rw [a.toArray.get_push_lt _ i hi'] at h
            rw [←a.toArray.get_eq_getElem ⟨i,hi'⟩] at h
            have h' := locate?_none a (p value) ⟨i,hi'⟩ hk
            rw [bne, h] at h'
            contradiction
          · intro h
            rw [BEq.eq_of_beq h] at hnei
            contradiction
        | isFalse hnei, isFalse hnej =>
          have hi' : i < a.size := by
            rw [hsz] at hi
            apply Nat.lt_of_le_of_ne
            · exact Nat.le_of_lt_succ hi
            · exact hnei
          have hj' : j < a.size := by
            rw [hsz] at hj
            apply Nat.lt_of_le_of_ne
            · exact Nat.le_of_lt_succ hj
            · exact hnej
          rw [a.toArray.get_push_lt _ i hi']
          rw [a.toArray.get_push_lt _ j hj']
          exact a.uniq ..

theorem find?_insert [EquivBEq α] (value : β) : (a.insert value).find? (p value) = some value := sorry

theorem find?_insert_bne [EquivBEq α] {key : α} {value : β} : key != p value → (a.insert value).find? key = a.find? key := sorry

def erase [EquivBEq α] (key : α) : KeyedArray β p where
  toArray :=
    match a.locate? key with
    | none => a.toArray
    | some k => a.del k
  uniq :=
    match a.locate? key with
    | none => a.uniq
    | some k => fun
      | ⟨i, (hi : i < (a.del k).size)⟩,
        ⟨j, (hj : j < (a.del k).size)⟩ => by
        by_cases k.val = i, k.val = j with
        | isTrue hik, isTrue hjk =>
          simp [←hik, ←hjk]
          exact BEq.refl ..
        | isTrue hik, isFalse hjk =>
          simp [←hik]
          rw [a.toArray.get_del, if_pos rfl]
          rw [a.toArray.get_del, if_neg hjk]
          rw [a.uniq']
          match hj': a.size-1 == j, hjk': k.val == j with
          | true, true => rfl
          | true, false => absurd hj; rw [Array.size_del, BEq.eq_of_beq hj']; irreflexivity
          | false, true => absurd hjk; exact BEq.eq_of_beq hjk'
          | false, false => rfl
        | isFalse hik, isTrue hjk =>
          simp [←hjk]
          rw [a.toArray.get_del, if_neg hik]
          rw [a.toArray.get_del, if_pos rfl]
          rw [a.uniq']
          match hi': i == a.size-1, hik': i == k.val with
          | true, true => rfl
          | true, false => absurd hi; rw [Array.size_del, BEq.eq_of_beq hi']; irreflexivity
          | false, true => absurd hik; symmetry; exact BEq.eq_of_beq hik'
          | false, false => rfl
        | isFalse hik, isFalse hjk =>
          simp
          rw [a.toArray.get_del, if_neg hik]
          rw [a.toArray.get_del, if_neg hjk]
          rw [a.uniq']

theorem find?_erase [EquivBEq α] (key : α) : (a.erase key).find? key = none := sorry

theorem find?_erase_bne [EquivBEq α] {key k : α} : k != key → (a.erase key).find? k = a.find? k := sorry

end KeyedArray
