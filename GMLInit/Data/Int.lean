import GMLInit.Data.Basic
import GMLInit.Data.Nat

namespace Int

attribute [local eliminator] Nat.recDiag

alias add_cross_comm := Int.add_add_add_comm

protected theorem add_left_cancel' (i : Int) {j k : Int} (h : i + j = i + k) : j = k :=
  calc
  _ = 0 + j := by rw [Int.zero_add]
  _ = (-i + i) + j := by rw [Int.add_neg_self_left]
  _ = -i + (i + j) := by rw [Int.add_assoc]
  _ = -i + (i + k) := by rw [h]
  _ = (-i + i) + k := by rw [Int.add_assoc]
  _ = 0 + k := by rw [Int.add_neg_self_left]
  _ = k := by rw [Int.zero_add]

protected theorem add_right_cancel' (i : Int) {j k : Int} (h : j + i = k + i) : j = k :=
  calc
  _ = j + 0 := by rw [Int.add_zero]
  _ = j + (i + -i) := by rw [Int.add_neg_self_right]
  _ = (j + i) + -i := by rw [Int.add_assoc]
  _ = (k + i) + -i := by rw [h]
  _ = k + (i + -i) := by rw [Int.add_assoc]
  _ = k + 0 := by rw [Int.add_neg_self_right]
  _ = k := by rw [Int.add_zero]

alias mul_cross_comm := Int.mul_mul_mul_comm

theorem le.intro' (i : Int) (k : Nat) : i ≤ i + k :=
  show (NonNeg ((i+k)-i)) by
  rw [Int.sub_eq, Int.add_right_comm, Int.add_neg_self_right, Int.zero_add]
  apply NonNeg.mk

theorem le.dest' {i j : Int} : i ≤ j → ∃ (k : Nat), j = i + ofNat k := by
  intro (h : NonNeg (j - i))
  match hk : j - i with
  | ofNat k => exists k; rw [←hk, Int.sub_eq, Int.add_left_comm, Int.add_neg_self_right, Int.add_zero]
  | negSucc _ => rw [hk] at h; contradiction

protected theorem le_succ_self (i : Int) : i ≤ i + 1 := le.intro' ..

protected theorem lt_iff_succ_le (i j : Int) : i < j ↔ i + 1 ≤ j := Iff.rfl

protected theorem le_iff_lt_succ (i j : Int) : i ≤ j ↔ i < j + 1 := by
  rw [Int.lt_iff_succ_le]
  constructor
  · apply Int.add_le_add_right (c:=1)
  · apply Int.le_of_add_le_add_right

protected theorem le_or_gt (i j : Int) : i ≤ j ∨ j < i := by
  induction i using Int.casesMkOn with
  | mk mi ni =>
    induction j using Int.casesMkOn with
    | mk mj nj =>
      rw [mk_le_mk, mk_lt_mk]
      rw [Nat.add_comm mi, Nat.add_comm mj]
      exact (Nat.lt_or_ge ..).symm

protected theorem lt_or_ge (i j : Int) : i < j ∨ j ≤ i := by
  cases Int.le_or_gt j i with
  | inl h => right; exact h
  | inr h => left; exact h

theorem lt_or_eq_of_le {i j : Int} : i ≤ j → i < j ∨ i = j := by
  intro hle
  match le.dest' hle with
  | ⟨0, (h : j = i + 0)⟩ =>
    right
    rw [h, Int.add_zero]
  | ⟨n+1, (h : j = i + (ofNat n + 1))⟩ =>
    left
    rw [Int.lt_iff_succ_le]
    rw [h, ←Int.add_assoc, Int.add_right_comm]
    apply Int.le.intro'

protected theorem lt_of_le_of_ne {i j : Int} : i ≤ j → i ≠ j → i < j := by
  intro hle hne
  cases lt_or_eq_of_le hle with
  | inl hlt => exact hlt
  | inr heq => absurd heq; exact hne

protected theorem lt_connex {i j : Int} : i ≠ j → i < j ∨ j < i := by
  intro hne
  cases Int.le_or_gt i j with
  | inl hle => left; apply Int.lt_of_le_of_ne hle hne
  | inr hgt => right; exact hgt

protected theorem lt_compare {i j : Int} : i < j → ∀ (k : Int), i < k ∨ k < j := by
  intro hij k
  cases Int.le_or_gt k i with
  | inl hle => right; exact Int.lt_of_le_of_lt hle hij
  | inr hgt => left; exact hgt

instance : Logic.Reflexive (α:=Int) (.≤.) := ⟨Int.le_refl⟩
instance : Logic.Transitive (α:=Int) (.≤.) := ⟨Int.le_trans⟩
instance : Logic.Antisymmetric (α:=Int) (.≤.) := ⟨Int.le_antisymm⟩
instance : Logic.Total (α:=Int) (.≤.) := ⟨Int.le_total⟩
instance : Logic.Irreflexive (α:=Int) (.<.) := ⟨Int.lt_irrefl⟩
instance : Logic.Transitive (α:=Int) (.<.) := ⟨Int.lt_trans⟩
instance : Logic.Comparison (α:=Int) (.<.) := ⟨Int.lt_compare⟩
instance : Logic.Connex (α:=Int) (.<.) := ⟨Int.lt_connex⟩
instance : Logic.HTransitive (α:=Int) (.≤.) (.<.) (.<.) := ⟨Int.lt_of_le_of_lt⟩
instance : Logic.HTransitive (α:=Int) (.<.) (.≤.) (.<.) := ⟨Int.lt_of_lt_of_le⟩

end Int
