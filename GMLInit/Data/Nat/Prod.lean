import GMLInit.Data.Nat.Basic
import GMLInit.Data.Nat.Order

namespace Nat

def tri : Nat → Nat
| 0 => 0
| n+1 => tri n + n + 1

theorem tri_zero : tri 0 = 0 := rfl
theorem tri_succ (n) : tri (n+1) = tri n + n + 1 := rfl

theorem tri_mono {m n : Nat} : m ≤ n → tri m ≤ tri n := by
  induction m, n using Nat.recDiag with
  | zero_zero => intro; reflexivity
  | zero_succ n => intro; exact Nat.zero_le _
  | succ_zero m => intro; contradiction
  | succ_succ m n H =>
    intro h
    rw [tri_succ, tri_succ]
    apply Nat.add_le_add_right
    apply Nat.add_le_add
    · exact H (Nat.le_of_succ_le_succ h)
    · exact Nat.le_of_succ_le_succ h

theorem two_tri_eq (n : Nat) : 2 * tri n = n * (n + 1) := by
  induction n with
  | zero => rfl
  | succ n H => calc
    _ = 2 * (tri n + (n + 1)) := by rfl
    _ = 2 * tri n + 2 * (n + 1) := by rw [Nat.mul_add]
    _ = n * (n + 1) + 2 * (n + 1) := by rw [H]
    _ = (n + 2) * (n + 1) := by rw [Nat.add_mul]
    _ = (n + 1) * (n + 1 + 1) := by rw [Nat.mul_comm]

private theorem tri_add_self_lt_tri_of_lt {m n : Nat} : m < n → tri m + m < tri n := by
  intro h
  transitivity (tri (m+1)) using (.<.), (.≤.)
  · exact Nat.lt_succ_self _
  · apply Nat.tri_mono
    apply Nat.succ_le_of_lt
    exact h

theorem tri_add_inj {m₁ n₁ m₂ n₂} : m₁ ≤ n₁ → m₂ ≤ n₂ → tri n₁ + m₁ = tri n₂ + m₂ → n₁ = n₂ := by
  intro h₁ h₂ h
  by_cases n₁ ≤ n₂, n₁ ≥ n₂ with
  | isTrue hle, isTrue hge =>
    antisymmetry using LE.le
    · exact hle
    · exact hge
  | _, isFalse hlt =>
    absurd h
    apply Nat.ne_of_lt
    transitivity (tri n₁ + n₁) using LE.le, LT.lt
    · apply Nat.add_le_add_left
      exact h₁
    · transitivity (tri n₂) using LT.lt, LE.le
      · apply Nat.tri_add_self_lt_tri_of_lt
        exact Nat.lt_of_not_ge hlt
      · exact Nat.le_add_right ..
  | isFalse hgt, _ =>
    absurd h
    symmetry using (.≠.)
    apply Nat.ne_of_lt
    transitivity (tri n₂ + n₂) using LE.le, LT.lt
    · apply Nat.add_le_add_left
      exact h₂
    · transitivity (tri n₁) using LT.lt, LE.le
      · apply Nat.tri_add_self_lt_tri_of_lt
        exact Nat.gt_of_not_le hgt
      · exact Nat.le_add_right ..

abbrev pair (x y : Nat) : Nat := tri (x + y) + x

theorem pair_zero_right (x : Nat) : pair x 0 = tri x + x := rfl

theorem pair_succ_right (x y : Nat) : pair x (y+1) = pair x y + (x + y) + 1 := calc
  _ = (tri (x + y) + (x + y) + 1) + x := by rfl
  _ = ((tri (x + y) + (x + y)) + x) + 1 := by rw [Nat.add_right_comm _ x 1]
  _ = ((tri (x + y) + x) + (x + y)) + 1 := by rw [Nat.add_right_comm _ (x+y) x]

theorem pair_zero_left (y : Nat) : pair 0 y = tri y := calc
  _ = tri (0 + y) := by rfl
  _ = tri y := by rw [Nat.zero_add]

theorem pair_succ_left (x y : Nat) : pair (x+1) y = pair x y + (x + y) + 2 := calc
  _ = (tri (x + 1 + y)) + (x + 1) := by rfl
  _ = (tri (x + y + 1)) + (x + 1) := by rw [Nat.add_right_comm _ y 1]
  _ = (tri (x + y) + (x + y) + 1) + (x + 1) := by rfl
  _ = (tri (x + y) + x + y + 1) + (x + 1) := by rw [Nat.add_assoc _ x y]
  _ = (pair x y + y + 1) + (x + 1) := by rfl
  _ = (pair x y + y) + (x + 1) + 1 := by rw [Nat.add_right_comm _ (x+1) 1]
  _ = (pair x y + y) + x + 1 + 1 := by rw [Nat.add_assoc _ x 1]
  _ = pair x y + (y + x) + 1 + 1 := by rw [Nat.add_assoc _ y x]
  _ = pair x y + (x + y) + 1 + 1 := by rw [Nat.add_comm x y]

def split : Nat → (t : Nat) × Fin (t+1)
| 0 => ⟨0,0⟩
| n+1 => match split n with
  | ⟨t,s,hs⟩ =>
    if h: s < t
    then ⟨t, s+1, Nat.succ_lt_succ h⟩
    else ⟨t+1, 0, Nat.zero_lt_succ (t+1)⟩

theorem split_eq (n : Nat) : tri (split n).fst + (split n).snd = n := by
  induction n with
  | zero => rfl
  | succ n H =>
    symmetry
    transitivity (tri (split n).fst + ((split n).snd + 1))
    · rw [←Nat.add_assoc (tri (split n).fst) (split n).snd 1, H]
    · symmetry
      unfold split
      split
      next h =>
        simp [Nat.zero_eq, Nat.add_eq, Nat.add_zero n] at h ⊢
        rw [Nat.add_zero n] at h
        rw [dif_pos h]
      next h =>
        have heq: (split n).snd.val = (split n).fst := by
          apply Nat.le_antisymm
          · apply Nat.le_of_lt_succ
            exact (split n).snd.isLt
          · apply Nat.le_of_not_gt
            exact h
        unfold tri
        clean
        dsimp [Nat.add_eq, Nat.add_zero n] at h ⊢
        rw [Nat.add_zero n] at h
        rw [dif_neg h, ←Nat.add_assoc, heq]; rfl

protected abbrev fst (n : Nat) : Nat := (split n).snd

protected abbrev snd (n : Nat) : Nat := (split n).fst - (split n).snd

private theorem split_pair_fst (x y) : (split (pair x y)).fst = x + y := by
  match h: (split (pair x y)) with
  | ⟨t,⟨s,hs⟩⟩ =>
    apply Nat.tri_add_inj (Nat.le_of_lt_succ hs) (Nat.le_add_right x y)
    transitivity (tri (split (pair x y)).fst + (split (pair x y)).snd)
    · rw [h]
    · rw [split_eq, pair]

private theorem split_pair_snd (x y) : (split (pair x y)).snd = x := by
  apply Nat.add_left_cancel (n:=tri (split (pair x y)).fst)
  rw [split_eq, split_pair_fst, pair]

theorem fst_pair (x y) : (pair x y).fst = x := split_pair_snd x y

theorem snd_pair (x y) : (pair x y).snd = y := by
  unfold Nat.snd
  rw [Nat.split_pair_snd]
  rw [Nat.split_pair_fst]
  rw [Nat.add_sub_cancel_left]

theorem pair_fst_snd (n) : pair n.fst n.snd = n := by
  unfold pair Nat.fst Nat.snd
  match h: (split n) with
  | ⟨t,⟨s,hs⟩⟩ =>
    rw [Nat.add_comm s, Nat.sub_add_cancel (Nat.le_of_lt_succ hs)]
    rw [←split_eq n, h]

def prodEquiv : Equiv Nat (Nat × Nat) where
  fwd n := (n.fst, n.snd)
  rev | (n₁,n₂) => pair n₁ n₂
  spec := by intro
    | n, (n₁,n₂) =>
      clean
      constr
      · intro h
        cases h
        rw [pair_fst_snd]
      · intro h
        cases h
        rw [fst_pair, snd_pair]

end Nat
