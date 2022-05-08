import GMLInit.Data.Nat.Extended.Basic

namespace ENat

abbrev Finite (e : ENat) : Prop := ∃ x, e.isLE x

namespace Finite
variable (e : ENat)

private def rel (x y : Nat) : Prop := x = y + 1 ∧ ¬e.isLE y

private def wf (isFinite : Finite e) : WellFounded (Finite.rel e) := by
  constr
  intro x
  match isFinite with
  | ⟨n,hn⟩ =>
    apply Acc.intro
    intro x' ⟨h', hx⟩
    cases h'
    have : x + 1 ≤ n := by
      apply Nat.succ_le_of_lt
      apply Nat.lt_of_not_ge
      intro hge
      apply hx
      apply e.mono hge
      exact hn
    match Nat.le.dest this with
    | ⟨y, hxy⟩ =>
      clear this
      induction y generalizing x with
      | zero =>
        rw [hxy]
        apply Acc.intro
        intro | _, ⟨rfl, _⟩ => contradiction
      | succ y H =>
        apply Acc.intro
        intro
        | _, ⟨rfl, h⟩ =>
          apply H
          · exact h
          · rw [←hxy]
            simp_arith

end Finite

private def toNatAux {e : ENat} (isFinite : Finite e) (x : Nat) : Nat :=
  if h : e.isLE x then x else toNatAux isFinite (x+1)
termination_by' ⟨Finite.rel e, Finite.wf e isFinite⟩
decreasing_by trivial

private theorem toNatAux_eq {e : ENat} (isFinite : Finite e) (x : Nat) : toNatAux isFinite x = if h : e.isLE x then x else toNatAux isFinite (x+1) :=
  WellFounded.fix_eq _ _ _

private theorem isLE_toNatAux {e : ENat} (isFinite : Finite e) (x : Nat) : e.isLE (toNatAux isFinite x) := by
  rw [toNatAux_eq]
  split
  · assumption
  · apply isLE_toNatAux
termination_by' ⟨Finite.rel e, Finite.wf e isFinite⟩
decreasing_by trivial

private theorem toNatAux_le {e : ENat} {y : Nat} (hy : e.isLE y) {x} (hle : x ≤ y) : toNatAux ⟨y,hy⟩ x ≤ y := by
  rw [toNatAux_eq]
  split
  · assumption
  · apply toNatAux_le hy
    apply Nat.succ_le_of_lt
    apply Nat.lt_of_le_of_ne
    · exact hle
    · intro heq
      cases heq
      contradiction
termination_by' invImage PSigma.fst ⟨Finite.rel e, Finite.wf e ⟨y,hy⟩⟩
decreasing_by trivial

def toNat (e : ENat) (isFinite : Finite e) : Nat := toNatAux isFinite 0

theorem isLE_toNat (e : ENat) (isFinite : Finite e) : e.isLE (e.toNat isFinite) :=
  isLE_toNatAux isFinite 0

theorem toNat_le_of_isLE {e : ENat} {x : Nat} (h : e.isLE x) : toNat e ⟨x,h⟩ ≤ x := by
  apply toNatAux_le
  · exact h
  · exact Nat.zero_le x

theorem isLE_iff_toNat_le (e : ENat) (isFinite : Finite e) (x : Nat) : e.isLE x ↔ e.toNat isFinite ≤ x := by
  constr
  · intro h
    apply toNat_le_of_isLE
    exact h
  · intro h
    apply mono _ h
    apply isLE_toNat

@[simp] theorem toNat_ofNat (x : Nat) : toNat (ENat.ofNat x) ⟨x, ofNat_isLE_self x⟩ = x := by
  antisymmetry using (.≤.:Nat→Nat→Prop)
  · rw [←isLE_iff_toNat_le]
    exact ofNat_isLE_self x
  · cases x with
    | zero => exact Nat.zero_le _
    | succ x =>
      apply Nat.succ_le_of_lt
      apply Nat.lt_of_not_ge
      intro (h : _ ≤ x)
      rw [←isLE_iff_toNat_le, ofNat_isLE_iff_le] at h
      apply Nat.not_gt_of_le h
      exact Nat.lt_succ_self x

@[simp] theorem ofNat_toNat (e : ENat) (h : Finite e) : ENat.ofNat (toNat e h) = e := by
  apply ENat.ext
  intro x
  cases hx : e.isLE x with
  | true => rw [ofNat_isLE_iff_le, ←isLE_iff_toNat_le, hx]
  | false =>
    rw [←Bool.not_eq_true] at hx ⊢
    apply mt _ hx
    intro hx
    rw [ofNat_isLE_iff_le] at hx
    rw [isLE_iff_toNat_le _ h]
    exact hx

end ENat
