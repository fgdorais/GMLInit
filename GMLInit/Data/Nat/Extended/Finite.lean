import GMLInit.Data.Nat.Extended.Basic

namespace ENat

abbrev Finite (x : ENat) : Prop := ∃ n, x.leNat n

namespace Finite
variable (e : ENat)

private def rel (n m : Nat) : Prop := n = m + 1 ∧ e.leNat m ≠ true

private def wf (isFinite : Finite e) : WellFounded (Finite.rel e) := by
  constructor
  intro m
  match isFinite with
  | ⟨n, hn⟩ =>
    constructor
    intro t ⟨heq, hm⟩
    cases heq
    have hlt : m + 1 ≤ n := by
      rw [Nat.succ_le, ←Nat.not_le]
      intro h
      simp only [mono h hn] at hm
    match Nat.le.dest hlt with
    | ⟨k, hk⟩ =>
      cases hk
      induction k generalizing m with
      | zero =>
        constructor; intro
        | _, ⟨rfl, h⟩ =>
          simp only [h] at hn
      | succ k ih =>
        constructor; intro
        | _, ⟨rfl, h⟩ =>
          apply ih _ h
          · apply mono _ hn
            simp only [Nat.succ_add]
            exact Nat.le_refl ..
          · exact Nat.le_add_right ..

end Finite

private def toNatAux {e : ENat} (isFinite : Finite e) (x : Nat) : Nat :=
  if h : e.leNat x = true then x else toNatAux isFinite (x+1)
termination_by' ⟨Finite.rel e, Finite.wf e isFinite⟩
decreasing_by trivial

private theorem toNatAux_eq {e : ENat} (isFinite : Finite e) (x : Nat) : toNatAux isFinite x = if e.leNat x then x else toNatAux isFinite (x+1) :=
  WellFounded.fix_eq _ _ _

private theorem leNat_toNatAux {e : ENat} (isFinite : Finite e) (x : Nat) : e.leNat (toNatAux isFinite x) := by
  rw [toNatAux_eq]
  split
  next h => exact h
  next => apply leNat_toNatAux
termination_by' ⟨Finite.rel e, Finite.wf e isFinite⟩
decreasing_by trivial

private theorem toNatAux_le {e : ENat} {y : Nat} (hy : e.leNat y) {x} (hle : x ≤ y) : toNatAux ⟨y,hy⟩ x ≤ y := by
  rw [toNatAux_eq]
  split
  next => exact hle
  next =>
    apply toNatAux_le hy
    apply Nat.succ_le_of_lt
    apply Nat.lt_of_le_of_ne hle
    intro | rfl => contradiction
termination_by' invImage PSigma.fst ⟨Finite.rel e, Finite.wf e ⟨y,hy⟩⟩
decreasing_by trivial

def toNat (e : ENat) (isFinite : Finite e) : Nat := toNatAux isFinite 0

theorem leNat_toNat (e : ENat) (isFinite : Finite e) : e.leNat (e.toNat isFinite) :=
  leNat_toNatAux isFinite 0

theorem toNat_le_of_leNat {e : ENat} {x : Nat} (h : e.leNat x) : toNat e ⟨x,h⟩ ≤ x := by
  apply toNatAux_le h
  exact Nat.zero_le x

theorem leNat_iff_toNat_le (e : ENat) (isFinite : Finite e) (x : Nat) : e.leNat x ↔ e.toNat isFinite ≤ x := by
  constructor
  · intro h
    exact toNat_le_of_leNat h
  · intro h
    exact mono h (leNat_toNat ..)

@[simp] theorem toNat_ofNat (x : Nat) : toNat (ENat.ofNat x) ⟨x, leNat_coe_eq_true_iff_le.2 (Nat.le_refl _)⟩ = x := by
  antisymmetry using (.≤.:Nat→Nat→Prop)
  · rw [←leNat_iff_toNat_le, leNat_coe_eq_true_iff_le]
    exact Nat.le_refl ..
  · cases x with
    | zero => exact Nat.zero_le _
    | succ x =>
      apply Nat.succ_le_of_lt
      apply Nat.not_le.1
      intro (h : _ ≤ x)
      rw [←leNat_iff_toNat_le, leNat_coe_eq_true_iff_le] at h
      apply Nat.not_lt.2 h
      exact Nat.lt_succ_self _

@[simp] theorem ofNat_toNat (e : ENat) (h : Finite e) : ENat.ofNat (toNat e h) = e := by
  ext x; cases hx : e.leNat x with
  | true => rw [leNat_coe_eq_true_iff_le, ←leNat_iff_toNat_le, hx]
  | false =>
    rw [←Bool.not_eq_true] at hx ⊢
    apply mt _ hx
    intro hx
    rw [leNat_iff_toNat_le _ h]
    rwa [leNat_coe_eq_true_iff_le] at hx

end ENat
