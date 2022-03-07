import GMLInit.Data.Nat.Basic
import GMLInit.Data.Nat.Order

class Infinity (α) where
  infinity : α
notation "∞" => Infinity.infinity

structure ENat where
  isLE : Nat → Bool
  step (x : Nat) : isLE x → isLE (x + 1)

namespace ENat

protected theorem eq : {e₁ e₂ : ENat} → e₁.isLE = e₂.isLE → e₁ = e₂
| ⟨_,_⟩, ⟨_,_⟩, rfl => rfl

protected theorem ext {e₁ e₂ : ENat} : (∀ x, e₁.isLE x = e₂.isLE x) → e₁ = e₂
| h => ENat.eq $ funext h

theorem mono (e : ENat) {x y : Nat} : x ≤ y → e.isLE x → e.isLE y := by
  intro h hx
  match Nat.le.dest h with
  | ⟨z,hz⟩ =>
    cases hz
    induction z using Nat.recAux with
    | zero => exact hx
    | succ z H =>
      apply e.step
      apply H
      exact Nat.le_add_right x z

protected def zero : ENat where
  isLE _ := true
  step _ := id
instance : OfNat ENat (nat_lit 0) := ⟨ENat.zero⟩

@[simp] theorem isLE_zero (n) : ENat.isLE 0 n = true := rfl

protected def infinity : ENat where
  isLE _ := false
  step _ := Bool.noConfusion
instance : Infinity ENat := ⟨ENat.infinity⟩

@[simp] theorem isLE_infinity (n) : ENat.isLE ∞ n = false := rfl

protected def ofNat (n : Nat) : ENat where
  isLE := Nat.ble n
  step x := by
    intro h
    rw [Nat.ble_eq] at h ⊢
    transitivity x
    · exact h
    · exact Nat.le_succ_self x

instance : Coe Nat ENat := ⟨ENat.ofNat⟩

@[simp] theorem ofNat_isLE_iff_le (n m : Nat) : ENat.isLE n m ↔ n ≤ m := by
  unfold ENat.ofNat
  rw [Nat.ble_eq]
  reflexivity

theorem ofNat_isLE_self (n : Nat) : ENat.isLE n n := by
  rw [ofNat_isLE_iff_le]
  reflexivity

protected def le (x y : ENat) : Prop := ∀ n, x.isLE n || !y.isLE n
instance : LE ENat := ⟨ENat.le⟩

protected def lt (x y : ENat) : Prop := ∃ n, x.isLE n && !y.isLE n
instance : LT ENat := ⟨ENat.lt⟩

theorem zero_le (x : ENat) : 0 ≤ x := by
  intro n
  rw [isLE_zero, Bool.true_or]

theorem le_infinity (x : ENat) : x ≤ ∞ := by
  intro n
  rw [isLE_infinity, Bool.not_false, Bool.or_true]

theorem le_refl (x : ENat) : x ≤ x := by
  intro n
  cases x.isLE n <;> rfl

theorem le_trans {x y z : ENat} : x ≤ y → y ≤ z → x ≤ z := by
  intro hxy hyz n
  match hx : x.isLE n, hy : y.isLE n, hz : z.isLE n with
  | true, true, true => rfl
  | true, true, false => rfl
  | true, false, true => rfl
  | true, false, false => rfl
  | false, true, true =>
    have : false = true := by rw [←hxy n, hx, hy]; rfl
    contradiction
  | false, true, false => rfl
  | false, false, true =>
    have : false = true := by rw [←hyz n, hy, hz]; rfl
    contradiction
  | false, false, false => rfl

theorem le_antisymm {x y : ENat} : x ≤ y → y ≤ x → x = y := by
  intro hxy hyx
  apply ENat.ext
  intro n
  match hx : x.isLE n, hy : y.isLE n with
  | true, true => rfl
  | true, false =>
    have : false = true := by rw [←hyx n, hx, hy]; rfl
    contradiction
  | false, true =>
    have : false = true := by rw [←hxy n, hx, hy]; rfl
    contradiction
  | false, false => rfl

theorem le_of_eq {x y : ENat} : x = y → x ≤ y | rfl => le_refl _

theorem le_of_lt {x y : ENat} : x < y → x ≤ y
| ⟨n₀,h₀⟩ => by
  rw [Bool.and_eq_true] at h₀
  intro n
  cases Nat.le_total n n₀ with
  | inl hle =>
    have : y.isLE n = false := by
      rw [←Bool.not_eq_true]
      intro hy
      have : y.isLE n₀ = true := by
        apply y.mono hle
        exact hy
      simp [this] at h₀
    rw [this, Bool.not_false, Bool.or_true]
  | inr hge =>
    have : x.isLE n = true := by
      apply x.mono hge
      exact h₀.1
    rw [this, Bool.true_or]

theorem lt_irrefl (x : ENat) : ¬ x < x := by
  intro ⟨n, hn⟩
  have : false = true := by rw [←hn]; cases x.isLE n <;> rfl
  contradiction

theorem lt_of_le_of_lt {x y z : ENat} : x ≤ y → y < z → x < z := by
  intro hxy ⟨n,h⟩
  rw [Bool.and_eq_true] at h
  have h' := hxy n
  rw [Bool.or_eq_true] at h'
  match h, h' with
  | ⟨_,hz⟩, Or.inl hx =>
    exists n
    rw [hx, hz]
    rfl
  | ⟨hy,_⟩, Or.inr hy' =>
    rw [hy] at hy'
    contradiction

theorem lt_of_lt_of_le {x y z : ENat} : x < y → y ≤ z → x < z := by
  intro ⟨n,h⟩ hyz
  rw [Bool.and_eq_true] at h
  have h' := hyz n
  rw [Bool.or_eq_true] at h'
  match h, h' with
  | ⟨_,hy⟩, Or.inl hy' =>
    rw [hy'] at hy
    contradiction
  | ⟨hx,_⟩, Or.inr hz =>
    exists n
    rw [hx, hz]
    rfl

theorem lt_trans {x y z : ENat} : x < y → y < z → x < z := by
  intro hxy hyz
  apply lt_of_lt_of_le
  · exact hxy
  · apply le_of_lt
    exact hyz

#exit

class inductive Finite (x : ENat) : Prop
| intro (n) : x.isLE n → Finite x

namespace Finite
variable (e : ENat)

private def rel (x y : Nat) : Prop := x = y + 1 ∧ ¬e.isLE y

private def wf [inst : Finite e] : WellFounded (Finite.rel e) := by
  constr
  intro x
  match inst with
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
      induction y using Nat.recAux generalizing x with
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

@[reducible] def next [Finite e] (x : Nat) : Nat :=
  if h : e.isLE x then x else next (x+1)
termination_by' ⟨Finite.rel e, Finite.wf e⟩
decreasing_by trivial

theorem next_eq [Finite e] (x : Nat) : next e x = if h : e.isLE x then x else next e (x+1) :=
  WellFounded.fix_eq _ _ _

theorem next_isLE [Finite e] (x : Nat) : e.isLE (next e x) := by
  rw [next_eq]
  split
  · assumption
  · apply next_isLE
termination_by' ⟨Finite.rel e, Finite.wf e⟩
decreasing_by trivial

theorem le_next_self [Finite e] (x : Nat) : x ≤ next e x := by
  rw [next_eq]
  split
  next => reflexivity
  next =>
    transitivity (x + 1)
    · apply Nat.le_succ
    · apply le_next_self
termination_by' ⟨Finite.rel e, Finite.wf e⟩
decreasing_by trivial

theorem next_isMin [Finite e] (x y : Nat) : x + y < next e x → ¬e.isLE (x + y) := by
  induction y using Nat.recAux generalizing x with
  | zero =>
    rw [next_eq]
    split
    next =>
      intro h
      absurd h
      apply Nat.not_gt_of_le
      reflexivity
    next h =>
      intro
      exact h
  | succ y H =>
    rw [next_eq]
    split
    next =>
      intro h
      absurd h
      apply Nat.not_gt_of_le
      apply Nat.le_add_right
    next =>
      rw [Nat.add_succ, ←Nat.succ_add]
      apply H

end Finite

section
variable (e : ENat) (h : ∃ n, e.isLE n)

local instance inst : Finite e :=
  match h with | ⟨n, hn⟩ => Finite.intro n hn

protected def toNat : Nat := @Finite.next e (inst e h) 0

theorem toNat_isLE : e.isLE (e.toNat h) := @Finite.next_isLE e (inst e h) 0

theorem toNat_isMin (x : Nat) : x < e.toNat h → ¬e.isLE x := by
  unfold ENat.toNat
  rw [←Nat.zero_add x]
  apply @Finite.next_isMin e (inst e h)

theorem ofNat_toNat : ofNat (e.toNat h) = e := by
  apply ENat.ext
  intro n
  unfold ofNat

  done

end

end ENat
