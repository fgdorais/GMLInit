import GMLInit.Data.Nat

namespace Pos

protected inductive asInd
| one : Pos.asInd
| succ : Pos.asInd → Pos.asInd
deriving Repr

protected def toInd : Pos → Pos.asInd
| .succOfNat 0 => .one
| .succOfNat (n+1) => .succ (Pos.toInd (.succOfNat n))

theorem toInd_one : (1 : Pos).toInd = asInd.one := rfl
theorem toInd_succ (n : Pos) : (n + 1).toInd = n.toInd.succ := sorry

protected def asInd.toNat : Pos.asInd → Nat
| .one => 1
| .succ n => asInd.toNat n + 1

theorem asInd.toNat_one : asInd.one.toNat = 1 := rfl
theorem asInd.toNat_succ (n : Pos.asInd) : n.succ.toNat = n.toNat + 1 := rfl

protected def ofInd (n : Pos.asInd) : Pos where
  toNat := n.toNat
  ne_zero :=
    match n with
    | .one => Nat.noConfusion
    | .succ n => Nat.succ_ne_zero n.toNat

theorem ofInd_one : Pos.ofInd asInd.one = 1 := rfl
theorem ofInd_succ (n : Pos.asInd) : Pos.ofInd n.succ = Pos.ofInd n + 1 := rfl

theorem toInd_ofInd (n : Pos.asInd) : Pos.toInd (Pos.ofInd n) = n := by
  induction n with
  | one => rfl
  | succ n ih =>
    rw [ofInd_succ]
    rw [toInd_succ]
    rw [ih]

theorem ofInd_toInd (n : Pos) : Pos.ofInd n.toInd = n := by
  induction n with
  | one => rfl
  | succ n ih =>
    rw [toInd_succ]
    rw [ofInd_succ]
    rw [ih]

theorem asIndEquiv : Equiv Pos Pos.asInd where
  fwd := Pos.toInd
  rev := Pos.ofInd
  fwd_eq_iff_rev_eq := by
    intros
    constructor
    · intro | rfl => exact ofInd_toInd ..
    · intro | rfl => exact toInd_ofInd ..

protected inductive asBin
| one : Pos.asBin
| bit0 : Pos.asBin → Pos.asBin
| bit1 : Pos.asBin → Pos.asBin
deriving Repr

protected def asBin.toNat : Pos.asBin → Nat
| one => 1
| bit0 n => 2 * asBin.toNat n
| bit1 n => 2 * asBin.toNat n + 1

theorem asBin.toNat_one : asBin.one.toNat = 1 := rfl
theorem asBin.toNat_bit0 (n : Pos.asBin) : n.bit0.toNat = 2 * n.toNat := rfl
theorem asBin.toNat_bit1 (n : Pos.asBin) : n.bit1.toNat = 2 * n.toNat + 1 := rfl

theorem asBin.toNat_ne_zero (n : Pos.asBin) : n.toNat ≠ 0 := by
  induction n with
  | one => exact Nat.one_ne_zero
  | bit0 n ih =>
    rw [←Nat.mul_zero 2, asBin.toNat_bit0]
    intro h
    absurd ih
    exact Nat.eq_of_mul_eq_mul_left (Nat.is_pos 2) h
  | bit1 n _ => exact Nat.succ_ne_zero (2 * n.toNat)

def ofBin (n : Pos.asBin) : Pos := ⟨n.toNat, n.toNat_ne_zero⟩

def div2 : Nat → Nat × Fin 2
| 0 => (0,0)
| 1 => (0,1)
| n+2 => match div2 n with | (q,r) => (q+1,r)

theorem div2_eq : (n : Nat) → 2 * (div2 n).fst + (div2 n).snd.val = n
| 0 => rfl
| 1 => rfl
| n+2 => by
  simp only [div2]
  rw [Nat.mul_succ]
  rw [Nat.add_right_comm]
  congr
  exact div2_eq n

def toBin (n : Pos) : Pos.asBin :=
  match h : div2 n.toNat with
  | (0,0) => absurd (Nat.zero_lt n.toNat) $ by
      rw [←div2_eq n.toNat, h]
      intro; contradiction
  | (0,1) => .one
  | (q+1,0) =>
    have : q + 1 < n.toNat := by
      rw [←div2_eq n.toNat, h]
      rw [Nat.mul_succ, Nat.two_mul]
      apply Nat.add_lt_add_right
      apply Nat.lt_succ_of_le
      apply Nat.le_add_right
    .bit0 (toBin (Pos.succOfNat q))
  | (q+1,1) =>
    have : q + 1 < n.toNat := by
      rw [←div2_eq n.toNat, h]
      rw [Nat.mul_succ, Nat.two_mul]
      apply Nat.add_lt_add_right
      apply Nat.lt_succ_of_le
      rw [Nat.add_assoc]
      apply Nat.le_add_right
    .bit1 (toBin (Pos.succOfNat q))
termination_by n.toNat

end Pos
