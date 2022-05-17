import GMLInit.Data.Nat

structure Pos where
  protected toNat : Nat
  protected is_pos : Nat.IsPos toNat
attribute [instance] Pos.is_pos

namespace Pos

instance : Coe Pos Nat := ⟨Pos.toNat⟩

lemma toNat.inj : {x y : Pos} → x.toNat = y.toNat → x = y
| ⟨_,_⟩, ⟨_,_⟩, rfl => rfl

@[simp] lemma toNat.injEq (x y : Pos) : (x.toNat = y.toNat) = (x = y) :=
  propext ⟨toNat.inj, congrArg Pos.toNat⟩

protected abbrev one : Pos := ⟨1, inferInstance⟩
instance : OfNat Pos (nat_lit 1) := ⟨Pos.one⟩

protected abbrev add (x y : Pos) : Pos := ⟨x.toNat + y.toNat, inferInstance⟩
instance : Add Pos := ⟨Pos.add⟩

protected abbrev mul (x y : Pos) : Pos := ⟨x.toNat * y.toNat, inferInstance⟩
instance : Mul Pos := ⟨Pos.mul⟩

protected abbrev pow (x : Pos) (y : Nat) : Pos := ⟨x.toNat ^ y, inferInstance⟩
instance : Pow Pos Nat := ⟨Pos.pow⟩

protected def le (x y : Pos) : Prop := x.toNat ≤ y.toNat
instance : LE Pos := ⟨Pos.le⟩

protected def lt (x y : Pos) : Prop := x.toNat < y.toNat
instance : LT Pos := ⟨Pos.lt⟩

@[simp,clean] protected lemma one_eq : Pos.one = 1 := rfl

@[simp,clean] protected lemma add_eq (x y : Pos) : Pos.add x y = x + y := rfl

@[simp,clean] protected lemma mul_eq (x y : Pos) : Pos.mul x y = x * y := rfl

@[simp,clean] protected lemma pow_eq (x : Pos) (y : Nat) : Pos.pow x y = x ^ y := rfl

@[simp,clean] protected lemma le_eq (x y : Pos) : Pos.le x y = (x ≤ y) := rfl

@[simp,clean] protected lemma lt_eq (x y : Pos) : Pos.lt x y = (x < y) := rfl

instance (n : Nat) : OfNat Pos n.succ := ⟨n.succ, inferInstance⟩

unif_hint succ (x : Pos) (y : Nat) where
  x =?= OfNat.ofNat y.succ ⊢ x + 1 =?= OfNat.ofNat y.succ.succ

@[eliminator] protected def recAux {motive : Pos → Sort _} (one : motive 1) (succ : (x : Pos) → motive x → motive (x+1)) : (x : Pos) → motive x
| ⟨1,_⟩ => one
| ⟨x+2,_⟩ => succ _ (Pos.recAux one succ ⟨x.succ, inferInstance⟩)

protected def recAuxOn {motive : Pos → Sort _} (x : Pos) (one : motive 1) (succ : (x : Pos) → motive x → motive (x+1)) : motive x :=
  Pos.recAux one succ x

protected def casesAuxOn {motive : Pos → Sort _} (x : Pos) (one : motive 1) (succ : (x : Pos) → motive (x+1)) : motive x :=
  Pos.recAux one (λ x _ => succ x) x

protected def recDiagAux.{u} {motive : Pos → Pos → Sort u}
  (left : (x : Pos) → motive x 1)
  (right : (y : Pos) → motive 1 y)
  (diag : (x y : Pos) → motive x y → motive (x + 1) (y + 1)) :
  (x y : Pos) → motive x y :=
  Pos.recAux (motive := λ x => (y : Pos) → motive x y) right succ
where
  succ (x : Pos) (h : (y : Pos) → motive x y) (y : Pos) : motive (x+1) y :=
    Pos.casesAuxOn y (left (x+1)) (λ y => diag x y (h y))

protected def recDiagAuxOn.{u} {motive : Pos → Pos → Sort u} (x y : Pos)
  (left : (x : Pos) → motive x 1)
  (right : (y : Pos) → motive 1 y)
  (diag : (x y : Pos) → motive x y → motive (x + 1) (y + 1)) :
  motive x y := Pos.recDiagAux left right diag x y

protected def casesDiagAuxOn.{u} {motive : Pos → Pos → Sort u} (x y : Pos)
  (left : (x : Pos) → motive x 1)
  (right : (y : Pos) → motive 1 y)
  (diag : (x y : Pos) → motive (x + 1) (y + 1)) :
  motive x y := Pos.recDiagAux left right (λ x y _ => diag x y) x y

@[local eliminator] protected def recDiag.{u} {motive : Pos → Pos → Sort u}
  (one_one : motive 1 1)
  (succ_one : (x : Pos) → motive x 1 → motive (x + 1) 1)
  (one_succ : (y : Pos) → motive 1 y → motive 1 (y + 1))
  (succ_succ : (x y : Pos) → motive x y → motive (x + 1) (y + 1)) :
  (x y : Pos) → motive x y :=
  Pos.recDiagAux left right succ_succ
where
  left (x : Pos) : motive x 1 := Pos.recAuxOn (motive := λ x => motive x 1) x one_one succ_one
  right (y : Pos) : motive 1 y := Pos.recAuxOn y one_one one_succ

protected def recDiagOn.{u} {motive : Pos → Pos → Sort u} (x y : Pos)
  (one_one : motive 1 1)
  (succ_one : (x : Pos) → motive x 1 → motive (x + 1) 1)
  (one_succ : (y : Pos) → motive 1 y → motive 1 (y + 1))
  (succ_succ : (x y : Pos) → motive x y → motive (x + 1) (y + 1)) :
  motive x y := Pos.recDiag one_one succ_one one_succ succ_succ x y

protected def casesDiagOn.{u} {motive : Pos → Pos → Sort u} (x y : Pos)
  (one_one : motive 1 1)
  (succ_one : (x : Pos) → motive (x + 1) 1)
  (one_succ : (y : Pos) → motive 1 (y + 1))
  (succ_succ : (x y : Pos) → motive (x + 1) (y + 1)) :
  motive x y := Pos.recDiag one_one (λ x _ => succ_one x) (λ y _ => one_succ y) (λ x y _ => succ_succ x y) x y

lemma toNat_one : (1:Pos).toNat = 1 := rfl

lemma toNat_add (x y : Pos) : (x + y).toNat = x.toNat + y.toNat := rfl

lemma toNat_mul (x y : Pos) : (x * y).toNat = x.toNat * y.toNat := rfl

lemma toNat_pow (x : Pos) (y : Nat) : (x ^ y).toNat = x.toNat ^ y := rfl

lemma toNat_eq (x y : Pos) : x = y ↔ x.toNat = y.toNat := ⟨congrArg Pos.toNat, Pos.toNat.inj⟩

lemma toNat_ne (x y : Pos) : x ≠ y ↔ x.toNat ≠ y.toNat := Iff.mt (toNat_eq x y).symm

lemma toNat_le (x y : Pos) : x ≤ y ↔ x.toNat ≤ y.toNat := Iff.rfl

lemma toNat_ge (x y : Pos) : x ≥ y ↔ x.toNat ≥ y.toNat := Iff.rfl

lemma toNat_lt (x y : Pos) : x < y ↔ x.toNat < y.toNat := Iff.rfl

lemma toNat_gt (x y : Pos) : x > y ↔ x.toNat > y.toNat := Iff.rfl

local macro "by_toNat" : tactic => `(tactic| simp only [toNat_eq, toNat_ge, toNat_gt, toNat_le, toNat_lt, toNat_ne, toNat_one, toNat_add, toNat_mul, toNat_pow])

protected theorem succ_ne_one (x : Pos) : x + 1 ≠ 1 := by
  by_toNat; intro h; absurd (Nat.succ.inj h); exact Nat.is_nonzero _

@[simp] protected theorem one_add_eq_add_one (x : Pos) : 1 + x = x + 1 := by
  by_toNat; exact Nat.one_add _

@[simp] protected theorem add_succ (x y : Pos) : x + (y + 1) = (x + y) + 1 := by
  by_toNat; exact Nat.add_succ ..

@[simp] protected theorem succ_add (x y : Pos) : (x + 1) + y = (x + y) + 1 := by
  by_toNat; exact Nat.succ_add ..

protected theorem add_assoc (x y z : Pos) : (x + y) + z = x + (y + z) := by
  by_toNat; exact Nat.add_assoc ..

protected theorem add_comm (x y : Pos) : x + y = y + x := by
  by_toNat; exact Nat.add_comm ..

protected theorem add_left_comm (x y z : Pos) : x + (y + z) = y + (x + z) := by
  by_toNat; exact Nat.add_left_comm ..

protected theorem add_right_comm (x y z : Pos) : (x + y) + z = (x + z) + y := by
  by_toNat; exact Nat.add_right_comm ..

protected theorem add_left_cancel {x y z : Pos} : x + y = x + z → y = z := by
  by_toNat; exact Nat.add_left_cancel

protected theorem add_right_cancel {x y z : Pos} : x + y = z + y → x = z := by
  by_toNat; exact Nat.add_right_cancel

protected theorem ne_add_self_left (x y : Pos) : x ≠ y + x := by
  induction x with
  | one =>
    symmetry
    exact Pos.succ_ne_one y
  | succ x H =>
    intro h
    rw [Pos.add_succ] at h
    apply H
    exact Pos.add_right_cancel h

protected theorem ne_add_self_right (x y : Pos) : x ≠ x + y := by
  induction x with
  | one =>
    symmetry
    rw [Pos.one_add_eq_add_one]
    exact Pos.succ_ne_one y
  | succ x H =>
    intro h
    rw [Pos.succ_add] at h
    apply H
    exact Pos.add_right_cancel h

@[simp] protected theorem one_mul (x : Pos) : 1 * x = x := by
  by_toNat; exact Nat.one_mul _

@[simp] protected theorem mul_one (x : Pos) : x * 1 = x := by
  by_toNat; exact Nat.mul_one _

protected theorem succ_mul (x y : Pos) : (x + 1) * y = x * y + y := by
  by_toNat; exact Nat.succ_mul ..

protected theorem mul_succ (x y : Pos) : x * (y + 1) = x * y + x := by
  by_toNat; exact Nat.mul_succ ..

protected theorem mul_assoc (x y z : Pos) : (x * y) * z = x * (y * z) := by
  by_toNat; exact Nat.mul_assoc ..

protected theorem mul_comm (x y : Pos) : x * y = y * x := by
  by_toNat; exact Nat.mul_comm ..

protected theorem mul_left_comm (x y z : Pos) : x * (y * z) = y * (x * z) := by
  by_toNat; exact Nat.mul_left_comm ..

protected theorem mul_right_comm (x y z : Pos) : (x * y) * z = (x * z) * y := by
  by_toNat; exact Nat.mul_right_comm ..

protected theorem left_distrib (x y z : Pos) : x * (y + z) = x * y + x * z := by
  by_toNat; exact Nat.left_distrib ..

protected theorem right_distrib (x y z : Pos) : (x + y) * z = x * z + y * z := by
  by_toNat; exact Nat.right_distrib ..

protected theorem mul_left_cancel {x y z : Pos} : x * y = x * z → y = z := by
  intro h
  induction y, z with
  | one_one => rfl
  | one_succ z _ =>
    rw [Pos.mul_one, Pos.mul_succ] at h
    absurd h
    apply Pos.ne_add_self_left
  | succ_one y _ =>
    rw [Pos.mul_one, Pos.mul_succ] at h
    absurd h.symm
    apply Pos.ne_add_self_left
  | succ_succ y z H =>
    rw [Pos.mul_succ, Pos.mul_succ] at h
    rw [H (Pos.add_right_cancel h)]

protected theorem mul_right_cancel {x y z : Pos} : x * y = z * y → x = z := by
  intro h
  induction x, z with
  | one_one => rfl
  | one_succ x _ =>
    rw [Pos.one_mul, Pos.succ_mul] at h
    absurd h
    apply Pos.ne_add_self_left
  | succ_one z _ =>
    rw [Pos.one_mul, Pos.succ_mul] at h
    absurd h.symm
    apply Pos.ne_add_self_left
  | succ_succ x z H =>
    rw [Pos.succ_mul, Pos.succ_mul] at h
    rw [H (Pos.add_right_cancel h)]

protected theorem pow_zero (x : Pos) : x ^ (0:Nat) = 1 := by
  by_toNat; exact Nat.pow_zero _

protected theorem pow_one (x : Pos) : x ^ (1:Nat) = x := by
  by_toNat; exact Nat.pow_one ..

protected theorem one_pow (x : Nat) : (1 : Pos) ^ x = 1 := by
  by_toNat; exact Nat.one_pow ..

protected theorem pow_succ (x : Pos) (y : Nat) : x ^ (y + 1) = x ^ y * x := by
  by_toNat; exact Nat.pow_succ ..

protected theorem pow_add (x : Pos) (y z : Nat) : x ^ (y + z) = x ^ y * x ^ z := by
  by_toNat; exact Nat.pow_add ..

protected theorem mul_pow (x y : Pos) (z : Nat) : (x * y) ^ z = x ^ z * y ^ z := by
  by_toNat; exact Nat.mul_pow ..

protected theorem pow_assoc (x : Pos) (y z : Nat) : (x ^ y) ^ z = x ^ (y * z) := by
  by_toNat; exact Nat.pow_assoc ..

protected theorem le_refl (x : Pos) : x ≤ x := by
  by_toNat; exact Nat.le_refl ..
instance : Relation.Reflexive (α:=Pos) (.≤.) := ⟨Pos.le_refl⟩

protected theorem le_trans {x y z : Pos} : x ≤ y → y ≤ z → x ≤ z := by
  by_toNat; exact Nat.le_trans
instance : Relation.Transitive (α:=Pos) (.≤.) := ⟨Pos.le_trans⟩

protected theorem le_antisymm {x y : Pos} : x ≤ y → y ≤ x → x = y := by
  by_toNat; exact Nat.le_antisymm
instance : Relation.Antisymmetric (α:=Pos) (.≤.) := ⟨Pos.le_antisymm⟩

protected theorem lt_irrefl (x : Pos) : ¬(x < x) := by
  by_toNat; exact Nat.lt_irrefl _
instance : Relation.Irreflexive (α:=Pos) (.<.) := ⟨Pos.lt_irrefl⟩

protected theorem lt_trans {x y z : Pos} : x < y → y < z → x < z := by
  by_toNat; exact Nat.lt_trans
instance : Relation.Transitive (α:=Pos) (.<.) := ⟨Pos.lt_trans⟩

protected theorem lt_of_le_of_lt {x y z : Pos} : x ≤ y → y < z → x < z := by
  by_toNat; exact Nat.lt_of_le_of_lt
instance : Relation.HTransitive (α:=Pos) (β:=Pos) (γ:=Pos) (.≤.) (.<.) (.<.) := ⟨Pos.lt_of_le_of_lt⟩

protected theorem lt_of_lt_of_le {x y z : Pos} : x < y → y ≤ z → x < z := by
  by_toNat; exact Nat.lt_of_lt_of_le
instance : Relation.HTransitive (α:=Pos) (β:=Pos) (γ:=Pos) (.<.) (.≤.) (.<.) := ⟨Pos.lt_of_lt_of_le⟩

protected theorem le_of_eq {x y : Pos} : x = y → x ≤ y := by
  by_toNat; exact Nat.le_of_eq

protected theorem le_of_lt {x y : Pos} : x < y → x ≤ y := by
  by_toNat; exact Nat.le_of_lt

protected theorem ne_of_lt {x y : Pos} : x < y → x ≠ y := by
  by_toNat; exact Nat.ne_of_lt

protected theorem lt_of_le_of_ne {x y : Pos} : x ≤ y → x ≠ y → x < y := by
  by_toNat; exact Nat.lt_of_le_of_ne

protected theorem le_of_not_gt {x y : Pos} : ¬ x > y → x ≤ y := by
  by_toNat; exact Nat.le_of_not_gt

protected theorem lt_of_not_ge {x y : Pos} : ¬ x ≥ y → x < y := by
  by_toNat; exact Nat.gt_of_not_le

protected theorem not_le_of_gt {x y : Pos} : x > y → ¬ x ≤ y := by
  by_toNat; exact Nat.not_le_of_gt

protected theorem not_lt_of_ge {x y : Pos} : x ≥ y → ¬ x < y := by
  by_toNat; exact Nat.not_lt_of_ge

protected theorem not_le_iff_gt (x y : Pos) : ¬ x ≤ y ↔ x > y :=
  Iff.intro Pos.lt_of_not_ge Pos.not_le_of_gt

protected theorem lt_iff_not_ge (x y : Pos) : x < y ↔ ¬ x ≥ y :=
  Iff.intro Pos.not_le_of_gt Pos.lt_of_not_ge

protected theorem not_lt_iff_ge (x y : Pos) : ¬ x < y ↔ x ≥ y :=
  Iff.intro Pos.le_of_not_gt Pos.not_lt_of_ge

protected theorem le_iff_not_gt (x y : Pos) : x ≤ y ↔ ¬ x > y :=
  Iff.intro Pos.not_lt_of_ge Pos.le_of_not_gt

protected theorem eq_or_lt_of_le {x y : Pos} : x ≤ y → x = y ∨ x < y := by
  by_toNat; exact Nat.eq_or_lt_of_le

protected abbrev le_total (x y : Pos) : x ≤ y ∨ x ≥ y := by
  by_toNat; exact Nat.le_total ..

protected theorem lt_or_ge (x y : Pos) : x < y ∨ x ≥ y := by
  by_toNat; exact Nat.lt_or_ge ..

protected theorem one_le (x : Pos) : 1 ≤ x := by
  by_toNat; apply Nat.succ_le_of_lt; exact Nat.is_pos _

protected theorem not_lt_one (x : Pos) : ¬(x < 1) := by
  by_toNat; intro h; absurd h; apply Nat.not_lt_of_ge; apply Nat.succ_le_of_lt; exact Nat.is_pos _

protected theorem one_lt_succ (x : Pos) : 1 < x + 1 := by
  by_toNat; apply Nat.succ_lt_succ; exact Nat.is_pos _

protected theorem not_succ_le_one (x : Pos) : ¬(x + 1 ≤ 1) := by
  by_toNat; intro h; absurd h; apply Nat.not_le_of_gt; apply Nat.succ_lt_succ; exact Nat.is_pos _

protected abbrev eq_one_of_le_one {x : Pos} : x ≤ 1 → x = 1 := by
  by_toNat; intro h; antisymmetry using LE.le; exact h; apply Nat.succ_le_of_lt; exact Nat.is_pos _

protected theorem le_succ_self (x : Pos) : x ≤ x + 1 := by
  by_toNat; exact Nat.le_add_right ..

protected theorem lt_succ_self (x : Pos) : x < x + 1 := by
  by_toNat; exact Nat.lt_succ_self ..

protected theorem not_succ_le_self (x : Pos) : ¬(x + 1 ≤ x) := by
  by_toNat; exact Nat.not_succ_le_self _

protected theorem not_succ_lt_self (x : Pos) : ¬(x + 1 < x) := by
  by_toNat; apply Nat.not_lt_of_ge; exact Nat.le_add_right ..

protected theorem le_of_lt_succ {x y : Pos} : x < y + 1 → x ≤ y := by
  by_toNat; exact Nat.le_of_lt_succ

protected theorem lt_succ_of_le {x y : Pos} : x ≤ y → x < y + 1 := by
  by_toNat; exact Nat.lt_succ_of_le

protected theorem lt_of_succ_le {x y : Pos} : x + 1 ≤ y → x < y := by
  by_toNat; exact Nat.lt_of_succ_le

protected theorem succ_le_of_lt {x y : Pos} : x < y → x + 1 ≤ y := by
  by_toNat; exact Nat.succ_le_of_lt

protected theorem le_succ_of_le {x y : Pos} : x ≤ y → x ≤ y + 1 := by
  by_toNat; exact Nat.le_succ_of_le

protected theorem le_of_succ_le {x y : Pos} : x + 1 ≤ y → x ≤ y := by
  by_toNat; exact Nat.le_of_succ_le

protected theorem succ_le_succ {x y : Pos} : x ≤ y → x + 1 ≤ y + 1 := by
  by_toNat; exact Nat.succ_le_succ

protected theorem le_of_succ_le_succ {x y : Pos} : x + 1 ≤ y + 1 → x ≤ y := by
  by_toNat; exact Nat.le_of_succ_le_succ

protected theorem succ_lt_succ {x y : Pos} : x < y → x + 1 < y + 1 := by
  by_toNat; exact Nat.succ_lt_succ

protected theorem lt_of_succ_lt_succ {x y : Pos} : x + 1 < y + 1 → x < y := by
  by_toNat; exact Nat.lt_of_succ_lt_succ

protected theorem lt_add_right (x y : Pos) : x < x + y := by
  induction y with
  | one => exact Pos.lt_succ_self x
  | succ y H => apply Pos.lt_trans H; rw [Pos.add_succ]; exact Pos.lt_succ_self (x + y)

protected theorem lt_add_left (x y : Pos) : x < y + x := by
  induction y with
  | one => rw [Pos.one_add_eq_add_one]; exact Pos.lt_succ_self x
  | succ y H => apply Pos.lt_trans H; rw [Pos.succ_add]; exact Pos.lt_succ_self (y + x)

protected theorem add_le_add_left {x y : Pos} : x ≤ y → ∀ z, z + x ≤ z + y := by
  by_toNat; intro h z; apply Nat.add_le_add_left h

protected theorem add_le_add_right {x y : Pos} : x ≤ y → ∀ z, x + z ≤ y + z := by
  by_toNat; intro h z; apply Nat.add_le_add_right h

protected theorem le_of_add_le_add_left {x y z : Pos} : z + x ≤ z + y → x ≤ y := by
  by_toNat; exact Nat.le_of_add_le_add_left

protected theorem le_of_add_le_add_right {x y z : Pos} : x + z ≤ y + z → x ≤ y := by
  by_toNat; exact Nat.le_of_add_le_add_right

protected theorem add_le_add {x₁ y₁ x₂ y₂ : Pos} : x₁ ≤ y₁ → x₂ ≤ y₂ → x₁ + x₂ ≤ y₁ + y₂ := by
  by_toNat; exact Nat.add_le_add

protected theorem add_lt_add_left {x y : Pos} : x < y → ∀ z, z + x < z + y := by
  by_toNat; intro h z; apply Nat.add_lt_add_left h

protected theorem add_lt_add_right {x y : Pos} : x < y → ∀ z, x + z < y + z := by
  by_toNat; intro h z; apply Nat.add_lt_add_right h

protected theorem lt_of_add_lt_add_left {x y z : Pos} : z + x < z + y → x < y := by
  by_toNat; exact Nat.lt_of_add_lt_add_left

protected theorem lt_of_add_lt_add_right {x y z : Pos} : x + z < y + z → x < y := by
  by_toNat; exact Nat.lt_of_add_lt_add_right

protected theorem add_lt_add {x₁ y₁ x₂ y₂ : Pos} : x₁ < y₁ → x₂ < y₂ → x₁ + x₂ < y₁ + y₂ := by
  by_toNat; exact Nat.add_lt_add

protected theorem mul_le_mul_left {x y : Pos} : x ≤ y → ∀ z, z * x ≤ z * y := by
  by_toNat; intro h z; apply Nat.mul_le_mul_left _ h

protected theorem mul_le_mul_right {x y : Pos} : x ≤ y → ∀ z, x * z ≤ y * z := by
  by_toNat; intro h z; apply Nat.mul_le_mul_right _ h

protected theorem le_of_mul_le_mul_left {x y z : Pos} : z * x ≤ z * y → x ≤ y := by
  by_toNat; intro h; exact Nat.le_of_mul_le_mul_of_pos_left (Nat.is_pos _) h

protected theorem le_of_mul_le_mul_right {x y z : Pos} : x * z ≤ y * z → x ≤ y := by
  by_toNat; intro h; exact Nat.le_of_mul_le_mul_of_pos_right (Nat.is_pos _) h

protected theorem mul_le_mul {x₁ y₁ x₂ y₂ : Pos} : x₁ ≤ y₁ → x₂ ≤ y₂ → x₁ * x₂ ≤ y₁ * y₂ := by
  by_toNat; exact Nat.mul_le_mul

protected theorem mul_lt_mul_left {x y : Pos} : x < y → ∀ z, z * x < z * y := by
  by_toNat; intro h z; apply Nat.mul_lt_mul_of_pos_left h; exact Nat.is_pos _

protected theorem mul_lt_mul_right {x y : Pos} : x < y → ∀ z, x * z < y * z := by
  by_toNat; intro h z; apply Nat.mul_lt_mul_of_pos_right h; exact Nat.is_pos _

protected theorem lt_of_mul_lt_mul_left {x y z : Pos} : z * x < z * y → x < y := by
  by_toNat; exact Nat.lt_of_mul_lt_mul_left _

protected theorem lt_of_mul_lt_mul_right {x y z : Pos} : x * z < y * z → x < y := by
  by_toNat; exact Nat.lt_of_mul_lt_mul_right _

protected theorem mul_lt_mul {x₁ y₁ x₂ y₂ : Pos} : x₁ < y₁ → x₂ < y₂ → x₁ * x₂ < y₁ * y₂ := by
  by_toNat; exact Nat.mul_lt_mul

protected theorem pow_le_pow_left {x y : Nat} : x ≤ y → (z : Pos) → z ^ x ≤ z ^ y := by
  by_toNat; intro h z; exact Nat.pow_le_pow_of_pos_left h (Nat.is_pos z)

protected theorem pow_le_pow_right {x y : Pos} : x ≤ y → (z : Nat) → x ^ z ≤ y ^ z := by
  by_toNat; exact Nat.pow_le_pow_left

protected theorem pow_lt_pow_of_pos_left {x y : Pos} : x < y → {z : Nat} → z > 0 → x ^ z < y ^ z := by
  by_toNat; exact Nat.pow_lt_pow_of_pos_right

protected theorem lt.dest {x y : Pos} : x < y → ∃ z, x + z = y := by
  intro h
  induction x, y with
  | one_one =>
    absurd h
    exact Pos.not_lt_one 1
  | one_succ y =>
    exists y
    exact Pos.one_add_eq_add_one y
  | succ_one x =>
    absurd h
    exact Pos.not_lt_one (x+1)
  | succ_succ x y H =>
    match H (Pos.lt_of_succ_lt_succ h) with
    | ⟨z, hz⟩ =>
      exists z
      rw [Pos.succ_add, hz]

protected theorem lt.intro {x y z : Pos} : x + z = y → x < y := by
  intro h; rw [←h]; exact Pos.lt_add_right x z

end Pos
