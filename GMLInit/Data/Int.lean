import GMLInit.Data.Basic
import GMLInit.Data.Nat

namespace Int

attribute [local eliminator] Nat.recDiag

protected abbrev mk := Int.subNatNat

scoped infix:55 " ⊖ " => Int.mk

theorem zero_mk_zero : 0 ⊖ 0 = 0 := rfl

theorem zero_mk_succ (n) : (0 ⊖ n + 1) = Int.negSucc n := rfl

theorem succ_mk_zero (m) : (m + 1 ⊖ 0) = Int.ofNat (m+1) := by
  rw [Int.mk, Int.subNatNat, Nat.zero_sub, Nat.sub_zero]

theorem succ_mk_succ (m n) : (m + 1 ⊖ n + 1) = (m ⊖ n) := by
  rw [Int.mk, Int.subNatNat, Int.subNatNat, Nat.succ_sub_succ, Nat.succ_sub_succ]

theorem mk_zero (m) : (m ⊖ 0) = m := by
  rw [Int.mk, Int.subNatNat, Nat.zero_sub, Nat.sub_zero]

theorem zero_mk (n) : (0 ⊖ n) = negOfNat n :=
  match n with
  | 0 => rfl
  | n+1 => rfl

protected def recMk.{u} {motive : Int → Sort u} (mk : (m n : Nat) → motive (m ⊖ n)) : (i : Int) → motive i
| Int.ofNat m => mk_zero m ▸ mk m 0
| Int.negSucc n => mk 0 (n + 1)

protected def recMkOn.{u} {motive : Int → Sort u} (i : Int) (mk : (m n : Nat) → motive (m ⊖ n)) : motive i := Int.recMk mk i

protected def casesMkOn.{u} {motive : Int → Sort u} (i : Int) (mk : (m n : Nat) → motive (m ⊖ n)) : motive i := Int.recMk mk i

protected theorem add_zero (x : Int) : x + 0 = x :=
  match x with
  | ofNat _ => rfl
  | negSucc _ => rfl

protected theorem zero_add (x : Int) : 0 + x = x :=
  match x with
  | ofNat _ => show ofNat _ = ofNat _ by rw [Nat.zero_add]
  | negSucc _ => rfl

theorem mk_self (m) : (m ⊖ m) = 0 := by
  induction m with
  | zero => rfl
  | succ m ih => rw [succ_mk_succ]; exact ih

theorem add_mk_add_left (k m n) : (k + m ⊖ k + n) = (m ⊖ n) := by
  induction k with
  | zero => rw [Nat.zero_add, Nat.zero_add]
  | succ k ih => rw [Nat.succ_add', Nat.succ_add', succ_mk_succ]; exact ih

theorem add_mk_add_right (k m n) : (m + k ⊖ n + k) = (m ⊖ n) := by
  induction k with
  | zero => rw [Nat.add_zero, Nat.add_zero]
  | succ k ih => rw [Nat.add_succ' m k, Nat.add_succ' n k, succ_mk_succ]; exact ih

theorem mk_add_ofNat (m n k) : (m ⊖ n) + ofNat k = (m + k ⊖ n) := by
  induction m, n with
  | zero_zero => rw [zero_mk_zero, Int.zero_add, Nat.zero_add, mk_zero]
  | zero_succ n => rw [zero_mk_succ, Nat.zero_add]; rfl
  | succ_zero m => rw [succ_mk_zero, mk_zero]; rfl
  | succ_succ m n ih => rw [succ_mk_succ, Nat.succ_add', succ_mk_succ, ih]

theorem mk_add_negSucc (m n k) : (m ⊖ n) + negSucc k = (m ⊖ n + k + 1) := by
  induction m, n with
  | zero_zero => rw [zero_mk_zero, Int.zero_add, Nat.zero_add]; rfl
  | zero_succ n => rw [zero_mk_succ, zero_mk_succ, Nat.succ_add']; rfl
  | succ_zero m => rw [succ_mk_zero, Nat.zero_add]; rfl
  | succ_succ m n ih => rw [succ_mk_succ, Nat.succ_add', succ_mk_succ]; exact ih

theorem mk_add_mk (m₁ n₁ m₂ n₂) : (m₁ ⊖ n₁) + (m₂ ⊖ n₂) = (m₁ + m₂ ⊖ n₁ + n₂) := by
  induction m₂, n₂ with
  | zero_zero => rw [zero_mk_zero, Int.add_zero, Nat.add_zero, Nat.add_zero]
  | zero_succ n₂ => rw [zero_mk_succ, Nat.add_succ', mk_add_negSucc]; rfl
  | succ_zero m₂ => rw [mk_zero, mk_add_ofNat]; rfl
  | succ_succ m₂ n₂ ih => rw [succ_mk_succ, Nat.add_succ' m₁ m₂, Nat.add_succ' n₁ n₂, succ_mk_succ]; exact ih

theorem neg_mk (m n) : -(m ⊖ n) = (n ⊖ m) := by
  induction m, n with
  | zero_zero => rw [zero_mk_zero]; rfl
  | zero_succ n => rw [zero_mk_succ, succ_mk_zero]; rfl
  | succ_zero m => rw [succ_mk_zero, zero_mk_succ]; rfl
  | succ_succ m n ih => rw [succ_mk_succ, succ_mk_succ]; exact ih

theorem mk_sub_mk (m₁ n₁ m₂ n₂) : (m₁ ⊖ n₁) - (m₂ ⊖ n₂) = (m₁ + n₂ ⊖ n₁ + m₂) :=
  show (m₁ ⊖ n₁) + -(m₂ ⊖ n₂) = (m₁ + n₂ ⊖ n₁ + m₂) by rw [neg_mk, mk_add_mk]

protected theorem add_assoc (i j k : Int) : (i + j) + k = i + (j + k) := by
  cases i using Int.casesMkOn with
  | mk mi ni =>
    cases j using Int.casesMkOn with
    | mk mj nj =>
      cases k using Int.casesMkOn with
      | mk mk nk =>
        repeat rw [mk_add_mk]
        repeat rw [Nat.add_assoc]

protected theorem add_comm (i j : Int) : i + j = j + i := by
  cases i using Int.casesMkOn with
  | mk mi ni =>
    cases j using Int.casesMkOn with
    | mk mj nj =>
      repeat rw [mk_add_mk]
      rw [Nat.add_comm mi mj, Nat.add_comm ni nj]

protected theorem add_left_comm (i j k : Int) : i + (j + k) = j + (i + k) := calc
  _ = (i + j) + k := by rw [Int.add_assoc]
  _ = (j + i) + k := by rw [Int.add_comm i j]
  _ = j + (i + k) := by rw [Int.add_assoc]

protected theorem add_right_comm (i j k : Int) : (i + j) + k = (i + k) + j := calc
  _ = i + (j + k) := by rw [Int.add_assoc]
  _ = i + (k + j) := by rw [Int.add_comm j k]
  _ = (i + k) + j := by rw [Int.add_assoc]

protected theorem add_cross_comm (i₁ i₂ j₁ j₂ : Int) : (i₁ + i₂) + (j₁ + j₂) = (i₁ + j₁) + (i₂ + j₂) := calc
  _ = i₁ + (i₂ + (j₁ + j₂)) := by rw [Int.add_assoc]
  _ = i₁ + (j₁ + (i₂ + j₂)) := by rw [Int.add_left_comm i₂ j₁ j₂]
  _ = (i₁ + j₁) + (i₂ + j₂) := by rw [Int.add_assoc]

protected theorem add_neg (i : Int) : i + -i = 0 := by
  cases i using Int.casesMkOn with
  | mk mi ni => rw [neg_mk, mk_add_mk, Nat.add_comm mi ni, mk_self]

protected theorem neg_add (i : Int) : -i + i = 0 := by
  cases i using Int.casesMkOn with
  | mk mi ni => rw [neg_mk, mk_add_mk, Nat.add_comm mi ni, mk_self]

protected theorem mul_zero (i : Int) : i * 0 = 0 :=
  match i with
  | ofNat _ => rfl
  | negSucc _ => rfl

protected theorem zero_mul (i : Int) : 0 * i = 0 :=
  match i with
  | ofNat _ => show ofNat _ = ofNat _ by simp_arith
  | negSucc _ => show negOfNat _ = ofNat _ by simp_arith

protected theorem mul_one (i : Int) : i * 1 = i :=
  match i with
  | ofNat _ => show ofNat _ = ofNat _ by simp_arith
  | negSucc _ => show negSucc _ = negSucc _ by simp_arith

protected theorem one_mul (i : Int) : 1 * i = i :=
  match i with
  | ofNat _ => show ofNat _ = ofNat _ by simp_arith
  | negSucc _ => show negSucc _ = negSucc _ by simp_arith

theorem mk_mul_ofNat (m n k) : (m ⊖ n) * ofNat k = (m * k ⊖ n * k) := by
  induction m, n with
  | zero_zero => rw [Nat.zero_mul, zero_mk_zero, Int.zero_mul]
  | zero_succ n => rw [Nat.zero_mul, zero_mk, zero_mk]; rfl
  | succ_zero m => rw [Nat.zero_mul, mk_zero, mk_zero]; rfl
  | succ_succ m n ih => rw [Nat.succ_mul, Nat.succ_mul, succ_mk_succ, add_mk_add_right]; exact ih

theorem mk_mul_negSucc (m n k) : (m ⊖ n) * negSucc k = (n * (k + 1) ⊖ m * (k + 1)) := by
  induction m, n with
  | zero_zero => rw [Nat.zero_mul, zero_mk_zero, Int.zero_mul]
  | zero_succ n => rw [Nat.zero_mul, zero_mk, mk_zero]; rfl
  | succ_zero m => rw [Nat.zero_mul, mk_zero, zero_mk]; rfl
  | succ_succ m n ih => rw [Nat.succ_mul, Nat.succ_mul, succ_mk_succ, add_mk_add_right]; exact ih

theorem mk_mul_mk (m₁ n₁ m₂ n₂) : (m₁ ⊖ n₁) * (m₂ ⊖ n₂) = (m₁ * m₂ + n₁ * n₂ ⊖ m₁ * n₂ + n₁ * m₂) := by
  induction m₂, n₂ with
  | zero_zero => simp only [Nat.zero_mul, Nat.mul_zero, Nat.add_zero, Nat.zero_add, zero_mk_zero, Int.mul_zero]
  | zero_succ n₂ => simp only [Nat.zero_mul, Nat.mul_zero, Nat.add_zero, Nat.zero_add, zero_mk_succ, mk_mul_negSucc]
  | succ_zero m₂ => simp only [Nat.zero_mul, Nat.mul_zero, Nat.add_zero, Nat.zero_add, succ_mk_zero, mk_mul_ofNat, Nat.mul_comm]
  | succ_succ m₂ n₂ ih => simp only [Nat.mul_succ, Nat.succ_mul]; rw [succ_mk_succ, Nat.add_cross_comm _ m₁ _ n₁, Nat.add_cross_comm _ m₁ _ n₁, add_mk_add_right]; exact ih

protected theorem mul_assoc (i j k : Int) : (i * j) * k = i * (j * k) := by
  cases i using Int.casesMkOn with
  | mk mi ni =>
    cases j using Int.casesMkOn with
    | mk mj nj =>
      cases k using Int.casesMkOn with
      | mk mk nk =>
        repeat rw [mk_mul_mk]
        simp only [Nat.mul_add, Nat.add_mul, ←Nat.mul_assoc]
        simp only [Nat.add_cross_comm, Nat.add_comm]

protected theorem mul_comm (i j : Int) : i * j = j * i := by
  cases i using Int.casesMkOn with
  | mk mi ni =>
    cases j using Int.casesMkOn with
    | mk mj nj =>
      repeat rw [mk_mul_mk]
      simp only [Nat.add_comm, Nat.mul_comm]

protected theorem mul_left_comm (i j k : Int) : i * (j * k) = j * (i * k) := calc
  _ = (i * j) * k := by rw [Int.mul_assoc]
  _ = (j * i) * k := by rw [Int.mul_comm i j]
  _ = j * (i * k) := by rw [Int.mul_assoc]

protected theorem mul_right_comm (i j k : Int) : (i * j) * k = (i * k) * j := calc
  _ = i * (j * k) := by rw [Int.mul_assoc]
  _ = i * (k * j) := by rw [Int.mul_comm j k]
  _ = (i * k) * j := by rw [Int.mul_assoc]

protected theorem mul_cross_comm (i₁ i₂ j₁ j₂ : Int) : (i₁ * i₂) * (j₁ * j₂) = (i₁ * j₁) * (i₂ * j₂) := calc
  _ = i₁ * (i₂ * (j₁ * j₂)) := by rw [Int.mul_assoc]
  _ = i₁ * (j₁ * (i₂ * j₂)) := by rw [Int.mul_left_comm i₂ j₁ j₂]
  _ = (i₁ * j₁) * (i₂ * j₂) := by rw [Int.mul_assoc]

protected theorem mul_neg (i j : Int) : i * (-j) = -(i * j) := by
  cases i using Int.casesMkOn with
  | mk mi ni =>
    cases j using Int.casesMkOn with
    | mk mj nj =>
      rw [neg_mk, mk_mul_mk, mk_mul_mk, neg_mk]

protected theorem neg_mul (i j : Int) : (-i) * j = -(i * j) := by
  cases i using Int.casesMkOn with
  | mk mi ni =>
    cases j using Int.casesMkOn with
    | mk mj nj =>
      rw [neg_mk, mk_mul_mk, mk_mul_mk, neg_mk, Nat.add_comm (mi * nj), Nat.add_comm (ni * nj)]

protected theorem mul_add (i j k : Int) : i * (j + k) = i * j + i * k := by
  cases i using Int.casesMkOn with
  | mk mi ni =>
    cases j using Int.casesMkOn with
    | mk mj nj =>
      cases k using Int.casesMkOn with
      | mk mk nk =>
        simp only [mk_mul_mk, mk_add_mk, Nat.mul_add, Nat.add_mul]
        rw [Nat.add_cross_comm (mi * mj), Nat.add_cross_comm (mi * nj)]

protected theorem add_mul (i j k : Int) : (i + j) * k = i * k + j * k := by
  cases i using Int.casesMkOn with
  | mk mi ni =>
    cases j using Int.casesMkOn with
    | mk mj nj =>
      cases k using Int.casesMkOn with
      | mk mk nk =>
        simp only [mk_mul_mk, mk_add_mk, Nat.mul_add, Nat.add_mul]
        rw [Nat.add_cross_comm (mi * mk), Nat.add_cross_comm (mi * nk)]

protected theorem mul_sub (i j k : Int) : i * (j - k) = i * j - i * k :=
  show i * (j + -k) = i * j + -(i * k) by rw [Int.mul_add, Int.mul_neg]

protected theorem sub_mul (i j k : Int) : (i - j) * k = i * k - j * k :=
  show (i + -j) * k = i * k + -(j * k) by rw [Int.add_mul, Int.neg_mul]

end Int
