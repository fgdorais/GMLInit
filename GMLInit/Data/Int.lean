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
  | _+1 => rfl

theorem one_mk_zero : (1 ⊖ 0) = 1 := rfl

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

theorem nonNeg_mk (m n) : NonNeg (m ⊖ n) ↔ n ≤ m := by
  induction m, n with
  | zero_zero => 
    rw [zero_mk_zero]
    constr
    · intro; reflexivity
    · intro; apply NonNeg.mk
  | zero_succ n => 
    rw [zero_mk_succ]
    constr
    · intro; contradiction
    · intro; contradiction
  | succ_zero m => 
    rw [succ_mk_zero]
    constr
    · intro; apply Nat.zero_le
    · intro; apply NonNeg.mk
  | succ_succ m n ih => 
    rw [succ_mk_succ]
    rw [Nat.succ_le_succ_iff_le]
    exact ih

theorem mk_le_mk (m₁ n₁ m₂ n₂) : (m₁ ⊖ n₁) ≤ (m₂ ⊖ n₂) ↔ n₂ + m₁ ≤ m₂ + n₁ := by
  unfold LE.le Int.le
  rw [mk_sub_mk, nonNeg_mk]
  reflexivity

theorem mk_lt_mk (m₁ n₁ m₂ n₂) : (m₁ ⊖ n₁) < (m₂ ⊖ n₂) ↔ n₂ + m₁ < m₂ + n₁ := by
  unfold LT.lt Int.lt Nat.lt
  rw [←one_mk_zero, mk_add_mk, mk_le_mk, Nat.add_succ, Nat.add_zero]
  reflexivity

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

protected theorem neg_zero : -0 = 0 := rfl

protected theorem neg_neg (i : Int) : -(-i) = i := by
  cases i using Int.casesMkOn with
  | mk mi ni => rw [neg_mk, neg_mk]

protected theorem neg_add (i j : Int) : -(i + j) = -i + -j := by
  cases i using Int.casesMkOn with
  | mk mi ni => 
    cases j using Int.casesMkOn with
    | mk mj nj => 
      rw [mk_add_mk, neg_mk, neg_mk, neg_mk, mk_add_mk]

protected theorem add_neg_self_left (i : Int) : -i + i = 0 := by
  cases i using Int.casesMkOn with
  | mk mi ni => rw [neg_mk, mk_add_mk, Nat.add_comm mi ni, mk_self]

protected theorem add_neg_self_right (i : Int) : i + -i = 0 := by
  cases i using Int.casesMkOn with
  | mk mi ni => rw [neg_mk, mk_add_mk, Nat.add_comm mi ni, mk_self]

protected theorem sub_eq (i j : Int) : i - j = i + -j := rfl

protected theorem sub_zero (i : Int) : i - 0 = i := by
  rw [Int.sub_eq, Int.neg_zero, Int.add_zero]

protected theorem zero_sub (i : Int) : 0 - i = -i := by
  rw [Int.sub_eq, Int.zero_add]

protected theorem sub_self (i : Int) : i - i = 0 := by
  rw [Int.sub_eq, Int.add_neg_self_right]

protected theorem add_sub_assoc (i j k : Int) : (i + j) - k = i + (j - k) := calc
  _ = (i + j) + -k := by rw [Int.sub_eq]
  _ = i + (j + -k) := by rw [Int.add_assoc]
  _ = i + (j - k) := by rw [Int.sub_eq]

protected theorem sub_add_assoc (i j k : Int) : (i - j) + k = i - (j - k) := calc
  _ = (i + -j) + k := by rw [Int.sub_eq]
  _ = i + (-j + k) := by rw [Int.add_assoc]
  _ = i + (-j + -(-k)) := by rw [Int.neg_neg]
  _ = i + -(j + -k) := by rw [Int.neg_add]
  _ = i - (j - k) := by rw [Int.sub_eq, Int.sub_eq]

protected theorem add_sub_cancel (i j : Int) : (i + j) - j = i := calc
  _ = i + (j - j) := by rw [Int.add_sub_assoc]
  _ = i + 0 := by rw [Int.sub_self]
  _ = i := by rw [Int.add_zero]

protected theorem sub_add_cancel (i j : Int) : (i - j) + j = i := calc
  _ = i - (j - j) := by rw [Int.sub_add_assoc]
  _ = i - 0 := by rw [Int.sub_self]
  _ = i := by rw [Int.sub_zero]

protected theorem neg_sub (i j : Int) : -(i - j) = j - i := by
  rw [Int.sub_eq, Int.sub_eq, Int.neg_add, Int.neg_neg, Int.add_comm]

protected theorem add_left_cancel' (i : Int) {j k : Int} (h : i + j = i + k) : j = k := calc
  _ = 0 + j := by rw [Int.zero_add]
  _ = (-i + i) + j := by rw [Int.add_neg_self_left]
  _ = -i + (i + j) := by rw [Int.add_assoc]
  _ = -i + (i + k) := by rw [h]
  _ = (-i + i) + k := by rw [Int.add_assoc]
  _ = 0 + k := by rw [Int.add_neg_self_left]
  _ = k := by rw [Int.zero_add]

protected theorem add_right_cancel' (i : Int) {j k : Int} (h : j + i = k + i) : j = k := calc
  _ = j + 0 := by rw [Int.add_zero]
  _ = j + (i + -i) := by rw [Int.add_neg_self_right]
  _ = (j + i) + -i := by rw [Int.add_assoc]
  _ = (k + i) + -i := by rw [h]
  _ = k + (i + -i) := by rw [Int.add_assoc]
  _ = k + 0 := by rw [Int.add_neg_self_right]
  _ = k := by rw [Int.add_zero]

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

theorem le.intro (i : Int) (k : Nat) : i ≤ i + k :=
  show (NonNeg ((i+k)-i)) by
  rw [Int.sub_eq, Int.add_right_comm, Int.add_neg_self_right, Int.zero_add]
  apply NonNeg.mk

theorem le.dest {i j : Int} : i ≤ j → ∃ (k : Nat), j = i + k := by
  intro (h : NonNeg (j - i))
  match hk : j - i with
  | ofNat k => exists k; rw [←hk, Int.sub_eq, Int.add_left_comm, Int.add_neg_self_right, Int.add_zero]
  | negSucc _ => rw [hk] at h; contradiction

protected theorem le_refl (i : Int) : i ≤ i := by
  cases i using Int.casesMkOn with
  | mk ni mi => 
    rw [mk_le_mk, Nat.add_comm]
    reflexivity

protected theorem le_trans {i j k : Int} : i ≤ j → j ≤ k → i ≤ k := by
  intro hij hjk
  cases i using Int.casesMkOn with
  | mk ni mi =>
    cases j using Int.casesMkOn with
    | mk nj mj =>
      cases k using Int.casesMkOn with
      | mk nk mk =>
        rw [mk_le_mk] at hij hjk ⊢
        apply Nat.le_of_add_le_add_left' mj
        apply Nat.le_of_add_le_add_right' nj
        calc
        _ = (mj + mk) + (ni + nj) := by simp only [Nat.add_assoc]
        _ = (mj + ni) + (mk + nj) := by rw [Nat.add_cross_comm]
        _ ≤ (nj + mi) + (nk + mj) := by exact Nat.add_le_add hij hjk
        _ = (nk + mj) + (nj + mi) := by rw [Nat.add_comm]
        _ = (mj + nk) + (mi + nj) := by rw [Nat.add_comm nj, Nat.add_comm mj]
        _ = _ := by simp only [Nat.add_assoc]

protected theorem le_antisymm {i j : Int} : i ≤ j → j ≤ i → i = j := by
  intro hij hji
  match le.dest hij, le.dest hji with
  | ⟨a,ha⟩, ⟨b,hb⟩ => 
    rw [hb, Int.add_assoc] at ha
    have : b + a = 0 := by
      apply ofNat.inj
      apply Int.add_left_cancel' j
      symmetry
      transitivity j
      · exact Int.add_zero ..
      · exact ha
    rw [Nat.eq_zero_of_add_eq_zero_left this] at hb
    rw [hb]
    exact Int.add_zero ..

protected theorem le_total (i j : Int) : i ≤ j ∨ j ≤ i := by
  cases i using Int.casesMkOn with
  | mk ni mi =>
    cases j using Int.casesMkOn with
    | mk nj mj =>
      rw [mk_le_mk, mk_le_mk, Nat.add_comm mi, Nat.add_comm ni]
      exact Nat.le_total ..

protected theorem add_le_add_left {i j : Int} : i ≤ j → ∀ (k : Int), k + i ≤ k + j := by
  intro h k
  match le.dest h with
  | ⟨d, hd⟩ => 
    rw [hd, ←Int.add_assoc]
    exact le.intro ..
    
protected theorem add_le_add_right {i j : Int} : i ≤ j → ∀ (k : Int), i + k ≤ j + k := by
  intro h k
  match le.dest h with
  | ⟨d, hd⟩ => 
    rw [hd, Int.add_right_comm]
    exact le.intro ..

protected theorem sub_le_sub_right {i j : Int} : i ≤ j → ∀ (k : Int), i - k ≤ j - k := by
  intro h k
  rw [Int.sub_eq, Int.sub_eq]
  exact Int.add_le_add_right h ..

protected theorem le_of_add_le_add_right {i j k : Int} (h : i + k ≤ j + k) : i ≤ j := calc
  _ = (i + k) - k := by rw [Int.add_sub_cancel]
  _ ≤ (j + k) - k := Int.sub_le_sub_right h k
  _ = j := by rw [Int.add_sub_cancel]

protected theorem le_of_add_le_add_left {i j k : Int} (h : i + j ≤ i + k) : j ≤ k := by
  rw [Int.add_comm i, Int.add_comm i] at h
  apply Int.le_of_add_le_add_right h

protected theorem le_succ_self (i : Int) : i ≤ i + 1 := by
  apply le.intro

protected theorem lt_iff_succ_le (i j : Int) : i < j ↔ i + 1 ≤ j := Iff.rfl

protected theorem le_iff_lt_succ (i j : Int) : i ≤ j ↔ i < j + 1 := by
  rw [Int.lt_iff_succ_le]
  constr
  · apply Int.add_le_add_right (k:=1)
  · apply Int.le_of_add_le_add_right

protected theorem le_of_lt {i j : Int} : i < j → i ≤ j := by
  intro hlt
  rw [Int.lt_iff_succ_le] at hlt
  apply Int.le_trans (Int.le_succ_self i) hlt

protected theorem lt_of_lt_of_le {i j k : Int} : i < j → j ≤ k → i < k := by
  intro hij hjk
  rw [Int.lt_iff_succ_le] at hij ⊢
  exact Int.le_trans hij hjk

protected theorem lt_of_le_of_lt {i j k : Int} : i ≤ j → j < k → i < k := by
  intro hij hjk
  rw [Int.le_iff_lt_succ] at hij
  rw [Int.lt_iff_succ_le] at hjk
  exact Int.lt_of_lt_of_le hij hjk

protected theorem lt_irrefl (i : Int) : ¬ i < i := by
  induction i using Int.casesMkOn with
  | mk ni mi => rw [mk_lt_mk, Nat.add_comm]; exact Nat.lt_irrefl _

protected theorem lt_trans {i j k : Int} : i < j → j < k → i < k := by
  intro hij hjk
  rw [Int.lt_iff_succ_le] at hij ⊢
  apply Int.le_of_lt
  exact Int.lt_of_le_of_lt hij hjk

protected theorem le_or_gt (i j : Int) : i ≤ j ∨ j < i := by
  induction i using Int.casesMkOn with
  | mk mi ni =>
    induction j using Int.casesMkOn with
    | mk mj nj =>
      rw [mk_le_mk, mk_lt_mk]
      rw [Nat.add_comm mi, Nat.add_comm mj]
      exact Nat.le_or_gt ..

protected theorem lt_or_ge (i j : Int) : i < j ∨ j ≤ i := by
  cases Int.le_or_gt j i with
  | inl h => right; exact h
  | inr h => left; exact h

theorem lt_or_eq_of_le {i j : Int} : i ≤ j → i < j ∨ i = j := by
  intro hle
  match le.dest hle with
  | ⟨0, (h : j = i + 0)⟩ =>
    right
    rw [h, Int.add_zero]
  | ⟨n+1, (h : j = i + (ofNat n + 1))⟩ =>
    left
    rw [Int.lt_iff_succ_le]
    rw [h, ←Int.add_assoc, Int.add_right_comm]
    apply Int.le.intro

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

instance : Relation.Reflexive (α:=Int) (.≤.) := ⟨Int.le_refl⟩
instance : Relation.Transitive (α:=Int) (.≤.) := ⟨Int.le_trans⟩
instance : Relation.Antisymmetric (α:=Int) (.≤.) := ⟨Int.le_antisymm⟩
instance : Relation.Total (α:=Int) (.≤.) := ⟨Int.le_total⟩
instance : Relation.Irreflexive (α:=Int) (.<.) := ⟨Int.lt_irrefl⟩
instance : Relation.Transitive (α:=Int) (.<.) := ⟨Int.lt_trans⟩
instance : Relation.Comparison (α:=Int) (.<.) := ⟨Int.lt_compare⟩
instance : Relation.Connex (α:=Int) (.<.) := ⟨Int.lt_connex⟩
instance : Relation.HTransitive (α:=Int) (.≤.) (.<.) (.<.) := ⟨Int.lt_of_le_of_lt⟩
instance : Relation.HTransitive (α:=Int) (.<.) (.≤.) (.<.) := ⟨Int.lt_of_lt_of_le⟩

end Int
