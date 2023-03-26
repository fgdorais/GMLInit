import GMLInit.Data.Fin.Basic

namespace Fin

def equivEmpty : Equiv (Fin 0) Empty where
  fwd := (nomatch .)
  rev := (nomatch .)
  spec {k} := nomatch k

def equivUnit : Equiv (Fin 1) Unit where
  fwd _ := ()
  rev _ := ⟨0, Nat.zero_lt_one⟩
  spec {k x} := match k, x with
  | ⟨0, _⟩, () => ⟨fun _ => rfl, fun _ => rfl⟩

def equivBool : Equiv (Fin 2) Bool where
  fwd
  | ⟨0, _⟩ => false
  | ⟨1, _⟩ => true
  rev
  | false => ⟨0, Nat.zero_lt_succ 1⟩
  | true => ⟨1, Nat.succ_lt_succ Nat.zero_lt_one⟩
  spec {k x} := match k, x with
  | ⟨0, _⟩, false  => ⟨fun _ => rfl, fun _ => rfl⟩
  | ⟨0, _⟩, true  => ⟨Bool.noConfusion, fun h => Nat.noConfusion (Fin.val_eq_of_eq h)⟩
  | ⟨1, _⟩, false  => ⟨Bool.noConfusion, fun h => Nat.noConfusion (Fin.val_eq_of_eq h)⟩
  | ⟨1, _⟩, true  => ⟨fun _ => rfl, fun _ => rfl⟩

def equivOrdering : Equiv (Fin 3) Ordering where
  fwd
  | ⟨0, _⟩ => .eq
  | ⟨1, _⟩ => .lt
  | ⟨2, _⟩ => .gt
  rev
  | .eq => ⟨0, Nat.zero_lt_succ 2⟩
  | .lt => ⟨1, Nat.succ_lt_succ (Nat.zero_lt_succ 1)⟩
  | .gt => ⟨2, Nat.succ_lt_succ (Nat.succ_lt_succ Nat.zero_lt_one)⟩
  spec {k x} := match k, x with
  | ⟨0, _⟩, .eq  => ⟨fun _ => rfl, fun _ => rfl⟩
  | ⟨0, _⟩, .lt  => ⟨Ordering.noConfusion, fun h => Nat.noConfusion (Fin.val_eq_of_eq h)⟩
  | ⟨0, _⟩, .gt  => ⟨Ordering.noConfusion, fun h => Nat.noConfusion (Fin.val_eq_of_eq h)⟩
  | ⟨1, _⟩, .eq  => ⟨Ordering.noConfusion, fun h => Nat.noConfusion (Fin.val_eq_of_eq h)⟩
  | ⟨1, _⟩, .lt  => ⟨fun _ => rfl, fun _ => rfl⟩
  | ⟨1, _⟩, .gt  => ⟨Ordering.noConfusion, fun h => Nat.noConfusion (Nat.succ.inj (Fin.val_eq_of_eq h))⟩
  | ⟨2, _⟩, .eq  => ⟨Ordering.noConfusion, fun h => Nat.noConfusion (Fin.val_eq_of_eq h)⟩
  | ⟨2, _⟩, .lt  => ⟨Ordering.noConfusion, fun h => Nat.noConfusion (Nat.succ.inj (Fin.val_eq_of_eq h))⟩
  | ⟨2, _⟩, .gt  => ⟨fun _ => rfl, fun _ => rfl⟩

def encodeOptionNone : Fin (n+1) := ⟨n, Nat.lt_succ_self n⟩

def encodeOptionSome : Fin n → Fin (n+1)
| ⟨i, hi⟩ => ⟨i, Nat.lt_trans hi (Nat.lt_succ_self n)⟩

def decodeOption : Fin (n+1) → Option (Fin n)
| ⟨k, _⟩ => if hk : k < n then some ⟨k, hk⟩ else none

def equivOption (n : Nat) : Equiv (Fin (n+1)) (Option (Fin n)) where
  fwd := decodeOption
  rev
  | some i => encodeOptionSome i
  | none => encodeOptionNone
  spec {k x} := match k, x with
  | ⟨k, hk⟩, some ⟨i, hi⟩ => by
    constr
    · intro h
      unfold decodeOption at h
      unfold encodeOptionSome
      simp at h ⊢
      split at h
      next =>
        cases h
        rfl
      next =>
        contradiction
    · intro h
      unfold decodeOption
      unfold encodeOptionSome at h
      simp at h ⊢
      cases h
      split
      next =>
        rfl
      next =>
        contradiction
  | ⟨k, hk⟩, none => by
    constr
    · intro h
      unfold decodeOption at h
      unfold encodeOptionNone
      simp at h ⊢
      split at h
      next =>
        contradiction
      next =>
        antisymmetry using LE.le
        · apply Nat.le_of_not_gt
          assumption
        · apply Nat.le_of_lt_succ
          assumption
    · intro h
      unfold decodeOption
      unfold encodeOptionNone at h
      simp at h ⊢
      cases h
      split
      next =>
        apply Nat.lt_irrefl n
        assumption
      next =>
        rfl

def encodeSumLeft : Fin m → Fin (m + n)
| ⟨i, hi⟩ => ⟨i, Nat.lt_of_lt_of_le hi (Nat.le_add_right m n)⟩

def encodeSumRight : Fin n → Fin (m + n)
| ⟨j, hj⟩ => ⟨m + j, Nat.add_lt_add_left hj m⟩

def decodeSum : Fin (m + n) → Sum (Fin m) (Fin n)
| ⟨k, hk⟩ =>
  if hkm : k < m then
    Sum.inl ⟨k, hkm⟩
  else
    have hn : n > 0 := by
      by_contradiction
      | assuming h =>
        have h : n = 0 := Nat.eq_zero_of_le_zero (Nat.le_of_not_gt h)
        cases h
        contradiction
    have hkm : k - m < n := by
      rw [Nat.sub_lt_iff_lt_add_of_pos k m n hn]
      exact hk
    Sum.inr ⟨k - m, hkm⟩

def equivSum (m n : Nat) : Equiv (Fin (m + n)) (Sum (Fin m) (Fin n)) where
  fwd := decodeSum
  rev
  | .inl x => encodeSumLeft x
  | .inr y => encodeSumRight y
  spec {k x} := match k, x with
  | ⟨k, hk⟩, .inl ⟨i, hi⟩ => by
    constr
    · intro h
      unfold decodeSum at h
      unfold encodeSumLeft
      simp at h ⊢
      split at h
      next =>
        cases h
        rfl
      next =>
        contradiction
    · intro h
      unfold decodeSum
      unfold encodeSumLeft at h
      simp at h ⊢
      cases h
      split
      next =>
        rfl
      next =>
        contradiction
  | ⟨k, hk⟩, .inr ⟨j, hj⟩ => by
    constr
    · intro h
      unfold decodeSum at h
      unfold encodeSumRight
      simp at h ⊢
      split at h
      next =>
        contradiction
      next =>
        cases h
        rw [Nat.add_sub_cancel']
        apply Nat.le_of_not_gt
        assumption
    · intro h
      unfold decodeSum
      unfold encodeSumRight at h
      simp at h ⊢
      cases h
      split
      next h =>
        absurd h
        apply Nat.not_lt_of_ge
        exact Nat.le_add_right ..
      next =>
        congr
        exact Nat.add_sub_cancel_left ..

def encodeProd : Fin m × Fin n → Fin (m * n)
| (⟨i, hi⟩, ⟨j,hj⟩) => Fin.mk (n * i + j) $ calc
  _ < n * i + n := Nat.add_lt_add_left hj ..
  _ = n * (i + 1) := Nat.mul_succ ..
  _ ≤ n * m := Nat.mul_le_mul_left n (Nat.succ_le_of_lt hi)
  _ = m * n := Nat.mul_comm ..

def decodeProdLeft : Fin (m * n) → Fin m
| ⟨k, hk⟩ =>
  have hn : n > 0 := by
    apply Nat.pos_of_nonzero
    intro hz
    rw [hz, Nat.mul_zero] at hk
    contradiction
  Fin.mk (k / n) $ by rw [Nat.div_lt_iff_lt_mul hn]; exact hk

def decodeProdRight : Fin (m * n) → Fin n
| ⟨k, hk⟩ =>
  have hn : n > 0 := by
    apply Nat.pos_of_nonzero
    intro hz
    rw [hz, Nat.mul_zero] at hk
    contradiction
  ⟨k % n, Nat.mod_lt k hn⟩

abbrev decodeProd (k : Fin (m * n)) := (decodeProdLeft k, decodeProdRight k)

def equivProd (m n : Nat) : Equiv (Fin (m * n)) (Fin m × Fin n) where
  fwd := decodeProd
  rev := encodeProd
  spec {k x} := match k, x with
  | ⟨k, hk⟩, (⟨i,hi⟩, ⟨j,hj⟩) => by
    constr
    · intro h
      unfold decodeProd decodeProdLeft decodeProdRight at h
      unfold encodeProd
      simp at h ⊢
      cases h with
      | intro hl hr =>
        cases hl
        cases hr
        exact Nat.div_add_mod ..
    · intro h
      unfold decodeProd decodeProdLeft decodeProdRight
      unfold encodeProd at h
      simp at h ⊢
      cases h
      have hn : n > 0 := by
        apply Nat.pos_of_nonzero
        intro hz
        rw [hz, Nat.mul_zero] at hk
        contradiction
      constr
      · rw [Nat.add_comm]
        rw [Nat.add_mul_div_left _ _ hn]
        rw [Nat.div_eq_of_lt hj]
        rw [Nat.zero_add]
      · rw [Nat.add_comm]
        rw [Nat.add_mul_mod_self_left]
        rw [Nat.mod_eq_of_lt hj]

def encodeFun : {m : Nat} → (Fin m → Fin n) → Fin (n ^ m)
| 0, _ => Fin.mk 0 $ by rw [Nat.pow_zero n]; exact Nat.zero_lt_one
| m+1, f => Fin.mk (n * (encodeFun fun k => f k.succ).val + (f 0).val) $ calc
  _ < n * (encodeFun fun k => f k.succ).val + n := Nat.add_lt_add_left (f 0).isLt _
  _ = n * ((encodeFun fun k => f k.succ).val + 1) := Nat.mul_succ ..
  _ ≤ n * n ^ m := Nat.mul_le_mul_left n (Nat.succ_le_of_lt (encodeFun fun k => f k.succ).isLt)
  _ = n ^ m * n := Nat.mul_comm ..
  _ = n ^ (m+1) := Nat.pow_succ ..

def decodeFun : {m : Nat} → Fin (n ^ m) → Fin m → Fin n
| 0, _ => (nomatch .)
| m+1, ⟨k, hk⟩ =>
  have hn : n > 0 := by
    apply Nat.pos_of_nonzero
    intro h
    rw [h, Nat.pow_succ, Nat.mul_zero] at hk
    contradiction
  fun
  | ⟨0, _⟩ => ⟨k % n, Nat.mod_lt k hn⟩
  | ⟨i+1, hi⟩ =>
    have h : k / n < n ^ m := by rw [Nat.div_lt_iff_lt_mul hn]; exact hk
    decodeFun ⟨k / n, h⟩ ⟨i, Nat.lt_of_succ_lt_succ hi⟩

theorem specFun (k : Fin (n ^ m)) (x : Fin m → Fin n) :
  decodeFun k = x ↔ encodeFun x = k := by
  induction m with
  | zero =>
    match k with
    | ⟨0, _⟩ =>
      constr
      · intro | rfl => rfl
      · intro; funext ⟨_,_⟩; contradiction
  | succ m ih =>
    have ih1 : decodeFun (encodeFun (fun k => x (succ k))) = fun k => x (succ k) := by rw [ih]
    match k with
    | ⟨k, hk⟩ =>
      have hnpos : n > 0 := by
        apply Nat.pos_of_nonzero
        intro h
        rw [h] at hk
        contradiction
      constr
      · intro h
        clean at h
        unfold encodeFun
        apply Fin.eq
        clean
        transitivity (n * (k / n) + k % n)
        · congr
          · have : k / n < n ^ m := by rw [Nat.div_lt_iff_lt_mul hnpos]; exact hk
            have : (encodeFun fun k => x (succ k)) = ⟨k / n, this⟩ := by rw [←ih, ←h]; rfl
            erw [this]
            done
          · rw [←h]
            unfold decodeFun
            clean
            split
            next => rfl
            next heq => injection heq; contradiction
        · rw [Nat.add_comm]
          exact Nat.mod_add_div ..
      · intro h
        unfold encodeFun at h
        injection h with h
        unfold decodeFun
        funext ⟨i, hi⟩
        clean
        split
        next heq =>
          cases heq
          apply Fin.eq
          simp only [←h]
          rw [Nat.add_comm]
          rw [Nat.add_mul_mod_self_left]
          rw [Nat.mod_eq_of_lt (x 0).isLt]
          rfl
        next i _ heq =>
          cases heq
          rw [Nat.add_comm] at h
          have : (encodeFun fun k => x (succ k)) = k / n := by
            rw [←h]
            rw [Nat.add_mul_div_left (H := hnpos)]
            rw [Nat.div_eq_of_lt (x 0).isLt]
            rw [Nat.zero_add]
            rfl
          transitivity ((decodeFun (encodeFun fun k => x (succ k))) ⟨i, Nat.lt_of_succ_lt_succ hi⟩)
          · congr
            rw [←h]
            rw [Nat.add_mul_div_left (H := hnpos)]
            rw [Nat.div_eq_of_lt (x 0).isLt]
            rw [Nat.zero_add]
            rfl
          · rw [ih1]
            rfl

def equivFun (n m : Nat) : Equiv (Fin (n ^ m)) (Fin m → Fin n) where
  fwd := decodeFun
  rev := encodeFun
  spec {k x} := specFun k x

def sum : {n : Nat} → (Fin n → Nat) → Nat
| 0, _ => 0
| n+1, f => f ⟨0, Nat.zero_lt_succ n⟩ + sum fun ⟨i, hi⟩ => f ⟨i+1, Nat.succ_lt_succ hi⟩

def encodeSigma (f : Fin n → Nat) (x : (i : Fin n) × Fin (f i)) : Fin (sum f) :=
  match n, f, x with
  | _+1, _, ⟨⟨0, _⟩, ⟨j, hj⟩⟩ =>
    ⟨j, Nat.lt_of_lt_of_le hj (Nat.le_add_right ..)⟩
  | n+1, f, ⟨⟨i+1, hi⟩, ⟨j, hj⟩⟩ =>
    match encodeSigma (fun ⟨i, hi⟩ => f ⟨i+1, Nat.succ_lt_succ hi⟩) ⟨⟨i, Nat.lt_of_succ_lt_succ hi⟩, ⟨j, hj⟩⟩ with
    | ⟨k, hk⟩ => ⟨f ⟨0, Nat.zero_lt_succ n⟩ + k, Nat.add_lt_add_left hk ..⟩

def decodeSigma (f : Fin n → Nat) (k : Fin (sum f)) : (i : Fin n) × Fin (f i) :=
  match n, f, k with
  | n+1, f, ⟨k, hk⟩ =>
    if hk0 : k < f ⟨0, Nat.zero_lt_succ n⟩ then
      ⟨⟨0, Nat.zero_lt_succ n⟩, ⟨k, hk0⟩⟩
    else
      have hpos : 0 < sum fun ⟨i, hi⟩ => f ⟨i+1, Nat.succ_lt_succ hi⟩ := by
        apply Nat.pos_of_nonzero
        intro hz
        rw [sum, hz, Nat.add_zero] at hk
        contradiction
      have hkf : k - f ⟨0, Nat.zero_lt_succ n⟩ < sum fun ⟨i, hi⟩ => f ⟨i+1, Nat.succ_lt_succ hi⟩ := by
        rw [Nat.sub_lt_iff_lt_add_of_pos _ _ _ hpos]
        exact hk
      match decodeSigma (fun ⟨i, hi⟩ => f ⟨i+1, Nat.succ_lt_succ hi⟩) ⟨k - f ⟨0, Nat.zero_lt_succ n⟩, hkf⟩ with
      | ⟨⟨i, hi⟩, j⟩ => ⟨⟨i+1, Nat.succ_lt_succ hi⟩, j⟩

theorem specSigma (f : Fin n → Nat) (k : Fin (sum f)) (x : (i : Fin n) × Fin (f i)) : decodeSigma f k = x ↔ encodeSigma f x = k := by
  induction n with
  | zero => match k, x with | ⟨_, _⟩, _ => contradiction
  | succ n ih =>
    match k, x with
    | ⟨k, hk⟩, ⟨⟨0, _⟩, ⟨_,_⟩⟩ =>
      constr
      · intro h
        unfold decodeSigma at h
        congr
        split at h
        next => cases h; rfl
        next => cases h
      · intro h
        unfold decodeSigma
        cases h
        split
        next => rfl
        next => contradiction
    | ⟨k, hk⟩, ⟨⟨i+1, hi⟩, ⟨j, hj⟩⟩ =>
      constr
      · intro h
        simp only [decodeSigma] at h
        split at h
        next => cases h
        next hge =>
          have hge := Nat.ge_of_not_lt hge
          have hpos : 0 < sum fun ⟨i, hi⟩ => f ⟨i+1, Nat.succ_lt_succ hi⟩ := by
            apply Nat.pos_of_nonzero
            intro hz
            rw [Fin.sum, hz, Nat.add_zero] at hk
            contradiction
          have hk' : k - f ⟨0, Nat.zero_lt_succ n⟩ < sum fun ⟨i, hi⟩ => f ⟨i+1, Nat.succ_lt_succ hi⟩ := by
            rw [Nat.sub_lt_iff_lt_add_of_pos _ _ _ hpos]
            exact hk
          have : encodeSigma (fun ⟨i,hi⟩ => f ⟨i+1, Nat.succ_lt_succ hi⟩) ⟨⟨i, Nat.lt_of_succ_lt_succ hi⟩, ⟨j, hj⟩⟩ = ⟨k - f ⟨0, Nat.zero_lt_succ n⟩, hk'⟩ := by
            rw [←ih]
            injection h with h1 h2
            cases h1
            apply Sigma.eq
            · rfl
            · exact h2
          simp [encodeSigma]
          transitivity (f ⟨0, Nat.zero_lt_succ n⟩ + (encodeSigma (fun ⟨i,hi⟩ => f ⟨i+1, Nat.succ_lt_succ hi⟩) ⟨⟨i, Nat.lt_of_succ_lt_succ hi⟩, ⟨j, hj⟩⟩).val)
          · rfl
          · rw [this]
            rw [Nat.add_comm, Nat.sub_add_cancel]
            exact hge
      · intro h
        simp only [decodeSigma]
        simp only [encodeSigma] at h
        split
        next hlt =>
          cases h
          absurd hlt
          apply Nat.not_lt_of_ge
          exact Nat.le_add_right ..
        next hge =>
          have hge := Nat.ge_of_not_lt hge
          have hpos : 0 < sum fun ⟨i, hi⟩ => f ⟨i+1, Nat.succ_lt_succ hi⟩ := by
            apply Nat.pos_of_nonzero
            intro hz
            rw [Fin.sum, hz] at hk
            contradiction
          have hk' : k - f ⟨0, Nat.zero_lt_succ n⟩ < sum fun ⟨i, hi⟩ => f ⟨i+1, Nat.succ_lt_succ hi⟩ := by
            rw [Nat.sub_lt_iff_lt_add_of_pos _ _ _ hpos]
            exact hk
          have : decodeSigma (fun ⟨i,hi⟩ => f ⟨i+1, Nat.succ_lt_succ hi⟩) ⟨k - f ⟨0, Nat.zero_lt_succ n⟩, hk'⟩ = ⟨⟨i, Nat.lt_of_succ_lt_succ hi⟩, ⟨j,hj⟩⟩ := by
            rw [ih]
            cases h
            apply Fin.eq
            clean
            rw [Nat.add_sub_cancel_left]
            rfl
          congr 1
          · apply Fin.eq
            transitivity ((decodeSigma (fun ⟨i,hi⟩ => f ⟨i+1, Nat.succ_lt_succ hi⟩) ⟨k - f ⟨0, Nat.zero_lt_succ n⟩, hk'⟩).1.1+1)
            · rfl
            · rw [this]
          · have t' : (decodeSigma (fun ⟨i,hi⟩ => f ⟨i+1, Nat.succ_lt_succ hi⟩) ⟨k - f ⟨0, Nat.zero_lt_succ n⟩, hk'⟩).fst.val = i := by
              rw [this]
            cases t'
            apply heq_of_eq
            transitivity ((decodeSigma (fun ⟨i,hi⟩ => f ⟨i+1, Nat.succ_lt_succ hi⟩) ⟨k - f ⟨0, Nat.zero_lt_succ n⟩, hk'⟩).2)
            · apply Fin.eq
              rfl
            · apply Fin.eq
              clean
              rw [this]

def equivSigma (f : Fin n → Nat) : Equiv (Fin (sum f)) ((i : Fin n) × Fin (f i)) where
  fwd := decodeSigma f
  rev := encodeSigma f
  spec {k x} := specSigma f k x

def prod : {n : Nat} → (Fin n → Nat) → Nat
| 0, _ => 1
| n+1, f => f ⟨0, Nat.zero_lt_succ n⟩ * prod fun ⟨i, hi⟩ => f ⟨i+1, Nat.succ_lt_succ hi⟩

def encodePi (f : Fin n → Nat) (x : (i : Fin n) → Fin (f i)) : Fin (prod f) :=
  match n, f, x with
  | 0, _, _ => ⟨0, Nat.zero_lt_one⟩
  | n+1, f, x =>
    match encodePi (fun ⟨i, hi⟩ => f ⟨i+1, Nat.succ_lt_succ hi⟩) (fun ⟨i, hi⟩ => x ⟨i+1, Nat.succ_lt_succ hi⟩) with
    | ⟨k, hk⟩ => Fin.mk (f ⟨0, Nat.zero_lt_succ n⟩ * k + (x ⟨0, Nat.zero_lt_succ n⟩).val) $ calc
      _ < f ⟨0, Nat.zero_lt_succ n⟩ * k + f ⟨0, Nat.zero_lt_succ n⟩ := Nat.add_lt_add_left (x ⟨0, Nat.zero_lt_succ n⟩).isLt ..
      _ = f ⟨0, Nat.zero_lt_succ n⟩ * (k + 1) := Nat.mul_succ ..
      _ ≤ f ⟨0, Nat.zero_lt_succ n⟩ * prod fun ⟨i, hi⟩ => f ⟨i+1, Nat.succ_lt_succ hi⟩ := Nat.mul_le_mul_left _ (Nat.succ_le_of_lt hk)

def decodePi (f : Fin n → Nat) (k : Fin (prod f)) : (i : Fin n) → Fin (f i) :=
  match n, f, k with
  | 0, _, _ => (nomatch .)
  | n+1, f, ⟨k, hk⟩ =>
    have hf : f ⟨0, Nat.zero_lt_succ n⟩ > 0 := by
      apply Nat.pos_of_nonzero
      intro h
      rw [prod, h, Nat.zero_mul] at hk
      contradiction
    have hk' : k / f ⟨0, Nat.zero_lt_succ n⟩ < prod fun ⟨i, hi⟩ => f ⟨i+1, Nat.succ_lt_succ hi⟩ := by
      rw [Nat.div_lt_iff_lt_mul hf, Nat.mul_comm]
      exact hk
    match decodePi (fun ⟨i, hi⟩ => f ⟨i+1, Nat.succ_lt_succ hi⟩) ⟨k / f ⟨0, Nat.zero_lt_succ n⟩, hk'⟩ with
    | x => fun
      | ⟨0, _⟩ => ⟨k % f ⟨0, Nat.zero_lt_succ n⟩, Nat.mod_lt k hf⟩
      | ⟨i+1, hi⟩ => x ⟨i, Nat.lt_of_succ_lt_succ hi⟩

theorem specPi (f : Fin n → Nat) (k : Fin (prod f)) (x : (i : Fin n) → Fin (f i)) :
  decodePi f k = x ↔ encodePi f x = k := by
    induction n with
    | zero =>
      constr
      · intro
        match k with
        | ⟨0, _⟩ => rfl
      · intro
        funext ⟨_,_⟩
        contradiction
    | succ n ih =>
      constr
      · intro h
        match k with
        | ⟨k, hk⟩ =>
          apply Fin.eq
          simp only [encodePi]
          transitivity (f ⟨0, Nat.zero_lt_succ n⟩ * (k / f ⟨0, Nat.zero_lt_succ n⟩) + k % f ⟨0, Nat.zero_lt_succ n⟩)
          · congr 1
            · congr 1
              have hpos : f ⟨0, Nat.zero_lt_succ n⟩ > 0 := by
                apply Nat.pos_of_nonzero
                intro hz
                rw [Fin.prod, hz, Nat.zero_mul] at hk
                contradiction
              have hk' : k / f ⟨0, Nat.zero_lt_succ n⟩ < Fin.prod fun k => f (succ k) := by
                rw [Nat.div_lt_iff_lt_mul hpos]
                rw [Nat.mul_comm]
                exact hk
              have : encodePi (fun i => f (succ i)) (fun i => x (succ i)) = ⟨k / f ⟨0, Nat.zero_lt_succ n⟩, hk'⟩ := by
                rw [←ih]
                funext i
                rw [←h]
                rfl
              transitivity (encodePi (fun i => f (succ i)) (fun i => x (succ i))).val
              · rfl
              · rw [this]
            · rw [←h]
              rfl
          · rw [Nat.add_comm]
            exact Nat.mod_add_div ..
      · intro h
        funext i
        simp only [decodePi]
        split
        next =>
          apply Fin.eq
          clean
          rw [←h]
          simp only [encodePi]
          rw [Nat.add_comm]
          rw [Nat.add_mul_mod_self_left]
          rw [Nat.mod_eq_of_lt]
          exact (x ⟨0, Nat.zero_lt_succ n⟩).isLt
        next i hi =>
          match k with
          | ⟨k, hk⟩ =>
            simp only [encodePi] at h
            apply Fin.eq
            have hpos : f ⟨0, Nat.zero_lt_succ n⟩ > 0 := by
              apply Nat.pos_of_nonzero
              intro hz
              rw [Fin.prod, hz, Nat.zero_mul] at hk
              contradiction
            have hk' : k / f ⟨0, Nat.zero_lt_succ n⟩ < Fin.prod fun k => f (succ k) := by
              rw [Nat.div_lt_iff_lt_mul hpos]
              rw [Nat.mul_comm]
              exact hk
            have : decodePi (fun i => f (succ i)) ⟨k / f ⟨0, Nat.zero_lt_succ n⟩, hk'⟩ = fun i => x (succ i) := by
              rw [ih]
              cases h
              apply Fin.eq
              clean
              rw [Nat.add_comm]
              rw [Nat.add_mul_div_left _ _ hpos]
              rw [Nat.div_eq_of_lt (x ⟨0, Nat.zero_lt_succ n⟩).isLt]
              rw [Nat.zero_add]
              rfl
            clean
            transitivity (decodePi (fun i => f (succ i)) ⟨k / f ⟨0, Nat.zero_lt_succ n⟩, hk'⟩ ⟨i, Nat.lt_of_succ_lt_succ hi⟩).val
            · rfl
            · rw [this]
              rfl

def equivPi (f : Fin n → Nat) : Equiv (Fin (prod f)) ((i : Fin n) → Fin (f i)) where
  fwd := decodePi f
  rev := encodePi f
  spec {k x} := specPi f k x

def count (p : Fin n → Prop) [DecidablePred p] : Nat :=
  sum fun i => if p i then 1 else 0

def encodeSubtype (p : Fin n → Prop) [inst : DecidablePred p] (i : { i // p i }) : Fin (count p) :=
  match n, p, inst, i with
  | n+1, p, inst, ⟨⟨0, _⟩, hp⟩ =>
    have : count p > 0 := by simp_arith only [count, sum, if_pos hp]
    ⟨0, this⟩
  | n+1, p, inst, ⟨⟨i+1, hi⟩, hp⟩ =>
    match encodeSubtype (fun i => p (succ i)) ⟨⟨i, Nat.lt_of_succ_lt_succ hi⟩, hp⟩ with
    | ⟨k, hk⟩ =>
      if h0 : p ⟨0, Nat.zero_lt_succ n⟩ then
        have : count p = count (fun i => p (succ i)) + 1 := by
          simp_arith only [count, sum, if_pos h0]; rfl
        this ▸ ⟨k+1, Nat.succ_lt_succ hk⟩
      else
        have : count p = count (fun i => p (succ i)) := by
          simp_arith only [count, sum, if_neg h0]; rfl
        this ▸ ⟨k, hk⟩

def decodeSubtype (p : Fin n → Prop) [inst : DecidablePred p] (k : Fin (count p)) : { i // p i } :=
  match n, p, inst, k with
  | n+1, p, inst, ⟨k, hk⟩ =>
    if h0 : p ⟨0, Nat.zero_lt_succ n⟩ then
      have : count p = count (fun i => p (succ i)) + 1 := by
        simp_arith only [count, sum, if_pos h0]; rfl
      match k with
      | 0 => ⟨⟨0, Nat.zero_lt_succ n⟩, h0⟩
      | k + 1 =>
        match decodeSubtype (fun i => p (succ i)) ⟨k, Nat.lt_of_succ_lt_succ' (this ▸ hk)⟩ with
        | ⟨⟨i, hi⟩, hp⟩ => ⟨⟨i+1, Nat.succ_lt_succ hi⟩, hp⟩
    else
      have : count p = count (fun i => p (succ i)) := by
        simp_arith only [count, sum, if_neg h0]; rfl
      match decodeSubtype (fun i => p (succ i)) ⟨k, this ▸ hk⟩ with
      | ⟨⟨i, hi⟩, hp⟩ => ⟨⟨i+1, Nat.succ_lt_succ hi⟩, hp⟩

theorem specSubtype (p : Fin n → Prop) [inst : DecidablePred p] (k : Fin (count p)) (i : { i // p i }) :
  decodeSubtype p k = i ↔ encodeSubtype p i = k := by
  induction n with
  | zero =>
    simp [count, sum] at k
    cases k
    contradiction
  | succ n ih =>
    constr
    · intro h
      simp only [decodeSubtype] at h
      split at h
      next h0 =>
        have : count p = count (fun i => p (succ i)) + 1 := by
          simp_arith only [count, sum, if_pos h0]; rfl
        split at h
        next =>
          cases h
          simp only [encodeSubtype]
          apply Fin.eq
          symmetry
          assumption
        next heq _ =>
          cases h
          simp only [encodeSubtype, dif_pos h0]
          apply Fin.eq
          simp only [val_ndrec]
          match k with
          | ⟨0, _⟩ => contradiction
          | ⟨k+1, hk⟩ =>
            cases heq
            congr 1
            transitivity (Fin.mk k (Nat.lt_of_succ_lt_succ (this ▸ hk))).val
            · apply Fin.val_eq_of_eq
              rw [←ih]
              rfl
            · rfl
      next h0 =>
        have : count p = count (fun i => p (succ i)) := by
          simp_arith only [count, sum, if_neg h0]; rfl
        match k, i with
        | ⟨_, _⟩, ⟨⟨0, _⟩, _⟩ => contradiction
        | ⟨k, hk⟩, ⟨⟨i+1, hi⟩, hp⟩ =>
          apply Fin.eq
          simp only [encodeSubtype, dif_neg h0, val_ndrec]
          clean at h
          transitivity (Fin.mk k (this ▸ hk)).val
          · apply Fin.val_eq_of_eq
            rw [←ih]
            cases h
            rfl
          · rfl
    · intro h
      simp only [decodeSubtype]
      split
      next h0 =>
        have : count p = count (fun i => p (succ i)) + 1 := by
          simp_arith only [count, sum, if_pos h0]; rfl
        split
        next heq _ =>
          match k, i with
          | ⟨_,_⟩, ⟨⟨0,_⟩, _⟩ => rfl
          | ⟨k,hk⟩, ⟨⟨i+1,hi⟩, hp⟩ =>
            cases heq
            simp only [encodeSubtype, dif_pos h0] at h
            have h := val_eq_of_eq h
            rw [val_ndrec] at h
            contradiction
        next k' hk' heq _ =>
          match k, i with
          | ⟨_,_⟩, ⟨⟨0, _⟩, _⟩ =>
            simp only [encodeSubtype] at h
            cases h
            contradiction
          | ⟨k,hk⟩, ⟨⟨i+1, hi⟩, hp⟩ =>
            cases heq
            have : decodeSubtype (fun i => p (succ i)) ⟨k', Nat.lt_of_succ_lt_succ' (this ▸ hk')⟩ = ⟨⟨i, Nat.lt_of_succ_lt_succ hi⟩, hp⟩ := by
              rw [ih]
              simp only [encodeSubtype, dif_pos h0] at h
              let h := val_eq_of_eq h
              rw [val_ndrec] at h
              cases h
              rfl
            congr
            transitivity (⟨⟨i, Nat.lt_of_succ_lt_succ hi⟩, hp⟩ : { i // p (succ i) }).val.val
            · apply congrArg Fin.val
              apply congrArg Subtype.val
              rw [ih]
              have h := Fin.val_eq_of_eq h
              simp only [encodeSubtype, dif_pos h0, val_ndrec] at h
              cases h
              rfl
            · rfl
      next h0 =>
        match k, i with
        | ⟨k, hk⟩, ⟨⟨0, _⟩, hp⟩ =>
          contradiction
        | ⟨k, hk⟩, ⟨⟨i+1, hi⟩, hp⟩ =>
          congr
          transitivity (⟨⟨i, Nat.lt_of_succ_lt_succ hi⟩, hp⟩ : { i // p (succ i) }).val.val
          · apply congrArg Fin.val
            apply congrArg Subtype.val
            rw [ih]
            apply Fin.eq
            have h := Fin.val_eq_of_eq h
            simp only [encodeSubtype, dif_neg h0, val_ndrec] at h
            cases h
            rfl
          · rfl

def equivSubtype (p : Fin n → Prop) [DecidablePred p] : Equiv (Fin (count p)) { i // p i } where
  fwd := decodeSubtype p
  rev := encodeSubtype p
  spec {k x} := specSubtype p k x

abbrev repr (s : Setoid (Fin n)) [DecidableRel s.r] (i : Fin n) : Prop := Fin.find? (s.r i) = some i

def quot (s : Setoid (Fin n)) [DecidableRel s.r] : Nat := count (repr s)

private def getRepr (s : Setoid (Fin n)) [DecidableRel s.r] (i : Fin n) : Fin (quot s) :=
    match h : Fin.find? (s.r i) with
    | some j =>
      have : repr s j := by
        have hij := of_decide_eq_true <| Fin.find?_some _ h
        unfold repr
        rw [←h]
        congr
        funext k
        rw [decide_eq_decide]
        constr
        · intro hjk
          transitivity j
          · exact hij
          · exact hjk
        · intro hik
          transitivity i
          · symmetry
            exact hij
          · exact hik
      encodeSubtype (repr s) ⟨j, this⟩
    | none => absurd (Fin.find?_none i h) $ by
      rw [decide_eq_false_iff_not]
      intro h
      apply h
      exact Setoid.refl ..

private theorem getRepr_eq_getRepr_of_equiv (s : Setoid (Fin n)) [DecidableRel s.r] {{i j : Fin n}} : s.r i j → getRepr s i = getRepr s j := by
  intro hij
  unfold getRepr
  split
  next i' hi' =>
    split
    next j' hj' =>
      clean
      congr
      apply Option.some.inj
      rw [←hi', ←hj']
      congr
      funext k
      rw [decide_eq_decide]
      constr
      · intro hik
        transitivity i
        · symmetry
          exact hij
        · exact hik
      · intro hjk
        transitivity j
        · exact hij
        · exact hjk
    next h =>
      absurd (Fin.find?_none j h)
      rw [decide_eq_false_iff_not]
      intro h
      apply h
      exact Setoid.refl ..
  next h =>
    absurd (Fin.find?_none i h)
    rw [decide_eq_false_iff_not]
    intro h
    apply h
    exact Setoid.refl ..

private theorem subtype_eq_of_val_equiv_val (s : Setoid (Fin n)) [DecidableRel s.r] {{i j : Subtype (repr s)}} : s.r i.val j.val → i = j := by
  intro hij
  match i, j with
  | ⟨i, hri⟩, ⟨j, hrj⟩ =>
    unfold repr at hri hrj
    apply Subtype.eq
    apply Option.some.inj
    rw [←hri, ←hrj]
    congr
    funext k
    rw [decide_eq_decide]
    constr
    · intro hik
      transitivity i
      · symmetry
        exact hij
      · exact hik
    · intro hjk
      transitivity j
      · exact hij
      · exact hjk

def encodeQuotient (s : Setoid (Fin n)) [DecidableRel s.r] (i : Quotient s) : Fin (quot s) :=
  Quotient.liftOn i (getRepr s) (getRepr_eq_getRepr_of_equiv s)

def decodeQuotient (s : Setoid (Fin n)) [DecidableRel s.r] (i : Fin (quot s)) : Quotient s :=
  Quotient.mk s (decodeSubtype (repr s) i)

theorem specQuotient (s : Setoid (Fin n)) [DecidableRel s.r] (k : Fin (quot s)) (i : Quotient s) :
  decodeQuotient s k = i ↔ encodeQuotient s i = k := by
  induction i using Quotient.inductionOn with
  | _ i =>
  unfold decodeQuotient encodeQuotient
  constr
  · intro h
    have h := Quotient.exact h
    transitivity (getRepr s i)
    · rfl
    · unfold getRepr
      split
      next j hj =>
        rw [←specSubtype]
        have hij := of_decide_eq_true (Fin.find?_some j hj)
        apply subtype_eq_of_val_equiv_val
        transitivity i
        · exact h
        · exact hij
      next hnone =>
        absurd (Fin.find?_none i hnone)
        rw [decide_eq_false_iff_not]
        intro h
        apply h
        exact Setoid.refl ..
  · intro h
    have h : getRepr s i = k := h
    apply Quotient.sound
    unfold getRepr at h
    split at h
    next j hj =>
      rw [←specSubtype] at h
      rw [h]
      symmetry
      apply of_decide_eq_true
      exact Fin.find?_some j hj
    next hnone =>
      absurd (Fin.find?_none i hnone)
      rw [decide_eq_false_iff_not]
      intro h
      apply h
      exact Setoid.refl ..

def equivQuotient (s : Setoid (Fin n)) [DecidableRel s.r] : Equiv (Fin (quot s)) (Quotient s) where
  fwd := decodeQuotient s
  rev := encodeQuotient s
  spec {k i} := specQuotient s k i

end Fin
