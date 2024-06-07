import GMLInit.Data.Basic
import GMLInit.Data.Nat

namespace Fin
variable {n : Nat}

protected theorem eq : {i j : Fin n} → i.val = j.val → i = j
| ⟨_,_⟩, ⟨_,_⟩, rfl => rfl

protected theorem eta' (i : Fin n) : i = ⟨i.val, i.isLt⟩ := Fin.eq rfl

protected abbrev modulus (_ : Fin n) := n

theorem val_eq_val_of_heq : {m n : Nat} → m = n → (x : Fin m) → (y : Fin n) → HEq x y → x.val = y.val
| _, _, rfl, ⟨_,_⟩, ⟨_,_⟩, HEq.rfl => rfl

theorem val_ndrec (i : Fin n) (h : n = m) : (h ▸ i : Fin m).val = i.val := by cases h; rfl

instance (i : Fin n) : Nat.IsPos i.modulus where
  is_pos := Nat.lt_of_le_of_lt (Nat.zero_le i.val) i.isLt

protected def zero (is_pos : n > 0 := by nat_is_pos) : Fin n := ⟨0, is_pos⟩

protected def last' (is_pos : n > 0 := by nat_is_pos) : Fin n := ⟨n.pred, Nat.pred_lt_self is_pos⟩

protected def lift : Fin n → Fin (n+1)
| ⟨i, hi⟩ => ⟨i, Nat.lt_succ_of_le (Nat.le_of_lt hi)⟩

protected def next : Fin n → Option (Fin n)
| ⟨i, _⟩ => if h : i+1 < n then some ⟨i+1, h⟩ else none

protected def pred? : Fin n → Option (Fin n)
| ⟨i, h⟩ => if i ≠ 0 then some ⟨i-1, Nat.lt_of_le_of_lt (Nat.pred_le i) h⟩ else none

theorem lift_inj : {i j : Fin n} → i.lift = j.lift → i = j
| ⟨_, _⟩, ⟨_, _⟩, rfl => rfl

theorem succ_inj' : {i j : Fin n} → i.succ = j.succ → i = j
| ⟨_, _⟩, ⟨_, _⟩, rfl => rfl

protected inductive IndView : Nat → Type
| zero {n : Nat} : Fin.IndView (n+1)
| succ {n : Nat} : Fin.IndView n → Fin.IndView (n+1)

@[inline] protected def IndView.toFin : {n : Nat} → Fin.IndView n → Fin n
| _+1, IndView.zero => Fin.zero
| _+1, IndView.succ i => Fin.succ (IndView.toFin i)

@[inline] protected def toIndView : {n : Nat} → Fin n → Fin.IndView n
| _+1, ⟨0, _⟩ => IndView.zero
| _+1, ⟨i+1, hi⟩ => IndView.succ (Fin.toIndView ⟨i, Nat.lt_of_succ_lt_succ hi⟩)

theorem toIndView_eq_iff_toFin_eq {n : Nat} {i : Fin n} {j : Fin.IndView n} : i.toIndView = j ↔ j.toFin = i := by
  match n, i, j with
  | n+1, ⟨0, _⟩, IndView.zero =>
    constructor
    · intro; reflexivity
    · intro; reflexivity
  | n+1, ⟨0, _⟩, IndView.succ j =>
    constructor
    · intro; contradiction
    · intro h; cases h
  | n+1, ⟨i+1, hi⟩, IndView.zero =>
    constructor
    · intro; contradiction
    · intro h; cases h
  | n+1, ⟨i+1, hi⟩, IndView.succ j =>
    have hsucc : ⟨i+1, hi⟩ = Fin.succ ⟨i, Nat.lt_of_succ_lt_succ hi⟩ := rfl
    constructor
    · intro h
      rw [IndView.toFin, hsucc]
      congr
      rw [←toIndView_eq_iff_toFin_eq]
      exact IndView.succ.inj h
    · intro h
      rw [IndView.toFin, hsucc] at h
      rw [Fin.toIndView]
      congr
      rw [toIndView_eq_iff_toFin_eq]
      exact succ_inj.mp h

theorem toIndView_toFin {n : Nat} (i : Fin.IndView n) : i.toFin.toIndView = i :=
  toIndView_eq_iff_toFin_eq.mpr rfl

theorem toFin_toIndView {n : Nat} (i : Fin n) : i.toIndView.toFin = i :=
  toIndView_eq_iff_toFin_eq.mp rfl

def equivIndView (n : Nat) : Equiv (Fin n) (Fin.IndView n) where
  fwd := Fin.toIndView
  rev := IndView.toFin
  fwd_eq_iff_rev_eq := toIndView_eq_iff_toFin_eq

protected def recInd.{u} {motive : (n : Nat) → Fin n → Sort u}
  (zero : {n : Nat} → motive (n+1) Fin.zero)
  (succ : {n : Nat} → (i : Fin n) → motive n i → motive (n + 1) (Fin.succ i)) :
  {n : Nat} → (i : Fin n) → motive n i
| Nat.succ _, i => match hi : i.toIndView with
  | IndView.zero => toIndView_eq_iff_toFin_eq.mp hi ▸ zero
  | IndView.succ _ => toIndView_eq_iff_toFin_eq.mp hi ▸ succ _ (Fin.recInd zero succ _)

protected abbrev recIndOn.{u} {motive : (n : Nat) → Fin n → Sort u} {n : Nat} (i : Fin n)
  (zero : {n : Nat} → motive (n+1) Fin.zero)
  (succ : {n : Nat} → (i : Fin n) → motive n i → motive (n + 1) (Fin.succ i)) :
  motive n i := Fin.recInd zero succ i

protected abbrev casesIndOn.{u} {motive : (n : Nat) → Fin n → Sort u} {n : Nat} (i : Fin n)
  (zero : {n : Nat} → motive (n+1) Fin.zero)
  (succ : {n : Nat} → (i : Fin n) → motive (n + 1) (Fin.succ i)) :
  motive n i := Fin.recInd zero (fun i _ => succ i) i

protected def iota : (n : Nat) → List (Fin n)
| 0 => []
| n+1 => Fin.zero :: (Fin.iota n).map Fin.succ

def iotaFind : {n : Nat} → Fin n → List.Index (Fin.iota n)
| _+1, ⟨0,_⟩ => .head
| _+1, ⟨i+1,hi⟩ => .tail ((iotaFind ⟨i, Nat.lt_of_succ_lt_succ hi⟩).map Fin.succ)

theorem iotaFind_zero {n : Nat} : iotaFind (Fin.zero : Fin (n+1)) = .head := by rfl

theorem iotaFind_succ {n : Nat} (i : Fin n) : iotaFind (Fin.succ i) = .tail (List.Index.map Fin.succ (iotaFind i)) := by cases i; rfl

theorem iotaFind_val {n : Nat} (i : List.Index (Fin.iota n)) : i.val.iotaFind = i := by
  induction n with
  | zero => contradiction
  | succ n H =>
    match i with
    | .head => rfl
    | .tail (i : List.Index ((Fin.iota n).map Fin.succ)) =>
      calc
      _ = iotaFind (List.Index.val (.tail i : List.Index (Fin.iota (n+1)))) := rfl
      _ = iotaFind (List.Index.val i) := by rw [List.Index.val_tail]
      _ = iotaFind (List.Index.val (List.Index.map Fin.succ (List.Index.unmap Fin.succ i))) := by rw [List.Index.map_unmap]
      _ = iotaFind (Fin.succ (List.Index.val (List.Index.unmap Fin.succ i))) := by rw [List.Index.val_map]
      _ = .tail (List.Index.map Fin.succ (iotaFind (List.Index.val (List.Index.unmap Fin.succ i)))) := by rw [iotaFind_succ]
      _ = .tail (List.Index.map Fin.succ (List.Index.unmap Fin.succ i)) := by rw [H]
      _ = .tail i := by rw [List.Index.map_unmap]

theorem val_iotaFind {n : Nat} (i : Fin n) : i.iotaFind.val = i := by
  induction n with
  | zero => cases i; contradiction
  | succ n H =>
    match i with
    | ⟨0,_⟩ => rfl
    | ⟨i+1,hi⟩ =>
      apply Fin.eq
      open List.Index in rw [iotaFind, val_tail, val_map, H, Fin.succ]

protected def find? (p : Fin n → Bool) : Option (Fin n) :=
  loop 0 (Nat.zero_le n)
where
  loop (i : Nat) (hi : i ≤ n) : Option (Fin n) :=
    if h : i = n then
      none
    else
      have hi : i < n := Nat.lt_of_le_of_ne hi h
      if p ⟨i, hi⟩ then
        some ⟨i, hi⟩
      else
        loop (i+1) (Nat.succ_le_of_lt hi)
termination_by n - i

theorem find?.loop_some {p : Fin n → Bool} (i hi) (k : Fin n) : Fin.find?.loop p i hi = some k → p k = true := by
  intro h
  unfold loop at h
  split at h
  next => contradiction
  next hne =>
    have hi : i < n := Nat.lt_of_le_of_ne hi hne
    simp only at h
    split at h
    next hp =>
      cases h
      exact hp
    next =>
      exact loop_some (i+1) (Nat.succ_le_of_lt hi) k h
termination_by n - i

private theorem find?.loop_none {p : Fin n → Bool} (i hi) (k : Fin n) : i ≤ k.val → Fin.find?.loop p i hi = none → p k = false := by
  intro hik h
  unfold loop at h
  split at h
  next heq =>
    absurd hik
    rw [heq]
    apply Nat.not_le_of_gt
    exact k.isLt
  next hne =>
    have hi : i < n := Nat.lt_of_le_of_ne hi hne
    simp only at h
    split at h
    next hp =>
      contradiction
    next hp =>
      by_cases i = k.val with
      | isTrue heq =>
        rw [Bool.eq_false_iff]
        intro hk
        apply hp
        rw [←hk]
        congr
      | isFalse hik' =>
        have hik : i < k.val := Nat.lt_of_le_of_ne hik hik'
        exact loop_none (i+1) (Nat.succ_le_of_lt hi) k (Nat.succ_le_of_lt hik) h
termination_by n - i

theorem find?_some {p : Fin n → Bool} (k : Fin n) : Fin.find? p = some k → p k = true :=
  find?.loop_some 0 (Nat.zero_le n) k

theorem find?_none {p : Fin n → Bool} (k : Fin n) : Fin.find? p = none → p k = false :=
  find?.loop_none 0 (Nat.zero_le n) k (Nat.zero_le k.val)

def sum [Add α] [OfNat α (nat_lit 0)] (f : Fin n → α) : α :=
  foldr n (fun i s => f i + s) 0

theorem sum_zero [Add α] [OfNat α (nat_lit 0)] (f : Fin 0 → α) : sum f = 0 := by
  simp [sum]

theorem sum_succ [Add α] [OfNat α (nat_lit 0)] (f : Fin (n+1) → α) : sum f = f 0 + sum (f ∘ succ) := by
  simp [sum, foldr_succ]

def prod [Mul α] [OfNat α (nat_lit 1)] (f : Fin n → α) : α :=
  foldr n (fun i p => f i * p) 1

theorem prod_zero [Mul α] [OfNat α (nat_lit 1)] (f : Fin 0 → α) : prod f = 1 := by
  simp [prod]

theorem prod_succ [Mul α] [OfNat α (nat_lit 1)] (f : Fin (n+1) → α) : prod f = f 0 * prod (f ∘ succ) := by
  simp [prod, foldr_succ]

end Fin
