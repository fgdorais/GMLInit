import GMLInit.Data.Basic
import GMLInit.Data.Index.Basic
import GMLInit.Data.Index.Map
import GMLInit.Data.Nat

namespace Fin
variable {n : Nat}

protected theorem eq : {i j : Fin n} → i.val = j.val → i = j
| ⟨_,_⟩, ⟨_,_⟩, rfl => rfl

protected abbrev modulus (i : Fin n) := n

instance (i : Fin n) : Nat.IsPos i.modulus where
  is_pos := Nat.lt_of_le_of_lt (Nat.zero_le i.val) i.isLt

protected def zero (is_pos : n > 0 := by nat_is_pos) : Fin n := ⟨0, is_pos⟩

protected def last (is_pos : n > 0 := by nat_is_pos) : Fin n := ⟨n.pred, Nat.pred_lt_self n is_pos⟩

protected def lift : Fin n → Fin (n+1)
| ⟨i, hi⟩ => ⟨i, Nat.lt_succ_of_le (Nat.le_of_lt hi)⟩

protected def recZeroSucc {motive : Fin (n+1) → Sort _} (zero : motive Fin.zero) (succ : (i : Fin n) → motive (Fin.succ i)) : (i : Fin (n+1)) → motive i
| ⟨0, _⟩ => zero
| ⟨i+1, hi⟩ => succ ⟨i, Nat.lt_of_succ_lt_succ hi⟩

protected def recZeroSuccOn {motive : Fin (n+1) → Sort _} (i : Fin (n+1)) (zero : motive Fin.zero) (succ : (i : Fin n) → motive (Fin.succ i)) : motive i :=
  Fin.recZeroSucc zero succ i

protected def casesZeroSuccOn {motive : Fin (n+1) → Sort _} (i : Fin (n+1)) (zero : motive Fin.zero) (succ : (i : Fin n) → motive (Fin.succ i)) : motive i :=
  Fin.recZeroSucc zero succ i

protected def iota : (n : Nat) → List (Fin n)
| 0 => []
| n+1 => Fin.zero :: (Fin.iota n).map Fin.succ

def iotaFind : {n : Nat} → Fin n → Index (Fin.iota n)
| n+1, ⟨0,_⟩ => Index.head
| n+1, ⟨i+1,hi⟩ => Index.tail ((iotaFind ⟨i, Nat.lt_of_succ_lt_succ hi⟩).map Fin.succ)

theorem iotaFind_zero {n : Nat} : iotaFind (Fin.zero : Fin (n+1)) = Index.head := by rfl

theorem iotaFind_succ {n : Nat} (i : Fin n) : iotaFind (Fin.succ i) = Index.tail (Index.map Fin.succ (iotaFind i)) := by cases i; rfl

theorem iotaFind_val {n : Nat} (i : Index (Fin.iota n)) : i.val.iotaFind = i := by
  induction n with
  | zero => contradiction
  | succ n H =>
    cases i with
    | head => rfl
    | tail i => calc
      _ = iotaFind (Index.val (Index.tail i)) := by rfl
      _ = iotaFind (Index.val i) := by rw [Index.val_tail]
      _ = iotaFind (Index.val (Index.map Fin.succ (Index.unmap Fin.succ i))) := by rw [Index.map_unmap]
      _ = iotaFind (Fin.succ (Index.val (Index.unmap Fin.succ i))) := by rw [Index.val_map]
      _ = Index.tail (Index.map Fin.succ (iotaFind (Index.val (Index.unmap Fin.succ i)))) := by rw [iotaFind_succ]
      _ = Index.tail (Index.map Fin.succ (Index.unmap Fin.succ i)) := by rw [H]
      _ = Index.tail i := by rw [Index.map_unmap]

theorem val_iotaFind {n : Nat} (i : Fin n) : i.iotaFind.val = i := by
  induction n with
  | zero => cases i; contradiction
  | succ n H =>
    match i with
    | ⟨0,_⟩ => rfl
    | ⟨i+1,hi⟩ =>
      apply Fin.eq
      unfold iotaFind
      open Index in rw [val_tail, val_map, H]
      rfl

protected def find? : {n : Nat} → (p : Fin n → Bool) → Option (Fin n)
| 0, _ => none
| n+1, p =>
  match p Fin.zero, Fin.find? (λ x => p x.succ) with
  | true, _ => some Fin.zero
  | false, some x => some x.succ
  | false, none => none

def find_some {p : Fin n → Bool} (i) : Fin.find? p = some i → p i = true := by
  induction n with
  | zero => exact i.elim0
  | succ n H =>
    intro h
    unfold Fin.find? at h
    split at h
    next h0 => cases h; exact h0
    next hs => cases h; exact H _ hs
    next => contradiction

def find_none {p : Fin n → Bool} (x) : Fin.find? p = none → p x = false := by
  induction n with
  | zero => absurd x.isLt; apply Nat.not_lt_zero
  | succ n H =>
    intro h
    unfold Fin.find? at h
    split at h
    next => contradiction
    next => contradiction
    next h0 hs =>
      match x with
      | ⟨0,_⟩ => exact h0
      | ⟨x+1,hx⟩ => exact H ⟨x, Nat.lt_of_succ_lt_succ hx⟩ hs

end Fin
