import GMLInit.Data.Basic
import GMLInit.Data.Nat

namespace Fin
variable {n : Nat}

protected theorem eq : {i j : Fin n} → i.val = j.val → i = j
| ⟨_,_⟩, ⟨_,_⟩, rfl => rfl

protected def zero {n : Nat} (is_pos : n > 0 := by nat_is_pos) : Fin n := ⟨0, is_pos⟩

protected def last {n : Nat} (is_pos : n > 0 := by nat_is_pos) : Fin n := ⟨n.pred, Nat.pred_lt_self n is_pos⟩

protected def lift : Fin n → Fin (n+1)
| ⟨i, hi⟩ => ⟨i, Nat.lt_succ_of_le (Nat.le_of_lt hi)⟩

protected def recZeroSucc {motive : Fin (n+1) → Sort _} (zero : motive Fin.zero) (succ : (i : Fin n) → motive (Fin.succ i)) : (i : Fin (n+1)) → motive i
| ⟨0, _⟩ => zero
| ⟨i+1, hi⟩ => succ ⟨i, Nat.lt_of_succ_lt_succ hi⟩

protected def recZeroSuccOn {motive : Fin (n+1) → Sort _} (i : Fin (n+1)) (zero : motive Fin.zero) (succ : (i : Fin n) → motive (Fin.succ i)) : motive i :=
  Fin.recZeroSucc zero succ i

protected def casesZeroSuccOn {motive : Fin (n+1) → Sort _} (i : Fin (n+1)) (zero : motive Fin.zero) (succ : (i : Fin n) → motive (Fin.succ i)) : motive i :=
  Fin.recZeroSucc zero succ i

protected def find? : {n : Nat} → (p : Fin n → Bool) → Option (Fin n)
| 0, _ => none
| n+1, p =>
  match p Fin.zero, Fin.find? (λ x => p x.succ) with
  | true, _ => some Fin.zero
  | false, some x => some x.succ
  | false, none => none

def find_some {p : Fin n → Bool} (i) : Fin.find? p = some i → p i = true := by
  induction n using Nat.recAux with
  | zero => exact i.elim0
  | succ n H =>
    intro h
    unfold Fin.find? at h
    split at h
    next h0 => cases h; exact h0
    next hs => cases h; exact H _ hs
    next => contradiction

def find_none {p : Fin n → Bool} (x) : Fin.find? p = none → p x = false := by
  induction n using Nat.recAux with
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
