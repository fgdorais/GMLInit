import GMLInit.Data.Basic
import GMLInit.Data.Index.Basic
import GMLInit.Data.Index.Map
import GMLInit.Data.Nat

namespace Fin
variable {n : Nat}

protected theorem eq : {i j : Fin n} → i.val = j.val → i = j
| ⟨_,_⟩, ⟨_,_⟩, rfl => rfl

protected theorem eta (i : Fin n) : i = ⟨i.val, i.isLt⟩ := Fin.eq rfl

protected abbrev modulus (_ : Fin n) := n

instance (i : Fin n) : Nat.IsPos i.modulus where
  is_pos := Nat.lt_of_le_of_lt (Nat.zero_le i.val) i.isLt

protected def zero (is_pos : n > 0 := by nat_is_pos) : Fin n := ⟨0, is_pos⟩

protected def last (is_pos : n > 0 := by nat_is_pos) : Fin n := ⟨n.pred, Nat.pred_lt_self n is_pos⟩

protected def lift : Fin n → Fin (n+1)
| ⟨i, hi⟩ => ⟨i, Nat.lt_succ_of_le (Nat.le_of_lt hi)⟩

theorem lift_inj : {i j : Fin n} → i.lift = j.lift → i = j
| ⟨_, _⟩, ⟨_, _⟩, rfl => rfl

theorem succ_inj : {i j : Fin n} → i.succ = j.succ → i = j
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
    constr
    · intro; reflexivity
    · intro; reflexivity
  | n+1, ⟨0, _⟩, IndView.succ j =>
    constr
    · intro; contradiction
    · intro h; cases h
  | n+1, ⟨i+1, hi⟩, IndView.zero =>
    constr
    · intro; contradiction
    · intro h; cases h
  | n+1, ⟨i+1, hi⟩, IndView.succ j =>
    have hsucc : ⟨i+1, hi⟩ = Fin.succ ⟨i, Nat.lt_of_succ_lt_succ hi⟩ := rfl
    constr
    · intro h
      rw [IndView.toFin, hsucc]
      congr
      apply toIndView_eq_iff_toFin_eq.mp
      exact IndView.succ.inj h
    · intro h
      rw [IndView.toFin, hsucc] at h
      rw [Fin.toIndView]
      congr
      apply toIndView_eq_iff_toFin_eq.mpr
      exact succ_inj h

theorem toIndView_toFin {n : Nat} (i : Fin.IndView n) : i.toFin.toIndView = i :=
  toIndView_eq_iff_toFin_eq.mpr rfl

theorem toFin_toIndView {n : Nat} (i : Fin n) : i.toIndView.toFin = i :=
  toIndView_eq_iff_toFin_eq.mp rfl

def equivIndView (n : Nat) : Equiv (Fin n) (Fin.IndView n) where
  fwd := Fin.toIndView
  rev := IndView.toFin
  spec := toIndView_eq_iff_toFin_eq

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

def iotaFind : {n : Nat} → Fin n → Index (Fin.iota n)
| _+1, ⟨0,_⟩ => Index.head
| _+1, ⟨i+1,hi⟩ => Index.tail ((iotaFind ⟨i, Nat.lt_of_succ_lt_succ hi⟩).map Fin.succ)

theorem iotaFind_zero {n : Nat} : iotaFind (Fin.zero : Fin (n+1)) = Index.head := by rfl

theorem iotaFind_succ {n : Nat} (i : Fin n) : iotaFind (Fin.succ i) = Index.tail (Index.map Fin.succ (iotaFind i)) := by cases i; rfl

theorem iotaFind_val {n : Nat} (i : Index (Fin.iota n)) : i.val.iotaFind = i := by
  induction n with
  | zero => contradiction
  | succ n H =>
    match i with
    | .head => rfl
    | .tail (i : Index ((Fin.iota n).map Fin.succ)) =>
      calc
      _ = iotaFind (Index.val (Index.tail i : Index (Fin.iota (n+1)))) := rfl
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
      open Index in rw [iotaFind, val_tail, val_map, H, Fin.succ]

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
    clean unfold Fin.find? at h
    split at h
    next h0 => cases h; exact h0
    next hs => cases h; exact H _ hs
    next => contradiction

def find_none {p : Fin n → Bool} (x) : Fin.find? p = none → p x = false := by
  induction n with
  | zero => absurd x.isLt; apply Nat.not_lt_zero
  | succ n H =>
    intro h
    clean unfold Fin.find? at h
    split at h
    next => contradiction
    next => contradiction
    next h0 hs =>
      match x with
      | ⟨0,_⟩ => exact h0
      | ⟨x+1,hx⟩ => exact H ⟨x, Nat.lt_of_succ_lt_succ hx⟩ hs

end Fin
