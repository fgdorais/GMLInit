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

theorem val_eq_val_of_heq : {m n : Nat} → m = n → (x : Fin m) → (y : Fin n) → HEq x y → x.val = y.val
| _, _, rfl, ⟨_,_⟩, ⟨_,_⟩, HEq.rfl => rfl

theorem val_ndrec (i : Fin n) (h : n = m) : (h ▸ i : Fin m).val = i.val := by cases h; rfl

instance (i : Fin n) : Nat.IsPos i.modulus where
  is_pos := Nat.lt_of_le_of_lt (Nat.zero_le i.val) i.isLt

protected def zero (is_pos : n > 0 := by nat_is_pos) : Fin n := ⟨0, is_pos⟩

protected def last (is_pos : n > 0 := by nat_is_pos) : Fin n := ⟨n.pred, Nat.pred_lt_self n is_pos⟩

protected def lift : Fin n → Fin (n+1)
| ⟨i, hi⟩ => ⟨i, Nat.lt_succ_of_le (Nat.le_of_lt hi)⟩

protected def next : Fin n → Option (Fin n)
| ⟨i, _⟩ => if h : i+1 < n then some ⟨i+1, h⟩ else none

protected def pred : Fin n → Option (Fin n)
| ⟨i, h⟩ => if i ≠ 0 then some ⟨i-1, Nat.lt_of_le_of_lt (Nat.pred_le i) h⟩ else none

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

theorem toIndView_eq_iff_toFin_eq {n : Nat} {{i : Fin n}} {{j : Fin.IndView n}} : i.toIndView = j ↔ j.toFin = i := by
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
      rw [←toIndView_eq_iff_toFin_eq]
      exact IndView.succ.inj h
    · intro h
      rw [IndView.toFin, hsucc] at h
      rw [Fin.toIndView]
      congr
      rw [toIndView_eq_iff_toFin_eq]
      exact succ_inj h

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

protected def find? (p : Fin n → Bool) : Option (Fin n) :=
  let rec loop (i : Nat) (hi : i ≤ n) : Option (Fin n) :=
    if h : i = n then
      none
    else
      have hi : i < n := Nat.lt_of_le_of_ne hi h
      if p ⟨i, hi⟩ then
        some ⟨i, hi⟩
      else
        loop (i+1) (Nat.succ_le_of_lt hi)
  loop 0 (Nat.zero_le n)
termination_by loop i _ => n - i

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
termination_by loop_some i _ _ _ => n - i

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
termination_by loop_none i _ _ _ _ => n - i

theorem find?_some {p : Fin n → Bool} (k : Fin n) : Fin.find? p = some k → p k = true :=
  find?.loop_some 0 (Nat.zero_le n) k

theorem find?_none {p : Fin n → Bool} (k : Fin n) : Fin.find? p = none → p k = false :=
  find?.loop_none 0 (Nat.zero_le n) k (Nat.zero_le k.val)

@[specialize]
protected def foldl : {n : Nat} → (α → Fin n → α) → α → α
| 0, _, i => i
| n+1, f, i => Fin.foldl (fun x i => f x i.succ) (f i ⟨0, Nat.zero_lt_succ n⟩)

theorem foldl_zero (f : α → Fin 0 → α) (i : α) : Fin.foldl f i = i := rfl

theorem foldl_succ {n} (f : α → Fin (n+1) → α) (i : α) : Fin.foldl f i = f (Fin.foldl (fun x i => f x i.lift) i) ⟨n, Nat.lt_succ_self n⟩ := by
  induction n generalizing i with
  | zero => rfl
  | succ n ih => conv => lhs; unfold Fin.foldl; rw [ih]

@[specialize]
protected def foldr : {n : Nat} → (Fin n → α → α) → α → α
| 0, _, i => i
| n+1, f, i => Fin.foldr (fun i => f i.lift) (f ⟨n, Nat.lt_succ_self n⟩ i)

theorem foldr_zero (f : Fin 0 → α → α) (i : α) : Fin.foldr f i = i := rfl

theorem foldr_succ {n} (f : Fin (n+1) → α → α) (i : α) : Fin.foldr f i = f ⟨0, Nat.zero_lt_succ n⟩ (Fin.foldr (fun i => f i.succ) i) := by
  induction n generalizing i with
  | zero => rfl
  | succ n ih => conv => lhs; unfold Fin.foldr; rw [ih]

protected abbrev all {n} (p : Fin n → Bool) : Bool :=
  Fin.foldr (fun i v => p i && v) true

theorem forall_eq_true_of_all_eq_true : {n : Nat} → {p : Fin n → Bool} → Fin.all p = true → ∀ i, p i = true
| n+1, p, h, ⟨0, _⟩ => by
  rw [Fin.all, Fin.foldr_succ, Bool.and_eq_true] at h
  exact h.left
| n+1, p, h, ⟨i+1, hi⟩ => by
  rw [Fin.all, Fin.foldr_succ, Bool.and_eq_true] at h
  exact forall_eq_true_of_all_eq_true h.right ⟨i, Nat.lt_of_succ_lt_succ hi⟩

theorem exists_eq_false_of_all_eq_false : {n : Nat} → {p : Fin n → Bool} → Fin.all p = false → ∃ i, p i = false
| 0, _, h => Bool.noConfusion h
| n+1, p, h => by
  rw [Fin.all, Fin.foldr_succ, Bool.and_eq_false_iff] at h
  match h with
  | .inl h => exists ⟨0, Nat.zero_lt_succ n⟩
  | .inr h => match exists_eq_false_of_all_eq_false h with
    | ⟨⟨i,hi⟩,hp⟩ => exists ⟨i+1, Nat.succ_lt_succ hi⟩

instance (p : Fin n → Prop) [DecidablePred p] : Decidable (∀ i, p i) :=
  match hall : Fin.all fun i => decide (p i) with
  | true => isTrue $ by
    intro i
    apply of_decide_eq_true
    exact forall_eq_true_of_all_eq_true hall i
  | false => isFalse $ by
    intro h
    match exists_eq_false_of_all_eq_false hall with
    | ⟨i, hi⟩ => absurd h i; exact of_decide_eq_false hi

theorem decide_forall_eq_all {n} (p : Fin n → Prop) [(i : Fin n) → Decidable (p i)] : decide (∀ i, p i) = Fin.all fun i => decide (p i) := by
  match h : Fin.all fun i => decide (p i) with
  | true =>
    have h := forall_eq_true_of_all_eq_true h
    apply decide_eq_true
    intro i
    apply of_decide_eq_true
    exact h i
  | false =>
    match exists_eq_false_of_all_eq_false h with
    | ⟨i, hi⟩ =>
      have hi := of_decide_eq_false hi
      apply decide_eq_false
      intro h
      apply hi
      exact h i

instance (p : Fin n → Bool) [(i : Fin n) → DecLift (p i)] : DecLift (Fin.all p) where
  toProp := ∀ i, DecLift.toProp (p i)
  instDecidable := inferInstance
  decide_eq := by
    rw [decide_forall_eq_all]
    congr
    funext
    rw [DecLift.decide_eq]

protected abbrev any {n} (p : Fin n → Bool) : Bool :=
  Fin.foldr (fun i v => p i || v) false

theorem exists_eq_true_of_any_eq_true : {n : Nat} → {p : Fin n → Bool} → Fin.any p = true → ∃ i, p i = true
| 0, _, h => Bool.noConfusion h
| n+1, p, h => by
  rw [Fin.any, Fin.foldr_succ, Bool.or_eq_true] at h
  match h with
  | .inl h => exists ⟨0, Nat.zero_lt_succ n⟩
  | .inr h => match exists_eq_true_of_any_eq_true h with
    | ⟨⟨i,hi⟩,hp⟩ => exists ⟨i+1, Nat.succ_lt_succ hi⟩

theorem forall_eq_false_of_any_eq_false : {n : Nat} → {p : Fin n → Bool} → Fin.any p = false → ∀ i, p i = false
| n+1, p, h, ⟨0, _⟩ => by
  rw [Fin.any, Fin.foldr_succ, Bool.or_eq_false_iff] at h
  exact h.left
| n+1, p, h, ⟨i+1, hi⟩ => by
  rw [Fin.any, Fin.foldr_succ, Bool.or_eq_false_iff] at h
  exact forall_eq_false_of_any_eq_false h.right ⟨i, Nat.lt_of_succ_lt_succ hi⟩

instance (p : Fin n → Prop) [DecidablePred p] : Decidable (∃ i, p i) :=
  match hany : Fin.any fun i => decide (p i) with
  | true => isTrue $ by
    match exists_eq_true_of_any_eq_true hany with
    | ⟨i, h⟩ => exists i; exact of_decide_eq_true h
  | false => isFalse $ by
    intro ⟨i, h⟩
    absurd h
    apply of_decide_eq_false
    exact forall_eq_false_of_any_eq_false hany i

theorem decide_exists_eq_any {n} (p : Fin n → Prop) [(i : Fin n) → Decidable (p i)] : decide (∃ i, p i) = Fin.any fun i => decide (p i) := by
  match h : Fin.any fun i => decide (p i) with
  | true =>
    match exists_eq_true_of_any_eq_true h with
    | ⟨i, hi⟩ =>
      have hi := of_decide_eq_true hi
      apply decide_eq_true
      exists i
  | false =>
    have h := forall_eq_false_of_any_eq_false h
    apply decide_eq_false
    intro ⟨i, hi⟩
    absurd hi
    apply of_decide_eq_false
    exact h i

instance (p : Fin n → Bool) [(i : Fin n) → DecLift (p i)] : DecLift (Fin.any p) where
  toProp := ∃ i, DecLift.toProp (p i)
  instDecidable := inferInstance
  decide_eq := by
    rw [decide_exists_eq_any]
    congr
    funext
    rw [DecLift.decide_eq]

end Fin
