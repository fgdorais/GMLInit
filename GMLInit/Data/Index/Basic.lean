import GMLInit.Data.Basic
import GMLInit.Data.Ord
import GMLInit.Meta.Basic
import GMLInit.Meta.Decidable
import GMLInit.Meta.Relation

namespace Index

instance {α} (a : α) (as : List α) : Inhabited (Index (a :: as)) := ⟨head⟩

protected abbrev recNilOn {α} {motive : Index ([]:List α) → Sort _} (i : Index ([]:List α)) : motive i := nomatch i

protected abbrev casesNilOn {α} {motive : Index ([]:List α) → Sort _} (i : Index ([]:List α)) : motive i := nomatch i

lemma val_head {α} (a : α) (as : List α) : (@head α a as).val = a := rfl

@[simp] lemma val_tail {α} (a : α) (as : List α) (i : Index as) : (@tail α a as i).val = i.val := rfl

@[simp] lemma val_ndrec {xs ys : List α} (i : Index xs) : (h : xs = ys) → val (h ▸ i : Index ys) = i.val | rfl => rfl

open Ordering in
protected def compare : Index xs → Index xs → Ordering
| head, head => eq
| head, tail _ => lt
| tail _, head => gt
| tail i, tail j => Index.compare i j

instance instOrd (xs : List α) : Ord (Index xs) := ⟨Index.compare⟩

open Ordering in instance instLawfulOrd : (xs : List α) → Ord.LawfulOrd (Index xs)
| [] => {
  eq_refl := (nomatch .)
  eq_tight := (nomatch .)
  lt_trans := (nomatch .)
  gt_trans := (nomatch .)
}
| _::xs => {
  eq_refl := fun
  | head => rfl
  | tail i => (instLawfulOrd xs).eq_refl i
  eq_tight := fun {i j} h => match i, j, h with
  | head, head, _ => rfl
  | head, tail _, h => Ordering.noConfusion h
  | tail _, head, h => Ordering.noConfusion h
  | tail _, tail _, h => congrArg tail ((instLawfulOrd xs).eq_tight h)
  lt_trans := fun {i j k} hij hjk => match i, j, k, hij, hjk with
  | head, _, tail _, _, _ => rfl
  | head, head, _, h, _ => Ordering.noConfusion h
  | tail _, head, _, h, _ => Ordering.noConfusion h
  | _, tail _, head, _, h => Ordering.noConfusion h
  | tail _, tail _, tail _, hij, hjk => (instLawfulOrd xs).lt_trans hij hjk
  gt_trans := fun {i j k} hij hjk => match i, j, k, hij, hjk with
  | tail _, _, head, _, _ => rfl
  | head, head, _, h, _ => Ordering.noConfusion h
  | head, tail _, _, h, _ => Ordering.noConfusion h
  | _, head, tail _, _, h => Ordering.noConfusion h
  | tail _, tail _, tail _, hij, hjk => (instLawfulOrd xs).gt_trans hij hjk
}

instance : LE (Index xs) := open Ord in inferInstance

instance : LT (Index xs) := open Ord in inferInstance

protected def head? {α} : (as : List α) → Option (Index as)
| [] => none
| _::_ => some head

protected def last? {α} : (as : List α) → Option (Index as)
| [] => none
| _::as =>
  match Index.last? as with
  | some i => some (tail i)
  | none => some head

protected def next? {α} : {as : List α} → Index as → Option (Index as)
| _::as, head => Option.map tail (Index.head? as)
| _::_, tail i => Option.map tail (Index.next? i)

protected def pred? {α} : {as : List α} → Index as → Option (Index as)
| _::_, head => none
| _::_, tail i =>
  match Index.pred? i with
  | some i => some (tail i)
  | none => some head

protected def find? {α} : {xs : List α} → (p : Index xs → Bool) → Option (Index xs)
| [], _ => none
| _::_, p =>
  match p head, Index.find? (λ i => p (tail i)) with
  | true, _ => some head
  | false, some i => some (tail i)
  | false, none => none

theorem find_some {α} {xs : List α} {p : Index xs → Bool} (i : Index xs) : Index.find? p = some i → p i = true := by
  induction xs with
  | nil => cases i
  | cons x xs H =>
    intro h
    unfold Index.find? at h
    clean at h
    split at h
    next hh => cases h; exact hh
    next ht => cases h; exact H _ ht
    next => contradiction

theorem find_none {α} {xs : List α} {p : Index xs → Bool} (i : Index xs) : Index.find? p = none → p i = false := by
  induction xs with
  | nil => cases i
  | cons x xs H =>
    intro h
    unfold Index.find? at h
    clean at h
    split at h
    next => contradiction
    next => contradiction
    next hh ht =>
      cases i with
      | head => exact hh
      | tail i => exact H _ ht

def search {α} {xs : List α} {p : Index xs → Prop} [DecidablePred p] (h : ∃ i, p i) : Index xs :=
  match hi : Index.find? λ i => p i with
  | some i => i
  | none => absurd h $ by
    intro ⟨j, hj⟩
    have := find_none j hi
    rw [decide_eq_true hj] at this
    contradiction

theorem search_prop {α} {xs : List α} {p : Index xs → Prop} [DecidablePred p] (h : ∃ i, p i) : p (search h) := by
  unfold search
  split
  next h =>
    apply of_decide_eq_true
    apply find_some _ h
  next f =>
    absurd h
    intro ⟨j, hj⟩
    have := find_none j f
    rw [decide_eq_true hj] at this
    contradiction

theorem search_eq {α} {xs : List α} {p q : Index xs → Prop} [ip : DecidablePred p] [iq : DecidablePred q] {hp : ∃ i, p i} {hq : ∃ j, q j}  (h : p = q) : search hp = search hq := by
  cases h
  cases Subsingleton.elim ip iq
  cases Subsingleton.elim hp hq
  rfl

theorem search_ext {α} {xs : List α} {p q : Index xs → Prop} [DecidablePred p] [DecidablePred q] {hp : ∃ i, p i} {hq : ∃ j, q j} : (∀ i, p i ↔ q i) → search hp = search hq := by
  intro h
  apply search_eq
  funext i
  exact propext (h i)

end Index
