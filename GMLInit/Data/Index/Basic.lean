import GMLInit.Data.Basic
import GMLInit.Data.Equiv
import GMLInit.Data.Ord
import GMLInit.Meta.Basic
import GMLInit.Meta.Decidable
import GMLInit.Meta.Relation

namespace Index

instance {α} (a : α) (as : List α) : Inhabited (Index (a :: as)) := ⟨head⟩

protected abbrev recNilOn {α} {motive : Index ([]:List α) → Sort _} (i : Index ([]:List α)) : motive i := nomatch i

protected abbrev casesNilOn {α} {motive : Index ([]:List α) → Sort _} (i : Index ([]:List α)) : motive i := nomatch i

lemma val_head {α} (a : α) (as : List α) : (@head α a as).val = a := rfl

lemma val_tail {α} (a : α) (as : List α) (i : Index as) : (@tail α a as i).val = i.val := rfl

lemma val_ndrec {xs ys : List α} (i : Index xs) : (h : xs = ys) → val (h ▸ i : Index ys) = i.val | rfl => rfl

protected def compare : Index xs → Index xs → Ordering
| head, head => .eq
| head, tail _ => .lt
| tail _, head => .gt
| tail i, tail j => Index.compare i j

instance instOrd (xs : List α) : Ord (Index xs) := ⟨Index.compare⟩

instance instLinearOrd : (xs : List α) → LinearOrd (Index xs)
| [] => {
  symm := (nomatch .)
  le_trans := (nomatch .)
  eq_strict := (nomatch .)
}
| _::xs => {
  symm := fun
  | head, head => rfl
  | head, tail _ => rfl
  | tail _, head => rfl
  | tail i, tail j => (instLinearOrd xs).symm i j
  le_trans := fun {i j k} hij hjk => match i, j, k, hij, hjk with
  | head, _, head, _, _ => Ordering.noConfusion
  | head, _, tail _, _, _ => Ordering.noConfusion
  | tail _, head, tail _, h, _ => absurd rfl h
  | tail _, tail _, tail _, hij, hjk => (instLinearOrd xs).le_trans hij hjk
  eq_strict := fun {i j} h => match i, j, h with
  | head, head, _ => rfl
  | head, tail _, h => Ordering.noConfusion h
  | tail _, head, h => Ordering.noConfusion h
  | tail _, tail _, h => congrArg tail ((instLinearOrd xs).eq_strict h)
}

instance : LE (Index xs) := ⟨fun i j => Ord.compare i j ≠ .gt⟩

instance : LT (Index xs) := ⟨fun i j => Ord.compare i j = .lt⟩

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
  | cons x xs ih =>
    intro h
    clean unfold Index.find? at h
    clean at h
    split at h
    next hh => injection h with h; rw [←h, hh]
    next ht => injection h with h; rw [←h, ih _ ht]
    next => contradiction

theorem find_none {α} {xs : List α} {p : Index xs → Bool} (i : Index xs) : Index.find? p = none → p i = false := by
  induction xs with
  | nil => cases i
  | cons x xs ih =>
    intro h
    clean unfold Index.find? at h
    clean at h
    split at h
    next => contradiction
    next => contradiction
    next hh ht =>
      cases i with
      | head => exact hh
      | tail i => exact ih _ ht

def search {α} {xs : List α} {p : Index xs → Prop} [DecidablePred p] (h : ∃ i, p i) : Index xs :=
  match hi : Index.find? λ i => p i with
  | some i => i
  | none => absurd h $ by
    intro ⟨j, hj⟩
    have := find_none j hi
    rw [decide_eq_true hj] at this
    contradiction

theorem search_prop {α} {xs : List α} {p : Index xs → Prop} [DecidablePred p] (h : ∃ i, p i) : p (search h) := by
  clean unfold search
  split
  next h =>
    apply of_decide_eq_true
    exact find_some _ h
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

protected def toNat {α} : {xs : List α} → (i : Index xs) → Nat
| _, head => 0
| _, tail i => Index.toNat i + 1

theorem toNat_lt_length {α} {xs : List α} (i : Index xs) : i.toNat < xs.length := by
  induction xs with
  | nil => cases i
  | cons x xs ih =>
    cases i with
    | head =>
      exact Nat.zero_lt_succ ..
    | tail i =>
      apply Nat.succ_lt_succ
      exact ih ..

protected def toFin {α} {xs : List α} (i : Index xs) : Fin xs.length := ⟨i.toNat, i.toNat_lt_length⟩

protected def ofFin {α} : {xs : List α} → Fin xs.length → Index xs
| _::_, ⟨0,_⟩ => head
| _::_, ⟨i+1,h⟩ => tail (Index.ofFin ⟨i, Nat.lt_of_succ_lt_succ h⟩)

theorem ofFin_toFin {α} {xs : List α} (i : Index xs) : Index.ofFin i.toFin = i := by
  induction xs with
  | nil => cases i
  | cons x xs ih =>
    cases i with
    | head => rfl
    | tail i =>
      apply congrArg tail
      exact ih ..

theorem toNat_ofFin {α} {xs : List α} (i : Fin xs.length) : (Index.ofFin i).toNat = i.val := by
  induction xs with
  | nil => cases i; contradiction
  | cons x xs ih =>
    match i with
    | ⟨0,_⟩ => rfl
    | ⟨i+1,h⟩ =>
      apply congrArg Nat.succ
      rw [ih]; rfl

theorem toFin_ofFin {α} {xs : List α} (i : Fin xs.length) : (Index.ofFin i).toFin = i := by
  apply Fin.eq_of_val_eq
  apply toNat_ofFin

def equivFin {α} (xs : List α) : Equiv (Index xs) (Fin xs.length) where
  fwd := Index.toFin
  rev := Index.ofFin
  spec {_ _} := by
    constr
    · intro | rfl => exact ofFin_toFin ..
    · intro | rfl => exact toFin_ofFin ..

theorem val_ofFin_eq_get {α} (xs : List α) (i : Fin xs.length) : (Index.ofFin i).val = xs.get i := by
  induction xs with
  | nil => cases i; contradiction
  | cons x xs ih =>
    match i with
    | ⟨0, _⟩ => rfl
    | ⟨i+1, hi⟩ =>
      unfold Index.ofFin
      rw [val_tail, ih]
      rfl

end Index
