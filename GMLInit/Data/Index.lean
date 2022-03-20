import GMLInit.Data.Basic
import GMLInit.Meta.Basic

namespace Index

instance {α} (a : α) (as : List α) : Inhabited (Index (a :: as)) := ⟨head⟩

protected abbrev recNilOn {α} {motive : Index ([]:List α) → Sort _} (i : Index ([]:List α)) : motive i := nomatch i

protected abbrev casesNilOn {α} {motive : Index ([]:List α) → Sort _} (i : Index ([]:List α)) : motive i := nomatch i

lemma val_head {α} (a : α) (as : List α) : (@head α a as).val = a := rfl

@[simp] lemma val_tail {α} (a : α) (as : List α) (i : Index as) : (@tail α a as i).val = i.val := rfl

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
    split at h
    next => contradiction
    next => contradiction
    next hh ht =>
      cases i with
      | head => exact hh
      | tail i => exact H _ ht

end Index
