import GMLInit.Data.Basic
import GMLInit.Meta.Basic

namespace Index

instance {α} (a : α) (as : List α) : Inhabited (Index (a :: as)) := ⟨head⟩

protected abbrev recNilOn {α} {motive : Index ([]:List α) → Sort _} (i : Index ([]:List α)) : motive i := nomatch i

protected abbrev casesNilOn {α} {motive : Index ([]:List α) → Sort _} (i : Index ([]:List α)) : motive i := nomatch i

@[simp] lemma val_head {α} (a : α) (as : List α) : (@head α a as).val = a := rfl

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

end Index
