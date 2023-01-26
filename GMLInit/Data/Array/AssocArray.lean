import GMLInit.Data.Array.Basic
import GMLInit.Data.Array.KeyedArray

structure AssocArray (α β : Type _) [BEq α] extends KeyedArray (α × β) Prod.fst

namespace AssocArray
variable {α β} [BEq α] [EquivBEq α] (a : AssocArray α β)

@[inline] def find? (key : α) : Option β :=
  match a.toKeyedArray.find? key with
  | some (_, value) => some value
  | none => none

@[inline] def insert (key : α) (value : β) : AssocArray α β where
  toKeyedArray := a.toKeyedArray.insert (key, value)

theorem find?_insert (key : α) (value : β) : (a.insert key value).find? key = some value := by
  unfold find? insert; rw [a.toKeyedArray.find?_insert (key, value)]

theorem find?_insert_bne {key : α} {value : β} {k : α} : k != key → (a.insert key value).find? k = a.find? k := by
  intro h; unfold find? insert; rw [a.toKeyedArray.find?_insert_bne h]

@[inline] def erase (key : α) : AssocArray α β where
  toKeyedArray := a.toKeyedArray.erase key

theorem find?_erase (key : α) : (a.erase key).find? key = none := by
  unfold find? erase; rw [a.toKeyedArray.find?_erase key]

theorem find?_erase_bne {key : α} {k : α} : k != key → (a.erase key).find? k = a.find? k := by
  intro h; unfold find? erase; rw [a.toKeyedArray.find?_erase_bne h]

end AssocArray

