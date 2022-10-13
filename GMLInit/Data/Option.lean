import GMLInit.Data.Basic
import GMLInit.Data.Equiv
import GMLInit.Meta.Basic

namespace Option

@[simp] lemma none_map {α β} (f : α → β) : none.map f = none := rfl

@[simp] lemma some_map {α β} (f : α → β) (a : α) : (some a).map f = some (f a) := rfl

@[simp] lemma id_map {α} (a : Option α) : a.map id = a := by cases a <;> rfl

def equiv {α β} (e : Equiv α β) : Equiv (Option α) (Option β) where
  fwd
  | some x => some (e.fwd x)
  | none => none
  rev
  | some x => some (e.rev x)
  | none => none
  spec := by
    intro
    | some _, some _ =>
      constr
      · intro | rfl => clean; rw [e.rev_fwd]
      · intro | rfl => clean; rw [e.fwd_rev]
    | some _, none => constr <;> (intro h; cases h)
    | none, some _ => constr <;> (intro h; cases h)
    | none, none => constr <;> intro | rfl => rfl

end Option
